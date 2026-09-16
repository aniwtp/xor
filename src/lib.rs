//! Obfuscation middleware with replay protection and built-in compression.
//!
//! Wire format: MAGIC(4) + raw-deflate(payload), obfuscated with a keyed
//! byte codec. Compression happens *before* obfuscation: any keyed byte
//! transform destroys compressibility, so the compressor must see the
//! plaintext. This also shrinks traffic instead of just hiding it.
//!
//! The codec is a seeded S-box + slowly rotating XOR mask: bijective per
//! position class, O(1 lookup + xor) per byte, trivial to reimplement on the
//! client (see `Codec::decode` / `decode_body`).
//!
//! Lock-free, u32 keys, Double-Buffered rotating bitsets for replay
//! protection.

use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::task::{Context, Poll};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use ntex::SharedCfg;
use ntex::http::body::{Body, ResponseBody};
use ntex::http::error::PayloadError;
use ntex::http::header::{HeaderName, HeaderValue};
use ntex::http::{Payload, StatusCode};
use ntex::service::{Middleware, Service, ServiceCtx};
use ntex::util::{Bytes, Stream};
use ntex::web::{ErrorRenderer, WebRequest, WebResponse};

use miniz_oxide::deflate::compress_to_vec;
use miniz_oxide::inflate::decompress_to_vec;

const MAGIC_LEN: usize = 4;
const MAGIC: [u8; MAGIC_LEN] = [0xC0, 0xDE, 0x5E, 0xED];

/// Уровень сжатия miniz_oxide: 1 (быстро) … 10 (максимально). 4 — быстрый
/// режим, сопоставимый с flate2's Compression::fast.
const COMPRESSION_LEVEL: u8 = 4;

pub const KEY_HEADER: &str = "x-key";

pub const MAX_BODY_LEN: usize = 8 * 1024 * 1024;

// ---------------------------------------------------------------------------
// Codec: keyed, bijective, cheap byte obfuscation
// ---------------------------------------------------------------------------

/// Биективный кодек, производный от u32-ключа.
///
/// `encode`: b -> sbox[b] ^ mask[i % 32]
/// `decode`: b -> inv[b ^ mask[i % 32]]
pub struct Codec {
    sbox: [u8; 256],
    inv: [u8; 256],
    mask: [u8; MASK_LEN],
}

const MASK_LEN: usize = 32;
const SPLITMIX32_GAMMA: u32 = 0x9E3779B9;

fn splitmix32_finalize(mut z: u32) -> u32 {
    z ^= z >> 16;
    z = z.wrapping_mul(0x85EBCA6B);
    z ^= z >> 13;
    z = z.wrapping_mul(0xC2B2AE35);
    z ^ (z >> 16)
}

fn splitmix32(state: &mut u32) -> u32 {
    *state = state.wrapping_add(SPLITMIX32_GAMMA);
    splitmix32_finalize(*state)
}

impl Codec {
    pub fn new(key: u32) -> Self {
        let mut st = key;

        let mut sbox = [0u8; 256];
        for (i, v) in sbox.iter_mut().enumerate() {
            *v = i as u8;
        }
        // Fisher-Yates поверх splitmix32 — детерминированная перестановка алфавита.
        for i in (1..256).rev() {
            let j = (splitmix32(&mut st) as usize) % (i + 1);
            sbox.swap(i, j);
        }

        let mut inv = [0u8; 256];
        for (i, &v) in sbox.iter().enumerate() {
            inv[v as usize] = i as u8;
        }

        let mut mask = [0u8; MASK_LEN];
        for m in mask.iter_mut() {
            *m = splitmix32(&mut st) as u8;
        }

        Self { sbox, inv, mask }
    }

    #[inline]
    pub fn encode(&self, data: &mut [u8]) {
        for (i, b) in data.iter_mut().enumerate() {
            *b = self.sbox[*b as usize] ^ self.mask[i & (MASK_LEN - 1)];
        }
    }

    #[inline]
    pub fn decode(&self, data: &mut [u8]) {
        for (i, b) in data.iter_mut().enumerate() {
            *b = self.inv[(*b ^ self.mask[i & (MASK_LEN - 1)]) as usize];
        }
    }
}

/// Кодирование с ключом (хелпер для клиентской стороны).
pub fn encode_body(data: &mut [u8], key: u32) {
    Codec::new(key).encode(data);
}

/// Декодирование с ключом (хелпер для клиентской стороны).
pub fn decode_body(data: &mut [u8], key: u32) {
    Codec::new(key).decode(data);
}

/// Полный формат кадра: MAGIC + raw-deflate(payload), всё закодировано ключом.
pub fn encode_frame(payload: &[u8], key: u32) -> Vec<u8> {
    let frame = compress_to_vec(payload, COMPRESSION_LEVEL);

    let mut out = Vec::with_capacity(frame.len() + MAGIC_LEN);
    out.extend_from_slice(&MAGIC);
    out.extend_from_slice(&frame);
    Codec::new(key).encode(&mut out);
    out
}

/// Обратное к `encode_frame`. Возвращает распакованный payload.
pub fn decode_frame(frame: &[u8], key: u32) -> Option<Vec<u8>> {
    if frame.len() < MAGIC_LEN {
        return None;
    }
    let mut buf = frame.to_vec();
    Codec::new(key).decode(&mut buf);
    if buf[..MAGIC_LEN] != MAGIC {
        return None;
    }

    let decompressed = decompress_to_vec(&buf[MAGIC_LEN..]).ok()?;
    Some(decompressed)
}

// ---------------------------------------------------------------------------
// Lock-Free Double-Buffered Bitset
// ---------------------------------------------------------------------------

struct XorInner {
    /// Два битсета для ротации (текущий и предыдущий).
    bitsets: [Vec<AtomicU64>; 2],
    /// Индекс активного битсета (0 или 1).
    active_idx: AtomicUsize,
    /// Lock-free генератор ключей ответов.
    resp_prng_state: AtomicU32,
    /// Размер одного битсета в u64 словах.
    words_len: usize,
    /// Секунды UNIX последней ротации.
    last_rotation: AtomicU64,
    /// Интервал ротации в секундах.
    rotation_secs: u64,
}

#[derive(Clone)]
pub struct XorState {
    inner: Arc<XorInner>,
}

fn random_u32_seed() -> u32 {
    let mut buf = [0u8; 4];
    getrandom::fill(&mut buf).expect("failed to seed response-key PRNG");
    u32::from_le_bytes(buf)
}

impl XorState {
    /// Создает стейт и запускает фоновую ротацию (вызывать внутри ntex worker'а)
    ///
    /// * `bitset_words` - размер одного буфера. 65536 = 512 КБ памяти = 4.1 млн бит.
    /// * `rotation_interval` - как часто сбрасывать старые ключи (например, 60 секунд).
    pub fn new(bitset_words: usize, rotation_interval: Duration) -> Self {
        let mut b1 = Vec::with_capacity(bitset_words);
        let mut b2 = Vec::with_capacity(bitset_words);
        for _ in 0..bitset_words {
            b1.push(AtomicU64::new(0));
            b2.push(AtomicU64::new(0));
        }

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        let rotation_secs = rotation_interval.as_secs().max(1);
        let inner = Arc::new(XorInner {
            bitsets: [b1, b2],
            active_idx: AtomicUsize::new(0),
            resp_prng_state: AtomicU32::new(random_u32_seed()),
            words_len: bitset_words,
            last_rotation: AtomicU64::new(now),
            rotation_secs,
        });
        Self { inner }
    }

    fn rotate_bitsets(&self) {
        let current = self.inner.active_idx.load(Ordering::Relaxed);
        let next = current ^ 1; // меняем 0 на 1 или 1 на 0

        // 1. Очищаем "неактивный" битсет (пока в него никто не пишет)
        for word in &self.inner.bitsets[next] {
            word.store(0, Ordering::Relaxed);
        }

        // 2. Атомарно переключаем активный индекс.
        // Теперь все новые mark_used пойдут в свежий пустой битсет.
        self.inner.active_idx.store(next, Ordering::Release);
    }

    /// Ленивая ротация: вызывается на пути запросов, реально выполняется
    /// не чаще одного раза за интервал (CAS на timestamp).
    fn maybe_rotate(&self) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        let last = self.inner.last_rotation.load(Ordering::Relaxed);
        if now.saturating_sub(last) < self.inner.rotation_secs {
            return;
        }
        if self
            .inner
            .last_rotation
            .compare_exchange(last, now, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            self.rotate_bitsets();
        }
    }

    pub fn is_fresh(&self, key: u32) -> bool {
        let bit_index = key as usize % (self.inner.words_len * 64);
        let word_idx = bit_index / 64;
        let mask = 1 << (bit_index % 64);

        let active = self.inner.active_idx.load(Ordering::Relaxed);
        let inactive = active ^ 1;

        // Проверяем текущий буфер
        if (self.inner.bitsets[active][word_idx].load(Ordering::Relaxed) & mask) != 0 {
            return false;
        }

        // Проверяем предыдущий буфер (чтобы защититься от реплеев сразу после ротации)
        if (self.inner.bitsets[inactive][word_idx].load(Ordering::Relaxed) & mask) != 0 {
            return false;
        }

        true
    }

    pub fn mark_used(&self, key: u32) {
        let bit_index = key as usize % (self.inner.words_len * 64);
        let word_idx = bit_index / 64;
        let mask = 1 << (bit_index % 64);

        let active = self.inner.active_idx.load(Ordering::Relaxed);

        // Пишем только в активный буфер
        self.inner.bitsets[active][word_idx].fetch_or(mask, Ordering::Relaxed);
    }

    pub fn next_resp_key(&self) -> u32 {
        let x = self.inner.resp_prng_state.fetch_add(SPLITMIX32_GAMMA, Ordering::Relaxed);
        splitmix32_finalize(x)
    }
}

// ---------------------------------------------------------------------------
// Helpers & Middleware Boilerplate
// ---------------------------------------------------------------------------

struct OneShot(Option<Bytes>);

impl Stream for OneShot {
    type Item = Result<Bytes, PayloadError>;

    fn poll_next(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        Poll::Ready(self.0.take().map(Ok))
    }
}

async fn drain_payload(pl: &mut Payload) -> Bytes {
    let mut body = Vec::new();
    while let Some(chunk) = pl.recv().await {
        if let Ok(b) = chunk {
            if body.len().saturating_add(b.len()) > MAX_BODY_LEN {
                continue;
            }
            body.extend_from_slice(&b);
        } else {
            break;
        }
    }
    Bytes::from(body)
}

fn body_to_bytes(body: &Body) -> Bytes {
    match body {
        Body::Bytes(b) => b.clone(),
        _ => Bytes::new(),
    }
}

fn bad_request<Err: ErrorRenderer>(req: WebRequest<Err>) -> WebResponse {
    let mut res = req.into_response(ntex::http::Response::new(StatusCode::BAD_REQUEST));
    with_cors(res.headers_mut());
    res
}

/// CORS-заголовки для браузерных фронтов: токены едут заголовками
/// (`x-key`, `X-Session-Token`, `X-Team-Token`), кук нет — `*` достаточно.
/// Публичная: error_response хендлеры сервисов добавляют её вручную,
/// т.к. middleware не видит ответы ошибок.
pub fn with_cors(headers: &mut ntex::http::header::HeaderMap) {
    headers.insert(
        HeaderName::from_static("access-control-allow-origin"),
        HeaderValue::from_static("*"),
    );
    headers.insert(
        HeaderName::from_static("access-control-allow-headers"),
        HeaderValue::from_static("x-key, X-Session-Token, X-Team-Token, content-type"),
    );
    headers.insert(
        HeaderName::from_static("access-control-allow-methods"),
        HeaderValue::from_static("GET, POST, PUT, DELETE, OPTIONS"),
    );
    headers.insert(
        HeaderName::from_static("access-control-max-age"),
        HeaderValue::from_static("86400"),
    );
    // Ключ ответа обязан быть ВИДИМ кросс-доменному JS: без expose-headers
    // браузер отдаёт из `x-key` только safelisted-заголовки, клиент не может
    // декодировать кадр («нет x-key в ответе»).
    headers.insert(
        HeaderName::from_static("access-control-expose-headers"),
        HeaderValue::from_static("x-key"),
    );
}

pub struct XorMiddleware {
    state: XorState,
}

impl XorMiddleware {
    pub fn new(state: XorState) -> Self {
        Self { state }
    }
}

impl<S> Middleware<S, SharedCfg> for XorMiddleware {
    type Service = XorService<S>;

    fn create(&self, service: S, _cfg: SharedCfg) -> Self::Service {
        XorService { service, state: self.state.clone() }
    }
}

pub struct XorService<S> {
    service: S,
    state: XorState,
}

impl<S, Err> Service<WebRequest<Err>> for XorService<S>
where
    S: Service<WebRequest<Err>, Response = WebResponse>,
    Err: ErrorRenderer,
    Err::Container: From<<S as Service<WebRequest<Err>>>::Error>,
{
    type Response = WebResponse;
    type Error = Err::Container;

    async fn ready(&self, ctx: ServiceCtx<'_, Self>) -> Result<(), Self::Error> {
        ctx.ready(&self.service).await.map_err(Into::into)
    }

    fn poll(&self, cx: &mut Context<'_>) -> Result<(), Self::Error> {
        self.service.poll(cx).map_err(Into::into)
    }

    async fn shutdown(&self) {
        self.service.shutdown().await;
    }

    async fn call(
        &self,
        mut req: WebRequest<Err>,
        ctx: ServiceCtx<'_, Self>,
    ) -> Result<WebResponse, Self::Error> {
        // CORS для браузерных фронтов (админка ходит на домены сервисов
        // напрямую): preflight закрываем здесь, простым запросам ставим
        // разрешающие заголовки внизу через `with_cors`.
        if req.method() == ntex::http::Method::OPTIONS {
            let mut res = req.into_response(ntex::http::Response::new(StatusCode::NO_CONTENT));
            with_cors(res.headers_mut());
            return Ok(res);
        }
        let key: Option<u32> = req
            .headers()
            .get(KEY_HEADER)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.parse().ok());

        let mut payload = req.take_payload();
        let body_bytes = drain_payload(&mut payload).await;

        let clean_body = if body_bytes.is_empty() {
            body_bytes
        } else {
            let Some(k) = key else {
                return Ok(bad_request(req));
            };

            if !self.state.is_fresh(k) {
                return Ok(bad_request(req));
            }

            let Some(dec) = decode_frame(&body_bytes, k) else {
                return Ok(bad_request(req));
            };

            self.state.mark_used(k);
            self.state.maybe_rotate();
            Bytes::from(dec)
        };

        req.set_payload(Payload::from_stream(OneShot(Some(clean_body))));
        let mut res = ctx.call(&self.service, req).await.map_err(Err::Container::from)?;

        // Стримовые тела (`ResponseBody::Other`) — не наши: их байты пойдут
        // клиенту как есть (картинки, файлы). `take_body()` их бы обнулил,
        // поэтому проверяем вариант по ссылке и выходим ДО изъятия тела.
        if matches!(res.response().body(), ResponseBody::Other(_)) {
            with_cors(res.headers_mut());
            return Ok(res);
        }

        let raw = match res.take_body() {
            ResponseBody::Body(b) => body_to_bytes(&b),
            // Недостижимо: выше поймали Other до take_body.
            ResponseBody::Other(_) => {
                with_cors(res.headers_mut());
                return Ok(res);
            },
        };

        if raw.is_empty() {
            with_cors(res.headers_mut());
            Ok(res.map_body(|_head, _body| ResponseBody::Body(Body::Empty)))
        } else {
            let rk = self.state.next_resp_key();
            let buf = encode_frame(&raw, rk);
            res = res.map_body(|_head, _body| ResponseBody::from(Body::from(buf)));
            if let Ok(val) = HeaderValue::from_str(&rk.to_string()) {
                res.headers_mut().insert(HeaderName::from_static(KEY_HEADER), val);
            }
            with_cors(res.headers_mut());
            Ok(res)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_plaintext() -> Vec<u8> {
        let mut v = Vec::new();
        for i in 0..20000u32 {
            let line = format!(
                "item_id={};title=Example Title {};price={}\n",
                i % 9973,
                i % 500,
                i % 40000
            );
            v.extend_from_slice(line.as_bytes());
        }
        v
    }

    #[test]
    fn roundtrip_all_keys() {
        for key in [0u32, 1, 0xDEADBEEF, 0xFFFFFFFF, 123456789] {
            let mut data = (0..=255u8).cycle().take(1000).collect::<Vec<u8>>();
            let orig = data.clone();
            encode_body(&mut data, key);
            assert_ne!(data, orig);
            decode_body(&mut data, key);
            assert_eq!(data, orig);
        }
    }

    #[test]
    fn frame_roundtrip() {
        let plain = sample_plaintext();
        for key in [0u32, 42, 0xCAFEBABE] {
            let frame = encode_frame(&plain, key);
            assert_eq!(decode_frame(&frame, key), Some(plain.clone()));
        }
    }

    #[test]
    fn wrong_key_fails() {
        let plain = b"hello world";
        let frame = encode_frame(plain, 42);
        assert!(decode_frame(&frame, 43).is_none());
    }

    #[test]
    fn frame_is_compressed() {
        let plain = sample_plaintext();
        let frame = encode_frame(&plain, 0xCAFEBABE);
        assert!(
            frame.len() < plain.len() / 3,
            "frame {} not compressed (plain {})",
            frame.len(),
            plain.len()
        );
    }

    /// Стримовое (`ResponseBody::Other`) тело — не наше: байты обязаны дойти
    /// до клиента как есть, без XOR-кадра. Регресс: `take_body()` их обнулял.
    #[ntex::test]
    async fn other_body_passes_through() {
        use ntex::http::body::Body;
        use ntex::web::{self, test};

        let state = XorState::new(1024, Duration::from_secs(60));
        let app = test::init_service(
            web::App::new().middleware(XorMiddleware::new(state)).service(
                web::resource("/img").route(web::get().to(|| async {
                    Ok::<_, web::Error>(
                        web::HttpResponse::Ok()
                            .content_type("image/png")
                            .body(Body::from_slice(b"PNGDATA"))
                            .into_body::<Body>(),
                    )
                })),
            ),
        )
        .await;

        let req = test::TestRequest::get().uri("/img").to_request();
        let resp = test::call_service(&app, req).await;
        assert_eq!(resp.status(), ntex::http::StatusCode::OK);
        assert_eq!(resp.headers().get("content-type").unwrap(), "image/png");
        let body = test::read_body(resp).await;
        assert_eq!(body.as_ref(), b"PNGDATA", "тело искажено middleware");
    }

    #[test]
    fn cors_exposes_response_key() {
        // Кросс-доменный JS читает только safelisted-заголовки: без
        // expose-headers клиент не увидит `x-key` и не декодирует кадр.
        let mut headers = ntex::http::header::HeaderMap::new();
        with_cors(&mut headers);
        let exposed = headers
            .get("access-control-expose-headers")
            .and_then(|v| v.to_str().ok())
            .unwrap_or("");
        assert_eq!(exposed, "x-key");
        assert_eq!(
            headers.get("access-control-allow-origin").unwrap(),
            "*"
        );
    }

    #[test]
    fn perf_smoke() {
        let plain = sample_plaintext();
        let n = 20;

        let t = std::time::Instant::now();
        let mut frame = Vec::new();
        for _ in 0..n {
            frame = encode_frame(&plain, 0xCAFEBABE);
        }
        let enc_mb_s = (plain.len() * n) as f64 / t.elapsed().as_secs_f64() / 1e6;

        let t = std::time::Instant::now();
        for _ in 0..n {
            assert!(decode_frame(&frame, 0xCAFEBABE).is_some());
        }
        let dec_mb_s = (plain.len() * n) as f64 / t.elapsed().as_secs_f64() / 1e6;

        println!("encode: {enc_mb_s:.0} MB/s, decode: {dec_mb_s:.0} MB/s");
        assert!(enc_mb_s > 50.0, "encode too slow: {enc_mb_s}");
        assert!(dec_mb_s > 50.0, "decode too slow: {dec_mb_s}");
    }
}
