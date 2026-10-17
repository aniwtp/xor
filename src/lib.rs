//! Obfuscation middleware with replay protection and built-in compression.
//!
//! Goal: make bodies unreadable at a glance and small on the wire, at near
//! zero CPU cost on both ends. This is obfuscation, not encryption: the u32
//! key travels in the `x-key` header next to the body, confidentiality must
//! come from TLS.
//!
//! # Wire format (v2)
//!
//! `frame = xor_keystream(key, MAGIC(2) || MODE(1) || body)`
//!
//! * `MODE_RAW`     — `body` is the payload as is (tiny or incompressible).
//! * `MODE_DEFLATE` — `body` is raw deflate (RFC 1951) of the payload.
//!
//! Compression runs *before* obfuscation: any keyed byte transform destroys
//! compressibility. Raw deflate is what every client already has natively
//! (Node `zlib.*RawSync`, browsers `DecompressionStream('deflate-raw')`).
//!
//! # Keystream
//!
//! Counter mode over a 32-bit mixer: `ks[i] = fmix32(seed + (i + 1) * GAMMA)`
//! with `seed = fmix32(key)`, applied to little-endian u32 words (the tail is
//! xored with the leading bytes of the next word). Symmetric, no per-key
//! setup, no tables, no allocation; the same code encodes and decodes.
//!
//! # Replay protection
//!
//! Lock-free, u32 keys, double-buffered rotating bitsets: a key is accepted at
//! most once per `rotation_interval`..`2 * rotation_interval` window.

use std::cell::RefCell;
use std::pin::Pin;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, LazyLock};
use std::task::{Context, Poll};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use flate2::{Compress, Compression, Decompress, FlushCompress, FlushDecompress, Status};
use ntex::SharedCfg;
use ntex::http::body::{Body, ResponseBody};
use ntex::http::error::PayloadError;
use ntex::http::header::{HeaderMap, HeaderName, HeaderValue};
use ntex::http::{Method, Payload, StatusCode};
use ntex::service::{Middleware, Service, ServiceCtx};
use ntex::util::{Bytes, Stream};
use ntex::web::{ErrorRenderer, WebRequest, WebResponse};

pub const KEY_HEADER: &str = "x-key";

/// Лимит и на размер тела запроса (кадр), и на размер распакованного
/// payload (защита от deflate-бомб).
pub const MAX_BODY_LEN: usize = 8 * 1024 * 1024;

const MAGIC: [u8; 2] = [0xC0, 0xDE];
const MODE_RAW: u8 = 0;
const MODE_DEFLATE: u8 = 1;
const HEADER_LEN: usize = 3;

/// Короче этого сжатие не окупается (оверхед инициализации > выигрыш).
const MIN_COMPRESS_LEN: usize = 32;
/// До порога — лучшее сжатие (запросы/ответы API обычно мелкие), выше —
/// быстрый уровень, чтобы большие ответы не держали воркер.
const LEVEL_SMALL: u32 = 6;
const LEVEL_LARGE: u32 = 4;
const LEVEL_THRESHOLD: usize = 64 * 1024;

// ---------------------------------------------------------------------------
// Keystream codec
// ---------------------------------------------------------------------------

const GAMMA: u32 = 0x9E3779B9;

/// murmur3 fmix32 — биекция на u32.
#[inline(always)]
fn fmix32(mut z: u32) -> u32 {
    z ^= z >> 16;
    z = z.wrapping_mul(0x85EBCA6B);
    z ^= z >> 13;
    z = z.wrapping_mul(0xC2B2AE35);
    z ^ (z >> 16)
}

/// Накладывает keystream на `data` (кодирование и декодирование — одна и
/// та же операция).
pub fn xor_in_place(data: &mut [u8], key: u32) {
    let seed = fmix32(key);
    let (words, tail) = data.as_chunks_mut::<4>();
    for (i, word) in words.iter_mut().enumerate() {
        let ks = fmix32(seed.wrapping_add(GAMMA.wrapping_mul(i as u32 + 1)));
        *word = (u32::from_le_bytes(*word) ^ ks).to_le_bytes();
    }
    if !tail.is_empty() {
        let ks = fmix32(seed.wrapping_add(GAMMA.wrapping_mul(words.len() as u32 + 1))).to_le_bytes();
        for (b, k) in tail.iter_mut().zip(ks) {
            *b ^= k;
        }
    }
}

// ---------------------------------------------------------------------------
// Frame: header + (raw | deflate), keystream over everything
// ---------------------------------------------------------------------------

thread_local! {
    // Воркеры ntex — потоки: переиспользуем состояние zlib на поток
    // (reset дешевле, чем аллокация ~256 КБ окна/хеш-таблиц на запрос).
    static DEFLATE: RefCell<Compress> = RefCell::new(Compress::new(Compression::new(LEVEL_SMALL), false));
    static INFLATE: RefCell<Decompress> = RefCell::new(Decompress::new(false));
}

/// Raw-deflate `payload` в `out` (в пределах его ёмкости). `true` — влезло
/// целиком.
fn deflate_into(payload: &[u8], out: &mut Vec<u8>) -> bool {
    DEFLATE.with(|c| {
        let mut c = c.borrow_mut();
        c.reset();
        let level = if payload.len() <= LEVEL_THRESHOLD { LEVEL_SMALL } else { LEVEL_LARGE };
        if c.set_level(Compression::new(level)).is_err() {
            return false;
        }
        matches!(c.compress_vec(payload, out, FlushCompress::Finish), Ok(Status::StreamEnd))
    })
}

/// Raw-inflate `src`. `None` — битый поток, обрыв или результат > `MAX_BODY_LEN`.
fn inflate(src: &[u8]) -> Option<Vec<u8>> {
    INFLATE.with(|d| {
        let mut d = d.borrow_mut();
        d.reset(false);
        let mut out = Vec::with_capacity((src.len() * 4).clamp(512, MAX_BODY_LEN + 1));
        loop {
            let consumed = d.total_in() as usize;
            let status = d.decompress_vec(&src[consumed..], &mut out, FlushDecompress::Finish).ok()?;
            if out.len() > MAX_BODY_LEN {
                return None;
            }
            match status {
                Status::StreamEnd => return Some(out),
                // Нет места под вывод — растим (до лимита); иначе вход оборван.
                _ if out.len() == out.capacity() => {
                    out.reserve(out.capacity().min(MAX_BODY_LEN + 1 - out.len()));
                }
                _ => return None,
            }
        }
    })
}

/// Строит кадр: сжимает, если это даёт выигрыш, иначе кладёт payload как есть.
pub fn encode_frame(payload: &[u8], key: u32) -> Vec<u8> {
    // Ёмкость = размер raw-кадра: не влезло при сжатии — значит выигрыша нет.
    let mut out = Vec::with_capacity(HEADER_LEN + payload.len());
    out.extend_from_slice(&MAGIC);
    out.push(MODE_DEFLATE);

    let deflated = payload.len() >= MIN_COMPRESS_LEN
        && deflate_into(payload, &mut out)
        && out.len() < HEADER_LEN + payload.len();
    if !deflated {
        out.truncate(HEADER_LEN);
        out[HEADER_LEN - 1] = MODE_RAW;
        out.extend_from_slice(payload);
    }

    xor_in_place(&mut out, key);
    out
}

/// Обратное к `encode_frame`, потребляет буфер (без лишней копии).
/// `None` — неверный ключ, битый кадр или распакованный размер > `MAX_BODY_LEN`.
pub fn decode_frame_owned(mut frame: Vec<u8>, key: u32) -> Option<Vec<u8>> {
    if frame.len() < HEADER_LEN {
        return None;
    }
    xor_in_place(&mut frame, key);
    if frame[..MAGIC.len()] != MAGIC {
        return None;
    }
    match frame[HEADER_LEN - 1] {
        MODE_RAW if frame.len() - HEADER_LEN <= MAX_BODY_LEN => {
            frame.copy_within(HEADER_LEN.., 0);
            frame.truncate(frame.len() - HEADER_LEN);
            Some(frame)
        }
        MODE_DEFLATE => inflate(&frame[HEADER_LEN..]),
        _ => None,
    }
}

/// Как `decode_frame_owned`, но не трогает входной буфер.
pub fn decode_frame(frame: &[u8], key: u32) -> Option<Vec<u8>> {
    decode_frame_owned(frame.to_vec(), key)
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

fn now_secs() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

impl XorState {
    /// * `bitset_words` - размер одного буфера в u64-словах (> 0).
    ///   65536 = 512 КБ на буфер = 4.2 млн бит.
    /// * `rotation_interval` - период смены буферов (например, 60 секунд).
    ///   Ротация ленивая: выполняется на пути запросов, фоновых задач нет.
    pub fn new(bitset_words: usize, rotation_interval: Duration) -> Self {
        assert!(bitset_words > 0, "bitset_words must be > 0");
        let new_bitset = || (0..bitset_words).map(|_| AtomicU64::new(0)).collect::<Vec<_>>();
        let inner = Arc::new(XorInner {
            bitsets: [new_bitset(), new_bitset()],
            active_idx: AtomicUsize::new(0),
            resp_prng_state: AtomicU32::new(random_u32_seed()),
            last_rotation: AtomicU64::new(now_secs()),
            rotation_secs: rotation_interval.as_secs().max(1),
        });
        Self { inner }
    }

    /// Позиция ключа в битсете: (индекс слова, маска из двух бит в этом слове).
    ///
    /// Два бита в одном u64-слове (blocked bloom, k=2): ложный реплей
    /// (коллизия честного ключа) на порядок реже, чем при одном бите, а
    /// проверка и пометка остаются одной атомарной операцией над словом.
    fn slot(&self, key: u32) -> (usize, u64) {
        let h1 = fmix32(key);
        let h2 = fmix32(h1 ^ GAMMA);
        let word = ((u64::from(h1) * self.inner.bitsets[0].len() as u64) >> 32) as usize;
        let b1 = h2 & 63;
        let b2 = (b1 + 1 + (h2 >> 6) % 63) & 63;
        (word, 1u64 << b1 | 1u64 << b2)
    }

    fn rotate_bitsets(&self) {
        let next = self.inner.active_idx.load(Ordering::Relaxed) ^ 1;

        // 1. Очищаем "неактивный" битсет (пока в него никто не пишет)
        for word in &self.inner.bitsets[next] {
            word.store(0, Ordering::Relaxed);
        }

        // 2. Атомарно переключаем активный индекс.
        // Теперь все новые claim пойдут в свежий пустой битсет.
        self.inner.active_idx.store(next, Ordering::Release);
    }

    /// Ленивая ротация: вызывается на пути запросов, реально выполняется
    /// не чаще одного раза за интервал (CAS на timestamp).
    fn maybe_rotate(&self) {
        let now = now_secs();
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

    /// Дешёвая предпроверка (без пометки): ключ не встречался в текущем и
    /// предыдущем окне. Авторитетна только `claim`.
    pub fn is_fresh(&self, key: u32) -> bool {
        let (word, mask) = self.slot(key);
        // Проверяем оба буфера: текущий и предыдущий (реплеи сразу после ротации).
        self.inner.bitsets.iter().all(|b| b[word].load(Ordering::Relaxed) & mask != mask)
    }

    /// Атомарно помечает ключ использованным. `true` — ключ был свежим и
    /// теперь заявлен нами; `false` — реплей (в т.ч. гонка двух одновременных
    /// запросов с одним ключом: выигрывает ровно один).
    pub fn claim(&self, key: u32) -> bool {
        let (word, mask) = self.slot(key);
        let active = self.inner.active_idx.load(Ordering::Acquire);

        if self.inner.bitsets[active ^ 1][word].load(Ordering::Relaxed) & mask == mask {
            return false;
        }
        self.inner.bitsets[active][word].fetch_or(mask, Ordering::Relaxed) & mask != mask
    }

    pub fn next_resp_key(&self) -> u32 {
        let x = self.inner.resp_prng_state.fetch_add(GAMMA, Ordering::Relaxed);
        fmix32(x)
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

enum DrainError {
    TooLarge,
    Io,
}

/// Собирает тело запроса целиком в `Vec` (его же потом декодируем на месте).
/// `size_hint` — Content-Length, если есть.
async fn drain_payload(pl: &mut Payload, size_hint: usize) -> Result<Vec<u8>, DrainError> {
    let mut body = Vec::with_capacity(size_hint);
    while let Some(chunk) = pl.recv().await {
        let chunk = chunk.map_err(|_| DrainError::Io)?;
        if body.len().saturating_add(chunk.len()) > MAX_BODY_LEN {
            return Err(DrainError::TooLarge);
        }
        body.extend_from_slice(&chunk);
    }
    Ok(body)
}

/// Предсозданные заголовки: имена/значения валидируются один раз, а не на
/// каждый ответ.
struct Headers {
    key: HeaderName,
    cors: [(HeaderName, HeaderValue); 5],
}

static HEADERS: LazyLock<Headers> = LazyLock::new(|| {
    let h = |name: &'static str, value: &'static str| {
        (HeaderName::from_static(name), HeaderValue::from_static(value))
    };
    Headers {
        key: HeaderName::from_static(KEY_HEADER),
        cors: [
            h("access-control-allow-origin", "*"),
            h("access-control-allow-headers", "x-key, X-Session-Token, X-Team-Token, content-type"),
            h("access-control-allow-methods", "GET, POST, PUT, DELETE, OPTIONS"),
            h("access-control-max-age", "86400"),
            // Ключ ответа обязан быть ВИДИМ кросс-доменному JS: без expose-headers
            // браузер отдаёт из `x-key` только safelisted-заголовки, клиент не может
            // декодировать кадр.
            h("access-control-expose-headers", "x-key"),
        ],
    }
});

/// CORS-заголовки для браузерных фронтов: токены едут заголовками
/// (`x-key`, `X-Session-Token`, `X-Team-Token`), кук нет — `*` достаточно.
/// Публичная: error_response хендлеры сервисов добавляют её вручную,
/// т.к. middleware не видит ответы ошибок.
pub fn with_cors(headers: &mut HeaderMap) {
    for (name, value) in &HEADERS.cors {
        headers.insert(name.clone(), value.clone());
    }
}

fn reject<Err: ErrorRenderer>(req: WebRequest<Err>, status: StatusCode) -> WebResponse {
    let mut res = req.into_response(ntex::http::Response::new(status));
    with_cors(res.headers_mut());
    res
}

/// Заменяет тело ответа XOR-кадром со свежим ключом (заголовок `x-key`).
/// Пустое тело остаётся пустым и без ключа.
fn encode_response(state: &XorState, mut res: WebResponse) -> WebResponse {
    let raw = match res.take_body() {
        ResponseBody::Body(Body::Bytes(b)) => b,
        // Стримовые тела отсеяны вызывающим до `take_body`.
        _ => Bytes::new(),
    };

    if raw.is_empty() {
        return res.map_body(|_head, _body| ResponseBody::Body(Body::Empty));
    }

    let key = state.next_resp_key();
    let frame = encode_frame(&raw, key);
    res = res.map_body(|_head, _body| ResponseBody::from(Body::from(frame)));
    res.headers_mut().insert(HEADERS.key.clone(), HeaderValue::from(key));
    res
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
        // напрямую): preflight закрываем здесь, остальным ставим заголовки внизу.
        if req.method() == Method::OPTIONS {
            let mut res = req.into_response(ntex::http::Response::new(StatusCode::NO_CONTENT));
            with_cors(res.headers_mut());
            return Ok(res);
        }

        self.state.maybe_rotate();

        let key: Option<u32> = req
            .headers()
            .get(KEY_HEADER)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.parse().ok());
        let size_hint = req
            .headers()
            .get(ntex::http::header::CONTENT_LENGTH)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(0);
        if size_hint > MAX_BODY_LEN {
            return Ok(reject(req, StatusCode::PAYLOAD_TOO_LARGE));
        }

        let mut payload = req.take_payload();
        let body = match drain_payload(&mut payload, size_hint).await {
            Ok(body) => body,
            Err(DrainError::TooLarge) => return Ok(reject(req, StatusCode::PAYLOAD_TOO_LARGE)),
            Err(DrainError::Io) => return Ok(reject(req, StatusCode::BAD_REQUEST)),
        };

        let clean_body = if body.is_empty() {
            Bytes::new()
        } else {
            let Some(k) = key else {
                return Ok(reject(req, StatusCode::BAD_REQUEST));
            };
            // Дешёвый отсев реплеев до распаковки; авторитетна `claim` ниже.
            if !self.state.is_fresh(k) {
                return Ok(reject(req, StatusCode::BAD_REQUEST));
            }
            let Some(decoded) = decode_frame_owned(body, k) else {
                return Ok(reject(req, StatusCode::BAD_REQUEST));
            };
            // Ключ сжигается только после успешного декодирования — мусор не
            // выжигает чужие ключи; claim атомарен, гонка двух реплеев невозможна.
            if !self.state.claim(k) {
                return Ok(reject(req, StatusCode::BAD_REQUEST));
            }
            Bytes::from(decoded)
        };

        req.set_payload(Payload::from_stream(OneShot(Some(clean_body))));
        let mut res = ctx.call(&self.service, req).await.map_err(Err::Container::from)?;

        // Стримовые тела (`ResponseBody::Other`) — не наши: байты идут клиенту
        // как есть (картинки, файлы). `take_body()` их бы обнулил, поэтому
        // проверяем вариант по ссылке ДО изъятия тела.
        if !matches!(res.response().body(), ResponseBody::Other(_)) {
            res = encode_response(&self.state, res);
        }
        with_cors(res.headers_mut());
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ntex::web::{self, test};

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

    fn noise(n: usize) -> Vec<u8> {
        let mut st = 12345u32;
        (0..n)
            .map(|_| {
                st = st.wrapping_add(GAMMA);
                fmix32(st) as u8
            })
            .collect()
    }

    #[test]
    fn keystream_is_involution_for_all_lengths() {
        for key in [0u32, 1, 0xDEADBEEF, 0xFFFFFFFF] {
            for len in 0..70 {
                let orig = noise(len);
                let mut data = orig.clone();
                xor_in_place(&mut data, key);
                if len >= 4 {
                    assert_ne!(data, orig);
                }
                xor_in_place(&mut data, key);
                assert_eq!(data, orig, "key {key} len {len}");
            }
        }
    }

    #[test]
    fn keystream_differs_per_key_and_has_no_short_period() {
        let zeros = vec![0u8; 256];
        let (mut a, mut b) = (zeros.clone(), zeros.clone());
        xor_in_place(&mut a, 1);
        xor_in_place(&mut b, 2);
        assert_ne!(a, b);
        assert_ne!(a[..32], a[32..64]);
    }

    #[test]
    fn frame_roundtrip_all_sizes() {
        for len in [0usize, 1, 2, 3, 31, 32, 33, 100, 4096, 70_000] {
            for payload in [vec![7u8; len], noise(len)] {
                for key in [0u32, 42, 0xCAFEBABE] {
                    let frame = encode_frame(&payload, key);
                    assert_eq!(decode_frame(&frame, key), Some(payload.clone()), "len {len}");
                    assert_eq!(decode_frame_owned(frame, key), Some(payload.clone()));
                }
            }
        }
    }

    #[test]
    fn tiny_and_incompressible_stay_raw() {
        let tiny = encode_frame(b"hello", 9);
        assert_eq!(tiny.len(), HEADER_LEN + 5);

        let n = noise(4096);
        let frame = encode_frame(&n, 9);
        assert_eq!(frame.len(), HEADER_LEN + n.len(), "incompressible must not grow beyond header");
    }

    #[test]
    fn wrong_key_fails() {
        for payload in [&b"hello world"[..], &[1u8; 1000][..]] {
            let frame = encode_frame(payload, 42);
            assert!(decode_frame(&frame, 43).is_none());
        }
    }

    #[test]
    fn garbage_frames_rejected() {
        assert!(decode_frame(&[], 1).is_none());
        assert!(decode_frame(&[1, 2], 1).is_none());

        // валидный заголовок, но оборванный deflate
        let mut frame = encode_frame(&sample_plaintext(), 5);
        frame.truncate(frame.len() / 2);
        assert!(decode_frame(&frame, 5).is_none());

        // неизвестный режим
        let mut bad = [MAGIC[0], MAGIC[1], 9, 0, 0].to_vec();
        xor_in_place(&mut bad, 5);
        assert!(decode_frame(&bad, 5).is_none());
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

    #[test]
    fn deflate_bomb_rejected() {
        let bomb = vec![0u8; MAX_BODY_LEN + 1];
        let frame = encode_frame(&bomb, 7);
        assert!(frame.len() < 64 * 1024, "bomb must be tiny on the wire: {}", frame.len());
        assert!(decode_frame(&frame, 7).is_none());
        // ровно на лимите — проходит
        let ok = vec![0u8; MAX_BODY_LEN];
        assert_eq!(decode_frame(&encode_frame(&ok, 7), 7).map(|v| v.len()), Some(MAX_BODY_LEN));
    }

    #[test]
    fn claim_is_single_use_and_rotates() {
        let state = XorState::new(16, Duration::from_secs(60));
        assert!(state.is_fresh(5));
        assert!(state.claim(5));
        assert!(!state.is_fresh(5));
        assert!(!state.claim(5));

        // после одной ротации ключ ещё помнится (предыдущий буфер)…
        state.rotate_bitsets();
        assert!(!state.claim(5));
        // …после второй — забыт.
        state.rotate_bitsets();
        assert!(state.claim(5));
    }

    #[test]
    fn claim_race_has_single_winner() {
        let state = XorState::new(16, Duration::from_secs(60));
        let wins: usize = (0..8)
            .map(|_| {
                let s = state.clone();
                std::thread::spawn(move || s.claim(99))
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|h| usize::from(h.join().unwrap()))
            .sum();
        assert_eq!(wins, 1);
    }

    /// ~20k честных запросов в окне при боевом размере битсета: ложных
    /// реплеев (коллизий) должно быть единицы, а не десятки (было ~0.3%).
    #[test]
    fn false_replay_rate_is_low() {
        let state = XorState::new(65536, Duration::from_secs(60));
        let mut st = 1u32;
        let rejected = (0..20_000)
            .filter(|_| {
                st = st.wrapping_add(GAMMA);
                !state.claim(fmix32(st ^ 0xABCD))
            })
            .count();
        assert!(rejected < 20, "false replays: {rejected}/20000");
    }

    #[test]
    fn cors_exposes_response_key() {
        // Кросс-доменный JS читает только safelisted-заголовки: без
        // expose-headers клиент не увидит `x-key` и не декодирует кадр.
        let mut headers = HeaderMap::new();
        with_cors(&mut headers);
        assert_eq!(headers.get("access-control-expose-headers").unwrap(), "x-key");
        assert_eq!(headers.get("access-control-allow-origin").unwrap(), "*");
    }

    /// Стримовое (`ResponseBody::Other`) тело — не наше: байты обязаны дойти
    /// до клиента как есть, без XOR-кадра. Регресс: `take_body()` их обнулял.
    #[ntex::test]
    async fn other_body_passes_through() {
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
        assert_eq!(resp.status(), StatusCode::OK);
        assert_eq!(resp.headers().get("content-type").unwrap(), "image/png");
        let body = test::read_body(resp).await;
        assert_eq!(body.as_ref(), b"PNGDATA", "тело искажено middleware");
    }

    /// Эхо-эндпоинт: запрос -> декод -> хендлер -> кадр с `x-key` ответа;
    /// повтор того же ключа -> 400.
    #[ntex::test]
    async fn middleware_roundtrip_and_replay() {
        let state = XorState::new(1024, Duration::from_secs(60));
        let app = test::init_service(
            web::App::new().middleware(XorMiddleware::new(state)).service(
                web::resource("/echo")
                    .route(web::post().to(|body: Bytes| async move { web::HttpResponse::Ok().body(body) })),
            ),
        )
        .await;

        let key = 0x1234_5678u32;
        // эхо-хендлер: дефолтный лимит web::Bytes-экстрактора < размера sample
        let plain = sample_plaintext()[..20_000].to_vec();
        let frame = encode_frame(&plain, key);
        let call = |frame: Vec<u8>| {
            test::TestRequest::post()
                .uri("/echo")
                .header(KEY_HEADER, key.to_string())
                .set_payload(frame)
                .to_request()
        };

        let resp = test::call_service(&app, call(frame.clone())).await;
        assert_eq!(resp.status(), StatusCode::OK);
        let resp_key: u32 = resp.headers().get(KEY_HEADER).unwrap().to_str().unwrap().parse().unwrap();
        let body = test::read_body(resp).await;
        assert_eq!(decode_frame(&body, resp_key).unwrap(), plain);

        let replay = test::call_service(&app, call(frame)).await;
        assert_eq!(replay.status(), StatusCode::BAD_REQUEST);

        let no_key = test::TestRequest::post().uri("/echo").set_payload(vec![1, 2, 3]).to_request();
        assert_eq!(test::call_service(&app, no_key).await.status(), StatusCode::BAD_REQUEST);
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
        // Пороги осмысленны только для оптимизированной сборки.
        if !cfg!(debug_assertions) {
            assert!(enc_mb_s > 100.0, "encode too slow: {enc_mb_s}");
            assert!(dec_mb_s > 500.0, "decode too slow: {dec_mb_s}");
        }
    }
}
