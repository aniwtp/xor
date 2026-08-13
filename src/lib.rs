//! XOR obfuscation middleware with replay protection.
//!
//! Lock-free, u32 optimized, with Double-Buffered rotating bitsets
//! to prevent long-term collisions.

use std::fs::File;
use std::io::Read;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::task::{Context, Poll};
use std::time::Duration;

use ntex::SharedCfg;
use ntex::http::body::{Body, ResponseBody};
use ntex::http::error::PayloadError;
use ntex::http::header::{HeaderName, HeaderValue};
use ntex::http::{Payload, StatusCode};
use ntex::service::{Middleware, Service, ServiceCtx};
use ntex::util::{Bytes, Stream};
use ntex::web::{ErrorRenderer, WebRequest, WebResponse};

const MAGIC_LEN: usize = 4;
const MAGIC: [u8; MAGIC_LEN] = [0xC0, 0xDE, 0x5E, 0xED];

pub const KEY_HEADER: &str = "x-key";

// ---------------------------------------------------------------------------
// Crypto Primitives
// ---------------------------------------------------------------------------

fn xor_body(data: &mut [u8], seed: u32) {
    let mut state = seed;
    for chunk in data.chunks_mut(4) {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        let key = state.to_le_bytes();
        for (b, k) in chunk.iter_mut().zip(key.iter()) {
            *b ^= *k;
        }
    }
}

fn xor_check_magic(data: &mut [u8], seed: u32) -> bool {
    if data.len() < MAGIC_LEN {
        return false;
    }
    let mut state = seed;
    for (i, chunk) in data.chunks_mut(4).enumerate() {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        let key = state.to_le_bytes();
        for (b, k) in chunk.iter_mut().zip(key.iter()) {
            *b ^= *k;
        }
        if i == 0 && chunk != MAGIC {
            return false;
        }
    }
    true
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
}

#[derive(Clone)]
pub struct XorState {
    inner: Arc<XorInner>,
}

const SPLITMIX32_GAMMA: u32 = 0x9E3779B9;

fn splitmix32_finalize(mut z: u32) -> u32 {
    z ^= z >> 16;
    z = z.wrapping_mul(0x85EBCA6B);
    z ^= z >> 13;
    z = z.wrapping_mul(0xC2B2AE35);
    z ^ (z >> 16)
}

fn random_u32_seed() -> u32 {
    let mut buf = [0u8; 4];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut buf))
        .expect("failed to seed response-key PRNG");
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

        let inner = Arc::new(XorInner {
            bitsets: [b1, b2],
            active_idx: AtomicUsize::new(0),
            resp_prng_state: AtomicU32::new(random_u32_seed()),
            words_len: bitset_words,
        });

        let state = Self { inner };

        // Запускаем фоновую задачу для очистки старых ключей без блокировок
        let state_clone = state.clone();
        ntex::rt::spawn(async move {
            loop {
                ntex::time::sleep(rotation_interval).await;
                state_clone.rotate_bitsets();
            }
        });

        state
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
    let mut body = Bytes::new();
    while let Some(chunk) = pl.recv().await {
        if let Ok(b) = chunk {
            let mut v = Vec::with_capacity(body.len() + b.len());
            v.extend_from_slice(&body);
            v.extend_from_slice(&b);
            body = Bytes::from(v);
        } else {
            break;
        }
    }
    body
}

fn body_to_bytes(body: &Body) -> Bytes {
    match body {
        Body::Bytes(b) => b.clone(),
        _ => Bytes::new(),
    }
}

fn bad_request<Err: ErrorRenderer>(req: WebRequest<Err>) -> WebResponse {
    req.into_response(ntex::http::Response::new(StatusCode::BAD_REQUEST))
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

            let mut dec = body_bytes.to_vec();
            if !xor_check_magic(&mut dec, k) {
                return Ok(bad_request(req));
            }

            self.state.mark_used(k);
            Bytes::copy_from_slice(&dec[MAGIC_LEN..])
        };

        req.set_payload(Payload::from_stream(OneShot(Some(clean_body))));
        let mut res = ctx.call(&self.service, req).await.map_err(Err::Container::from)?;

        let raw = match res.take_body() {
            ResponseBody::Body(b) => body_to_bytes(&b),
            ResponseBody::Other(_) => return Ok(res),
        };

        if raw.is_empty() {
            Ok(res.map_body(|_head, _body| ResponseBody::Body(Body::Empty)))
        } else {
            let mut buf = raw.to_vec();
            let rk = self.state.next_resp_key();
            xor_body(&mut buf, rk);

            res = res.map_body(|_head, _body| ResponseBody::from(Body::from(buf)));

            if let Ok(val) = HeaderValue::from_str(&rk.to_string()) {
                res.headers_mut().insert(HeaderName::from_static(KEY_HEADER), val);
            }
            Ok(res)
        }
    }
}
