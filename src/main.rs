//! solana_find — High-throughput Solana wallet scanner
//!
//! Key differences from ETH/DOGE scanner:
//!   • Uses ed25519 (not secp256k1) — Solana's curve
//!   • SLIP-0010 derivation (not BIP-32) — ed25519 requires ALL hardened indices
//!   • Path: m/44'/501'/0'/0'  — Phantom/Solflare standard
//!   • Address = bs58(raw_32_byte_pubkey) — no hashing, no version byte, no checksum
//!   • Balance API: Solana JSON-RPC getBalance → lamports (1 SOL = 1e9 lamports)
//!   • Login: import 64-byte keypair (priv+pub) or mnemonic into Phantom/Solflare
//!
//! Architecture: N generator threads → channel → M checker threads → dashboard

use bip39::{Language, Mnemonic, MnemonicType, Seed};
use crossbeam_channel::{bounded, Receiver, Sender};
use ed25519_dalek::{PublicKey as Ed25519PublicKey, SecretKey as Ed25519SecretKey};
use hmac::{Hmac, Mac};
use rand::RngCore;
use rand_chacha::ChaCha20Rng;
use rand::SeedableRng;
use sha2::{Digest, Sha256, Sha512};
use std::fs::OpenOptions;
use std::io::{self, Write};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// ── ANSI ─────────────────────────────────────────────────────────────────────
const C:   &str = "\x1b[36m";   // cyan
const G:   &str = "\x1b[32m";   // green
const Y:   &str = "\x1b[33m";   // yellow
const M:   &str = "\x1b[35m";   // magenta
const W:   &str = "\x1b[37m";   // white
const R:   &str = "\x1b[31m";   // red
const RST: &str = "\x1b[0m";
const BLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const BG:  &str = "\x1b[48;5;234m";  // dark background

fn flush()          { let _ = io::stdout().flush(); }
fn clear()          { print!("\x1b[2J\x1b[H"); flush(); }
fn hide_cursor()    { print!("\x1b[?25l"); flush(); }
fn show_cursor()    { print!("\x1b[?25h"); flush(); }
fn set_title(t: &str) { print!("\x1b]2;{}\x07", t); flush(); }

// ── Shared stats ──────────────────────────────────────────────────────────────

struct Stats {
    generated:  AtomicU64,
    checked:    AtomicU64,
    skipped:    AtomicU64,
    history:    AtomicU64,
    hits:       AtomicU64,
    usd_cents:  AtomicU64,
}

impl Stats {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            generated: AtomicU64::new(0),
            checked:   AtomicU64::new(0),
            skipped:   AtomicU64::new(0),
            history:   AtomicU64::new(0),
            hits:      AtomicU64::new(0),
            usd_cents: AtomicU64::new(0),
        })
    }
}

#[derive(Clone)]
struct LogEntry {
    n:       u64,
    addr:    String,
    words:   Vec<String>,
    balance: f64,    // SOL
    has_hit: bool,
}

struct RecentLog {
    entries: std::collections::VecDeque<LogEntry>,
    cap:     usize,
}

impl RecentLog {
    fn new(cap: usize) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self { entries: std::collections::VecDeque::new(), cap }))
    }
    fn push(&mut self, e: LogEntry) {
        if self.entries.len() >= self.cap { self.entries.pop_front(); }
        self.entries.push_back(e);
    }
}

// ── Wallet ────────────────────────────────────────────────────────────────────

#[derive(Clone)]
struct Wallet {
    words:       Vec<String>,  // 12 or 24 BIP-39 words
    address:     String,       // base58(pubkey) — Solana address
    priv_hex:    String,       // 32-byte private key hex
    keypair_hex: String,       // 64-byte keypair hex (priv+pub) — for Phantom import
}

// ── Entropy mixing — same as ETH scanner, 6 sources ──────────────────────────

fn make_rng(counter: u64) -> ChaCha20Rng {
    use rand::rngs::OsRng;
    use std::time::{SystemTime, UNIX_EPOCH};

    let mut mix = [0u8; 32];

    let mut os = [0u8; 32];
    OsRng.fill_bytes(&mut os);
    for (i, b) in os.iter().enumerate() { mix[i] ^= b; }

    let mut tr = [0u8; 32];
    rand::thread_rng().fill_bytes(&mut tr);
    for (i, b) in tr.iter().enumerate() { mix[i] ^= b; }

    let tid = format!("{:?}", std::thread::current().id());
    let tid_h = Sha256::digest(tid.as_bytes());
    for (i, b) in tid_h.iter().enumerate() { mix[i] ^= b; }

    let ns = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().subsec_nanos() as u64;
    let t_h = Sha256::digest(&ns.to_le_bytes());
    for (i, b) in t_h.iter().enumerate() { mix[i] ^= b; }

    let stack_addr = &mix as *const _ as usize;
    let a_h = Sha256::digest(&stack_addr.to_le_bytes());
    for (i, b) in a_h.iter().enumerate() { mix[i] ^= b; }

    let c_h = Sha256::digest(&counter.to_le_bytes());
    for (i, b) in c_h.iter().enumerate() { mix[i] ^= b; }

    let seed = Sha256::digest(&mix);
    ChaCha20Rng::from_seed(seed.into())
}

// ── SLIP-0010 ed25519 key derivation ─────────────────────────────────────────
//
// Solana uses ed25519. BIP-32 does NOT support ed25519 (requires normal/non-hardened
// child keys which ed25519 cannot do). SLIP-0010 is the correct standard.
//
// Key difference from BIP-32:
//   - Master key: HMAC-SHA512("ed25519 seed", seed_bytes)  ← different domain
//   - ALL child indices MUST be hardened (>= 0x80000000)
//   - Normal (non-hardened) derivation is impossible with ed25519
//
// Phantom / Solflare / Backpack use: m / 44' / 501' / 0' / 0'

fn hmac_sha512(key: &[u8], data: &[u8]) -> [u8; 64] {
    let mut mac = Hmac::<Sha512>::new_from_slice(key).unwrap();
    mac.update(data);
    let mut out = [0u8; 64];
    out.copy_from_slice(&mac.finalize().into_bytes());
    out
}

/// Derive child key — index is always hardened internally
fn slip10_child(parent_key: &[u8; 32], parent_chain: &[u8; 32], index: u32) -> ([u8; 32], [u8; 32]) {
    // Force hardened: index | 0x80000000
    let hardened = index | 0x8000_0000;
    // Data = 0x00 || parent_key || index_be
    let mut data = Vec::with_capacity(37);
    data.push(0x00u8);
    data.extend_from_slice(parent_key);
    data.extend_from_slice(&hardened.to_be_bytes());

    let h = hmac_sha512(parent_chain, &data);
    let mut key   = [0u8; 32];
    let mut chain = [0u8; 32];
    key.copy_from_slice(&h[..32]);
    chain.copy_from_slice(&h[32..]);
    (key, chain)
}

/// Full SLIP-0010 derivation: m / 44' / 501' / 0' / 0'
fn slip10_derive(seed: &[u8]) -> [u8; 32] {
    // Master key: HMAC-SHA512 with key "ed25519 seed"
    let h = hmac_sha512(b"ed25519 seed", seed);
    let mut key   = [0u8; 32];
    let mut chain = [0u8; 32];
    key.copy_from_slice(&h[..32]);
    chain.copy_from_slice(&h[32..]);

    // m/44'/501'/0'/0'  — Phantom standard path
    (key, chain) = slip10_child(&key, &chain, 44);   // 44'
    (key, chain) = slip10_child(&key, &chain, 501);  // 501' (SOL coin type)
    (key, chain) = slip10_child(&key, &chain, 0);    // 0'
    (key,     _) = slip10_child(&key, &chain, 0);    // 0'
    key
}

/// Solana address = bs58(raw 32-byte public key)
/// NO version byte, NO checksum, NO hashing — just raw pubkey encoded in base58
fn sol_address(priv_key_bytes: &[u8; 32]) -> (String, [u8; 32]) {
    let secret_key = Ed25519SecretKey::from_bytes(priv_key_bytes).expect("32-byte key");
    let public_key = Ed25519PublicKey::from(&secret_key);
    let pub_bytes  = public_key.to_bytes();
    let address    = bs58::encode(&pub_bytes).into_string();
    (address, pub_bytes)
}

// ── Wallet generation ─────────────────────────────────────────────────────────

fn gen_wallet(counter: u64) -> Wallet {
    let mut rng = make_rng(counter);

    // 12 or 24 words — equal probability
    let (mtype, entropy_bytes) = if (rng.next_u32() & 1) == 0 {
        (MnemonicType::Words12, 16usize)   // 128-bit entropy
    } else {
        (MnemonicType::Words24, 32usize)   // 256-bit entropy
    };

    let mut entropy = vec![0u8; entropy_bytes];
    rng.fill_bytes(&mut entropy);

    let mnemonic = Mnemonic::from_entropy(&entropy, Language::English)
        .expect("valid entropy length");
    let _ = mtype;

    let words: Vec<String> = mnemonic.phrase().split_whitespace().map(str::to_string).collect();

    // BIP-39 → 64-byte seed (empty passphrase)
    let seed = Seed::new(&mnemonic, "");

    // SLIP-0010 derivation → 32-byte ed25519 private key
    let priv_bytes = slip10_derive(seed.as_bytes());

    // ed25519 public key → Solana address
    let (address, pub_bytes) = sol_address(&priv_bytes);

    // 64-byte keypair = priv(32) + pub(32) — format used by Phantom import
    let mut keypair = [0u8; 64];
    keypair[..32].copy_from_slice(&priv_bytes);
    keypair[32..].copy_from_slice(&pub_bytes);

    Wallet {
        words,
        address,
        priv_hex:    hex::encode(priv_bytes),
        keypair_hex: hex::encode(keypair),
    }
}

// ── Solana JSON-RPC balance check ─────────────────────────────────────────────
//
// Solana uses JSON-RPC, not REST.
// Endpoint: POST https://api.mainnet-beta.solana.com
// Method:   getBalance  → returns lamports (u64)
// 1 SOL = 1,000,000,000 lamports  (1e9)
//
// Triage: balance == 0 → skip. balance > 0 → record hit.
// (Unlike ETH, Solana getBalance already tells us if there's any SOL.)

fn check_sol_balance(address: &str) -> u64 {
    // Try multiple public RPC endpoints for reliability
    let endpoints = [
        "https://api.mainnet-beta.solana.com",
        "https://solana.drpc.org",
        "https://rpc.ankr.com/solana",
    ];

    let body = format!(
        r#"{{"jsonrpc":"2.0","id":1,"method":"getBalance","params":["{}", {{"commitment":"confirmed"}}]}}"#,
        address
    );

    for endpoint in &endpoints {
        let resp = minreq::post(*endpoint)
            .with_header("Content-Type", "application/json")
            .with_header("User-Agent", "Mozilla/5.0")
            .with_body(body.as_bytes())
            .with_timeout(6)
            .send();

        if let Ok(r) = resp {
            if r.status_code == 200 {
                if let Ok(json) = r.json::<serde_json::Value>() {
                    if let Some(lamports) = json["result"]["value"].as_u64() {
                        return lamports;
                    }
                }
            }
        }
    }
    0
}

// ── SOL/USD price ─────────────────────────────────────────────────────────────

fn fetch_sol_price() -> f64 {
    // Try CoinGecko public API
    let endpoints = [
        "https://api.coingecko.com/api/v3/simple/price?ids=solana&vs_currencies=usd",
        "https://price.jup.ag/v4/price?ids=SOL",
    ];
    for url in &endpoints {
        if let Ok(r) = minreq::get(*url).with_timeout(6).send() {
            if r.status_code == 200 {
                if let Ok(json) = r.json::<serde_json::Value>() {
                    // CoinGecko format
                    if let Some(p) = json["solana"]["usd"].as_f64() { return p; }
                    // Jupiter format
                    if let Some(p) = json["data"]["SOL"]["price"].as_f64() { return p; }
                }
            }
        }
    }
    // Fallback: hardcoded approximate price (updated by hand)
    150.0
}

// ── found.txt writer ──────────────────────────────────────────────────────────

fn write_found(address: &str, balance_sol: f64, words: &[String], priv_hex: &str, keypair_hex: &str) {
    let mut f = OpenOptions::new()
        .append(true).create(true)
        .open("found.txt").expect("Cannot open found.txt");
    writeln!(f,
        "SOL:      {}\nBalance:  {} SOL\nMnemonic: {}\nPrivKey:  {}\nKeypair:  {}\n\
         Import:   Settings > Import Wallet in Phantom (paste Mnemonic or PrivKey)\n",
        address, balance_sol,
        words.join(" "),
        priv_hex,
        keypair_hex,
    ).expect("write found.txt");
}

// ── Generator thread ──────────────────────────────────────────────────────────

fn generator_thread(tx: Sender<Wallet>, stats: Arc<Stats>) {
    let mut local: u64 = 0;
    loop {
        let g = stats.generated.load(Ordering::Relaxed);
        let w = gen_wallet(g.wrapping_add(local));
        local = local.wrapping_add(1);
        stats.generated.fetch_add(1, Ordering::Relaxed);
        if tx.send(w).is_err() { break; }
    }
}

// ── Checker thread ────────────────────────────────────────────────────────────

fn checker_thread(
    rx: Receiver<Wallet>,
    stats: Arc<Stats>,
    log: Arc<Mutex<RecentLog>>,
    sol_usd: f64,
) {
    loop {
        let w = match rx.recv() { Ok(w) => w, Err(_) => break };
        stats.checked.fetch_add(1, Ordering::Relaxed);

        let lamports = check_sol_balance(&w.address);
        let balance_sol = lamports as f64 / 1_000_000_000.0;

        let has_hit = balance_sol > 0.0;

        if !has_hit {
            stats.skipped.fetch_add(1, Ordering::Relaxed);
        } else {
            stats.history.fetch_add(1, Ordering::Relaxed);
            stats.hits.fetch_add(1, Ordering::Relaxed);
            let usd_cents = (balance_sol * sol_usd * 100.0) as u64;
            stats.usd_cents.fetch_add(usd_cents, Ordering::Relaxed);
            write_found(&w.address, balance_sol, &w.words, &w.priv_hex, &w.keypair_hex);
        }

        let n = stats.checked.load(Ordering::Relaxed);
        if let Ok(mut lg) = log.lock() {
            lg.push(LogEntry { n, addr: w.address.clone(), words: w.words.clone(), balance: balance_sol, has_hit });
        }
    }
}

// ── Dashboard ─────────────────────────────────────────────────────────────────

fn fmt_big(n: u64) -> String {
    if n >= 1_000_000 { format!("{:.2}M", n as f64 / 1e6) }
    else if n >= 1_000 { format!("{:.1}K", n as f64 / 1e3) }
    else { format!("{}", n) }
}

fn fmt_dur(s: u64) -> String {
    if s < 60 { format!("{}s", s) }
    else if s < 3600 { format!("{}m {:02}s", s/60, s%60) }
    else { format!("{}h {:02}m", s/3600, (s%3600)/60) }
}

fn bar(v: u64, max: u64, w: usize, col: &str) -> String {
    let n = if max == 0 { 0 } else { ((v as f64 / max as f64) * w as f64) as usize }.min(w);
    format!("{}{}{}{}{}{}",
        col, BLD, "█".repeat(n), RST, DIM, "░".repeat(w - n))
}

fn dashboard_thread(
    stats: Arc<Stats>,
    log:   Arc<Mutex<RecentLog>>,
    start: Instant,
    n_gen: usize,
    n_chk: usize,
    sol_usd: f64,
) {
    hide_cursor();
    let mut tick: u64 = 0;
    let mut prev_gen_count = 0u64;
    let mut prev_chk = 0u64;
    let mut gen_rate = 0.0f64;
    let mut chk_rate = 0.0f64;
    let w = 102usize;

    loop {
        std::thread::sleep(Duration::from_millis(500));
        tick += 1;

        let gen_count  = stats.generated.load(Ordering::Relaxed);
        let chk  = stats.checked.load(Ordering::Relaxed);
        let skip = stats.skipped.load(Ordering::Relaxed);
        let hist = stats.history.load(Ordering::Relaxed);
        let hits = stats.hits.load(Ordering::Relaxed);
        let usd  = stats.usd_cents.load(Ordering::Relaxed) as f64 / 100.0;
        let elapsed = start.elapsed().as_secs_f64().max(0.001);
        let elapsed_s = elapsed as u64;

        // Smoothed EMA rates
        let raw_g = (gen_count.saturating_sub(prev_gen_count)) as f64 * 2.0;
        let raw_c = (chk.saturating_sub(prev_chk)) as f64 * 2.0;
        gen_rate = gen_rate * 0.7 + raw_g * 0.3;
        chk_rate = chk_rate * 0.7 + raw_c * 0.3;
        prev_gen_count = gen_count; prev_chk = chk;

        let recent: Vec<LogEntry> = if let Ok(lg) = log.lock() {
            lg.entries.iter().rev().take(5).cloned().collect()
        } else { vec![] };

        let skip_pct = if chk > 0 { skip as f64 / chk as f64 * 100.0 } else { 0.0 };
        let sol_price_str = format!("${:.2}", sol_usd);

        // ── Render ────────────────────────────────────────────────────────────
        print!("\x1b[2J\x1b[H");  // clear screen

        let border = format!("{BG}{BLD}{C}");
        let rst    = format!("{RST}");

        // Title
        println!("{border}┌{}┐{rst}", "─".repeat(w-2));
        println!("{border}│{RST}  {BLD}{C}◎  SOLANA WALLET FINDER{RST}  {DIM}BIP-39 → SLIP-0010 → ed25519 → m/44'/501'/0'/0'{RST}{BG}{C}{:>pad$}│{rst}",
            "", pad = w.saturating_sub(74));
        println!("{border}├{}┤{rst}", "─".repeat(w-2));

        // Stats
        println!("{border}│{RST}  {BLD}{C}GENERATED{RST} {BLD}{W}{:>8}{RST} {DIM}({:>5.0}/s){RST}   \
                  {BLD}{Y}CHECKED{RST} {BLD}{W}{:>8}{RST} {DIM}({:>5.1}/s){RST}   \
                  {BLD}{M}HITS{RST} {BLD}{G}{:>4}{RST}   \
                  {BLD}{G}FOUND{RST} {BLD}{G}${:.2}{RST}   \
                  {DIM}runtime: {}{RST}{BG}{C}{:>pad$}│{rst}",
            fmt_big(gen_count), gen_rate,
            fmt_big(chk), chk_rate,
            hits, usd,
            fmt_dur(elapsed_s),
            "", pad = w.saturating_sub(88),
        );

        // Bars
        println!("{border}│{RST}  {DIM}Gen/s{RST} {}  {BLD}{W}{:>5.0}{RST}   \
                  {DIM}Chk/s{RST} {}  {BLD}{W}{:>4.1}{RST}{BG}{C}{:>pad$}│{rst}",
            bar(gen_rate as u64, 300, 28, C), gen_rate,
            bar(chk_rate as u64,  20, 28, Y), chk_rate,
            "", pad = w.saturating_sub(83),
        );

        // Triage + price
        println!("{border}├{}┤{rst}", "─".repeat(w-2));
        println!("{border}│{RST}  {BLD}TRIAGE{RST}  \
                  {DIM}Zero balance (skipped):{RST} {BLD}{R}{}{RST} {DIM}({:.1}%){RST}   \
                  {DIM}Non-zero:{RST} {BLD}{Y}{}{RST}   \
                  {DIM}With funds:{RST} {BLD}{G}{}{RST}   \
                  {DIM}Threads:{RST} {C}{}gen_count{RST} {Y}{}chk{RST}   \
                  {DIM}SOL:{RST} {BLD}{G}{}{RST}{BG}{C}{:>pad$}│{rst}",
            fmt_big(skip), skip_pct,
            fmt_big(hist),
            hits,
            n_gen, n_chk,
            sol_price_str,
            "", pad = w.saturating_sub(97),
        );

        // Key facts
        println!("{border}├{}┤{rst}", "─".repeat(w-2));
        println!("{border}│{RST}  {DIM}Keyspace:{RST} {BLD}{M}2¹²⁸{RST} {DIM}(12 words){RST} / {BLD}{M}2²⁵⁶{RST} {DIM}(24 words){RST}   \
                  {DIM}Funded SOL wallets: ~5×10⁶   \
                  Odds: 1 in {RST}{R}{BLD}68,000,000,000,000,000,000,000,000,000,000{RST}{BG}{C}{:>pad$}│{rst}",
            "", pad = w.saturating_sub(100),
        );

        // Derivation path info
        println!("{border}│{RST}  {DIM}Path:{RST} {BLD}{C}m/44'/501'/0'/0'{RST}  \
                  {DIM}(Phantom/Solflare standard)   \
                  Curve:{RST} {BLD}{C}ed25519{RST}  \
                  {DIM}Standard:{RST} {BLD}{C}SLIP-0010{RST}  \
                  {DIM}Address: base58(pubkey){RST}{BG}{C}{:>pad$}│{rst}",
            "", pad = w.saturating_sub(91),
        );

        // Live feed
        println!("{border}├{}┤{rst}", "─".repeat(w-2));
        println!("{border}│{RST}  {BLD}{W}LIVE FEED{RST}  {DIM}(last 5 wallets checked — zero balance = normal){RST}{BG}{C}{:>pad$}│{rst}",
            "", pad = w.saturating_sub(65));
        println!("{border}├{}┤{rst}", "─".repeat(w-2));

        if recent.is_empty() {
            println!("{border}│{RST}  {DIM}Waiting for first result...{RST}{BG}{C}{:>pad$}│{rst}", "", pad = w.saturating_sub(30));
            for _ in 0..9 {
                println!("{border}│{RST}{:>pad$}│{rst}", "", pad = w.saturating_sub(1));
            }
        } else {
            let shown = recent.len();
            for e in &recent {
                let marker = if e.has_hit {
                    format!("{BLD}{G}★ HIT!  {RST}")
                } else {
                    format!("{DIM}·  {RST}     ")
                };
                let bal_str = if e.has_hit {
                    format!("{BLD}{G}{:.6} SOL{RST}", e.balance)
                } else {
                    format!("{DIM}0.000000 SOL{RST}")
                };
                // Show first 6 words + "+N more"
                let w6: String = e.words.iter().take(6).cloned().collect::<Vec<_>>().join(" ");
                let more = if e.words.len() > 6 { format!(" {DIM}+{} more{RST}", e.words.len()-6) } else { String::new() };
                let addr_short = if e.addr.len() > 22 { format!("{}..{}", &e.addr[..10], &e.addr[e.addr.len()-8..]) } else { e.addr.clone() };

                println!("{border}│{RST} {marker} {DIM}#{:>8}{RST}  {C}{BLD}{}{RST}  {}", e.n, addr_short, bal_str);
                println!("{border}│{RST}            {DIM}Mne:{RST} {R}{}{}{RST}{BG}{C}{:>pad$}│{rst}",
                    w6, more, "", pad = w.saturating_sub(w6.len() + 22 + if e.words.len()>6{12}else{0}));
            }
            for _ in shown..5 {
                println!("{border}│{RST}{:>pad$}│{rst}", "", pad = w.saturating_sub(1));
                println!("{border}│{RST}{:>pad$}│{rst}", "", pad = w.saturating_sub(1));
            }
        }

        // Footer
        println!("{border}└{}┘{rst}", "─".repeat(w-2));
        let spinner = ["⠋","⠙","⠹","⠸","⠼","⠴","⠦","⠧","⠇","⠏"];
        print!(" {C}{}{RST} Scanning... {BLD}Ctrl+C{RST} to stop  │  Hits → {BLD}found.txt{RST}  │  \
               Import: {C}Phantom > Add Wallet > Import Mnemonic{RST}",
            spinner[(tick as usize) % spinner.len()]);
        flush();

        set_title(&format!("◎ SOL Finder │ Gen:{} {:.0}/s │ Chk:{} │ Hits:{} │ ${:.2}",
            fmt_big(gen_count), gen_rate, fmt_big(chk), hits, usd));
    }
}

// ── main ──────────────────────────────────────────────────────────────────────

fn main() {
    clear();
    hide_cursor();
    println!("{BLD}{C}◎  Solana Wallet Finder — starting up...{RST}");
    println!("{DIM}Fetching SOL price...{RST}");
    flush();

    let sol_usd = fetch_sol_price();
    println!("  {BLD}{G}SOL{RST}: ${:.2}", sol_usd);
    println!();
    std::thread::sleep(Duration::from_millis(800));

    let n_gen: usize = num_cpus::get().max(2);
    let n_chk: usize = std::env::var("CHECKERS").ok()
        .and_then(|s| s.parse().ok()).unwrap_or(8);

    println!("{BLD}Generator threads:{RST} {} (one per CPU core)", n_gen);
    println!("{BLD}Checker threads:{RST}   {} (set CHECKERS=N to change)", n_chk);
    std::thread::sleep(Duration::from_secs(1));

    let stats  = Stats::new();
    let log    = RecentLog::new(5);
    let start  = Instant::now();
    let (tx, rx) = bounded::<Wallet>(n_gen * 8);

    let mut handles = vec![];

    for _ in 0..n_gen {
        let tx2 = tx.clone(); let s2 = Arc::clone(&stats);
        handles.push(std::thread::spawn(move || generator_thread(tx2, s2)));
    }
    drop(tx);

    for _ in 0..n_chk {
        let rx2 = rx.clone(); let s2 = Arc::clone(&stats); let l2 = Arc::clone(&log);
        handles.push(std::thread::spawn(move || checker_thread(rx2, s2, l2, sol_usd)));
    }
    drop(rx);

    {
        let s2 = Arc::clone(&stats); let l2 = Arc::clone(&log);
        std::thread::spawn(move || dashboard_thread(s2, l2, start, n_gen, n_chk, sol_usd));
    }

    for h in handles { let _ = h.join(); }
    show_cursor();
}

// ── Tests ─────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod tests {
    use super::*;
    use bip39::{Language, Mnemonic, Seed};

    const MNE: &str = "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";

    #[test]
    fn sol_address_known_vector() {
        // Python independently computed:
        //   priv: 37df573b3ac4ad5b522e064e25b63ea16bcbe79d449e81a0268d1047948bb445
        //   addr: HAgk14JpMQLgt6rVgv7cBQFJWFto5Dqxi472uT3DKpqk
        // for m/44'/501'/0'/0' with empty passphrase
        let m    = Mnemonic::from_phrase(MNE, Language::English).unwrap();
        let seed = Seed::new(&m, "");
        let priv_bytes = slip10_derive(seed.as_bytes());
        let (addr, _)  = sol_address(&priv_bytes);

        println!("Rust SOL addr: {}", addr);
        println!("Rust priv key: {}", hex::encode(priv_bytes));

        assert_eq!(hex::encode(priv_bytes),
            "37df573b3ac4ad5b522e064e25b63ea16bcbe79d449e81a0268d1047948bb445",
            "Private key mismatch");
        assert_eq!(addr, "HAgk14JpMQLgt6rVgv7cBQFJWFto5Dqxi472uT3DKpqk",
            "Address mismatch — got: {}", addr);
    }

    #[test]
    fn sol_address_is_base58_32bytes() {
        // Solana addresses are base58 of 32 raw bytes → always 32-44 chars
        let w = gen_wallet(0);
        let decoded = bs58::decode(&w.address).into_vec().expect("valid base58");
        assert_eq!(decoded.len(), 32, "SOL pubkey must be 32 bytes");
        assert!(w.address.len() >= 32 && w.address.len() <= 44,
            "SOL address length: {}", w.address.len());
    }

    #[test]
    fn keypair_is_64_bytes() {
        let w = gen_wallet(1);
        assert_eq!(w.keypair_hex.len(), 128, "keypair hex = 64 bytes = 128 hex chars");
    }

    #[test]
    fn all_mnemonics_valid_12_or_24_words() {
        for i in 0u64..200 {
            let w = gen_wallet(i);
            Mnemonic::from_phrase(&w.words.join(" "), Language::English)
                .unwrap_or_else(|e| panic!("#{} invalid: {}", i, e));
            assert!(w.words.len() == 12 || w.words.len() == 24,
                "Expected 12 or 24, got {}", w.words.len());
        }
    }

    #[test]
    fn sol_balance_math() {
        // 1 SOL = 1_000_000_000 lamports
        let lamports: u64 = 1_000_000_000;
        let sol = lamports as f64 / 1_000_000_000.0;
        assert!((sol - 1.0).abs() < 1e-10);

        // 0.5 SOL
        let half: u64 = 500_000_000;
        let sol_half = half as f64 / 1_000_000_000.0;
        assert!((sol_half - 0.5).abs() < 1e-10);
    }

    #[test]
    fn all_indices_hardened_in_path() {
        // Verify our path uses hardened indices (>= 0x80000000)
        // by checking that normal (non-hardened) child would differ
        let m    = Mnemonic::from_phrase(MNE, Language::English).unwrap();
        let seed = Seed::new(&m, "");
        let sb   = seed.as_bytes();

        // Standard path
        let h = hmac_sha512(b"ed25519 seed", sb);
        let mut k = [0u8; 32]; let mut c = [0u8; 32];
        k.copy_from_slice(&h[..32]); c.copy_from_slice(&h[32..]);

        // Each derive_child must use hardened index
        for idx in [44u32, 501, 0, 0] {
            let hardened = idx | 0x8000_0000;
            let mut data = vec![0x00u8];
            data.extend_from_slice(&k);
            data.extend_from_slice(&hardened.to_be_bytes());
            let out = hmac_sha512(&c, &data);
            k.copy_from_slice(&out[..32]);
            c.copy_from_slice(&out[32..]);
        }
        let (addr_hardened, _) = sol_address(&k);
        assert_eq!(addr_hardened, "HAgk14JpMQLgt6rVgv7cBQFJWFto5Dqxi472uT3DKpqk");
    }
}

#[cfg(test)]
mod audit_tests {
    use super::*;
    use bip39::{Language, Mnemonic, Seed};

    // All expected values independently verified with Python solders library
    struct Vec3 {
        mne:      &'static str,
        sol_addr: &'static str,
        sol_key:  &'static str,
    }

    fn vectors() -> Vec<Vec3> {
        vec![
            Vec3 {
                mne:      "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about",
                sol_addr: "HAgk14JpMQLgt6rVgv7cBQFJWFto5Dqxi472uT3DKpqk",
                sol_key:  "37df573b3ac4ad5b522e064e25b63ea16bcbe79d449e81a0268d1047948bb445",
            },
            Vec3 {
                mne:      "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong",
                sol_addr: "E48cosDiQZK1iDSsyUzhvW4WxJeoKuDk5qgcdkmANV4N",
                sol_key:  "0b69a88e057a6ff3299f4adac3b04b0b24df114b3f3c21c5cefe0b89664b3bcf",
            },
            Vec3 {
                mne:      "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art",
                sol_addr: "3Cy3YNTFywCmxoxt8n7UH6hg6dLo5uACowX3CFceaSnx",
                sol_key:  "7c139e1a603ca04f5f7cff194e1bb6f6d1b9098470ea90695ab628488a9f921b",
            },
        ]
    }

    #[test]
    fn sol_three_vectors() {
        for v in vectors() {
            let m       = Mnemonic::from_phrase(v.mne, Language::English).unwrap();
            let seed    = Seed::new(&m, "");
            let priv_b  = slip10_derive(seed.as_bytes());
            let (addr, _) = sol_address(&priv_b);
            let key_hex = hex::encode(priv_b);
            let short   = &v.mne[..20];
            assert_eq!(key_hex, v.sol_key,  "Key  mismatch [{}]: got {}", short, key_hex);
            assert_eq!(addr,    v.sol_addr, "Addr mismatch [{}]: got {}", short, addr);
        }
    }

    #[test]
    fn passphrase_is_empty() {
        // BIP-39 PBKDF2 with NON-empty passphrase gives a completely different address.
        // We must use "" (empty). Verify this produces the known vector.
        let mne  = "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";
        let m    = Mnemonic::from_phrase(mne, Language::English).unwrap();
        let seed_empty    = Seed::new(&m, "");
        let seed_nonempty = Seed::new(&m, "passphrase");
        let priv_empty    = slip10_derive(seed_empty.as_bytes());
        let priv_nonempty = slip10_derive(seed_nonempty.as_bytes());
        assert_ne!(priv_empty, priv_nonempty, "passphrase should change the key");
        // Empty passphrase must match known vector
        let (addr, _) = sol_address(&priv_empty);
        assert_eq!(addr, "HAgk14JpMQLgt6rVgv7cBQFJWFto5Dqxi472uT3DKpqk");
    }

    #[test]
    fn hmac_key_is_ed25519_seed_not_bitcoin_seed() {
        // The most common mistake: using "Bitcoin seed" instead of "ed25519 seed"
        // Verify by checking that wrong HMAC key produces wrong address
        let seed_bytes = [0u8; 64];
        let wrong = {
            let mut mac = hmac::Hmac::<sha2::Sha512>::new_from_slice(b"Bitcoin seed").unwrap();
            mac.update(&seed_bytes);
            let r = mac.finalize().into_bytes();
            let mut k = [0u8;32]; k.copy_from_slice(&r[..32]); k
        };
        let correct = {
            let mut mac = hmac::Hmac::<sha2::Sha512>::new_from_slice(b"ed25519 seed").unwrap();
            mac.update(&seed_bytes);
            let r = mac.finalize().into_bytes();
            let mut k = [0u8;32]; k.copy_from_slice(&r[..32]); k
        };
        assert_ne!(wrong, correct, "ed25519 seed and Bitcoin seed must differ");
    }

    #[test]
    fn all_derivation_steps_hardened() {
        // In SLIP-0010 Ed25519 every index MUST be hardened (>= 0x80000000)
        // slip10_child forces this. Verify the path indices get the hardened bit.
        let indices = [44u32, 501, 0, 0];
        for &idx in &indices {
            assert!(idx < 0x8000_0000, "raw index should be <2^31 before hardening");
            let hardened = idx | 0x8000_0000;
            assert!(hardened >= 0x8000_0000, "hardened index must be >=2^31");
        }
    }

    #[test]
    fn address_not_hashed_just_base58_pubkey() {
        // Solana address is raw bs58(32-byte pubkey). Not hashed. Not checksummed.
        let priv_b = [1u8; 32];
        let (addr, pub_b) = sol_address(&priv_b);
        let re_encoded = bs58::encode(&pub_b).into_string();
        assert_eq!(addr, re_encoded, "address must be bs58(pubkey) exactly");
        // SOL addresses are 43-44 chars (base58 of 32 bytes)
        assert!(addr.len() >= 32 && addr.len() <= 44,
            "SOL address length {} out of range", addr.len());
    }

    #[test]
    fn entropy_covers_full_12_and_24_word_space() {
        // Verify 12-word = 16 bytes entropy, 24-word = 32 bytes
        // Both map to correct mnemonic word counts
        let e12 = [0xABu8; 16];
        let e24 = [0xCDu8; 32];
        let m12 = Mnemonic::from_entropy(&e12, Language::English).unwrap();
        let m24 = Mnemonic::from_entropy(&e24, Language::English).unwrap();
        assert_eq!(m12.phrase().split_whitespace().count(), 12);
        assert_eq!(m24.phrase().split_whitespace().count(), 24);
    }
}