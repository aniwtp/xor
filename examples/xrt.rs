//! CLI для кросс-проверки JS<->Rust кодека (не часть библиотеки).
//!
//! `xrt encode <file> <key>`  — перезаписывает файл кадром encode_frame
//! `xrt decode <file> <key>`  — печатает {"data_hex": ...} распакованного payload
//! `xrt xor <file> <key>`     — только слой keystream: печатает {"data_hex": ...}
use std::fmt::Write;
use std::{env, fs, process};

fn main() {
    let args: Vec<String> = env::args().collect();
    let [_, cmd, path, key] = args.as_slice() else {
        eprintln!("usage: xrt <encode|decode|xor> <file> <key>");
        process::exit(1);
    };
    let data = fs::read(path).expect("read file");
    let key: u32 = key.parse().expect("u32 key");

    match cmd.as_str() {
        "encode" => fs::write(path, xor::encode_frame(&data, key)).expect("write"),
        "decode" => {
            let out = xor::decode_frame(&data, key).expect("decode_frame failed");
            println!("{{\"data_hex\":\"{}\"}}", hex(&out));
        }
        "xor" => {
            let mut buf = data;
            xor::xor_in_place(&mut buf, key);
            println!("{{\"data_hex\":\"{}\"}}", hex(&buf));
        }
        _ => {
            eprintln!("unknown command: {cmd}");
            process::exit(1);
        }
    }
}

fn hex(data: &[u8]) -> String {
    data.iter().fold(String::with_capacity(data.len() * 2), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}
