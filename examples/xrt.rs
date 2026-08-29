//! CLI для кросс-проверки JS<->Rust кодека (не часть библиотеки).
use std::fs;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: xrt <encode|decode|codec-decode> <file> <key>");
        std::process::exit(1);
    }
    let cmd = args[1].as_str();
    let data = fs::read(&args[2]).expect("read file");
    let key: u32 = args[3].parse().expect("u32 key");

    match cmd {
        "encode" => fs::write(&args[2], xor::encode_frame(&data, key)).expect("write"),
        "decode" => {
            let out = xor::decode_frame(&data, key).expect("decode_frame failed");
            println!("{{\"data_hex\":\"{}\"}}", hex_encode(&out));
        }
        "codec-decode" => {
            let mut buf = data;
            xor::decode_body(&mut buf, key);
            println!("{{\"data_hex\":\"{}\"}}", hex_encode(&buf));
        }
        _ => {
            eprintln!("unknown command: {cmd}");
            std::process::exit(1);
        }
    }
}

fn hex_encode(data: &[u8]) -> String {
    let mut s = String::with_capacity(data.len() * 2);
    for b in data {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
