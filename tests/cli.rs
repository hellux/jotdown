#![cfg(feature = "cli")]

const BIN: &'static str = env!("CARGO_BIN_EXE_jotdown");

#[test]
fn render() {
    use std::io::Read;
    use std::io::Write;
    let proc = std::process::Command::new(BIN)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    proc.stdin.unwrap().write_all(b"para").unwrap();
    let mut stdout = String::new();
    proc.stdout.unwrap().read_to_string(&mut stdout).unwrap();
    assert_eq!(stdout, "<p>para</p>\n");
}

#[test]
fn error() {
    let output = std::process::Command::new(BIN)
        .arg("/opt/nonexistent")
        .stdout(std::process::Stdio::piped())
        .output()
        .unwrap();
    let stderr = std::str::from_utf8(&output.stderr);
    assert_eq!(stderr, Ok("No such file or directory (os error 2)\n"));
}
