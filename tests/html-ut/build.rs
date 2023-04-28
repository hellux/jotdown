fn main() {
    let status = std::process::Command::new("make")
        .status()
        .expect("failed to execute make");
    assert!(status.success());
}
