fn main() {
    let has_dj = std::fs::read_dir(".").unwrap().any(|e| {
        e.map_or(false, |e| {
            e.path()
                .extension()
                .map_or(false, |ext| ext.to_str() == Some("dj"))
        })
    });
    if has_dj {
        let status = std::process::Command::new("make")
            .status()
            .expect("failed to execute make");
        assert!(status.success());
    } else {
        std::fs::write("ref.rs", &[b'\n']).unwrap();
    }
}
