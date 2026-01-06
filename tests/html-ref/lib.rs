#[cfg(test)]
mod r#ref;

#[macro_export]
macro_rules! compare {
    ($src:expr, $expected:expr) => {
        let src = $src;
        let expected = std::fs::read_to_string($expected).expect("read failed");
        let actual = jotup::html::Renderer::default().render_to_string(src);
        assert_eq!(actual, expected, "\n{}", {
            use std::io::Write;
            let mut child = std::process::Command::new("diff")
                .arg("--color=always")
                .arg("-")
                .arg($expected)
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .spawn()
                .expect("spawn diff failed");
            let mut stdin = child.stdin.take().unwrap();
            let actual = actual.clone();
            std::thread::spawn(move || stdin.write_all(actual.as_bytes()).unwrap());
            let stdout = child.wait_with_output().unwrap().stdout;
            String::from_utf8(stdout).unwrap()
        });
    };
}
