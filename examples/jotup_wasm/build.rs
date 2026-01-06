fn get_version() -> String {
    if let Ok(repo) = git2::Repository::discover(".") {
        if let Ok(describe) = repo.describe(&git2::DescribeOptions::new()) {
            if let Ok(format) = describe.format(None) {
                return format;
            }
        }
    }

    std::env::var("CARGO_PKG_VERSION").unwrap()
}

fn main() {
    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let dest_path = std::path::Path::new(&out_dir).join("version");
    std::fs::write(dest_path, get_version()).unwrap();
}
