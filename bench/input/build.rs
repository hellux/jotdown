use std::io::Write;

fn main() -> std::io::Result<()> {
    let inputs = std::fs::read_dir(".")?
        .filter_map(|entry| {
            let entry = entry.ok()?;
            if let Some(name) = entry.file_name().to_str() {
                if let Some(name) = name.strip_suffix(".dj") {
                    if entry.file_type().map_or(false, |ty| !ty.is_dir()) {
                        let input = std::fs::read_to_string(
                            std::path::Path::new(".").join(entry.file_name()),
                        )
                        .ok()?;
                        return Some((name.to_string(), input));
                    }
                }
            }
            None
        })
        .collect::<Vec<_>>();

    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let mut out = std::fs::File::create(std::path::Path::new(&out_dir).join("lib.rs"))?;

    inputs.iter().try_for_each(|(name, input)| {
        write!(
            out,
            "#[allow(dead_code)]\nconst {}: &str = r###\"{}\"###;",
            name.to_uppercase(),
            input,
        )
    })?;

    write!(
        out,
        "#[allow(dead_code)]\npub const ALL: &str = r###\"{}\"###;",
        inputs.iter().map(|(_, s)| s.as_str()).collect::<String>(),
    )?;

    write!(
        out,
        "#[allow(dead_code)]\npub const INPUTS: &[(&str, &str)] = &[",
    )?;
    for n in inputs
        .iter()
        .map(|(n, _)| n.as_ref())
        .chain(std::iter::once("all"))
    {
        write!(out, "(\"{}\", {}),", n, n.to_uppercase())?
    }
    write!(out, "];")?;

    println!("cargo:rerun-if-change=always_rerun");

    Ok(())
}
