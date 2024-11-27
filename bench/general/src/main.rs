use std::{
    fs::{exists, File},
    io::Write,
    process::{Command, Stdio},
    time::Instant,
};

use anyhow::Context;

const PANDOC_MANUAL: &str = "https://github.com/jgm/djot/files/11900633/pandoc-manual.txt";
const PANDOC_MANUAL_DJ: &str = "pandoc-manual.dj";

fn main() -> anyhow::Result<()> {
    if !exists(PANDOC_MANUAL_DJ)? {
        let body = reqwest::blocking::get(PANDOC_MANUAL)?.text()?;

        let mut f = File::create(PANDOC_MANUAL_DJ)?;
        f.write_all(body.as_bytes())?;
    }

    let mut t0 = Instant::now();
    match Command::new("djoths")
        .arg(PANDOC_MANUAL_DJ)
        .stdout(Stdio::null())
        .status()
        .context("Error trying to run djoths")
    {
        Ok(status) => {
            let t1 = Instant::now();
            println!(
                "(Haskell) djoths pandoc-manual.dj {:?}, {status}",
                t1.duration_since(t0)
            );
        }
        Err(error) => {
            let t1 = Instant::now();
            eprintln!(
                "(Haskell) djoths pandoc-manual.dj {:?}: {error}",
                t1.duration_since(t0)
            )
        }
    }

    t0 = Instant::now();
    match Command::new("djot")
        .arg(PANDOC_MANUAL_DJ)
        .stdout(Stdio::null())
        .status()
        .context("Error trying to run djot")
    {
        Ok(status) => {
            let t1 = Instant::now();
            println!(
                "(JavaScript) djot pandoc-manual.dj {:?}, {status}",
                t1.duration_since(t0)
            );
        }
        Err(error) => {
            let t1 = Instant::now();
            eprintln!(
                "(JavaScript) djot pandoc-manual.dj {:?}: {error}",
                t1.duration_since(t0)
            )
        }
    }

    t0 = Instant::now();
    match Command::new("jotdown")
        .arg(PANDOC_MANUAL_DJ)
        .stdout(Stdio::null())
        .status()
        .context("Error trying to run jotdown")
    {
        Ok(status) => {
            let t1 = Instant::now();
            println!(
                "(Rust) jotdown pandoc-manual.dj {:?}, {status}",
                t1.duration_since(t0)
            );
        }
        Err(error) => {
            let t1 = Instant::now();
            eprintln!(
                "(Rust) jotdown pandoc-manual.dj {:?}: {error}",
                t1.duration_since(t0)
            )
        }
    }

    Ok(())
}
