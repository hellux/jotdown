use std::ffi::OsString;
use std::fs::File;
use std::io::BufWriter;
use std::io::Read;
use std::process::exit;

use jotdown::Render;

#[derive(Default)]
struct App {
    input: Option<OsString>,
    output: Option<OsString>,
}

fn parse_args() -> App {
    let mut app = App::default();

    let mut args = std::env::args_os().skip(1).peekable();

    while let Some(arg) = args.next() {
        match (arg.to_string_lossy().as_ref(), args.peek()) {
            ("-h" | "--help", _) => {
                eprint!("{}", include_str!("./help.txt"));
                exit(0);
            }
            ("-v" | "--version", _) => {
                eprintln!("{} v{}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
                exit(0);
            }
            (flag @ ("-o" | "--output"), o) => match o {
                Some(o) => {
                    app.output = Some(o.into());
                    args.next();
                }
                None => {
                    eprintln!("please supply an argument to {}", flag);
                    exit(1);
                }
            },
            ("-", _) => {}
            (file, _) if !file.starts_with('-') => {
                if app.input.is_some() {
                    eprint!("too many arguments\n\n{}", include_str!("./help.txt"));
                    exit(1)
                }
                app.input = Some(file.into());
            }
            (flag, _) => {
                eprint!("unknown flag: {}\n\n{}", flag, include_str!("./help.txt"));
                exit(1)
            }
        }
    }

    app
}

fn run() -> Result<(), std::io::Error> {
    let app = parse_args();

    let content = match app.input {
        Some(path) => std::fs::read_to_string(path)?,
        None => {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s)?;
            s
        }
    };

    let parser = jotdown::Parser::new(&content);
    let renderer = jotdown::html::Renderer::default();

    match app.output {
        Some(path) => renderer.write(parser, File::create(path)?)?,
        None => renderer.write(parser, BufWriter::new(std::io::stdout()))?,
    }

    Ok(())
}

fn main() {
    match run() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{}", e);
            exit(1);
        }
    }
}
