use jotdown::{html, Parser};
use std::{
    ffi::OsString,
    fs::{self, File},
    io::{self, BufWriter},
    process::exit,
};

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
            (flag @ "-o" | flag @ "--output", o) => match o {
                Some(o) => {
                    app.output = Some(o.into());
                    args.next();
                }
                None => {
                    eprintln!("please supply an argument to {flag}");
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
                eprint!("unknown flag: {flag}\n\n{}", include_str!("./help.txt"));
                exit(1)
            }
        }
    }

    app
}

fn run() -> Result<(), io::Error> {
    let app = parse_args();

    let content = match app.input {
        Some(path) => fs::read_to_string(path)?,
        None => io::read_to_string(io::stdin())?,
    };

    let parser = Parser::new(&content);

    match app.output {
        Some(path) => html::write(parser, File::create(path)?)?,
        None => html::write(parser, BufWriter::new(io::stdout()))?,
    }

    Ok(())
}

fn main() {
    match run() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{e}");
            exit(1);
        }
    }
}
