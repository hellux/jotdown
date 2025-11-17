#[derive(Default)]
struct App {
    input: Option<std::ffi::OsString>,
    output: Option<std::ffi::OsString>,
    minified: bool,
    start_indent: usize,
    indent_string: String,
}

fn parse_args() -> App {
    let mut app = App::default();

    let mut args = std::env::args_os().skip(1).peekable();

    while let Some(arg) = args.next() {
        match (arg.to_string_lossy().as_ref(), args.peek()) {
            ("-h" | "--help", _) => {
                eprint!("{}", include_str!("./help.txt"));
                std::process::exit(0);
            }
            ("-v" | "--version", _) => {
                eprintln!("{} v{}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
                std::process::exit(0);
            }
            (flag @ ("-o" | "--output"), o) => match o {
                Some(o) => {
                    app.output = Some(o.into());
                    args.next();
                }
                None => {
                    eprintln!("please supply an argument to {}", flag);
                    std::process::exit(1);
                }
            },
            ("--minified", _) => app.minified = true,
            (flag @ "--indent-string", s) => {
                if let Some(s) = s {
                    app.indent_string = s.to_string_lossy().into_owned();
                    args.next();
                } else {
                    eprintln!("please supply an argument to {}", flag);
                    std::process::exit(1);
                }
            }
            (flag @ "--start-indent", s) => {
                if let Some(s) = s {
                    if let Ok(n) = s.to_string_lossy().parse() {
                        app.start_indent = n;
                    } else {
                        eprintln!(
                            "{} expected a non-negative integer, got '{}'",
                            flag,
                            s.to_string_lossy(),
                        );
                        std::process::exit(1);
                    }
                    args.next();
                } else {
                    eprintln!("please supply an argument to {}", flag);
                    std::process::exit(1);
                }
            }
            ("-", _) => {}
            (file, _) if !file.starts_with('-') => {
                if app.input.is_some() {
                    eprint!("too many arguments\n\n{}", include_str!("./help.txt"));
                    std::process::exit(1)
                }
                app.input = Some(file.into());
            }
            (flag, _) => {
                eprint!("unknown flag: {}\n\n{}", flag, include_str!("./help.txt"));
                std::process::exit(1)
            }
        }
    }

    app
}

fn run() -> Result<(), std::io::Error> {
    use jotdown::Render;
    use std::io::Read;

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
    let mut renderer = if app.minified {
        jotdown::html::Renderer::minified()
    } else {
        jotdown::html::Renderer::indented(jotdown::html::Indentation {
            string: app.indent_string,
            initial_level: app.start_indent,
        })
    };

    match app.output {
        Some(path) => renderer.write_events(parser, std::fs::File::create(path)?)?,
        None => renderer.write_events(parser, std::io::BufWriter::new(std::io::stdout()))?,
    }

    Ok(())
}

fn main() {
    match run() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    }
}
