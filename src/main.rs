#[derive(Default, clap::Parser)]
#[command(version)]
struct App {
    input: Option<std::ffi::OsString>,
    #[arg(short = 'o', long)]
    output: Option<std::ffi::OsString>,
    #[arg(long)]
    minified: bool,
    #[arg(long, default_value_t = 0)]
    start_indent: usize,
    #[arg(long, default_value = "")]
    indent_string: String,
}

fn run() -> Result<(), std::io::Error> {
    use jotdown::Render;
    use std::io::Read;

    let app: App = clap::Parser::parse();

    let content = match app.input {
        Some(path) => std::fs::read_to_string(path)?,
        None => {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s)?;
            s
        }
    };

    let parser = jotdown::Parser::new(&content);
    let renderer = if app.minified {
        jotdown::html::Renderer::minified()
    } else {
        jotdown::html::Renderer::indented(jotdown::html::Indentation {
            string: app.indent_string,
            initial_level: app.start_indent,
        })
    };

    match app.output {
        Some(path) => renderer.write(parser, std::fs::File::create(path)?)?,
        None => renderer.write(parser, std::io::BufWriter::new(std::io::stdout()))?,
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
