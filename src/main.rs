use jotdown::Render;
use std::io::Read;

fn main() {
    let mut src = String::new();
    std::io::stdin()
        .read_to_string(&mut src)
        .expect("failed to read utf-8 file");

    let events = jotdown::Parser::new(&src);
    let mut out = std::io::BufWriter::new(std::io::stdout());
    let html = jotdown::html::Renderer;
    html.write(events, &mut out).unwrap();
}
