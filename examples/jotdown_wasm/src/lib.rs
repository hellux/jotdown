use wasm_bindgen::prelude::*;

use jotdown::Render;
use std::fmt::Write;

#[must_use]
#[wasm_bindgen]
pub fn jotdown_render(djot: &str) -> String {
    let events = jotdown::Parser::new(djot);
    let mut html = String::new();
    jotdown::html::Renderer::default()
        .push(events, &mut html)
        .unwrap();
    html
}

#[must_use]
#[wasm_bindgen]
pub fn jotdown_parse(djot: &str) -> String {
    jotdown::Parser::new(djot)
        .map(|e| format!("{:?}\n", e))
        .collect()
}

#[must_use]
#[wasm_bindgen]
pub fn jotdown_parse_indent(djot: &str) -> String {
    let mut level = 0;
    let mut out = String::new();
    for e in jotdown::Parser::new(djot) {
        if !matches!(e, jotdown::Event::End(..)) {
            // use non-breaking space for indent because normal spaces gets squeezed by browser
            let nbsp = '\u{00a0}';
            (0..4 * level).for_each(|_| out.push(nbsp));
        }
        match e {
            jotdown::Event::Start(c, attrs) => {
                level += 1;
                if c.is_block() {
                    out.push('[');
                } else {
                    out.push('(');
                }
                out.write_fmt(format_args!("{:?}", c)).unwrap();
                if c.is_block() {
                    out.push(']');
                } else {
                    out.push(')');
                }
                if !attrs.is_empty() {
                    out.write_fmt(format_args!(" {:?}", attrs)).unwrap();
                }
                out.push('\n');
            }
            jotdown::Event::End(..) => {
                level -= 1;
            }
            e => {
                out.write_fmt(format_args!("{:?}\n", e)).unwrap();
            }
        };
    }
    out
}
