use wasm_bindgen::prelude::*;

use std::fmt::Write;

#[must_use]
#[wasm_bindgen]
pub fn jotup_version() -> String {
    include_str!(concat!(env!("OUT_DIR"), "/version")).to_string()
}

#[must_use]
#[wasm_bindgen]
pub fn jotup_render(djot: &str) -> String {
    jotup::html::render_to_string(djot)
}

#[must_use]
#[wasm_bindgen]
pub fn jotup_parse(djot: &str, spans: bool) -> String {
    let mut out = String::new();
    for (e, sp) in jotup::Parser::new(djot).into_offset_iter() {
        write!(out, "{:?}", e).unwrap();
        if spans {
            write!(out, " {:?} {:?}", &djot[sp.clone()], sp).unwrap();
        }
        writeln!(out).unwrap();
    }
    out
}

#[must_use]
#[wasm_bindgen]
pub fn jotup_parse_indent(djot: &str) -> String {
    let mut level = 0;
    let mut out = String::new();
    for e in jotup::Parser::new(djot) {
        if !matches!(e, jotup::Event::End) {
            // use non-breaking space for indent because normal spaces gets squeezed by browser
            let nbsp = '\u{00a0}';
            (0..4 * level).for_each(|_| out.push(nbsp));
        }
        match e {
            jotup::Event::Start(c, attrs) => {
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
            jotup::Event::End => {
                level -= 1;
            }
            e => {
                out.write_fmt(format_args!("{:?}\n", e)).unwrap();
            }
        };
    }
    out
}
