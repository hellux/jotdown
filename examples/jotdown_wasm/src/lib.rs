use wasm_bindgen::prelude::*;

use jotdown::Render;

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
