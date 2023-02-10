use wasm_bindgen::prelude::*;

use jotdown::Render;

#[must_use]
#[wasm_bindgen]
pub fn jotdown_render(djot: &str) -> String {
    let events = jotdown::Parser::new(djot);
    let mut html = String::new();
    jotdown::html::Renderer.push(events, &mut html).unwrap();
    html
}
