use wasm_bindgen::prelude::*;

#[must_use]
#[wasm_bindgen]
pub fn jotdown_render(djot: &str) -> String {
    let events = jotdown::Parser::new(djot);
    let mut html = String::new();
    jotdown::html::push(events, &mut html);
    html
}
