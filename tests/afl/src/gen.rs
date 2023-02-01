use afl::fuzz;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            let p = jotdown::Parser::new(s);
            let mut output = String::new();
            jotdown::html::push(p, &mut output);
        }
    });
}
