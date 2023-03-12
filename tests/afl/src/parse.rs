use afl::fuzz;

fn main() {
    fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            jotdown::Parser::new(s).last().unwrap();
        }
    });
}
