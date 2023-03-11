fn main() {
    afl::fuzz!(|data: &[u8]| { jotdown_afl::html(data) });
}
