fn main() {
    afl::fuzz!(|data: &[u8]| { jotdown_afl::attr(data) });
}
