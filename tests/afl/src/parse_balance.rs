fn main() {
    afl::fuzz!(|data: &[u8]| { jotdown_afl::parse_balance(data) });
}
