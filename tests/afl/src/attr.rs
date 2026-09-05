fn main() {
    afl::fuzz!(|data: &str| jotdown_afl::attr(data));
}
