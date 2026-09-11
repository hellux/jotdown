fn main() {
    afl::fuzz!(|data: &str| jotdown_afl::parse(data));
}
