fn main() {
    afl::fuzz!(|data: &str| jotdown_afl::html(data));
}
