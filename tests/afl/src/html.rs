fn main() {
    afl::fuzz!(|data: &[u8]| { jotup_afl::html(data) });
}
