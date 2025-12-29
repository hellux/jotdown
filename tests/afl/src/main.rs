use std::io::Read;

fn main() {
    let mut args = std::env::args();
    let _program = args.next();
    let target = args.next().expect("no target");
    assert_eq!(args.next(), None);

    let f = match target.as_str() {
        "parse" => jotdown_afl::parse,
        "html" => jotdown_afl::html,
        _ => panic!("unknown target '{target}'"),
    };

    let mut input = Vec::new();
    std::io::stdin().read_to_end(&mut input).unwrap();
    f(&input);
}
