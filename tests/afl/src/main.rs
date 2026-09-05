use std::io::Read;

fn main() {
    let mut args = std::env::args();
    let _program = args.next();
    let target = args.next().expect("no target");
    assert_eq!(args.next(), None);

    env_logger::init();

    let f = match target.as_str() {
        "attr" => jotdown_afl::attr,
        "parse" => jotdown_afl::parse,
        "html" => jotdown_afl::html,
        _ => panic!("unknown target '{target}'"),
    };

    let mut input = Vec::new();
    std::io::stdin().read_to_end(&mut input).unwrap();
    f(&input);
}
