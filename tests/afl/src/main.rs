use std::io::Read;

fn main() {
    let mut args = std::env::args();
    let _program = args.next();
    let target = args.next().expect("no target");
    assert_eq!(args.next(), None);

    env_logger::init();

    let f = match target.as_str() {
        "attr" => |data: &[u8]| {
            jotdown_afl::parse(
                arbitrary::Arbitrary::arbitrary(&mut arbitrary::Unstructured::new(data))
                    .unwrap_or_default(),
            );
        },
        "parse" => |data: &[u8]| {
            jotdown_afl::parse(
                arbitrary::Arbitrary::arbitrary(&mut arbitrary::Unstructured::new(data))
                    .unwrap_or_default(),
            );
        },
        "html" => |data: &[u8]| {
            jotdown_afl::html(
                arbitrary::Arbitrary::arbitrary(&mut arbitrary::Unstructured::new(data))
                    .unwrap_or_default(),
            );
        },
        _ => panic!("unknown target '{target}'"),
    };

    let mut input = Vec::new();
    std::io::stdin().read_to_end(&mut input).unwrap();
    f(&input);
}
