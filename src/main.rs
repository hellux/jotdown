use std::io::Read;

fn main() {
    let mut src = String::new();
    std::io::stdin()
        .read_to_string(&mut src)
        .expect("failed to read unicode file");

    print!("{}", jotdown::parse(&src));
}
