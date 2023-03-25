use iai::black_box;

use jotdown::Render;

fn block() -> jotdown::Parser<'static> {
    jotdown::Parser::new(black_box(bench_input::ALL))
}

fn block_inline() -> Option<jotdown::Event<'static>> {
    black_box(jotdown::Parser::new(black_box(bench_input::ALL))).last()
}

fn full() -> String {
    let mut s = String::new();
    jotdown::html::Renderer::default()
        .push(jotdown::Parser::new(bench_input::ALL), &mut s)
        .unwrap();
    s
}

iai::main!(block, block_inline, full);
