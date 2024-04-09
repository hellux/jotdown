use iai::black_box;

use jotdown::Render;

fn block() -> jotdown::Parser<'static> {
    jotdown::Parser::new(black_box(bench_input::ALL))
}

fn block_inline() -> Option<jotdown::Event<'static>> {
    black_box(jotdown::Parser::new(black_box(bench_input::ALL))).last()
}

fn full() -> String {
    jotdown::html::render_to_string(jotdown::Parser::new(bench_input::ALL))
}

iai::main!(block, block_inline, full);
