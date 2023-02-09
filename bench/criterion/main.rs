use criterion::criterion_group;
use criterion::criterion_main;

use jotdown::Render;

fn gen_block(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("block");
    for (name, input) in bench_input::INPUTS {
        group.throughput(criterion::Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(name),
            input,
            |b, &input| {
                b.iter(|| jotdown::Parser::new(input));
            },
        );
    }
}
criterion_group!(block, gen_block);

fn gen_inline(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("inline");
    for (name, input) in bench_input::INPUTS {
        group.throughput(criterion::Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(name),
            input,
            |b, &input| {
                b.iter_batched(
                    || jotdown::Parser::new(input),
                    |p| p.last().unwrap(),
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }
}
criterion_group!(inline, gen_inline);

fn gen_html(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("html");
    for (name, input) in bench_input::INPUTS {
        group.throughput(criterion::Throughput::Elements(
            jotdown::Parser::new(input).count() as u64,
        ));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(name),
            input,
            |b, &input| {
                b.iter_batched(
                    || jotdown::Parser::new(input).collect::<Vec<_>>(),
                    |p| {
                        let mut s = String::new();
                        jotdown::html::Renderer.push(p.into_iter(), &mut s).unwrap();
                        s
                    },
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }
}
criterion_group!(html, gen_html);

fn gen_full(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("full");
    for (name, input) in bench_input::INPUTS {
        group.throughput(criterion::Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(name),
            input,
            |b, &input| {
                b.iter_with_large_drop(|| {
                    let mut s = String::new();
                    jotdown::html::Renderer
                        .push(jotdown::Parser::new(input), &mut s)
                        .unwrap();
                    s
                });
            },
        );
    }
}
criterion_group!(full, gen_full);

criterion_main!(block, inline, html, full);
