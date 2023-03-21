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
                        jotdown::html::Renderer::default()
                            .push(p.into_iter(), &mut s)
                            .unwrap();
                        s
                    },
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }
}
criterion_group!(html, gen_html);

fn gen_html_borrow(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("html_borrow");
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
                        jotdown::html::Renderer::default()
                            .push_borrowed(p.as_slice().iter(), &mut s)
                            .unwrap();
                        s
                    },
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }
}
criterion_group!(html_borrow, gen_html_borrow);

fn gen_html_clone(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("html_clone");
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
                        jotdown::html::Renderer::default()
                            .push(p.iter().cloned(), &mut s)
                            .unwrap();
                        s
                    },
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }
}
criterion_group!(html_clone, gen_html_clone);

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
                    jotdown::html::Renderer::default()
                        .push(jotdown::Parser::new(input), &mut s)
                        .unwrap();
                    s
                });
            },
        );
    }
}
criterion_group!(full, gen_full);

criterion_main!(block, inline, html, html_borrow, html_clone, full);
