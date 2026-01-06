use criterion::criterion_group;
use criterion::criterion_main;
use jotup::RenderExt;

fn gen_block(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("block");
    for (name, input) in bench_input::INPUTS {
        group.throughput(criterion::Throughput::Bytes(input.len() as u64));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(name),
            input,
            |b, &input| {
                b.iter(|| jotup::Parser::new(input));
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
                    || jotup::Parser::new(input),
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
            jotup::Parser::new(input).count() as u64,
        ));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(name),
            input,
            |b, &input| {
                b.iter_batched(
                    || jotup::Parser::new(input).collect::<Vec<_>>(),
                    |p| jotup::html::Renderer::default().render_events(p.into_iter()),
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }
}
criterion_group!(html, gen_html);

fn gen_html_clone(c: &mut criterion::Criterion) {
    let mut group = c.benchmark_group("html_clone");
    for (name, input) in bench_input::INPUTS {
        group.throughput(criterion::Throughput::Elements(
            jotup::Parser::new(input).count() as u64,
        ));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(name),
            input,
            |b, &input| {
                b.iter_batched(
                    || jotup::Parser::new(input).collect::<Vec<_>>(),
                    |p| jotup::html::Renderer::default().render_events(p.into_iter()),
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
                b.iter_with_large_drop(|| jotup::html::render_to_string(input));
            },
        );
    }
}
criterion_group!(full, gen_full);

criterion_main!(block, inline, html, html_clone, full);
