# Jotdown

Jotdown is a pull parser Rust library for the [Djot][djot] markup language. It
parses a Djot document into a sequence of events and may also render the events
to HTML.

Jotdown aims to be fast and efficient, using a minimal number of allocations.
The API should use idiomatic Rust and be easy to use and flexible. The event
interface allows clients to e.g. construct an AST or generate any type of
output format. It also allows one to perform filters on the document before
generating the output. Jotdown aims to be feature complete and match the
[syntax reference][djot-syntax] and the [reference implementation][djot-js] in
terms of output.

Another goal is to keep the implementation minimal and build times low. The
current implementation has zero dependencies, if major non-essential features
are added or larger dependencies are utilized, these should be optional using
feature flags.

Jotdown supports Rust edition 2021, i.e. Rust 1.56 and above.

[djot]: https://djot.net
[djot-syntax]: https://htmlpreview.github.io/?https://github.com/jgm/djot/blob/master/doc/syntax.html
[djot-js]: https://github.com/jgm/djot.js

## Usage

Jotdown is primarily a parsing library but also has a minimal CLI
implementation and a simple web demo version.

### Library

The Jotdown API is inspired by [pulldown-cmark] and is overall very similar.
The Jotdown crate contains in-source documentation, a rendered version is
available at <https://docs.rs/jotdown>.

While Jotdown is usable, it is still in early development and breaking changes
to the API may occur frequently. The Djot syntax is also in quite early stages
and may also change significantly.

[pulldown-cmark]: https://github.com/raphlinus/pulldown-cmark

### CLI

The Jotdown crate contains a minimal implementation of a CLI that simply reads
from standard input and writes HTML to standard output. It can be built from
this repository and run locally with cargo:

```
$ cargo build --release
$ echo "hello world" | ./target/release/djot
<p>hello world</p>
```

Alternatively, it can be installed from the crates.io repository using simply:

```
$ cargo install jotdown
```

It will be placed in `~/.cargo/bin/jotdown`.

### Web demo

The web demo is a version of Jotdown compiled to WebAssembly and runnable in a
web browser. It is useful for experimenting with the djot syntax and exploring
what events are emitted or what output is rendered.

An online version is available at <https://hllmn.net/projects/jotdown/demo>. It
can also be run locally:

```
$ cd examples/jotdown_wasm
$ make run
```

You may need to install [wasm-pack] and make sure your Rust compiler has the
WebAssembly backend.

[wasm-pack]: https://rustwasm.github.io/wasm-pack/

## Status

### Correctness

As of writing, Jotdown implements all the current features of the Djot syntax,
including:

- links, images, either inline or with reference link definitions,
- autolinks,
- inline typesetting
    - emphasis,
    - highlight,
    - super/subscript,
    - insert/delete,
    - smart punctuation,
- inline verbatim, code and code blocks,
- math,
- line breaks,
- comments,
- symbols,
- headings, including hierarchical sections, and automatic links
- block quotes,
- lists,
    - unordered,
    - ordered,
    - task,
    - definitions,
- raw inline and blocks,
- thematic breaks,
- pipe tables,
- attributes, on inline and block elements,
- inline spans and div blocks,
- footnotes.

The HTML output is in some cases not exactly identical to the [reference
implementation][djot-js]. There are two test suites that compares Jotdown with
the reference implementation. One uses the unit tests of the reference
implementation and runs them with Jotdown. It can be run with:

```
$ make suite
```

Another target uses the reference implementation to generate html output for
its benchmark files and compares it to the output of Jotdown:

```
$ make suite_bench
```

Note that it requires node in order to run the reference implementation.

### Performance

There are benchmarks available to measure the performance. The input files are
borrowed from the [reference implementation][djot-js]. To fetch the input files
symlink them to the bench directory, run:

```
make bench
```

There are two separate benchmarks suites that can be run; criterion and iai.
Criterion measures statistical real-time performance while iai measures exact
number of executed instructions and memory accesses. To run the criterion
benchmarks, use

```
cargo bench -p bench-crit [filter]
```

Alternatively, if `cargo-criterion` is installed:

```
cargo criterion -p bench-crit -- [filter]
```

To run the iai benchmarks, use

```
cargo bench -p bench-iai
```
