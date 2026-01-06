> **Note:** This is a fork of [jotdown](https://github.com/hellux/jotdown) pursuing slightly different API design and async support. All credit for the original implementation goes to the original authors.

# Jotup

[API documentation] | [Repository]

[API documentation]: https://docs.rs/jotup
[repository]: https://github.com/dpc/jotup

Jotup is a pull parser Rust library for the [Djot][djot] markup language. It
parses a Djot document into a sequence of events and may also render the events
to HTML.

Jotup aims to be fast and efficient, using a minimal number of allocations.
The API should use idiomatic Rust and be easy to use and flexible. The event
interface allows downstream crates to e.g. construct an AST or generate any
type of output format. It also allows one to perform filters on the document
before generating the output. Jotup aims to be feature complete and match the
[syntax reference][djot-syntax] and the [reference implementation][djot-js] in
terms of output.

Another goal is to keep the implementation minimal and build times low. The
current implementation has zero dependencies, if major non-essential features
are added or larger dependencies are utilized, these should be optional using
feature flags.

Jotup supports Rust edition 2021, i.e. Rust 1.56 and above.

[djot]: https://djot.net
[djot-syntax]: https://htmlpreview.github.io/?https://github.com/jgm/djot/blob/master/doc/syntax.html
[djot-js]: https://github.com/jgm/djot.js

## Usage

Jotup is primarily a parsing library but also has a minimal CLI
implementation and a simple web demo version.

### Library

The Jotup API is inspired by [pulldown-cmark] and is overall very similar.
The Jotup crate contains in-source documentation, a rendered version is
available at <https://docs.rs/jotup>.

While Jotup is usable, it is still in development and breaking changes to the
API may occur. The Djot syntax is also not stabilized and may change.

[pulldown-cmark]: https://github.com/raphlinus/pulldown-cmark

### CLI

The Jotup crate contains a minimal implementation of a CLI that simply reads
from standard input and writes HTML to standard output. It can be built from
this repository and run locally with cargo:

```
$ cargo build --release
$ echo "hello world" | ./target/release/jotup
<p>hello world</p>
```

Note: Jotup is not currently published to crates.io. You can install it from source:

```
$ cargo install --path .
```

It will be placed in `~/.cargo/bin/jotup`.

### Web demo

The web demo is a version of Jotup compiled to WebAssembly and runnable in a
web browser. It is useful for experimenting with the djot syntax and exploring
what events are emitted or what output is rendered.

You can run it locally:

```
$ cd examples/jotup_wasm
$ make run
```

You may need to install [wasm-pack] and make sure your Rust compiler has the
WebAssembly backend.

[wasm-pack]: https://rustwasm.github.io/wasm-pack/

## Status

### Correctness

As of writing, Jotup implements all current features of the Djot syntax. Any
difference in parsing or HTML rendering from the [reference
implementation][djot-js] is considered a bug.

Feature requests for changed syntax or HTML rendering will be implemented if it
is agreed to be implemented in the reference implementation first. Create a new
[issue][djot-issue] or a new [discussion][djot-discussion] in the official djot
repo first for such requests.

[djot-issue]: https://github.com/jgm/djot/issues
[djot-discussion]: https://github.com/jgm/djot/discussions

There are still some known HTML differences from the reference implementation.
There are two test suites that compares Jotup's HTML output with that of the
reference implementation. Their known failures are listed in
`tests/html-ut/skip` and `tests/html-ref/skip`.

One of the suites uses the unit tests of the reference implementation and runs
them with Jotdown. It can be run with:

```
$ make test_html_ut
```

Another target uses the reference implementation to generate html output for
its benchmark files and compares it to the output of Jotup:

```
$ make test_html_ref
```

Note that it requires node in order to run the reference implementation.

### Performance

There are benchmarks available to measure the performance. The input files are
borrowed from the [reference implementation][djot-js]. To fetch the input files
symlink them to the bench directory, run:

```
make bench
```

To run the benchmarks, use

```
cargo bench -p bench-crit [filter]
```

Alternatively, if `cargo-criterion` is installed:

```
cargo criterion -p bench-crit -- [filter]
```

There are also external benchmarks that compare the original jotdown to other markdown/djot
implementations:

- https://github.com/rosetta-rs/md-rosetta-rs
- https://github.com/dcampbell24/djot-implementations

### See also

- [djot_ast][]: Rust crate with djot AST types.
- [djotfmt][]: Djot source code formatter.
- [mdbook-djot][]: Plugin for mdbook to add support for djot files.

[djot_ast]: https://github.com/clbarnes/djot_ast
[djotfmt]: https://github.com/black-desk/djotfmt
[mdbook-djot]: https://github.com/dcampbell24/mdbook-djot
