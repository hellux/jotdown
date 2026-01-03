# Fuzzing for jotdown

This directory contains fuzzing targets for jotdown using cargo-fuzz.

## Prerequisites

### Using Nix (Recommended)

The project's Nix flake provides a fuzzing environment with nightly Rust:

```bash
# Enter the fuzzing environment
nix develop .#fuzz

# Or run directly
nix develop .#fuzz -c bash -c "cd fuzz && cargo fuzz run compare_renderers"
```

### Manual Setup

Install cargo-fuzz (requires nightly Rust):
```bash
rustup toolchain install nightly
cargo +nightly install cargo-fuzz
```

## Fuzzing Targets

### compare_renderers

Compares the sync and async HTML renderers to ensure they:
1. Don't crash on random Djot input
2. Produce identical HTML output

This ensures the async implementation is logically equivalent to the sync implementation.

## Running the Fuzzer

### With Nix

```bash
# Run the fuzzer (will run indefinitely until stopped with Ctrl+C)
nix develop .#fuzz -c bash -c "cd fuzz && cargo fuzz run compare_renderers"

# Run for a specific duration (60 seconds)
nix develop .#fuzz -c bash -c "cd fuzz && cargo fuzz run compare_renderers -- -max_total_time=60"

# Run with more jobs (parallel fuzzing)
nix develop .#fuzz -c bash -c "cd fuzz && cargo fuzz run compare_renderers -- -jobs=4"
```

### Manual

```bash
cd fuzz

# Run the fuzzer (will run indefinitely until stopped with Ctrl+C)
cargo +nightly fuzz run compare_renderers

# Run for a specific duration
cargo +nightly fuzz run compare_renderers -- -max_total_time=60

# Run with more jobs (parallel fuzzing)
cargo +nightly fuzz run compare_renderers -- -jobs=4

# List all fuzz targets
cargo +nightly fuzz list
```

## Examining Results

If the fuzzer finds a crash:
```bash
# Crashes are saved in fuzz/artifacts/compare_renderers/
ls artifacts/compare_renderers/

# Reproduce a crash
cargo fuzz run compare_renderers fuzz/artifacts/compare_renderers/crash-<hash>
```

## Coverage

Generate coverage information:
```bash
cargo fuzz coverage compare_renderers
```
