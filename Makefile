.POSIX:

all: jotdown docs
	cargo build --workspace

jotdown: target/release/jotdown
	cp $< $@

target/release/jotdown:
	cargo build --release

.PHONY:
docs:
	cargo doc --no-deps --workspace

.PHONY: lint
lint:
	cargo fmt --all -- --check
	cargo clippy -- -D warnings
	cargo clippy --no-default-features -- -D warnings
	cargo clippy --all-features -- -D warnings

.PHONY: check
check:
	cargo test --workspace
	cargo test --workspace --no-default-features

.PHONY: suite
suite:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/test -name '*.test' | xargs basename -a); do \
		ln -fs ../../modules/djot.js/test/$$f tests/suite/$$f; \
	done
	(cd tests/suite && make)
	cargo test --features suite suite::

.PHONY: suite_bench
suite_bench:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		ln -fs ../../modules/djot.js/bench/$$f tests/bench/$$f; \
	done
	(cd tests/bench && make)
	cargo test --features suite_bench bench::

.PHONY: bench
bench:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		ln -fs ../modules/djot.js/bench/$$f bench/$$f; \
	done

cov: suite suite_bench
	LLVM_COV=llvm-cov LLVM_PROFDATA=llvm-profdata cargo llvm-cov --features=suite,suite_bench --workspace --html --ignore-run-fail

AFL_TARGET?=parse
AFL_JOBS?=1
AFL_TARGET_CRASH?=crashes

afl:
	rm -rf tests/afl/out
	(cd tests/afl && \
		cargo afl build --release --config profile.release.debug-assertions=true && \
		(AFL_NO_UI=1 cargo afl fuzz -i in -o out -Mm target/release/${AFL_TARGET} &) && \
		for i in $$(seq $$((${AFL_JOBS} - 1))); do \
			AFL_NO_UI=1 cargo afl fuzz -i in -o out -Ss$$i target/release/${AFL_TARGET} & \
		done; \
		trap - EXIT;\
		cat) # keep process alive for trap

afl_quick:
	rm -rf tests/afl/out
	(cd tests/afl && \
		cargo afl build --release --config profile.release.debug-assertions=true && \
		AFL_NO_UI=1 AFL_BENCH_UNTIL_CRASH=1 \
			cargo afl fuzz -i in -o out -V 60 target/release/${AFL_TARGET})

afl_crash:
	set +e; \
	for f in $$(find tests/afl/out -path '*/${AFL_TARGET_CRASH}/id*'); do \
		echo $$f; \
		out=$$(cat $$f | (cd tests/afl && RUST_BACKTRACE=1 cargo run ${AFL_TARGET} 2>&1)); \
		if [ $$? -ne 0 ]; then \
			echo; \
			echo "FAIL"; \
			echo "$$out"; \
			exit 1; \
		fi; \
	done

clean:
	cargo clean
	git submodule deinit -f --all
	rm -f tests/suite/*.test
	(cd tests/suite && make clean)
	rm -f tests/bench/*.dj
	(cd tests/bench && make clean)
	rm -f bench/*.dj
	rm -rf tests/afl/out
	(cd examples/jotdown_wasm && make clean)
