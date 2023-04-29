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
	cargo clippy --workspace -- -D warnings
	cargo clippy --workspace --no-default-features -- -D warnings
	cargo clippy --workspace --all-features -- -D warnings

.PHONY: check
check:
	cargo test --workspace
	cargo test --workspace --no-default-features

.PHONY: suite
suite:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/test -name '*.test' | xargs basename -a); do \
		ln -fs ../../modules/djot.js/test/$$f tests/suite/djot_js_$$f; \
	done
	(cd tests/suite && make)
	cargo test --features suite suite::

.PHONY: suite_bench
suite_bench:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		dst=$$(echo $$f | sed 's/-/_/g'); \
		ln -fs ../../modules/djot.js/bench/$$f tests/bench/$$dst; \
	done
	(cd tests/bench && make)
	cargo test --features suite_bench bench::

.PHONY: bench
bench:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		dst=$$(echo $$f | sed 's/-/_/g'); \
		ln -fs ../../modules/djot.js/bench/$$f bench/input/$$dst; \
	done

cov: suite suite_bench
	LLVM_COV=llvm-cov LLVM_PROFDATA=llvm-profdata cargo llvm-cov --features=suite,suite_bench --workspace --html --ignore-run-fail

AFL_TARGET?=parse
AFL_JOBS?=1
AFL_TARGET_CRASH?=crashes

afl:
	rm -rf tests/afl/out
	(cd tests/afl && \
		cargo afl build --no-default-features --release --config profile.release.debug-assertions=true && \
		(AFL_NO_UI=1 cargo afl fuzz -i in -o out -Mm target/release/${AFL_TARGET} &) && \
		for i in $$(seq $$((${AFL_JOBS} - 1))); do \
			AFL_NO_UI=1 cargo afl fuzz -i in -o out -Ss$$i target/release/${AFL_TARGET} & \
		done; \
		trap - EXIT;\
		cat) # keep process alive for trap

afl_quick:
	rm -rf tests/afl/out
	(cd tests/afl && \
		cargo afl build --no-default-features --release --config profile.release.debug-assertions=true && \
		AFL_NO_UI=1 AFL_BENCH_UNTIL_CRASH=1 \
			cargo afl fuzz -i in -o out -V 60 target/release/${AFL_TARGET})
	[ -z "$$(find tests/afl/out/default/crashes -type f -name 'id:*')" ]

afl_crash:
	set +e; \
	failures="$$(find . -path './tmin/*') $$(find tests/afl/out -path '*/${AFL_TARGET_CRASH}/id*')"; \
	for f in $$failures; do \
		echo $$f; \
		out=$$(cat $$f | (cd tests/afl && RUST_BACKTRACE=1 cargo run ${AFL_TARGET} 2>&1)); \
		if [ $$? -ne 0 ]; then \
			echo; \
			echo "FAIL"; \
			echo "$$out"; \
			exit 1; \
		fi; \
	done

afl_tmin:
	rm -rf tmin
	mkdir tmin
	for f in $$(find tests/afl/out -path '*/${AFL_TARGET_CRASH}/id*'); do \
		cargo afl tmin -i $$f -o tmin/$$(basename $$f) tests/afl/target/release/${AFL_TARGET}; \
	done

clean:
	cargo clean
	rm -rf bench/iai/target
	git submodule deinit -f --all
	find tests -type l -path 'tests/suite/*.test' -print0 | xargs -0 rm -f
	(cd tests/suite && make clean)
	rm -f tests/bench/*.dj
	(cd tests/bench && make clean)
	find bench -type l -path 'bench/*.dj' -print0 | xargs -0 rm -f
	rm -rf tests/afl/out
	(cd examples/jotdown_wasm && make clean)
