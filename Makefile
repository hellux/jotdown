.POSIX:

all: jotdown docs
	cargo build --workspace

jotdown: target/release/jotdown
	cp $< $@

target/release/jotdown:
	cargo build --release --all-features

.PHONY:
docs:
	RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --workspace

.PHONY: lint
lint:
	cargo clippy -- -D warnings
	cargo clippy --no-default-features -- -D warnings
	cargo clippy --all-features -- -D warnings
	cargo check --all
	cargo fmt --all -- --check

.PHONY: check
check:
	cargo test --workspace
	cargo test --workspace --no-default-features

.PHONY: enable-git-hooks
enable-git-hooks:
	git config --local core.hooksPath contrib/

.PHONY: test_html_ut
test_html_ut:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/test -name '*.test' | xargs basename -a); do \
		ln -fs ../../../modules/djot.js/test/$$f tests/html-ut/ut/djot_js_$$f; \
	done
	cargo test -p test-html-ut
	cargo test -p test-html-ut -- --ignored 2>/dev/null | grep -qE 'test result: .* 0 passed'

.PHONY: test_html_ref
test_html_ref:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		dst=$$(echo $$f | sed 's/-/_/g'); \
		ln -fs ../../modules/djot.js/bench/$$f tests/html-ref/$$dst; \
	done
	cargo test -p test-html-ref
	cargo test -p test-html-ut -- --ignored 2>/dev/null | grep -qE 'test result: .* 0 passed'

.PHONY: bench
bench:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		dst=$$(echo $$f | sed 's/-/_/g'); \
		ln -fs ../../modules/djot.js/bench/$$f bench/input/$$dst; \
	done

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
	while [ -n "$$(md5sum tmin/* | sort -k1 | rev | uniq -d -f1)" ]; do \
		md5sum tmin/* | sort -k1 | rev | uniq -d -f1 | rev | awk '{print $$2}' | xargs rm -f; \
	done

clean:
	cargo clean
	(cd tests/afl && cargo clean)
	git submodule deinit -f --all
	find tests -type l -path 'tests/html-ut/ut/*.test' -print0 | xargs -0 rm -f
	(cd tests/html-ut && make clean)
	rm -f tests/html-ref/*.dj
	(cd tests/html-ref && make clean)
	find bench -type l -path 'bench/*.dj' -print0 | xargs -0 rm -f
	rm -rf tests/afl/out
	(cd examples/jotdown_wasm && make clean)
