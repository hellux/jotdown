.POSIX:

.PHONY: suite
suite:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/test -name '*.test' | xargs basename -a); do \
		ln -fs ../../modules/djot.js/test/$$f tests/suite/$$f; \
	done
	(cd tests/suite && make)
	cargo test --features suite

.PHONY: suite_bench
suite_bench:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		ln -fs ../../modules/djot.js/bench/$$f tests/bench/$$f; \
	done
	(cd tests/bench && make)
	cargo test --features suite_bench

.PHONY: bench
bench:
	git submodule update --init modules/djot.js
	for f in $$(find modules/djot.js/bench -name '*.dj' | xargs basename -a); do \
		ln -fs ../modules/djot.js/bench/$$f benches/$$f; \
	done

clean:
	cargo clean
	git submodule deinit -f --all
	rm -f tests/suite/*.test
	(cd tests/suite && make clean)
	rm -f tests/bench/*.dj
	(cd tests/bench && make clean)
	rm -f benches/*.dj
