.POSIX:

.PHONY: suite
suite:
	git submodule update --init modules/djot
	for f in $$(find modules/djot/test -name '*.test' | xargs basename -a); do \
		ln -fs ../../modules/djot/test/$$f tests/suite/$$f; \
	done
	(cd tests/suite && make)
	cargo test --features suite

clean:
	cargo clean
	git submodule deinit -f --all
	rm -f tests/suite/*.test
	(cd tests/suite && make clean)
