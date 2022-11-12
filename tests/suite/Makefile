.POSIX:

.SUFFIXES: .test .rs

TEST=$(shell find . -name '*.test' | sort)
TEST_RS=${TEST:.test=.rs}

.PHONY: suite
suite: mod.rs

mod.rs: ${TEST_RS}
	printf "" > $@
	for f in ${TEST}; do \
		name=$$(basename -s .test $$f); \
		echo "mod $$name;" >> $@; \
	done

.test.rs:
	awk -fgen.awk $< > $@

clean:
	rm -f *.rs
