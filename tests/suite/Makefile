.POSIX:

.SUFFIXES: .test .rs

TEST=$(shell find . -name '*.test' | sort)
TEST_RS=${TEST:.test=.rs}

BLACKLIST += filters # lua filters not implemented
BLACKLIST += symb # uses ast
BLACKLIST += sourcepos # not parsable

.PHONY: suite
suite: mod.rs

mod.rs: ${TEST_RS}
	printf "" > $@
	for f in ${TEST}; do \
		name=$$(basename -s .test $$f); \
		echo ${BLACKLIST} | tr ' ' '\n' | grep -q $$name || echo "mod $$name;" >> $@; \
	done

.test.rs:
	gawk -fgen.awk $< > $@

clean:
	rm -f *.rs
