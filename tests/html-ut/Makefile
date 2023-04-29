.POSIX:

.SUFFIXES: .test .rs

TEST=$(shell find ut -name '*.test' | sort)
TEST_RS=${TEST:.test=.rs}

BLACKLIST += djot_js_filters # lua filters not implemented
BLACKLIST += djot_js_symb # uses ast
BLACKLIST += djot_js_sourcepos # not parsable

ut/mod.rs: ${TEST_RS}
	mkdir -p ut
	rm -f $@
	for f in ${TEST}; do \
		name=$$(basename -s .test $$f); \
		echo ${BLACKLIST} | tr ' ' '\n' | grep -q $$name || echo "mod $$name;" >> $@; \
	done

.test.rs:
	gawk -fgen.awk $< | head -n-1 > $@

clean:
	rm -f ut/*.rs
