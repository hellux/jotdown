TEST=$(shell find ut -name '*.test' | sort)

BLACKLIST += djot_js_filters # lua filters not implemented
BLACKLIST += djot_js_symb # uses ast
BLACKLIST += djot_js_sourcepos # not parsable

ut/mod.rs: ${TEST} gen.awk skip
	mkdir -p ut
	rm -f $@
	for f in ${TEST}; do \
		gawk -fgen.awk $$f | head -n-1 > $${f%%test}rs; \
		name=$$(basename -s .test $$f); \
		echo ${BLACKLIST} | tr ' ' '\n' | grep -q $$name || echo "mod $$name;" >> $@; \
	done

clean:
	rm -f ut/*.rs
