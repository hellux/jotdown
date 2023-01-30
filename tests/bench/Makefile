.POSIX:

TEST_DJ=$(shell find . -name '*.dj' | sort)
TEST=${TEST_DJ:.dj=}

DJOT_JS=../../modules/djot.js
DJOT_JS_SRC=$(shell find ${DJOT_JS}/src -name '.ts')

mod.rs: ${TEST_DJ} html
	echo "use crate::suite_test;" > $@
	for name in ${TEST}; do \
		name_snake=$$(basename -a $$name | sed 's/-/_/g'); \
		echo "#[test]" >> $@; \
		echo "fn test_$$name_snake() {" >> $@; \
		printf '    let src = r###"' >> $@; \
		cat $$name.dj >> $@; \
		echo '"###;' >> $@; \
		printf '    let expected = r###"' >> $@; \
		cat $$name.html >> $@; \
		echo '"###;' >> $@; \
		echo "    suite_test!(src, expected);" >> $@; \
		echo "}" >> $@; \
	done

html: djot-js ${TEST_DJ}
	echo ${TEST}
	for name in ${TEST}; do cat $$name.dj | ./djot-js > $$name.html; done
	touch $@

djot-js: ${DJOT_JS_SRC}
	(cd "${DJOT_JS}" && npm install && npm run build)
	echo "#!/bin/sh" > $@
	echo 'node ${DJOT_JS}/lib/cli.js "$$@"' >> $@
	chmod +x $@

clean:
	rm -f *.rs *.html
	rm -f html
	rm -f djot-js
