WASM=pkg/jotdown_wasm_bg.wasm

SRC=$(shell find . ../../src -name '*.rs')

${WASM}: ${SRC}
	wasm-pack build --release --target web

wasm: ${WASM}

index.html: Makefile demo.html
	# demo.html doesn't contain a doctype so that it can be easily
	# embedded in other web pages (which is used for the online demo)
	echo '<!DOCTYPE html><html>' > $@
	echo '<head>' >> $@
	echo '<title>Jotdown Demo</title>' >> $@
	echo '</head>' >> $@
	echo '<body style="display:flex;flex-direction:column;height:100vh;margin:0">' >> $@
	cat demo.html >> $@
	echo '</body>' >> $@
	echo '</html>' >> $@

run: ${WASM} index.html
	python -m http.server

clean:
	rm -rf pkg index.html
	cargo clean
