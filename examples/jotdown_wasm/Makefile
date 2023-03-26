WASM=pkg/jotdown_wasm_bg.wasm

SRC=$(shell find src ../../src -name '*.rs')

${WASM}: ${SRC}
	wasm-pack build --release --target web

wasm: ${WASM}

index.html: Makefile demo.html
	echo '<!DOCTYPE html><html>' > $@
	echo '<head>' >> $@
	echo '<title>Jotdown Demo</title>' >> $@
	echo '</head>' >> $@
	echo '<body>' >> $@
	cat demo.html >> $@
	echo '</body>' >> $@
	echo '</html>' >> $@

run: ${WASM} index.html
	python -m http.server

clean:
	rm -rf pkg index.html
	cargo clean
