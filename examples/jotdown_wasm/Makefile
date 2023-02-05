WASM=pkg/jotdown_wasm_bg.wasm

SRC=$(shell find src ../../src -name '*.rs')

${WASM}: ${SRC}
	wasm-pack build --release --target web

wasm: ${WASM}

run: ${WASM}
	python -m http.server

clean:
	rm -rf pkg
	cargo clean
