#!/bin/bash

# The wasm-build executable that is used to tree-shake the wasm binary
# resulting from the cargo build in the first step expects to find it
# under target/release/wasm32-unknown-unknown/ in the cwd.

cargo +nightly build --release --target=wasm32-unknown-unknown --verbose
wasm-build target subpeep --target-runtime=substrate --final=subpeep --save-raw=./target/subpeep-deployed.wasm --target wasm32-unknown-unknown
