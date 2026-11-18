#!/usr/bin/env bash
# Compile the generated C (Init/Std from gen-stdlib-c.sh, Exegra from formal's `lake build`, the
# WasmEntry module) with emscripten and link it with the wasm runtime into exegra-lean.mjs/.wasm.
# Usage: LEAN4=<lean4 v4.35.0 checkout> build-wasm.sh <stdlib C dir> <runtime out dir> <libuv build dir> <out dir> [jobs]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
stdc="$1"; rt="$2"; uvb="$3"; out="$4"; jobs="${5:-8}"
formal="$here/../../formal"
tc="$(cd "$formal" && lean --print-prefix | tr -d '\r')"
command -v cygpath >/dev/null && tc="$(cygpath -u "$tc")"
sep=":"; command -v cygpath >/dev/null && sep=";"
lp="$tc/lib/lean$sep$formal/.lake/build/lib/lean"
command -v cygpath >/dev/null && lp="$(cygpath -w "$tc/lib/lean");$(cygpath -w "$formal/.lake/build/lib/lean")"
mkdir -p "$out/c" "$out/obj"
LEAN_PATH="$lp" "$tc/bin/lean" -c "$out/c/WasmEntry.c" "$here/WasmEntry.lean"
cp -p "$stdc"/*.c "$out/c/"
for f in "$formal"/.lake/build/ir/Exegra/*.c; do cp -p "$f" "$out/c/Exegra.$(basename "$f")"; done
cp -p "$here/glue.c" "$out/c/glue.c"
export out rt LEAN4
# lean.h lays out the 8-byte scalar literals of static constructor objects (LEAN_SCALAR_PTR_LITERAL)
# as two 4-byte pointers only when LEAN_EMSCRIPTEN is defined; without it, wasm32 objects come out
# 4 bytes short and reads run past them. Under wasm64 (-sMEMORY64=1) pointers are 8 bytes, so the
# 64-bit layout is the right one and LEAN_EMSCRIPTEN must stay undefined for the generated C.
case "${EXTRA_FLAGS:-}" in *MEMORY64*) PLAT="" ;; *) PLAT="-DLEAN_EMSCRIPTEN" ;; esac
CFLAGS="-O3 -DNDEBUG $PLAT -fwasm-exceptions -ffp-contract=off -Wno-unused-parameter -Wno-unused-label ${EXTRA_FLAGS:-}"
export CFLAGS
ls "$out/c" | grep '\.c$' | xargs -P "$jobs" -I{} sh -c '
  o="$out/obj/{}.o"
  [ "$o" -nt "$out/c/{}" ] || emcc $CFLAGS -I"$rt/gen" -I"$LEAN4/src/include" -c "$out/c/{}" -o "$o"'
# the object list is too long for one command line on Windows: pass it in a response file
(cd "$out/obj" && ls *.o | sed "s|^|obj/|") > "$out/objs.rsp"
cd "$out"
em++ -O3 -fwasm-exceptions ${EXTRA_FLAGS:-} @objs.rsp "$rt/libleanrt.a" "$uvb/libuv.a" -o "$out/exegra-lean.mjs" \
  -sALLOW_MEMORY_GROWTH=1 -sSTACK_SIZE=8MB -sMODULARIZE=1 -sEXPORT_ES6=1 -sENVIRONMENT=web,node \
  -sEXPORTED_FUNCTIONS=_exegra_init,_exegra_run,_exegra_result_ptr,_exegra_result_len,_malloc,_free \
  -sEXPORTED_RUNTIME_METHODS=UTF8ToString,stringToUTF8,lengthBytesUTF8,HEAPU8
ls -l "$out/exegra-lean.mjs" "$out/exegra-lean.wasm"
