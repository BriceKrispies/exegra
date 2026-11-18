#!/usr/bin/env bash
# Compile the Lean v4.35.0 C++ runtime (src/runtime of the lean4 repository at tag v4.35.0) to
# wasm32 objects with emscripten, single-threaded (no LEAN_MULTI_THREAD, no -pthread), without
# GMP (Lean's own mpn bignums) and without mimalloc, plus Lean's patched libuv include path.
# Usage: build-runtime.sh <lean4 checkout> <libuv source> <out dir>
set -euo pipefail
lean4="$1"; uv="$2"; out="$3"
mkdir -p "$out/obj" "$out/gen/lean"
cat > "$out/gen/lean/config.h" <<'H'
#pragma once
#include <lean/version.h>
#define LEAN_IS_STAGE0 0
H
cat > "$out/gen/lean/version.h" <<'H'
#pragma once
#define LEAN_VERSION_MAJOR 4
#define LEAN_VERSION_MINOR 35
#define LEAN_VERSION_PATCH 0
#define LEAN_VERSION_IS_RELEASE 1
#define LEAN_SPECIAL_VERSION_DESC ""
#define LEAN_VERSION_STRING "4.35.0"
#define LEAN_PLATFORM_TARGET "wasm32-unknown-emscripten"
#define LEAN_MANUAL_ROOT "https://lean-lang.org/doc/reference/4.35.0/"
H
echo '#define LEAN_GITHASH ""' > "$out/gen/githash.h"
srcs="debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module
  io hash byteslice platform alloc allocprof sharecommon stack_overflow process object_ref mpn
  mutex libuv uv/net_addr uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal openssl"
# EXTRA_FLAGS: e.g. "-sMEMORY64=1" for a wasm64 build (then pass the same to build-wasm.sh)
FLAGS=(-std=c++20 -O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -ffp-contract=off ${EXTRA_FLAGS:-}
  -I"$out/gen" -I"$lean4/src" -I"$lean4/src/include" -I"$uv/include" -Wno-deprecated
  # runtime/thread.h: the single-threaded unique_lock stub names std::adopt_lock_t but only the
  # multi-threaded branch includes <mutex>, so force-include it (a v4.35.0 build bug)
  -include mutex)
export out lean4
printf '%s
' $srcs | xargs -P 6 -I{} sh -c   'em++ "$@" -c "$lean4/src/runtime/{}.cpp" -o "$out/obj/$(echo {} | tr / _).o"' sh "${FLAGS[@]}"
rm -f "$out/libleanrt.a"
emar rcs "$out/libleanrt.a" "$out"/obj/*.o
echo "built $out/libleanrt.a"
