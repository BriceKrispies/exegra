#!/usr/bin/env bash
# Build formal/ (the Lean engine) to wasm32 and wasm64 from scratch and check it in Node.
# Usage: spike/lean-wasm/reproduce.sh <work dir>   (Git Bash on Windows, or any POSIX shell)
#   EMSDK=<existing emsdk checkout> to reuse one; otherwise emsdk is cloned and `latest` installed.
# Everything downloaded goes under <work dir>, each download in its own directory.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
work="$(mkdir -p "$1" && cd "$1" && pwd)"

# 1. emscripten
if [ -z "${EMSDK:-}" ]; then
  EMSDK="$work/emsdk-dl/emsdk"
  if [ ! -d "$EMSDK" ]; then
    mkdir -p "$work/emsdk-dl" && git clone --depth 1 https://github.com/emscripten-core/emsdk.git "$EMSDK"
    (cd "$EMSDK" && ./emsdk install latest && ./emsdk activate latest)
  fi
fi
export PATH="$EMSDK/upstream/emscripten:$PATH"
emcc --version | head -1

# 2. the Lean runtime sources of the toolchain's exact version, with the wasm patches
ver="v$(cd "$repo/formal" && lean --version | sed -E 's/.*version ([0-9.]+).*/\1/')"
lean4="$work/lean4-src/lean4"
if [ ! -d "$lean4" ]; then
  mkdir -p "$work/lean4-src"
  git clone --depth 1 --branch "$ver" --filter=blob:none --sparse https://github.com/leanprover/lean4.git "$lean4"
  (cd "$lean4" && MSYS_NO_PATHCONV=1 git sparse-checkout set --no-cone '/src/runtime/' '/src/include/' '/src/util/' && git apply "$repo/formal/wasm/patches/lean-v4.35.0-runtime-wasm.patch")
fi

# 3. libuv at the version Lean pins for its wasm build, with Lean's emscripten patch (no-proctitle.c)
uv="$work/libuv-dl/libuv"
if [ ! -d "$uv" ]; then
  mkdir -p "$work/libuv-dl" && git clone --depth 1 --branch v1.48.0 https://github.com/libuv/libuv.git "$uv"
  python -I - "$uv/CMakeLists.txt" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read(); a = 'if(CMAKE_SYSTEM_NAME STREQUAL "Linux")'
s = s.replace(a, 'if(CMAKE_SYSTEM_NAME STREQUAL "Emscripten")\n  list(APPEND uv_sources\n       src/unix/no-proctitle.c)\nendif()\n\n' + a, 1)
open(p, 'w', newline='\n').write(s)
PY
fi

# 4. formal/ itself, and C for the Init/Std modules it imports
(cd "$repo/formal" && lake build)
"$here/gen-stdlib-c.sh" "$work/c" 8

# 5. wasm32 and wasm64 builds
export LEAN4="$lean4"
for variant in 32 64; do
  out="$work/build$variant"
  if [ "$variant" = 64 ]; then export EXTRA_FLAGS="-sMEMORY64=1"; else unset EXTRA_FLAGS; fi
  mkdir -p "$out/libuv"
  (cd "$out/libuv" && emcmake cmake "$uv" -G Ninja -DCMAKE_BUILD_TYPE=Release -DLIBUV_BUILD_TESTS=OFF \
     -DLIBUV_BUILD_SHARED=OFF "-DCMAKE_C_FLAGS=-fwasm-exceptions ${EXTRA_FLAGS:-}" > cfg.log && ninja > build.log)
  "$here/build-runtime.sh" "$lean4" "$uv" "$out/rt"
  "$here/build-wasm.sh" "$work/c" "$out/rt" "$out/libuv" "$out/wasm" 8
done

# 6. check every golden in Node against the goldens and the native exegra-lean
native="$repo/formal/.lake/build/bin/exegra-lean"; [ -f "$native.exe" ] && native="$native.exe"
for variant in 32 64; do
  echo "== wasm$variant"
  (cd "$repo" && node spike/lean-wasm/run-node.mjs "$work/build$variant/wasm" --native "$native")
done
