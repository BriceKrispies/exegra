#!/usr/bin/env bash
# Emit C for every Init/Std module in the import closure of formal/Main.lean, using the installed
# toolchain's own `lean -c` on the sources it ships (src/lean). The toolchain's .olean files of
# the imports are reused, so no module is rebuilt; only the code generator runs.
# Usage: gen-stdlib-c.sh <out dir> [jobs]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="$1"; jobs="${2:-6}"
# elan's `lean` is a proxy; ask it for the real sysroot of the project's toolchain
tc="$(cd "$here/../../formal" && lean --print-prefix | tr -d '')"
command -v cygpath >/dev/null && tc="$(cygpath -u "$tc")"
mkdir -p "$out"
python -I "$here/modules.py" "$here/../../formal" "$tc/src/lean" | grep -E '^(Init|Std)' > "$out/modules.txt"
export LEAN_PATH="$tc/lib/lean" TC="$tc" OUT="$out"
cd "$tc/src/lean"
xargs -P "$jobs" -I{} bash -c '
  m="{}"; f="${m//.//}.lean"
  "$TC/bin/lean" --root=. -c "$OUT/$m.c" "$f" > "$OUT/$m.log" 2>&1 || echo "FAILED $m"
' < "$out/modules.txt"
echo "emitted $(ls "$out"/*.c | wc -l) C files"
