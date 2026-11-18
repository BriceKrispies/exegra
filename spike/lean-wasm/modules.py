"""Print the transitive import closure of formal/Main.lean, one module name per line.

Every Lean module implicitly imports `Init` unless it starts with `prelude`. Modules are looked up
in formal/ first, then in the toolchain's src/lean (Init, Std, Lean sources ship with it).
Usage: python modules.py <formal dir> <toolchain src/lean dir>
"""
import re
import sys
from pathlib import Path

formal, stdsrc = Path(sys.argv[1]), Path(sys.argv[2])
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)", re.M)


def find(mod):
    rel = Path(*mod.split(".")).with_suffix(".lean")
    for root in (formal, stdsrc):
        if (root / rel).exists():
            return root / rel
    raise SystemExit(f"module not found: {mod}")


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


seen, order, todo = set(), [], ["Main"]
while todo:
    mod = todo.pop()
    if mod in seen:
        continue
    seen.add(mod)
    order.append(mod)
    text = strip_comments(find(mod).read_text(encoding="utf-8"))
    header = text.split("\nnamespace", 1)[0]
    imports = IMPORT.findall(header)
    if not re.search(r"^\s*prelude\b", header, re.M):
        imports.append("Init")
    todo.extend(imports)
for mod in sorted(order):
    print(mod)
