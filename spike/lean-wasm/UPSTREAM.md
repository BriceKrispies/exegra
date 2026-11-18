# Lean runtime bugs met by the wasm spike, and their upstream status

Checked 2026-11-18 against the v4.35.0 and v4.36.0 tags and `master` of leanprover/lean4.

## 1. `String.toList` returns a malformed list on 32-bit targets (v4.35.0 and earlier)

**What is wrong.** In `src/runtime/object.cpp` (v4.35.0), `string_to_list_core` builds the list of
characters behind `String.toList` / `String.data` (`lean_string_data`) and ends it with:

```cpp
obj_res r = lean_box_uint32(0);   // meant to be List.nil
```

`List.nil` is the scalar `lean_box(0)`. `lean_box_uint32` (`src/include/lean/lean.h`) is the boxing of
a `UInt32` value, and it depends on the pointer width:

```cpp
static inline lean_obj_res lean_box_uint32(uint32_t v) {
    if (sizeof(void*) == 4) {            // 32-bit: a heap object holding the value
        lean_obj_res r = lean_alloc_ctor(0, 0, sizeof(uint32_t));
        lean_ctor_set_uint32(r, 0, v);
        return r;
    } else {                             // 64-bit: the scalar lean_box(v)
        return lean_box(v);
    }
}
```

On 64-bit targets `lean_box_uint32(0) == lean_box(0)`, so the bug is invisible. On any 32-bit target
(wasm32, i686, armv7) the list ends in a heap constructor with tag 0 and no object fields instead of
the scalar nil. Code that walks the list stops at the first scalar, so it treats the "nil" as a cons
cell and reads fields it does not have. `lean_string_mk` (`String.mk`, `String.ofList`) is the first
victim: it reads a NULL character pointer. In the spike this gave `std::bad_alloc` or out-of-bounds
traps on almost every engine input. AddressSanitizer reported a null-pointer dereference in
`lean_unbox_uint32` under `lean_string_mk`.

**Fix.** `obj_res r = lean_box(0);`. This is the first hunk of `patches/lean-v4.35.0-runtime-wasm.patch`.

**Minimal reproduction** (any 32-bit build of the v4.35.0 runtime; 64-bit builds are unaffected):

```lean
-- Repro.lean
def main : IO Unit := do
  let s := "ab"
  -- toList goes through lean_string_data -> string_to_list_core; String.mk walks the result.
  IO.println (String.mk s.toList)
```

Expected output: `ab`. On a 32-bit target it crashes or prints garbage, because `String.mk` treats the
heap "nil" as a cons cell. `(String.mk s.toList).length` or `match s.toList with | d :: ds => ...`
fail the same way. To run it on wasm32 with the spike's scripts, build the runtime **without** the
patch's first hunk, compile `Repro.lean` with `lean -c` and link it the way `build-wasm.sh` links
`WasmEntry`.

**Upstream status: already gone. Nothing to report.** Upstream PR #15533 ("refactor: implement
`String.toList` in Lean") removed `string_to_list_core` and `lean_string_data`, so the C++ code no
longer exists in v4.36.0-rc1, v4.36.0 or master. Only toolchains up to v4.35.0 are affected.

## 2. `lean_uv_os_get_group` stub has the wrong signature (v4.35.0, v4.36.0)

In the non-libuv branch of `src/runtime/uv/system.cpp` the stub is declared `lean_uv_os_get_group()`,
but the header and the libuv branch take a `gid` parameter, so a build without libuv does not compile.
**Upstream status: fixed on master** (both definitions take `gid`). Still wrong in v4.36.0.

## 3. `thread.h` uses `std::adopt_lock_t` without `<mutex>` (single-threaded builds)

**Upstream status: fixed on master** (`#include <mutex>` at line 23).

## Consequence for Exegra

Exegra ships wasm64 only (decision 2026-11-18), where bug 1 cannot occur. Moving the toolchain to
v4.36.0 removes the need for hunk 1 altogether. Hunk 2 stays until a release includes the master fix.
