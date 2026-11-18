# Spike: the Lean engine as WebAssembly (WG-4786)

Question: can compiled Lean (formal/) run in the browser and in Node as WebAssembly, called from
JS, so that the code that runs is the code the theorems are about?

**Answer: yes.** formal/'s format-1 engine entry (`runAny`, the same dispatch as `exegra-lean`)
compiles to wasm through Lean's own C backend and emscripten, and it reproduces every conformance
golden in Node, headless Chrome, Firefox and WebKit. Its output is byte-identical to the native
`exegra-lean` on all 88 goldens. This works as wasm32 and as wasm64 (`-sMEMORY64`).

This directory is spike code. Delete it once the engine is moved over for real.

## Route

There is no official wasm toolchain for Lean v4.35.0:

- Lean published `lean-4.x-linux_wasm32` release assets from v4.5 through v4.15. Since then the
  "Web Assembly" job in `.github/workflows/ci.yml` has been commented out (it is still there at
  tag v4.35.0). The v4.35.0 release has no wasm asset.
- The runtime still carries `LEAN_EMSCRIPTEN` support, and upstream keeps fixing it in 2026
  (lean4#13233, #13234 and #16090; #16090 landed after v4.35.0).
- lean4web runs Lean on a server, which is not what we want.
- The disabled CI job built a native **32-bit** stage0 compiler and used it to generate the C for
  the wasm build. That matters for wasm32 (see "wasm32 caveats").

The spike assembles the pieces itself, keeping the trusted base explicit:

1. `formal/`: `lake build` already emits C for every Exegra module (`.lake/build/ir/*.c`).
2. Init/Std C (`gen-stdlib-c.sh`): `lean -c` from the installed v4.35.0 toolchain runs over the
   Init/Std sources the toolchain ships, for the 792 modules in Main's import closure
   (`modules.py`). The toolchain's own .olean files serve as imports, so nothing is re-elaborated
   beyond that one module. (`leanir` emits no code for the stdlib because its oleans hold no
   postponed-compile data.)
3. Runtime (`build-runtime.sh`): `src/runtime` of lean4 at tag v4.35.0, built with em++. It is
   single-threaded (no `LEAN_MULTI_THREAD`, no `-pthread`, so the browser needs no
   SharedArrayBuffer or COOP/COEP headers). It uses no GMP (Lean's own mpn) and no mimalloc. It
   links libuv v1.48.0 with Lean's emscripten patch.
4. `WasmEntry.lean`: one `@[export exegra_wasm_run]` function (mode 0 engine, 1 explore,
   2 temporal). `glue.c` wraps it with `exegra_init`, `exegra_run` and a result pointer and length.
   `lean-engine.mjs` is the JS binding, under 50 lines, for Node and the browser.
5. `build-wasm.sh` compiles everything with `emcc -O3 -fwasm-exceptions -ffp-contract=off` and
   links `exegra-lean.mjs` (57 KB of emscripten glue) and `exegra-lean.wasm`.

### Patches and build fixes needed (all v4.35.0 bugs on non-default targets)

`formal/wasm/patches/lean-v4.35.0-runtime-wasm.patch` (moved there by WG-4792) fixes two runtime bugs:

- **`string_to_list_core` ends the list with `lean_box_uint32(0)` instead of `lean_box(0)`.** On
  64-bit the two are the same. On any 32-bit target `lean_box_uint32` allocates a heap object, so
  `String.toList` ends in a heap "nil". `lean_string_mk` then treats that as a cons cell and reads
  a NULL char. The result is `std::bad_alloc` or out-of-bounds traps on almost every input. This
  bug was the whole wasm32 failure; ASan found it (`null-pointer-dereference` in
  `lean_unbox_uint32` under `lean_string_mk`). Minimal repro: `match s.toList with | d :: ds =>
  String.ofList (d :: ds)`.
- `lean_uv_os_get_group()`: the emscripten stub omits the `uint64_t gid` parameter that the header
  declares, so it does not compile.

Build flags:

- `runtime/thread.h`: the single-threaded `unique_lock` stub names `std::adopt_lock_t` without
  including `<mutex>`. The build uses `-include mutex`.
- **The generated C must be compiled with `-DLEAN_EMSCRIPTEN` for wasm32.** `lean.h` lays out the
  8-byte scalar literals of static constructor objects (`LEAN_SCALAR_PTR_LITERAL`, for example the
  hashes in `Name` literals) as two 4-byte words only under that macro. Without it, static objects
  come out 4 bytes short; ASan reported a `global-buffer-overflow` in
  `Std.Data.DHashMap.Internal.RawLemmas.c`. For wasm64 the macro must stay **off** for the
  generated C, because the 64-bit layout is the correct one there.
- wasm-ld warns `function signature mismatch: lean_io_create_tempfile/tempdir`. That is lean4#16090
  (fixed after v4.35.0). These calls would trap, and the engine never makes them.

### wasm32 caveats: why wasm64 is the faithful build

The C comes from the 64-bit compiler. Lean's compiler is mostly careful about 32-bit targets
(static boxed scalars capped at 2^31, no static boxed `UInt32`). One 64-bit assumption remains:
`Lean.Compiler.IR.ToIR.lowerLitValue` types every `Nat` literal below 2^32 as `tagged` (no
reference counting). On wasm32, literals in [2^31, 2^32) are heap objects. The generated C has
such literals, including in `Exegra.Value.c` (`4294967295`) and `Exegra.Format2.c`. As used today
they only leak, because the compiler omits the `lean_dec`. But nothing guarantees that the IR never
uses such a value in a way that frees it twice. Lean's own wasm build avoided this class of
problem by generating the C with a 32-bit compiler. **wasm64 runs exactly the C that native
64-bit runs, under the same assumptions.** The only difference is the runtime platform layer.

## Measurements (2026-11-18, Windows 10 x64, Node 24.15, emscripten 7.0.0, all measured)

Correctness: 88 of 88 goldens match (by `compareTraces`, and in the browser by canonical JSON
equality). The output is byte-identical to native `exegra-lean` on all 88 (checked in Node), for
both wasm32 and wasm64.

| | Lean wasm32 | Lean wasm64 | Rust wasm (today) | native exegra-lean |
|---|---|---|---|---|
| .wasm raw | 2,693,611 B | 2,789,882 B | 775,759 B | 5,972,992 B exe |
| gzip -9 | 502,287 B | 490,203 B | 273,547 B | |
| brotli | 339,178 B | 338,119 B | 216,479 B | |
| Node: compile + instantiate | 13 ms | 18 ms | | |
| Node: Lean module init (`exegra_init`) | 60-70 ms | 86 ms | | process start-up 17.6 ms |
| Chrome 157: fetch+compile+instantiate / init | 32 / 45 ms | 39 / 56 ms | 10 ms | |
| Firefox 159: same | 64 / 4 ms | 93 / 7 ms | 10 ms | |
| WebKit 27.2: same | 51 / 12 ms | 59 / 14 ms | 30 ms | |
| linear memory after init (and after all goldens) | 25.4 MB | 25.6 MB | 2.1 MB | peak working set about 13 MB (live-session) |
| live-session (95.6 KB input), Node | 33.3 ms | 33.6 ms | 1.5 ms | 34.4 ms per process, about 17 ms without start-up |
| app-start-and-open (65.5 KB), Node | 31.9 ms | 32.7 ms | 2.0 ms | 36.6 ms, about 19 ms |
| faults-combined--delay-tick-3 (5.8 KB), Node | 4.2 ms | 4.0 ms | 0.35 ms | 21.1 ms, about 3.5 ms |
| app-start-and-open in Chrome / Firefox / WebKit | 30.2 / 33.8 / 32.6 ms | 29.0 / 36.2 / 40.7 ms | 2.1 / 2.3 / 1.8 ms | |
| all 88 goldens, first pass, Node | 879 ms | 859 ms | | |

Per-call figures are means of 50 calls in Node and 30 in the browsers, after one warm-up call.
"Without start-up" subtracts the mean time of a native run that refuses `{}` at once, so those
figures are rough. Linear memory stays at its post-init size for all goldens: 16 MB initial,
8 MB stack, and the Lean module's initialized constants.

Reading the numbers:

- Lean wasm costs about 1.7-2x native Lean.
- The Lean engine is about 15-20x slower than the Rust engine on the same input, both as wasm.
  That gap comes from the Lean implementation (lists and strings), not from wasm. It would be
  closed in the Lean code (arrays, `HashMap`, fewer conversions), where the proofs then cover the
  faster code too.
- For an interactive app, about 30 ms for the largest golden is acceptable inside the existing
  worker. Start-up adds about 80 ms in total once per page.

Browser support: wasm32 runs everywhere wasm with exception handling runs (`-fwasm-exceptions`
needs Chrome 95+, Firefox 100+, Safari 15.2+). wasm64 needs Memory64: Chrome 133+ and
Firefox 134+. Stable Safari does not support it according to caniuse (checked 2026-11-18); it is
in Safari Technology Preview. Playwright's WebKit 27.2 build ran it, but that build is not
shipping Safari.

## Reproduce

Requirements: Git Bash, Python 3, CMake and Ninja, Node, elan with the project toolchain
(formal/lean-toolchain), and network access.

```sh
# everything in one go: emsdk, lean4 v4.35.0 runtime sources plus the patch, libuv v1.48.0 plus
# Lean's patch, lake build, stdlib C, wasm32 and wasm64 builds, then the Node check
spike/lean-wasm/reproduce.sh <work dir>        # EMSDK=<checkout> reuses an existing emsdk

# browser check (port 5209), against either build
node spike/lean-wasm/browser/serve.mjs <work dir>/build32/wasm 5209 &
node spike/lean-wasm/browser/check.mjs http://127.0.0.1:5209/ chromium,firefox,webkit
```

The measurements above came from running the individual scripts (`gen-stdlib-c.sh`,
`build-runtime.sh`, `build-wasm.sh`, `run-node.mjs`, `browser/*`) step by step. `reproduce.sh`
chains them together. Its first end-to-end run reached the runtime build and exposed a missing
`/src/util/` in the sparse checkout, which is now fixed. The second run was stopped by the host
for low memory before it finished, so the full chain has not yet completed in a single run.

`check.mjs` uses the installed Google Chrome (`channel: 'chrome'`) and Playwright's Firefox and
WebKit (`npx playwright install firefox webkit`). Measured step times on this machine: stdlib C
generation 2 min 45 s (8 jobs), runtime 15 s, C to wasm compile and link about 2 min (8 jobs).

## Recommendation

Make the Lean code the engine in every place it runs. In the browser and the worker, load it
through `lean-engine.mjs` behind the existing `src/core/engine.js` facade, replacing
`src/engine/pkg`. In the CLI and Node, use the same .wasm, or native `exegra-lean`, which compiles
from the same C.

- **Prefer wasm64 once Safari ships Memory64.** It is the same C under the same 64-bit
  assumptions as native. Until then, either ship wasm32 or ship both and pick by feature test
  (`WebAssembly.validate` of a memory64 module).
- If wasm32 ships, get the C from a 32-bit Lean compiler, as Lean's own wasm job did, or audit
  and remove the `Nat`-literal-below-2^32 assumption upstream.
- Upstream the runtime patch: the `string_to_list_core` nil is a real bug on every 32-bit target.

Trusted base of the wasm route:

- the Lean compiler (LCNF to C, the same as native);
- the Lean v4.35.0 runtime plus the two-hunk patch;
- clang/LLVM and wasm-ld from emscripten, emscripten's musl libc and libc++, and libuv (linked;
  only error-string paths are reachable);
- `glue.c`, `lean-engine.mjs` and emscripten's generated JS glue.

The Init/Std C comes from the toolchain's own `lean -c`, not from the release's `libInit.a`
objects. A production build should pin that step, or build the stdlib with Lean's CMake for
emscripten.

Fallbacks, assessed and not needed:

- A local Lean process behind the dev server (`tools/vite-plugin-exegra.js`), with the static
  production build shipping precomputed traces. The running code would be the proved code, but
  the static site could only replay recorded runs, with no live simulation of edited models, and
  the dev and production paths would differ.
- Native Lean for the CLI plus the Rust wasm in the browser. The browser would keep running code
  the theorems are not about, so the goal is not met there.
