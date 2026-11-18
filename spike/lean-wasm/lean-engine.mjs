// Thin JS binding for the Lean engine compiled to wasm (exegra-lean.mjs + exegra-lean.wasm, built by
// build-wasm.sh). Works in Node and in the browser: `createLeanEngine(factory)` takes the emscripten
// module factory (the default export of exegra-lean.mjs) and returns {run(text, mode) -> string}.
// mode: 0 engine input -> trace (formal/Main.lean default), 1 explore, 2 temporal.

const encoder = new TextEncoder();
const decoder = new TextDecoder();

export async function createLeanEngine(factory, options = {}) {
  const m = await factory(options);
  if (m._exegra_init() !== 0) throw new Error('Lean module initialization failed');
  // wasm64 (-sMEMORY64=1): pointers and size_t cross the JS boundary as BigInt
  const wide = typeof m._exegra_result_ptr() === 'bigint';
  const size = wide ? (n) => BigInt(n) : (n) => n;
  return {
    module: m,
    /** Run one input; returns the output text or throws with the refusal message. */
    run(text, mode = 0) {
      const bytes = encoder.encode(text);
      const ptr = Number(m._malloc(size(bytes.length + 1)));
      m.HEAPU8.set(bytes, ptr);
      try {
        m._exegra_run(mode, size(ptr), size(bytes.length));
      } finally {
        m._free(size(ptr));
      }
      const rp = Number(m._exegra_result_ptr());
      const rl = Number(m._exegra_result_len());
      const out = decoder.decode(m.HEAPU8.subarray(rp, rp + rl));
      if (out[0] === 'o') return out.slice(1);
      throw new Error(out.slice(1));
    },
    heapBytes() { return m.HEAPU8.length; },
  };
}
