/* JS-facing wrapper around the Lean entry point `exegra_wasm_run` (WasmEntry.lean). */
#include <lean/lean.h>
#include <emscripten/emscripten.h>

lean_object * initialize_WasmEntry(uint8_t builtin);
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
lean_object * exegra_wasm_run(uint32_t mode, lean_object * text);

static lean_object * g_last = NULL;

/* Initialize the Lean runtime and every module WasmEntry imports. Returns 0 on success. */
EMSCRIPTEN_KEEPALIVE int exegra_init(void) {
    lean_initialize_runtime_module();
    lean_object * res = initialize_WasmEntry(1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
        return 0;
    }
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
}

/* Run one input (UTF-8, `len` bytes). The result stays valid until the next call; read its bytes
   with exegra_result_ptr / exegra_result_len. */
EMSCRIPTEN_KEEPALIVE void exegra_run(uint32_t mode, const char * input, size_t len) {
    if (g_last) lean_dec(g_last);
    lean_object * text = lean_mk_string_from_bytes(input, len);
    g_last = exegra_wasm_run(mode, text);
}

EMSCRIPTEN_KEEPALIVE const char * exegra_result_ptr(void) { return lean_string_cstr(g_last); }
EMSCRIPTEN_KEEPALIVE size_t exegra_result_len(void) { return lean_string_size(g_last) - 1; }
