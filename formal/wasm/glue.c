/* The C side of the call boundary: Exegra.Api.handle (formal/Exegra/Api.lean, exported as
   `exegra_call`) behind three functions the JS binding (src/core/lean.js) calls.

   exegra_init()                 initialize the Lean runtime and Exegra.Api with everything it
                                 imports; 0 on success
   exegra_request(text, len)     handle one JSON request {"fn", "args"} (UTF-8, len bytes); the
                                 reply stays valid until the next request
   exegra_reply_ptr/len()        the reply's UTF-8 bytes: {"ok": ...} or {"error": ...}
   exegra_pointer_size()         4 (wasm32) or 8 (wasm64), so the binding knows how pointers cross

   Single-threaded: the runtime is built without LEAN_MULTI_THREAD. */
#include <lean/lean.h>
#include <emscripten/emscripten.h>

lean_object * initialize_exegra_Exegra_Api(uint8_t builtin);
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
lean_object * exegra_call(lean_object * text);

static lean_object * g_reply = NULL;

EMSCRIPTEN_KEEPALIVE int exegra_init(void) {
    lean_initialize_runtime_module();
    lean_object * res = initialize_exegra_Exegra_Api(1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
        return 0;
    }
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
}

EMSCRIPTEN_KEEPALIVE int exegra_pointer_size(void) { return (int)sizeof(void *); }

EMSCRIPTEN_KEEPALIVE void exegra_request(const char * text, size_t len) {
    if (g_reply) lean_dec(g_reply);
    g_reply = exegra_call(lean_mk_string_from_bytes(text, len));
}

EMSCRIPTEN_KEEPALIVE const char * exegra_reply_ptr(void) { return lean_string_cstr(g_reply); }

EMSCRIPTEN_KEEPALIVE size_t exegra_reply_len(void) { return lean_string_size(g_reply) - 1; }
