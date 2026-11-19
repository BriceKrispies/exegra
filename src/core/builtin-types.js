// Representation types a generator can map without a declaration. Shared by the readiness rules. `json` is any
// JSON value (free-form members such as view parameters); it cannot be the representation of an id or scalar.
// `unit` is the type with one value (Rust `()`, JSON null), so that a function returns result<unit, E> (WG-4957);
// it is not the representation of an id or scalar either.
export const BUILTIN_TYPES = Object.freeze([
  'bool', 'u8', 'u16', 'u32', 'u64', 'i32', 'i64', 'f64', 'string', 'bytes', 'timestamp', 'duration', 'uuid', 'json', 'unit',
]);

/** The wire cases a generator may name JSON members in (system.generation.wireCase, contract binding.case). */
export const WIRE_CASES = Object.freeze(['snake_case', 'kebab-case', 'camelCase']);

/** True when `name` is a built-in representation type. */
export function isBuiltinType(name) {
  return BUILTIN_TYPES.includes(name);
}
