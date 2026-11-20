# The specification store

A project's specification can be held in SQLite, in a database beside it: `<spec>.sqlite` (for Exegra,
`specs/exegra/spec.jsonc.sqlite`). The store is built from the JSONC text and gives it back byte for byte. Git
commits the JSONC; the database is rebuilt from it after a checkout and is never committed (`.gitignore` ignores
`*.sqlite` and its `-wal` and `-shm` files). The code is `tools/spec-store.js` (component `spec-store`), and it
uses `node:sqlite`, built into Node, so it needs no dependency and runs only in Node.

```
node cli/exegra.js store import --project <name> [--db <file>]
node cli/exegra.js store export --project <name> [--db <file>] [--out <file>]
```

`store import` replaces everything in the database with the specification. `store export` writes the stored text
to `--out`, or to the specification itself when `--out` is not given. An export to the specification is refused
with `store.stale` when the file changed since the store last synchronised with it (the sha-256 in `meta`), unless
the file is already the exported text; nothing is written then.

## Rows

The text is cut into verbatim slices, and every code unit of it belongs to exactly one row:

- **entity**: one row per item of an entity section, and one row per other top-level value, stored whole. The
  entity sections are the meta-model's (`components`, `claims`, ...) and those a vocabulary's `entityKinds`
  declare. Stored whole: `system` (kind `system`), `exegra`, `vocabulary`, any section with no entity kind
  (`decisions`, a scalar), and an entity section whose value is not an array.
- **trivia**: everything between those values. That is the text before the root's first member and after the
  last, member keys and colons, brackets, commas, comments, whitespace and line endings. A comment above an entity
  is in the trivia row before it.

| Table | Columns |
|---|---|
| `entity` | `position` (key), `section`, `id`, `kind`, `component`, `source_text`, `json`, `hash`, `refs` |
| `trivia` | `position` (key), `section`, `text` |
| `ref` | `position`, `target` (key both): the ids an entity row references, indexed by target |
| `meta` | `key`, `value`: `format` (`exegra-spec-store`), `format_version` (1), `project`, `semantic_hash`, `position_unit`, `source_sha256`, `source_length` |

`entity` is indexed on `(section, id)`, `id`, `kind` and `component`. `source_text` and `trivia.text` are the
authority. The other columns are derived when a row is written. `json` is the row's JSON value (key order kept, a
repeated key read as JSON reads it) and `hash` is its sha-256. `component` is the id of a component row, or the
`component` member of another entity. `refs` are the targets of the model's references declared inside the row.

**Positions** are UTF-16 code-unit offsets of the row's start in the imported text. These are the offsets
jsonc-parser reports and JavaScript string indices, not byte offsets. They order the rows, and export
concatenates the rows of both tables in position order. Rows are never empty, so positions are unique across
both tables.

## Exactness and refusals

Import parses the text once with jsonc-parser (comments and trailing commas allowed) and cuts it at the offsets of
the tree. Before it commits, it exports the rows inside the same transaction and compares them with the input, so
a store that would not give the text back is never committed. It refuses with a `StoreError`, and stores nothing,
a text that:

- does not parse (`store.syntax`, with the line and column of the first error);
- is not well-formed Unicode, or a file that is not valid UTF-8 (`store.encoding`).

A refused import leaves the rows the store held. A leading byte order mark is kept: it is the first code unit of
the first trivia row, and the store reads the text after it. Exegra's parser itself reports a byte order mark as a
syntax error, so such a specification is stored and given back, but it does not validate, either from the text
or from the store.

## Reading the model

`loadModelFromStore(db)` returns the analysis of the exported text (`analyzeSpec`): the same model, diagnostics,
error count and semantic hash as the file. It also returns `storedHash`, the hash recorded at import. The model is
still derived by the Lean kernel from text, not assembled from rows.

Every database is opened in WAL mode (`synchronous = NORMAL`, `busy_timeout` 5 s), so several processes can read
one store while one writes.

## Measured on Strata's specification

These figures were measured on a 7,118,836-byte specification of 202,684 lines, in Node 24.15.0 on Windows. Each
is a separate process, and three runs agreed within 2%.

| | |
|---|---|
| Rows | 5,167 entity, 5,214 trivia, 12,125 ref |
| Import | 3.7 s: the parser's model derivation 3.1 s (for references and the semantic hash), slicing 0.3 s, SQLite writes and the round-trip check the rest |
| Export | 71 ms (`store export`, writing the file); 0.3 s including a byte comparison with the original |
| Database | 14.5 MB after import (the text is held twice, as `source_text` and `json`, plus the indexes) |
| Peak memory (max RSS) | import 693 MB (the model derivation alone reaches 553 MB); export 104 MB |
| `loadModelFromStore` | 4.0 s, the same as `validate` on the file (4.2 s) |

## What the store does not do yet

The open work is in the `unknowns` of component `spec-store` and in WG-4979. `apply` still edits the text:
transactions through the store, which re-render only the edited rows, wait for WG-4974's batched transactions.
Incremental validation keyed by entity hash, and specc, Concordance and the application reading the store, are
also still to do.
