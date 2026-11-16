# Importing a Markdown specification

A specification kept as structured Markdown in another repository can be converted into one Exegra specification. `tools/import-markdown.js` does it. The result can replace the Markdown, and then it is the authority in that repository: Exegra opens it as a linked project through `specs/<project>/project.jsonc` ([transactions-and-persistence.md](transactions-and-persistence.md#where-a-project-keeps-its-files)). Linked projects are local data and are not part of Exegra's repository ([linked projects](#linked-projects)). This document says what the importer does, what it maps, how it shows that nothing was lost and how it reports what it cannot map.

## The conversion is one way

The importer refuses a source without the white paper named by the import map. Once the Markdown has been replaced by the converted file, the importer only runs against a checkout of an earlier commit, and it then writes through the project link, overwriting the authority file; run it with `--out` to write elsewhere. A converted specification is edited in Exegra or as text and checked with `node cli/exegra.js validate --project <name>`.

The importer's renderer (`renderEntity`, `reconstructMarkdown`) stays in use: `node cli/exegra.js markdown --project <name> [<documentPath>] [--out <dir>]` renders the documents from the file.

## Linked projects

Any directory under `specs/` other than the projects Exegra ships (`exegra` and `benchmark`) is a linked project: `.gitignore` ignores `specs/*` except those two. A project directory holds `project.jsonc` (naming the specification file, which can live in another repository), and optionally `import-map.jsonc`, `layout.jsonc`, `evidence/` and `generated/`. Tests that need a linked project are named `local-*` (for example `tests/core/local-<project>.test.js` or `tests/browser/local-<project>.spec.js`), which `.gitignore` also ignores; they skip themselves when the project or its repository is absent, and `tools/traceability.js` ignores `local-*` files. The tracked tests use a small fixture under `tests/fixtures/markdown-import/` instead.

## Running it

```sh
npm run import:markdown -- --project <name>              # map specs/<name>/import-map.jsonc; writes the file specs/<name>/project.jsonc names
node tools/import-markdown.js --project <name> --source D:/work/repo   # another checkout
node tools/import-markdown.js --map path/to/import-map.jsonc --out scratch/spec.jsonc
node tools/import-markdown.js --project <name> --check   # write nothing; exit 1 if the file on disk is out of date
node tools/import-markdown.js --project <name> --coverage   # write nothing; print the coverage check for every file
node tools/import-markdown.js --project <name> --export-md out/   # also write the Markdown tree rendered from the file
```

| Option | Default |
|---|---|
| `--project <name>` | none; names the project whose import map and specification file are the defaults below |
| `--source <dir>` | the `source` of the import map, relative to the map |
| `--out <file>` | the file `specs/<name>/project.jsonc` names (required without `--project`) |
| `--map <file>` | `specs/<name>/import-map.jsonc` (required without `--project`) |
| `--check` | off: write the file |
| `--coverage` | off |
| `--export-md <dir>` | off |

The same input gives the same bytes. The tool prints the source repository's git commit (read from its `.git` files, without running git), the number of entities imported per kind, the losses and the coverage check. Exit code 2 is a usage error; 1 is an import failure, a failed coverage check (nothing is written) or, with `--check`, an out-of-date file. `npm run generate` writes the derived artifacts of a project with `exegra generate --write --project <name>`.

## How the Markdown is held

Every file under the specification directory (`specifications/` unless the map says otherwise) becomes a `document`.

- A file under a `cases/` directory of that tree becomes a `caseTable` holding the whole file verbatim in `body`, with the header cells (`columns`) and data-row count (`rowCount`) of its first table. A requirement's `cases` names it.
- Any other file is split at its headings into `section` entities. Each has `title`, `level`, `parent`, `order` in the document, and `body`: the Markdown under the heading, verbatim. Text before the first heading is a level-0 section.
- Inside a section body, every line range imported as a separate entity (a requirement block, a white-paper list item or table row, a glossary entry, a roadmap milestone's text) is replaced by one `{{entity:<id>}}` marker line. The marker stands for that entity rendered from its properties.

The entities hold their text in properties, with inline Markdown (code spans, emphasis) as written. Text that spans several lines keeps its structure: wrapped lines are joined, while paragraphs, nested list items and table rows stay separate lines. A decision's sub-points, for example, are lines starting `- ` inside its `statement`. Nothing holds a second copy of the original lines.

`renderEntity` in the importer writes an entity back as Markdown, and Concordance's own renderer produces the same text byte for byte: a requirement as `**REF** statement` followed by its attribute lines (Status, Verify, Cases, Boundary, Traces, Depends, Rationale, Milestone, Seam, in that order), a goal or decision as a list item, a component, boundary or release stage as a table row, a glossary term as `- **Term**: definition`. `--export-md` writes the documents with every marker rendered this way.

## How completeness is checked

Every import runs two checks, and writes nothing if either fails:

1. **Every line is held.** With each marker expanded to the lines its entity was imported from, every file rebuilds exactly from the sections and case tables (after normalising line endings and trailing whitespace). Prose is therefore held verbatim, and every other line belongs to exactly one imported entity.
2. **Every entity renders back to its words.** Each imported entity, rendered from its properties alone, must equal the lines it came from once whitespace is collapsed. A requirement is compared as parsed instead: the same statement and the same attribute values, in any order. A property that lost a word, a reference that did not resolve, or a dropped attribute fails the check and names the entity.

What the JSONC does not keep is line wrapping and the order of a requirement's attribute lines. The tool also reports how many documents rendered from the written file alone are byte-identical to the Markdown; the rest differ only in those two respects.

## What is read

| Source file in the repository | Used for |
|---|---|
| every Markdown file of the specification directory | Documents, sections and case tables; requirements (each block that starts with an id in bold, for example `**KRN-002** statement`, followed by `- Key: value` lines). |
| `specifications/00-vision/whitepaper.md` | Also: components and their "Talks to" cells (process-topology table), the trust-boundaries list, the boundary table, goals, non-goals, decisions (body and index table), constraints, open questions, release stages, milestone paragraphs, glossary, the system description. |
| `specifications/00-vision/roadmap.md` | Also: milestones (the `RM-n` sections). |
| `specifications/glossary.md` | Also: glossary terms. |
| `docs/agents/verification.md` | The definition of each verification method named by a requirement, when present (optional). |
| the repository's git HEAD | The commit stamped into the file. |

## What is imported

| Markdown | Exegra |
|---|---|
| Components (`C-n`) from the process-topology table | `component` entities with `name`, `purpose` (the "Owns" cell), `talksTo` (the "Talks to" cell as written), `trustZone` and `trustLevel` (from the trust-boundaries list) and `category` (from the mapping file, below). |
| Component ids in "Talks to" cells | `talks-to` relationships between components, a relationship kind the specification declares in its own vocabulary. |
| Boundaries (`B-n`), goals (`G-n`), non-goals (`NG-n`), decisions (`D-n`), constraints (`K-n`), open questions (`Q-n`), release stages, roadmap milestones (`RM-n`), glossary entries | Entities of kinds the specification declares in `vocabulary.entityKinds`, in their own top-level sections. |
| Requirements | `claim` entities of kind `requirement`. |
| Files and headings | `document`, `section` and `caseTable` entities, above. |

Every imported entity carries `source` (`path:line` in the source repository), and those with an id in the Markdown carry `ref` (the id as written). The ids Exegra uses are the lower-cased `ref` (`KRN-002` becomes `krn-002`, `R0.5` becomes `r0_5`). Ids of the other classes mentioned in an entity's text become its `mentions`, a list-typed property.

A requirement becomes a claim with:

- `statement` and `rationale` from the block and its `Rationale` line;
- `evaluate.method` equal to its `Verify` value (for example `property`, `example`, `scenario`, `conformance`); a requirement without a `Verify` line stops the import, because Exegra requires an evaluation method;
- `boundary` (the `B-` id of the `Boundary` line) and `boundaryDetail` (the rest of that line);
- `traces` (goals, non-goals, constraints, decisions and open questions named in the `Traces` line) and `dependsOn` (other requirements named in `Depends`);
- `milestone` and `seam` (numbers; the milestone entity with that number is `rm-<number>`);
- `cases` (the case tables its `Cases` line names) and `casesPath` (any path naming no case-table file, as written);
- `subjects`: the components named in the statement or the Boundary line;
- `lifecycle` (`active`, or `retired` when the block says `Status: retired`), `area` (the numbered specification directory), `section` (the nearest heading above) and `inSection` (the section entity holding its marker).

The model also gets four views: `architecture` and `trust-levels` (structural, the second coloured by trust zone), `traceability` (the `references` projection, depth 1) and `claims`. The vocabulary of the generated file is a working example of model-defined vocabulary; see [model-and-format.md](model-and-format.md#meta-model-and-vocabulary).

For the exact numbers, read `system.notes` at the head of the converted specification.

## Nothing is verified

Every requirement states how it is to be verified, and those methods (property tests, example tests, scenario runs, conformance tables) are carried out by tools outside Exegra. The specification declares them as `vocabulary.verificationMethods`. A claim that uses one gets evaluator `external:<method>`, and its status can only be raised by recorded results: evidence executions, or per-claim outcomes an external tool such as Concordance writes into `evidence/results.json` ([claims-and-evidence.md](claims-and-evidence.md)). The importer records neither, so every requirement reports `not-evaluated`.

## The import map

`specs/<project>/import-map.jsonc` is input to the importer, not part of the source. It supplies what the Markdown does not state:

- `project`: `id`, `name` and `title`. The title is the `# <title>` heading whose first paragraph becomes the system description.
- `source`: the source repository, relative to the map (used when `--source` is not given).
- `layout` (optional): where the documents are in the source, as paths relative to its root: `whitepaper`, `roadmap`, `verification`, `specsDir` and `srcDir`. The defaults are `specifications/00-vision/whitepaper.md`, `specifications/00-vision/roadmap.md`, `docs/agents/verification.md`, `specifications` and `src`.
- `categories`: Exegra requires a `category` on every component and the Markdown does not state one, so the map assigns each component id (`C-1`, `C-2`, ...) a category (`logical`, `computational`, `client`, `storage`, `infrastructure`, `external`), chosen from what the component's "Owns" cell describes. They are an Exegra-side classification, not a claim the source makes. The import fails with a message naming any component that has no entry.

The small example in `tests/fixtures/markdown-import/` (its `import-map.jsonc` and the Markdown under `repo/`) shows all of it.

## What is not imported

Nothing outside the specification directory is imported: `contracts/`, `decisions/` (the ADRs), `diagrams/`, `threat-models/`, `runbooks/`, `workflows/`, `reviews/`, `traceability/` and `docs/` stay where they are, except the verification-method definitions read from the verification document.

## How losses are reported

The importer invents nothing. When it recognises a construct and cannot map it to a typed property, it records a loss: a kind, a count and up to ten examples. Losses are printed to standard error as `Not mapped (n items in k kinds)`, summarised on standard output, and written into the generated file as `NOT MAPPED, ...` lines of `system.notes`. Examples: a "Talks to" cell that names no component id (no relationship; the cell is still kept in `talksTo`), a range written as `C-2 to C-7` (only its endpoints are linked), a component absent from the trust-boundaries list (no `trustZone`), a repeated key inside a requirement (values joined with a space), a `Cases` path that matches no case-table file (kept in `casesPath`). A loss does not stop the import; a missing mapping entry, a requirement without `Verify`, a duplicate id, an id that does not match Exegra's id pattern, or a failed coverage check does.

## Tests

`tests/core/import-markdown.test.js` covers the parsers on small inputs (a requirement with every key, a retired one, unresolved references left out and counted, component and boundary rows, sections with markers, case tables, glossary terms), joining wrapped text while keeping sub-points, rendering a requirement and a decision from their properties, and the rendering check catching a lost word or an unresolved reference. On the fixture under `tests/fixtures/markdown-import/` it covers the whole conversion through an import map (validates, passes both coverage checks, deterministic, names and categories from the map), the command line (`--map`, `--out`, `--check`), and a linked project resolved through `project.jsonc` whose documents the `markdown` command renders. See [verification.md](verification.md).
