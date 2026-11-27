Read AGENTS.md before doing anything. Exegra is specified, built and validated from its own specification, specs/exegra/spec.jsonc: every change starts there.

## Running Lean and the full pipeline in a Claude Code cloud session

The cloud container's network proxy refuses the elan installer (it calls `github.com/.../releases/latest`
and `api.github.com`), so `npm run build:formal-wasm`, `validate`, `claims` and `verify` look impossible
there. They are not: the direct release-download URL on `github.com` is allowed and redirects to
`release-assets.githubusercontent.com`, which is also allowed. Set the toolchain up by hand, outside the
repository (in your scratchpad directory), and never commit it:

```sh
S=<your scratchpad directory>                      # not inside the repository
V=$(sed 's/.*:v//' formal/lean-toolchain)          # the pinned version, e.g. 4.35.0
curl -sSfL -o "$S/lean.zip" "https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-linux.zip"
(cd "$S" && unzip -q lean.zip && rm lean.zip)      # use the .zip: zstd is not installed, so the .tar.zst cannot be unpacked
export PATH="$S/lean-$V-linux/bin:/opt/node24/bin:$PATH"
lean --version                                     # its commit must match PINS.lean4 in tools/build-formal-wasm.js
```

- The download is about 0.9 GB and unpacks to about 3.2 GB.
- Node 24 is required, not the default Node 22: the Lean core is wasm64 (Memory64), and Node 22 reports "The Lean core could not be instantiated". Node 24 is preinstalled at `/opt/node24/bin`.
- `cd formal && lake build Exegra` checks every proof (about 35 s once built). Ask `lake` from `formal/`, where `formal/lean-toolchain` applies.
- `node tools/build-formal-wasm.js --jobs 4` builds `src/engine/lean/` (about 6 minutes the first time). It fetches emsdk, the Lean runtime and libuv with git and from storage.googleapis.com, both allowed.
- After that, `node cli/exegra.js validate --project exegra`, `traceability`, `claims` (which re-checks the lean-theorem claims when `lake` is on the PATH) and `verify` run locally.
- `npm run …` scripts with a `pre…` hook also build the Rust oracle. Call the underlying `node` commands directly when you only need the Lean engine.

The `Check` workflow (`.github/workflows/check.yml`) runs the same checks on every development branch and is the record of what is proved. A local run is for fast iteration, not a substitute for it.
