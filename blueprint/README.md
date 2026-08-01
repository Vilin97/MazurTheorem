# Mazur theorem Verso Blueprint

This directory is an isolated Lean project built with the official
[`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint)
package. The six chapters and 48 stable labels mirror
`../coordination/program.json`; every dependency in that file is represented by
a Blueprint `uses` edge. Labels are the node IDs verbatim (for example,
`MT-X11-COSET`), so no translation table is required.

The project runs on Lean `v4.33.0-rc1`. Until Verso Blueprint publishes a
matching tag, `lakefile.lean` pins the official v4.32 Blueprint commit and
overrides Verso, Verso Slides, and ProofWidgets with their v4.33-compatible
official commits.

## Local workflow

```bash
cd blueprint
lake update
LEAN_NUM_THREADS=1 lake exe vbp build
LEAN_NUM_THREADS=1 lake exe vbp check
```

The generated multi-page site is written to `_out/site/html-multi/`. Useful
queries include:

```bash
lake exe vbp query labels
lake exe vbp query node MT-X11-COSET
lake exe vbp query uses MT-FINAL-ASSEMBLY
```

`scripts/ci-pages.sh` runs the build/check sequence and verifies the Pages
artifacts expected by CI.
