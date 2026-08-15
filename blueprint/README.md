# Mazur theorem Verso Blueprint

This isolated Lean project renders the mathematical projection of schema-v4
[`coordination/program.json`](../coordination/program.json) with the official
[`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint)
package.

The six generated chapters contain the 48 stable top-level programme labels,
using node IDs verbatim, and reproduce their `uses` dependency edges. These
labels are the fixed 1,000-point accounting units. Nested work packages remain
in the ledger as nonweighted execution metadata; they are not extra Blueprint
theorems or independent progress credit.

The Integration projection leads to the full
`MazurTorsion.rationalTorsion_hasMazurClassification` release endpoint. The
immutable `Challenge.Mazur.torsion_ncard_le` contract is a sibling corollary.
For operational selection, package dependencies, and the current WIP plan,
navigate to the [ledger](../coordination/program.json) or compact
[owner queue](../coordination/OWNER_QUEUE.md).

## Regeneration

Do not hand-edit the six generated chapter files. From the repository root,
run:

```bash
python3 scripts/sync_roadmap_docs.py
python3 scripts/sync_roadmap_docs.py --check
```

The same command keeps `site/generated/program.json` byte-identical to the
ledger. Narrative Blueprint material may explain the programme, but the ledger
remains canonical.

## Local workflow

The project runs on Lean `v4.33.0-rc1`. Until Verso Blueprint publishes a
matching tag, `lakefile.lean` pins its official v4.32 commit and compatible
official Verso, Verso Slides, and ProofWidgets commits.

```bash
cd blueprint
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
