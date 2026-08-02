# Third-party notices

## EllipticCurves

- Author and upstream maintainer: Michael Stoll
- Source: https://github.com/MichaelStollBayreuth/EllipticCurves
- Source commit: `3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`
- License: Apache License 2.0; see `LICENSE`

The retained modules have been modified for Lean `4.33.0-rc1` and mathlib
`79d0395a1825a6264ad5d269e35e60537518955e`. The modifications and exact
production-file manifest are recorded in `PORTING.md`.

## Variable-change implementation

- Copyright holder: Kevin Buzzard
- Authors recorded in source: Michael Stoll and Claude
- Files:
  - `MazurTorsion/EllipticCurve/VariableChange.lean`
  - `EllipticCurves/VariableChange.lean`
- License: Apache License 2.0; see `LICENSE`

The copyright, license, and authorship headers are retained verbatim. The
compatibility file avoids duplicating the declarations.

## Lean Pool torsion foundations

- Author: Victor Aguiar
- Source:
  https://github.com/vaguiarl/lean-pool/tree/vaguiarl/mazur-foundations/LeanPool/MazurTorsionFoundations
- Source commit: `60bec1602de9e747b67ad69641bcfb4265849123`
- License: Apache License 2.0; see `LICENSE`

The retained `TwoTorsion.lean`, `ThreeTorsion.lean`, and
`FullFourTorsion.lean` files preserve their source headers. The exact-pin
audit and local changes are recorded in `docs/PRIOR_ART.md`.

## AINTLIB geometry foundations

- Author and copyright holder recorded in source: Chris Birkbeck
- Source: https://github.com/CBirkbeck/AINTLIB
- Source commit: `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`
- Source paths:
  - `projects/ModularCurves/ModularCurves/ForMathlib/CartierDual.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafOfModulesMonoidal.lean`
  - `projects/ModularCurves/ModularCurves/Picard/Pic.lean`
- License: Apache License 2.0, under the explicit header retained in each
  selected source file; see `LICENSE`

The selected files are stored under `MazurTorsion/Upstream/AINTLIB/`. Their
imports and a small exact-pin proof compatibility point were adjusted, and
source-level option commands and linter findings were eliminated. No other
AINTLIB source is included. Details are recorded in `PORTING.md` and
`docs/PRIOR_ART.md`.

## Tau Ceti

- Source: https://github.com/TauCetiProject/TauCeti
- Source commit: `a3913fd9111b851af857f720b4ce6721e6634183`
- License: Apache License 2.0

Tau Ceti is an exact Git dependency, not vendored source. The root package and
the separate upstream-contract package deliberately resolve the same Tau Ceti,
Lean, and Mathlib revisions.

## AI-assisted development

Parts of the proof development were produced in Claude Code and Codex agent
sessions, then reviewed, compiled, and committed under Vasily Ilin's
direction. Files that record `Claude` in their authorship header retain that
credit. AI generation is provenance, not verification: every completion
claim is based on compiled Lean and the repository's axiom/source gates.
