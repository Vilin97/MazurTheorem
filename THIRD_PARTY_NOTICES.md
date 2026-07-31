# Third-party notices

## EllipticCurves

- Author and upstream maintainer: Michael Stoll
- Source: https://github.com/MichaelStollBayreuth/EllipticCurves
- Source commit: `3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`
- License: Apache License 2.0; see `LICENSE`

The retained modules have been modified for Lean `4.32.0-rc1` and mathlib
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`. The modifications and exact
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

## AI-assisted development

Parts of the proof development were produced in a Claude Code session and
reviewed, compiled, and committed by Vasily Ilin. Files that record `Claude`
in their authorship header retain that credit. AI generation is provenance,
not verification: every completion claim is based on compiled Lean and the
repository's axiom/source gates.
