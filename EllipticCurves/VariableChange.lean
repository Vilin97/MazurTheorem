/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import MazurTorsion.EllipticCurve.VariableChange

/-!
# Compatibility import for variable changes

The LeanPool project already contains the exact point-group change-of-variables API needed by
the reduction cone, ported from Michael Stoll's Apache-2.0 `EllipticCurves` project at commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

Keeping this historical module name as a public import lets the Stoll reduction files retain
their original import graph without redeclaring the shared
`WeierstrassCurve.Affine.Point.equivVariableChange` API.
-/
