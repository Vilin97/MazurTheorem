/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat

/-!
# Rational algebras are flat over the integers

Every module over `ℚ` is flat, and `ℚ` is a localization of `ℤ`.
Transitivity therefore makes every rational algebra flat as a
`ℤ`-module.  We keep this as a named theorem so relative affine charts
can install the instance locally without adding a broad global instance.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- A commutative rational algebra is flat as an integer module. -/
theorem moduleFlat_int_of_algebra_rat
    (R : Type) [CommRing R] [Algebra ℚ R] :
    Module.Flat ℤ R := by
  letI : Module.Flat ℤ ℚ :=
    IsLocalization.flat ℚ (Submonoid.pos ℤ)
  letI : Module.Flat ℚ R :=
    RingHom.flat_algebraMap_iff.mp
      (RingHom.Flat.of_isField
        (Field.toIsField ℚ) (algebraMap ℚ R))
  exact Module.Flat.trans ℤ ℚ R

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
