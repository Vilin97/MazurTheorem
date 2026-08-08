/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `IdealSheafPowerSubscheme.lean` in
Vilin97/Clawristotle.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Positive powers and their closed subschemes

This file records the affine kernel and underlying closed set of the
subscheme defined by a positive power of an ideal sheaf.
-/

open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/-- On an affine open, a positive-power subscheme has the expected kernel. -/
@[simp]
theorem ker_positivePower_subschemeι_app (n : ℕ) (U : X.affineOpens) :
    RingHom.ker ((J ^ (n + 1)).subschemeι.app U).hom =
      (J.ideal U) ^ (n + 1) := by
  simpa using (J ^ (n + 1)).ker_subschemeι_app U

/-- Passing to a positive power does not change the underlying closed subset. -/
@[simp]
theorem range_positivePower_subschemeι (n : ℕ) :
    Set.range (J ^ (n + 1)).subschemeι = J.support := by
  rw [(J ^ (n + 1)).range_subschemeι]
  exact congrArg (fun Z : Closeds X ↦ (Z : Set X)) (J.support_pow_succ n)

/-- The subscheme inclusion associated to a positive power is a closed immersion. -/
theorem isClosedImmersion_positivePower_subschemeι (n : ℕ) :
    IsClosedImmersion (J ^ (n + 1)).subschemeι :=
  inferInstance

end AlgebraicGeometry.Scheme.IdealSheafData
