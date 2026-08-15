/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Positive powers and their closed subschemes

This file records the two interfaces used when an annihilation argument
produces a positive power of an ideal sheaf: on every affine open, the
kernel is the corresponding power of the local ideal, while globally the
underlying closed set is unchanged.
-/

open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/--
On an affine open, the closed immersion defined by a positive power of
an ideal sheaf has kernel the same positive power of the local ideal.
-/
@[simp]
theorem ker_positivePower_subschemeι_app (n : ℕ)
    (U : X.affineOpens) :
    RingHom.ker ((J ^ (n + 1)).subschemeι.app U).hom =
      (J.ideal U) ^ (n + 1) := by
  simpa using (J ^ (n + 1)).ker_subschemeι_app U

/--
Passing to a positive power does not change the underlying closed set
of the associated closed subscheme.
-/
@[simp]
theorem range_positivePower_subschemeι (n : ℕ) :
    Set.range (J ^ (n + 1)).subschemeι = J.support := by
  rw [(J ^ (n + 1)).range_subschemeι]
  exact congrArg (fun Z : Closeds X => (Z : Set X)) (J.support_pow_succ n)

/--
The morphism associated to a positive power is a closed immersion.
-/
theorem isClosedImmersion_positivePower_subschemeι (n : ℕ) :
    IsClosedImmersion (J ^ (n + 1)).subschemeι :=
  inferInstance

end AlgebraicGeometry.Scheme.IdealSheafData
