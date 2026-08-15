/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Mating an equivalence across an adjunction

If autoequivalences commute with a left adjoint, their inverse
autoequivalences commute with the corresponding right adjoint.  This
small categorical bridge converts pullback compatibility into the
pushforward compatibility used by relative Serre vanishing.
-/


open CategoryTheory

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Take right-adjoint mates of a natural isomorphism expressing that
two autoequivalences commute with a left adjoint. -/
noncomputable def inverseEquivalenceCommutesWithRightAdjoint
    (EC : C ≌ C) (ED : D ≌ D)
    (L : C ⥤ D) (U : D ⥤ C)
    (adj : L ⊣ U)
    (h : EC.functor ⋙ L ≅ L ⋙ ED.functor) :
    U ⋙ EC.inverse ≅ ED.inverse ⋙ U :=
  ((EC.toAdjunction.comp adj).ofNatIsoLeft h).rightAdjointUniq
    (adj.comp ED.toAdjunction)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
