/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `CanonicalSupportChowSupport.lean` in
Vilin97/Clawristotle.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleCanonicalSupportThickening

/-!
# Full support of the canonical support model

The model module on its canonical closed support thickening has a
nonzero stalk at every point. Consequently its closed stalk support is
the whole thickening.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace CanonicalSupportThickening

variable {X : Scheme.{u}} {F : X.Modules}
  [F.IsFiniteType] [F.IsQuasicoherent]

/-- Every point of the canonical support thickening lies in the stalk
support of its model module. -/
theorem modelModule_stalkSupport_eq_univ (A : CanonicalSupportThickening F) :
    stalkSupport A.modelModule = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  have hyClosed : A.inclusion x ∈ closedStalkSupport F := by
    change A.inclusion x ∈ (closedStalkSupport F : Set X)
    rw [← A.range_inclusion]
    exact ⟨x, rfl⟩
  have hy : A.inclusion x ∈ stalkSupport F := by
    rw [← coe_closedStalkSupport_eq_stalkSupport F]
    exact hyClosed
  intro hx
  apply hy
  let e :=
    (underlyingStalkFunctor (A.inclusion x)).mapIso A.comparisonIso
  apply e.isZero_iff.mpr
  let α :=
    TopCat.Presheaf.stalkPushforward
      AddCommGrpCat A.inclusion.base A.modelModule.sheaf.presheaf x
  letI : IsIso α :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat A.inclusion.isClosedEmbedding.isInducing
      A.modelModule.sheaf.presheaf x
  have hx' : IsZero (A.modelModule.sheaf.presheaf.stalk x) :=
    hx
  have hpush :
      IsZero
        (((TopCat.Presheaf.pushforward AddCommGrpCat A.inclusion.base).obj
          A.modelModule.sheaf.presheaf).stalk (A.inclusion x)) :=
    IsZero.of_iso hx' (asIso α)
  exact hpush

/-- The closed stalk support of the canonical model module is the whole
support thickening. -/
theorem modelModule_closedStalkSupport_eq_top
    (A : CanonicalSupportThickening F) :
    closedStalkSupport A.modelModule = ⊤ := by
  apply Closeds.ext
  change closure (stalkSupport A.modelModule) = Set.univ
  rw [A.modelModule_stalkSupport_eq_univ, closure_univ]

end CanonicalSupportThickening
end AlgebraicGeometry.Scheme.Modules
