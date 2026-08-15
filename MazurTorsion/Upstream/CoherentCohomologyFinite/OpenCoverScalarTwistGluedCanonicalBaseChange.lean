/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistGluedBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistBaseChange

/-!
# Canonical base change for scalar twists on glued open covers

The explicit identity-chart comparison for cover descent data supplies
the middle square in the abstract gluing bridge.  This yields the
canonical natural isomorphism between scalar twisting and pullback on
the glued schemes.
-/


open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- Scalar twisting on a glued open cover commutes with pullback along
the canonical morphism from a base-changed glued cover. -/
noncomputable def scalarTwistGluedBaseChangeNatIso
    (a : ∀ i j, Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition 𝒰.gluedCover a) :
    (scalarTwistGluedEquivalence
        a hself hcocycle).functor ⋙
        pullback (baseChangeGluedMap 𝒰 f) ≅
      pullback (baseChangeGluedMap 𝒰 f) ⋙
        (scalarTwistGluedEquivalence
          (baseChangeCoverUnit 𝒰 f a)
          (baseChangeCoverUnit_self 𝒰 f a hself)
          (baseChangeCoverUnit_cocycle
            𝒰 f a hcocycle)).functor :=
  scalarTwistGluedBaseChangeNatIsoOfDescent
    𝒰 f a hself hcocycle
    (scalarTwistBaseChangeNatIso
      𝒰 f a hself hcocycle)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
