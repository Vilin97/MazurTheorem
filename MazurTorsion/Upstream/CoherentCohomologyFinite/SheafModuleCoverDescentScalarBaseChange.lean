/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeUnitCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentBaseChangeFunctor
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistDescentFunctor

/-!
# Scalar twisting and base change of cover descent data

Pulling an overlap transition through a base-changed cover commutes with
multiplying that transition by a unit.  The scalar on the pulled-back
overlap is the pullback of the original unit.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- Explicit base change of a scalar-twisted transition is the scalar
twist of the explicitly base-changed transition. -/
theorem baseChangeTransition_scalarTwist
    (A : CoverDescentData 𝒰.gluedCover)
    (a : ∀ i j, Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition 𝒰.gluedCover a)
    (i j : 𝒰.I₀) :
    baseChangeTransition 𝒰 f
        (scalarTwistObject a hself hcocycle A) i j =
      baseChangeTransition 𝒰 f A i j ≪≫
        scalarIso
          ((pullback
            ((gluedCover (𝒰.pullback₁ f)).t i j ≫
              (gluedCover (𝒰.pullback₁ f)).f j i)).obj
            ((pullback (𝒰.pullbackHom f j)).obj
              (A.chart j)))
          (baseChangeCoverUnit 𝒰 f a i j) := by
  have hs :
      baseChangeSourceOverlapIso 𝒰 f
          (scalarTwistObject a hself hcocycle A) i j =
        baseChangeSourceOverlapIso 𝒰 f A i j :=
    rfl
  have ht :
      baseChangeTargetOverlapIso 𝒰 f
          (scalarTwistObject a hself hcocycle A) i j =
        baseChangeTargetOverlapIso 𝒰 f A i j :=
    rfl
  unfold baseChangeTransition
  rw [hs, ht]
  unfold scalarTwistObject scalarTwistedTransition
    baseChangeCoverUnit
  rw [Functor.mapIso_trans, pullback_scalarIso]
  have hn :=
    scalarIso_naturality
      (baseChangeTargetOverlapIso 𝒰 f A i j).symm
      (pullbackGlobalUnit
        (baseChangeOverlapMap 𝒰 f i j) (a i j))
  simp only [Iso.trans_assoc]
  rw [hn]

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
