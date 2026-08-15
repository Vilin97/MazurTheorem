/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ConjugatedScalarTwistBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedEquivalence

/-!
# Scalar twists on glued covers under base change

Restriction to cover descent data identifies pullback along the canonical
map between glued covers with chartwise base change.  Consequently a
base-change square for scalar twisting on descent data transports to the
corresponding square for scalar twisting on the glued schemes.
-/


open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/--
A base-change square for scalar twists on descent data induces the
corresponding square on the glued schemes.
-/
noncomputable def scalarTwistGluedBaseChangeNatIsoOfDescent
    (a : ∀ i j, Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition 𝒰.gluedCover a)
    (hmiddle :
      scalarTwistFunctor a hself hcocycle ⋙
          baseChangeFunctor 𝒰 f ≅
        baseChangeFunctor 𝒰 f ⋙
          scalarTwistFunctor
            (baseChangeCoverUnit 𝒰 f a)
            (baseChangeCoverUnit_self 𝒰 f a hself)
            (baseChangeCoverUnit_cocycle 𝒰 f a hcocycle)) :
    (scalarTwistGluedEquivalence
        a hself hcocycle).functor ⋙
        pullback (baseChangeGluedMap 𝒰 f) ≅
        pullback (baseChangeGluedMap 𝒰 f) ⋙
        (scalarTwistGluedEquivalence
          (D := gluedCover (𝒰.pullback₁ f))
          (baseChangeCoverUnit 𝒰 f a)
          (baseChangeCoverUnit_self 𝒰 f a hself)
          (baseChangeCoverUnit_cocycle
            𝒰 f a hcocycle)).functor :=
  by
    let sourceRestriction :=
      restrictionFunctor (D := 𝒰.gluedCover)
    let sourceTwist :=
      scalarTwistFunctor a hself hcocycle
    let sourceGlue :=
      glueFunctor (D := 𝒰.gluedCover)
    let targetRestriction :=
      restrictionFunctor
        (D := gluedCover (𝒰.pullback₁ f))
    let targetTwist :=
      scalarTwistFunctor
        (D := gluedCover (𝒰.pullback₁ f))
        (baseChangeCoverUnit 𝒰 f a)
        (baseChangeCoverUnit_self 𝒰 f a hself)
        (baseChangeCoverUnit_cocycle
          𝒰 f a hcocycle)
    let targetGlue :=
      glueFunctor (D := gluedCover (𝒰.pullback₁ f))
    let gluedPullback :=
      pullback (baseChangeGluedMap 𝒰 f)
    let e :=
      Functor.isoWhiskerRight
          (Functor.associator
            sourceRestriction
            sourceTwist
            sourceGlue).symm
          gluedPullback ≪≫
        conjugatedScalarTwistBaseChangeNatIsoOfDescent
          𝒰 f a hself hcocycle hmiddle ≪≫
        Functor.isoWhiskerLeft
          gluedPullback
          (Functor.associator
            targetRestriction
            targetTwist
            targetGlue)
    change
      ((sourceRestriction ⋙ sourceTwist) ⋙ sourceGlue) ⋙
          gluedPullback ≅
        gluedPullback ⋙
          ((targetRestriction ⋙ targetTwist) ⋙ targetGlue)
    exact e

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
