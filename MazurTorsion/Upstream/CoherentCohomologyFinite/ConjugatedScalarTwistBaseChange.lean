/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ConjugatedAutoequivalenceNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeDescentNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeUnitCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistDescentFunctor

/-!
# Base change for conjugated scalar-twist functors

This file records the purely categorical transport before identifying
the conjugated endofunctors with the named glued scalar twists.
-/


open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/--
The scalar-twist base-change square after conjugating both twists by
effective cover descent.
-/
noncomputable def conjugatedScalarTwistBaseChangeNatIsoOfDescent
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
    (((restrictionEquivalence (D := 𝒰.gluedCover)).functor ⋙
        scalarTwistFunctor a hself hcocycle) ⋙
        (restrictionEquivalence (D := 𝒰.gluedCover)).inverse) ⋙
        pullback (baseChangeGluedMap 𝒰 f) ≅
      pullback (baseChangeGluedMap 𝒰 f) ⋙
        (((restrictionEquivalence
          (D := gluedCover (𝒰.pullback₁ f))).functor ⋙
          scalarTwistFunctor
            (baseChangeCoverUnit 𝒰 f a)
            (baseChangeCoverUnit_self 𝒰 f a hself)
            (baseChangeCoverUnit_cocycle
              𝒰 f a hcocycle)) ⋙
          (restrictionEquivalence
            (D := gluedCover (𝒰.pullback₁ f))).inverse) :=
  conjugatedEndofunctorNaturalityOfForward
    (restrictionEquivalence (D := 𝒰.gluedCover))
    (restrictionEquivalence
      (D := gluedCover (𝒰.pullback₁ f)))
    (pullback (baseChangeGluedMap 𝒰 f))
    (baseChangeFunctor 𝒰 f)
    (scalarTwistFunctor a hself hcocycle)
    (scalarTwistFunctor
      (baseChangeCoverUnit 𝒰 f a)
      (baseChangeCoverUnit_self 𝒰 f a hself)
      (baseChangeCoverUnit_cocycle 𝒰 f a hcocycle))
    (restrictionBaseChangeNatIso 𝒰 f)
    hmiddle

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
