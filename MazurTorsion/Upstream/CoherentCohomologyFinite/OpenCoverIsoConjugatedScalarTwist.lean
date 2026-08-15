/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ConjugatedAutoequivalenceNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentGlobalFunctor

/-!
# Conjugated scalar twists under an isomorphism of open covers

This file isolates the purely categorical transport of the descent-level
scalar-twist square through the two effective-descent equivalences.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- The scalar-twist cover-isomorphism square after conjugating both
twists by effective descent. -/
noncomputable def conjugatedScalarTwistCoverIsoNatIsoOfDescent
    (e : 𝒰 ≅ 𝒱)
    (a : ∀ i j,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (haself : ∀ i, a i i = 1)
    (hacocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover a)
    (hbself : ∀ i, b i i = 1)
    (hbcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (hab :
      pullbackCoverUnitAlongIso e b = a) :
    (((restrictionEquivalence
          (D := 𝒱.gluedCover)).functor ⋙
        scalarTwistFunctor
          b hbself hbcocycle) ⋙
      (restrictionEquivalence
        (D := 𝒱.gluedCover)).inverse) ⋙
      pullback (coverIsoGluedIso e).hom ≅
    pullback (coverIsoGluedIso e).hom ⋙
      (((restrictionEquivalence
            (D := 𝒰.gluedCover)).functor ⋙
          scalarTwistFunctor
            a haself hacocycle) ⋙
        (restrictionEquivalence
          (D := 𝒰.gluedCover)).inverse) :=
  conjugatedEndofunctorNaturalityOfForward
    (restrictionEquivalence
      (D := 𝒱.gluedCover))
    (restrictionEquivalence
      (D := 𝒰.gluedCover))
    (pullback (coverIsoGluedIso e).hom)
    (pullbackAlongCoverIsoFunctor e)
    (scalarTwistFunctor
      b hbself hbcocycle)
    (scalarTwistFunctor
      a haself hacocycle)
    (restrictionCoverIsoNatIso e)
    (scalarTwistPullbackAlongCoverIsoNatIsoOfUnitsEq
      e a b haself hacocycle
      hbself hbcocycle hab)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
