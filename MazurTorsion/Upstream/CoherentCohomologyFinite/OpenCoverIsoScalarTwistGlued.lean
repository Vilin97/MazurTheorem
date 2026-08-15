/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoConjugatedScalarTwist
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedEquivalence

/-!
# Glued scalar twists under an isomorphism of open covers

Effective descent transports scalar-twist naturality along a cover
isomorphism to the corresponding pullback square on the two glued
schemes.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Scalar twists on the schemes glued from isomorphic open covers
commute with pullback along the induced glued-scheme isomorphism. -/
noncomputable def scalarTwistGluedCoverIsoNatIsoOfUnitsEq
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
    (scalarTwistGluedEquivalence
        b hbself hbcocycle).functor ⋙
        pullback (coverIsoGluedIso e).hom ≅
      pullback (coverIsoGluedIso e).hom ⋙
        (scalarTwistGluedEquivalence
          a haself hacocycle).functor := by
  let sourceRestriction :=
    restrictionFunctor (D := 𝒱.gluedCover)
  let sourceTwist :=
    scalarTwistFunctor b hbself hbcocycle
  let sourceGlue :=
    glueFunctor (D := 𝒱.gluedCover)
  let targetRestriction :=
    restrictionFunctor (D := 𝒰.gluedCover)
  let targetTwist :=
    scalarTwistFunctor a haself hacocycle
  let targetGlue :=
    glueFunctor (D := 𝒰.gluedCover)
  let gluedPullback :=
    pullback (coverIsoGluedIso e).hom
  let q :=
    Functor.isoWhiskerRight
        (Functor.associator
          sourceRestriction
          sourceTwist
          sourceGlue).symm
        gluedPullback ≪≫
      conjugatedScalarTwistCoverIsoNatIsoOfDescent
        e a b haself hacocycle
        hbself hbcocycle hab ≪≫
      Functor.isoWhiskerLeft
        gluedPullback
        (Functor.associator
          targetRestriction
          targetTwist
          targetGlue)
  simpa only [scalarTwistGluedEquivalence_functor,
    restrictionEquivalence, sourceRestriction,
    sourceTwist, sourceGlue, targetRestriction,
    targetTwist, targetGlue, gluedPullback] using q

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
