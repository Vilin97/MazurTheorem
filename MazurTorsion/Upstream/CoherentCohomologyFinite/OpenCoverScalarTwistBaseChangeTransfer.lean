/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ConjugatedAutoequivalenceNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeModulesEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeUnitCocycle

/-!
# Transporting glued scalar-twist base change to the covered schemes

Once scalar twisting on the two glued covers is known to commute with
pullback, the corresponding statement on the schemes covered by those
covers follows formally by conjugating through the canonical
glued-cover equivalences.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData
open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/--
Transfer a scalar-twist pullback isomorphism on glued covers to the
open-cover scalar-twist autoequivalences on the original schemes.
-/
noncomputable def openCoverScalarTwistBaseChangeNatIsoOfGlued
    (a : ∀ i j,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover a)
    (hglued :
      (scalarTwistGluedEquivalence
          a hself hcocycle).functor ⋙
          pullback (baseChangeGluedMap 𝒰 f) ≅
        pullback (baseChangeGluedMap 𝒰 f) ⋙
          (scalarTwistGluedEquivalence
            (baseChangeCoverUnit 𝒰 f a)
            (baseChangeCoverUnit_self
              𝒰 f a hself)
            (baseChangeCoverUnit_cocycle
              𝒰 f a hcocycle)).functor) :
    (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).functor ⋙
        pullback f ≅
      pullback f ⋙
        (openCoverScalarTwistEquivalence
          (𝒰.pullback₁ f)
          (baseChangeCoverUnit 𝒰 f a)
          (baseChangeCoverUnit_self
            𝒰 f a hself)
          (baseChangeCoverUnit_cocycle
            𝒰 f a hcocycle)).functor := by
  let EC := modulesToGluedEquivalence 𝒰
  let ED :=
    modulesToGluedEquivalence (𝒰.pullback₁ f)
  let A :=
    scalarTwistGluedEquivalence
      a hself hcocycle
  let B :=
    scalarTwistGluedEquivalence
      (D := gluedCover (𝒰.pullback₁ f))
      (baseChangeCoverUnit 𝒰 f a)
      (baseChangeCoverUnit_self
        𝒰 f a hself)
      (baseChangeCoverUnit_cocycle
        𝒰 f a hcocycle)
  change
    ((EC.functor ⋙ A.functor) ⋙ EC.inverse) ⋙
        pullback f ≅
      pullback f ⋙
        ((ED.functor ⋙ B.functor) ⋙ ED.inverse)
  exact
    conjugatedAutoequivalenceNaturalityOfForward
      EC ED
      (pullback f)
      (pullback (baseChangeGluedMap 𝒰 f))
      A B
      (modulesToGluedBaseChangeNatIso 𝒰 f)
      hglued

end AlgebraicGeometry.Scheme.Modules
