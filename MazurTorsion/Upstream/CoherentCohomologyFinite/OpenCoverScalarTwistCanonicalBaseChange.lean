/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistBaseChangeTransfer
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistGluedCanonicalBaseChange

/-!
# Canonical base change for open-cover scalar twists

The canonical descent comparison gives the glued-cover square required
by the general transfer theorem.  Thus scalar twisting by an overlap
unit cocycle commutes with pullback to the base-changed open cover.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData
open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- An open-cover scalar twist commutes with pullback, with both the
cover and its unit cocycle pulled back along the given morphism. -/
noncomputable def openCoverScalarTwistCanonicalBaseChangeNatIso
    (a : ∀ i j, Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition 𝒰.gluedCover a) :
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
            𝒰 f a hcocycle)).functor :=
  openCoverScalarTwistBaseChangeNatIsoOfGlued
    𝒰 f a hself hcocycle
    (scalarTwistGluedBaseChangeNatIso
      𝒰 f a hself hcocycle)

end AlgebraicGeometry.Scheme.Modules
