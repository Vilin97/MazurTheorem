/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoConjugatedScalarTwistAmbient

/-!
# Scalar twists are invariant under isomorphism of open covers

An isomorphism of open covers which transports one overlap-unit cocycle
to another induces a natural isomorphism between the corresponding
scalar-twist functors on the ambient scheme.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData
open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Scalar-twist functors defined from isomorphic open covers agree when
the cover isomorphism transports the target cocycle to the source
cocycle. -/
noncomputable def openCoverScalarTwistCoverIsoNatIso
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
    (openCoverScalarTwistEquivalence
        𝒱 b hbself hbcocycle).functor ≅
      (openCoverScalarTwistEquivalence
        𝒰 a haself hacocycle).functor :=
  (openCoverScalarTwistEquivalence
      𝒱 b hbself hbcocycle).functor.rightUnitor.symm ≪≫
    conjugatedScalarTwistCoverIsoAmbientNatIso
      e a b haself hacocycle
      hbself hbcocycle hab ≪≫
    (openCoverScalarTwistEquivalence
      𝒰 a haself hacocycle).functor.leftUnitor

end AlgebraicGeometry.Scheme.Modules
