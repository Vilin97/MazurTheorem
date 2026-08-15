/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ConjugatedAutoequivalenceNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoModulesComparison

/-!
# Ambient conjugation for scalar twists on isomorphic open covers

This file isolates the categorical transport from the glued-scheme
scalar-twist square to the common ambient module category.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData
open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- The glued scalar-twist square after conjugation through the two
open-cover module equivalences. -/
noncomputable def conjugatedScalarTwistCoverIsoAmbientNatIso
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
    (((modulesToGluedEquivalence 𝒱).functor ⋙
        (scalarTwistGluedEquivalence
          b hbself hbcocycle).functor) ⋙
      (modulesToGluedEquivalence 𝒱).inverse) ⋙
      𝟭 X.Modules ≅
    𝟭 X.Modules ⋙
      (((modulesToGluedEquivalence 𝒰).functor ⋙
          (scalarTwistGluedEquivalence
            a haself hacocycle).functor) ⋙
        (modulesToGluedEquivalence 𝒰).inverse) :=
  conjugatedAutoequivalenceNaturalityOfForward
    (modulesToGluedEquivalence 𝒱)
    (modulesToGluedEquivalence 𝒰)
    (𝟭 X.Modules)
    (pullback (coverIsoGluedIso e).hom)
    (scalarTwistGluedEquivalence
      b hbself hbcocycle)
    (scalarTwistGluedEquivalence
      a haself hacocycle)
    ((modulesToGluedEquivalence
        𝒰).functor.leftUnitor ≪≫
      modulesToGluedCoverIsoNatIso e)
    (scalarTwistGluedCoverIsoNatIsoOfUnitsEq
      e a b haself hacocycle
      hbself hbcocycle hab)

end AlgebraicGeometry.Scheme.Modules
