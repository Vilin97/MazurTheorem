/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistCoefficientBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistCongruence
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistPullbackComposition
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreVanishingAffineRestriction

/-!
# Relative Serre twists restricted to affine base opens

For a relative projective factorization, restriction to the inverse
image of an affine base open turns the global relative Serre twist into
the relative twist attached to the chosen affine projective embedding.
The comparison combines pullback naturality, composition of pullbacks,
the affine factorization square, and extension of coefficients.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
namespace IsRelativeProjectiveFactorization

open SerreTwist

variable {k : Type} [CommRing k]
  {Y S : Scheme.{0}}
  {s : S ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ S}

/--
The objectwise comparison between restriction of the global relative
Serre twist and the local relative Serre twist over an affine base open.
-/
noncomputable def affineRestrictionTwistIso
    (h : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules)
    (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (((relativeProjectiveSerreTwistEquivalence
        k h.chosenDimension h.chosenProjectiveMap
        (n : ℤ)).functor.obj M).restrict
          (f ⁻¹ᵁ U).ι ≅
      (relativeProjectiveSerreTwistEquivalence
        Γ(S, U) h.chosenDimension
        (h.chosenAffineProjectiveEmbedding U hU)
        (n : ℤ)).functor.obj
          (M.restrict (f ⁻¹ᵁ U).ι)) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  let j := (f ⁻¹ᵁ U).ι
  let i := h.chosenAffineProjectiveEmbedding U hU
  have hi :
      i ≫ coefficientMap
          (algebraMap k Γ(S, U))
          h.chosenDimension =
        j ≫ h.chosenProjectiveMap :=
    h.chosenAffineProjectiveEmbedding_coefficientMap U hU
  exact
    (Scheme.Modules.restrictFunctorIsoPullback j).app
        ((relativeProjectiveSerreTwistEquivalence
          k h.chosenDimension h.chosenProjectiveMap
          (n : ℤ)).functor.obj M) ≪≫
      (relativeProjectiveSerreTwistPullbackCompositionNatIso
        k h.chosenDimension h.chosenProjectiveMap
        j (n : ℤ)).app M ≪≫
      (relativeProjectiveSerreTwistFunctorCongr
        k h.chosenDimension hi.symm (n : ℤ)).app
          ((Scheme.Modules.pullback j).obj M) ≪≫
      (relativeProjectiveSerreTwistCoefficientBaseChangeNatIso
        (k := k) (R := Γ(S, U))
        h.chosenDimension i (n : ℤ)).app
          ((Scheme.Modules.pullback j).obj M) ≪≫
      (relativeProjectiveSerreTwistEquivalence
        Γ(S, U) h.chosenDimension i
        (n : ℤ)).functor.mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app M)

/--
The canonical pullback and coefficient comparisons supply the affine
restriction compatibility interface for every relative projective
factorization.
-/
theorem affineRestrictionTwistCompatible
    (h : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules) :
    h.AffineRestrictionTwistCompatible M := by
  intro U hU n
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  exact ⟨h.affineRestrictionTwistIso M U hU n⟩

end IsRelativeProjectiveFactorization
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
