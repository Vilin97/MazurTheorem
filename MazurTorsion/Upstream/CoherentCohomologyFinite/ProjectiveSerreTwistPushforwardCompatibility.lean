/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistPullbackCompatibility
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreVanishingAffineRestriction

/-!
# Projective Serre twists and pushforward

Pullback naturality of projective Serre twists mates across the
pullback--pushforward adjunction.  This file packages the resulting
closed-immersion and affine-relative compatibility statements.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

/-- The central glued-cover base-change statement implies the
pushforward compatibility used in relative Serre vanishing. -/
theorem closedImmersionTwistPushforwardCompatible_of_glued
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d)
    (hglued :
      ProjectiveGluedTwistPullbackCompatible
        R d f) :
    ClosedImmersionTwistPushforwardCompatible
      R d f :=
  closedImmersionTwistPushforwardCompatible_of_pullback
    R d f
    (projectiveTwistPullbackCompatible_of_glued
      R d f hglued)

/-- Projective Serre twists commute with pushforward along every
morphism into projective space. -/
theorem closedImmersionTwistPushforwardCompatible
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d) :
    ClosedImmersionTwistPushforwardCompatible R d f :=
  closedImmersionTwistPushforwardCompatible_of_pullback
    R d f
    (projectiveTwistPullbackCompatible R d f)

namespace IsRelativeProjectiveFactorization

variable {k : Type} [CommRing k]
  {Y S : Scheme.{0}}
  {s : S ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ S}

/-- A family of glued-cover base-change comparisons over affine base
opens supplies the affine pushforward compatibility interface. -/
theorem affineTwistPushforwardCompatible_of_glued
    (h : IsRelativeProjectiveFactorization s f)
    (hglued :
      ∀ (U : S.Opens) (hU : IsAffineOpen U),
        letI : Algebra k Γ(S, U) :=
          (affineOpenCoefficientMap s U hU).hom.toAlgebra
        ProjectiveGluedTwistPullbackCompatible
          Γ(S, U) h.chosenDimension
          (h.chosenAffineProjectiveEmbedding U hU)) :
    h.AffineTwistPushforwardCompatible := by
  intro U hU
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  exact
    closedImmersionTwistPushforwardCompatible_of_glued
      Γ(S, U) h.chosenDimension
      (h.chosenAffineProjectiveEmbedding U hU)
      (hglued U hU)

/-- The canonical projective scalar-twist comparison supplies the
affine pushforward compatibility for every relative projective
factorization. -/
theorem affineTwistPushforwardCompatible
    (h : IsRelativeProjectiveFactorization s f) :
    h.AffineTwistPushforwardCompatible := by
  intro U hU
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  exact
    closedImmersionTwistPushforwardCompatible
      Γ(S, U) h.chosenDimension
      (h.chosenAffineProjectiveEmbedding U hU)

end IsRelativeProjectiveFactorization
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
