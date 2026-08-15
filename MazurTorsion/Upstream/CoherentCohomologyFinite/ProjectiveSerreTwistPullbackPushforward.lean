/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.EquivalencePullbackPushforwardMate
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInverseDegree
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreVanishingTransfer

/-!
# From pullback naturality to pushforward naturality

Base-change naturality of projective scalar twists mates across the
pullback--pushforward adjunction.  The inverse-degree identifications
then turn the mate into the pushforward comparison needed by the
closed-immersion Serre-vanishing transfer.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules

/-- Projective scalar twists commute with pullback along a fixed
morphism, in every integer degree. -/
def ProjectiveTwistPullbackCompatible
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d) : Prop :=
  ∀ m : ℤ,
    Nonempty
      ((projectiveIntegerScalarTwistEquivalence
          R d m).functor ⋙ pullback f ≅
        pullback f ⋙
          (relativeProjectiveSerreTwistEquivalence
            R d f m).functor)

/-- Pullback compatibility in all degrees implies the corresponding
pushforward compatibility in every nonnegative degree. -/
theorem closedImmersionTwistPushforwardCompatible_of_pullback
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d)
    (hpull :
      ProjectiveTwistPullbackCompatible
        R d f) :
    ClosedImmersionTwistPushforwardCompatible
      R d f := by
  intro n
  let m : ℤ := n
  let EP :=
    projectiveIntegerScalarTwistEquivalence
      R d (-m)
  let EY :=
    relativeProjectiveSerreTwistEquivalence
      R d f (-m)
  let hPull :
      EP.functor ⋙ pullback f ≅
        pullback f ⋙ EY.functor :=
    Classical.choice (hpull (-m))
  let hMate :
      pushforward f ⋙ EP.inverse ≅
        EY.inverse ⋙ pushforward f :=
    inverseEquivalenceCommutesWithRightAdjoint
      EP EY
      (pullback f) (pushforward f)
      (pullbackPushforwardAdjunction f)
      hPull
  let hAmbient :
      EP.inverse ≅
        (projectiveIntegerScalarTwistEquivalence
          R d m).functor :=
    projectiveIntegerScalarTwistInverseNegIso
      R d m
  let hRelative :
      EY.inverse ≅
        (relativeProjectiveSerreTwistEquivalence
          R d f m).functor :=
    relativeProjectiveSerreTwistInverseNegIso
      R d f m
  exact
    ⟨(Functor.isoWhiskerLeft
          (pushforward f) hAmbient).symm ≪≫
        hMate ≪≫
        Functor.isoWhiskerRight
          hRelative (pushforward f) |>.symm⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
