/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowDevissage
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowPositiveTwistInput

/-!
# Geometric interfaces for the canonical support-Chow assembly

This module gives reasonably general names to the two functorial inputs
used by the final assembly.  It then proves that those inputs produce
acyclic extensions for every coherent module on a proper rational
scheme.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace
open ProjectiveSpace.IsRelativeProjectiveFactorization
open ProjectiveSpace.SerreTwist

/--
Relative Serre twists commute with restriction to affine base opens and
with local closed-immersion pushforward.
-/
def HasRelativeSerreAffineComparisons : Prop :=
  ∀ {Y S : Scheme.{0}}
    {s : S ⟶ Spec (CommRingCat.of ℚ)}
    {g : Y ⟶ S}
    (h : IsRelativeProjectiveFactorization s g)
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent],
      h.AffineRestrictionTwistCompatible M ∧
        h.AffineTwistPushforwardCompatible

/--
Every projective coordinate defines a map into the corresponding
nonnegative relative Serre twist, invertible on the selected chart.
-/
def HasRelativeProjectiveCoordinateMaps : Prop :=
  ∀ {T : Scheme.{0}} (d : ℕ)
    (g : T ⟶ scheme ℚ d)
    (n : ℕ) (r : Fin (d + 1))
    (M : T.Modules),
      ∃ α :
          M ⟶
            (relativeProjectiveSerreTwistEquivalence
              ℚ d g (n : ℤ)).functor.obj M,
        IsIso
          ((Scheme.Modules.restrictFunctor
            (g ⁻¹ᵁ standardChart ℚ r).ι).map α)

/--
The two relative geometric interfaces furnish all canonical
support-Chow acyclic-extension inputs.
-/
theorem hasCanonicalSupportChowAcyclicExtensions_of_relativeSerreInputs
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (hserre : HasRelativeSerreAffineComparisons)
    (hcoordinate : HasRelativeProjectiveCoordinateMaps) :
    HasCanonicalSupportChowAcyclicExtensions f := by
  intro F hF
  letI : F.IsFiniteType := hF.1
  letI : F.IsQuasicoherent := hF.2
  let A :=
    CanonicalSupportThickening.ofProperToField
      (k := ℚ) (f := f) F
  let P := A.chowModification (k := ℚ) (f := f)
  let N₀ :=
    (Scheme.Modules.pullback P.toOriginal).obj
      A.modelModule
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  have hpullback : CoherentModule N₀ :=
    A.chowPullback_coherent (f := f)
  letI : N₀.IsFiniteType := hpullback.1
  letI : N₀.IsQuasicoherent := hpullback.2
  have hcomparisons :=
    hserre P.relativeProjective N₀
  apply
    A.nonempty_chowPositiveTwistAcyclicExtensionInput
      hcomparisons.1 hcomparisons.2
  dsimp only
  intro n r
  exact
    hcoordinate
      P.relativeProjective.chosenDimension
      P.relativeProjective.chosenProjectiveMap
      n r N₀

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
