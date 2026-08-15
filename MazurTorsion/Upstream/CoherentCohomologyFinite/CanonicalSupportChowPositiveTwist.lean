/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationSerreTwist
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectivePushforwardCoherenceUnconditional

/-!
# Positive-twist models on the canonical Chow modification

Starting from the coherent pullback of the canonical support module,
apply the relative Serre-twist autoequivalence on its Chow
modification.  Coherence of the model and of its direct image is then
automatic.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace CanonicalSupportThickening

variable {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of ℚ)} [IsProper f]
  {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]

/-- The pullback of the support module followed by a nonnegative
relative Serre twist. -/
noncomputable def chowPositiveTwistModelModule
    (A : CanonicalSupportThickening F) (n : ℕ) :
    let P := A.chowModification (k := ℚ) (f := f)
    P.model.Modules := by
  let P := A.chowModification (k := ℚ) (f := f)
  exact
    P.serreTwistModule (n : ℤ)
      ((Scheme.Modules.pullback P.toOriginal).obj
        A.modelModule)

/-- The positive-twist model remains coherent. -/
theorem chowPositiveTwistModelModule_coherent
    (A : CanonicalSupportThickening F) (n : ℕ) :
    CoherentModule
      (A.chowPositiveTwistModelModule (f := f) n) := by
  let P := A.chowModification (k := ℚ) (f := f)
  have hpull :
      CoherentModule
        ((Scheme.Modules.pullback P.toOriginal).obj
          A.modelModule) :=
    A.chowPullback_coherent (f := f)
  exact
    P.serreTwistModule_coherent
      (n : ℤ)
      ((Scheme.Modules.pullback P.toOriginal).obj
        A.modelModule)
      hpull

/-- The direct image of the positive-twist model is coherent. -/
theorem chowPositiveTwistPushforward_coherent
    (A : CanonicalSupportThickening F) (n : ℕ) :
    let P := A.chowModification (k := ℚ) (f := f)
    CoherentModule
      ((Scheme.Modules.pushforward P.toOriginal).obj
        (A.chowPositiveTwistModelModule (f := f) n)) := by
  dsimp only
  let P := A.chowModification (k := ℚ) (f := f)
  let N := A.chowPositiveTwistModelModule (f := f) n
  have hN : CoherentModule N :=
    A.chowPositiveTwistModelModule_coherent (f := f) n
  letI : N.IsFiniteType := hN.1
  letI : N.IsQuasicoherent := hN.2
  letI : IsNoetherian A.supportScheme :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field
      (A.inclusion ≫ f)
  exact
    ProjectiveSpace.pushforward_coherent_of_relativeProjectiveFactorization
      P.relativeProjective N

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
