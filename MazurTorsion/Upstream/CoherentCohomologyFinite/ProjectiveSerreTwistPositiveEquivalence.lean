/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerEquivalenceShift
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistEquivalenceQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveTwistFiniteSumShift

/-!
# The positive family of projective scalar-twist functors

Natural-number degrees select the positive half of the integer scalar-twist
autoequivalences.  These functors preserve finite limits, epimorphisms, and
finite coproducts, and eventually move every finite sum of integer twists
into nonnegative degrees.
-/


open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable (R : Type) [CommRing R] (d : ℕ)

/-- The natural-number-indexed positive scalar-twist functor. -/
noncomputable def positiveScalarTwistFunctor
    (n : ℕ) :
    (scheme R d).Modules ⥤ (scheme R d).Modules :=
  (projectiveIntegerScalarTwistEquivalence
    R d (n : ℤ)).functor

noncomputable instance positiveScalarTwistFunctor_preservesFiniteLimits
    (n : ℕ) :
    PreservesFiniteLimits
      (positiveScalarTwistFunctor R d n) := by
  dsimp only [positiveScalarTwistFunctor]
  infer_instance

instance positiveScalarTwistFunctor_preservesEpimorphisms
    (n : ℕ) :
    (positiveScalarTwistFunctor
      R d n).PreservesEpimorphisms := by
  dsimp only [positiveScalarTwistFunctor]
  infer_instance

noncomputable instance
    positiveScalarTwistFunctor_preservesFiniteCoproducts
    (n : ℕ) :
    PreservesFiniteCoproducts
      (positiveScalarTwistFunctor R d n) := by
  dsimp only [positiveScalarTwistFunctor]
  infer_instance

/-- Positive scalar twisting eventually sends every finite integer-twist
sum to a finite sum of nonnegative twists. -/
theorem eventually_isBaseFiniteNonnegativeTwistSum_positiveScalarTwist
    (E : (scheme R d).Modules)
    (hE : IsBaseFiniteIntegerTwistSum R d E) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      IsBaseFiniteNonnegativeTwistSum R d
        ((positiveScalarTwistFunctor R d n).obj E) :=
  eventually_isBaseFiniteNonnegativeTwistSum_map
    (positiveScalarTwistFunctor R d)
    (fun n m =>
      nonempty_projectiveIntegerScalarTwistShiftIso
        R d m (n : ℤ))
    E hE

/-- Every positive scalar-twist functor preserves quasicoherence. -/
theorem positiveScalarTwistFunctor_isQuasicoherent
    (n : ℕ) (E : (scheme R d).Modules)
    (hE : E.IsQuasicoherent) :
    ((positiveScalarTwistFunctor
      R d n).obj E).IsQuasicoherent :=
  projectiveIntegerScalarTwist_isQuasicoherent
    R d E (n : ℤ) hE

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
