/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeAcyclicPushforwardCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectivePushforwardCoherenceUnconditional
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistFiniteness
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreVanishingFiniteAffine

/-!
# Relative Serre twists and Leray comparison

Uniform relative Serre vanishing on the inverse images of the canonical
finite affine cover makes a sufficiently positive twist acyclic for the
relative-projective morphism.  The finite Čech comparison then identifies
the cohomology of that twist with the cohomology of its direct image.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
namespace IsRelativeProjectiveFactorization

open SerreTwist
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.RelativeAcyclicPushforwardCohomology

noncomputable local instance relativeSerreLeraySheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

variable {Y S : Scheme.{0}}
  {s : S ⟶ Spec (CommRingCat.of ℚ)}
  {f : Y ⟶ S}

/--
A common positive twist degree can be chosen so that every later twist
satisfies the degreewise Leray comparison.
-/
theorem eventually_relativeProjectiveSerreTwist_pushforwardHAddEquiv
    [CompactSpace S] [S.IsSeparated] [IsLocallyNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (hrestrict : h.AffineRestrictionTwistCompatible M)
    (hpushforward : h.AffineTwistPushforwardCompatible) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ q : ℕ,
        Nonempty
          (((Scheme.Modules.pushforward f).obj
              ((relativeProjectiveSerreTwistEquivalence
                ℚ h.chosenDimension h.chosenProjectiveMap
                (n : ℤ)).functor.obj M)).sheaf.H q ≃+
            ((relativeProjectiveSerreTwistEquivalence
              ℚ h.chosenDimension h.chosenProjectiveMap
              (n : ℤ)).functor.obj M).sheaf.H q) := by
  obtain ⟨b, hb⟩ :=
    h.eventually_finiteAffineIntersections_restrict_sheafH_subsingleton
      M hrestrict hpushforward
  refine ⟨b, fun n hn q => ?_⟩
  let N :=
    (relativeProjectiveSerreTwistEquivalence
      ℚ h.chosenDimension h.chosenProjectiveMap
      (n : ℤ)).functor.obj M
  have hN : CoherentModule N :=
    ⟨SerreTwist.relativeProjectiveSerreTwist_isFiniteType
        ℚ h.chosenDimension h.chosenProjectiveMap
        (n : ℤ) M,
      SerreTwist.relativeProjectiveSerreTwist_isQuasicoherent
        ℚ h.chosenDimension h.chosenProjectiveMap
        (n : ℤ) M⟩
  letI : N.IsFiniteType := hN.1
  letI : N.IsQuasicoherent := hN.2
  have hpush :
      CoherentModule
        ((Scheme.Modules.pushforward f).obj N) :=
    pushforward_coherent_of_relativeProjectiveFactorization
      h N
  letI :
      ((Scheme.Modules.pushforward f).obj N).IsQuasicoherent :=
    hpush.2
  exact
    ⟨(pushforwardHAddEquiv_of_finiteAffineCoverRestrictAcyclic
          f N (hb n hn) q).symm⟩

end IsRelativeProjectiveFactorization
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
