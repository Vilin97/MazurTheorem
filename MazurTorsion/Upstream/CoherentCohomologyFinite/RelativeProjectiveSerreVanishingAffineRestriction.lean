/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveFactorizationAffineMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreVanishingTransfer
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction

/-!
# Relative Serre vanishing over one affine base open

This file states the two precise functorial compatibilities needed to
transport absolute Serre vanishing to a relative projective
factorization:

* restriction of the global relative twist agrees with the twist
  defined by the affine-projective closed embedding;
* that local twist commutes with closed-immersion pushforward.

Once these comparisons are supplied, higher cohomology on the inverse
image of the affine open eventually vanishes.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
namespace IsRelativeProjectiveFactorization

open SerreTwist

noncomputable local instance relativeAffineSerreSheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

variable {k : Type} [CommRing k]
  {Y S : Scheme.{0}}
  {s : S ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ S}

/-- Restriction of the global relative twist to every affine base open
agrees objectwise with the scalar twist defined by the corresponding
closed embedding into projective space over the section ring. -/
def AffineRestrictionTwistCompatible
    (h : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules) : Prop :=
  ∀ (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ),
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    Nonempty
      (((relativeProjectiveSerreTwistEquivalence
          k h.chosenDimension h.chosenProjectiveMap
          (n : ℤ)).functor.obj M).restrict
            (f ⁻¹ᵁ U).ι ≅
        (relativeProjectiveSerreTwistEquivalence
          Γ(S, U) h.chosenDimension
          (h.chosenAffineProjectiveEmbedding U hU)
          (n : ℤ)).functor.obj
            (M.restrict (f ⁻¹ᵁ U).ι))

/-- On every affine base open, the local relative twist commutes with
pushforward along the chosen closed projective embedding. -/
def AffineTwistPushforwardCompatible
    (h : IsRelativeProjectiveFactorization s f) : Prop :=
  ∀ (U : S.Opens) (hU : IsAffineOpen U),
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    ClosedImmersionTwistPushforwardCompatible
      Γ(S, U) h.chosenDimension
      (h.chosenAffineProjectiveEmbedding U hU)

/-- The two affine comparison interfaces imply eventual higher
cohomology vanishing over one affine base open. -/
theorem eventually_restrict_relativeProjectiveSerreTwist_sheafH_subsingleton
    (h : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (hrestrict : h.AffineRestrictionTwistCompatible M)
    (hpushforward : h.AffineTwistPushforwardCompatible)
    (U : S.Opens) (hU : IsAffineOpen U)
    [Module.Flat ℤ Γ(S, U)]
    [IsNoetherianRing Γ(S, U)] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ q : ℕ, 0 < q →
        Subsingleton
          ((((relativeProjectiveSerreTwistEquivalence
            k h.chosenDimension h.chosenProjectiveMap
            (n : ℤ)).functor.obj M).restrict
              (f ⁻¹ᵁ U).ι).sheaf.H q) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  let i :=
    h.chosenAffineProjectiveEmbedding U hU
  let MU := M.restrict (f ⁻¹ᵁ U).ι
  letI : IsClosedImmersion i :=
    h.chosenAffineProjectiveEmbedding_isClosedImmersion U hU
  letI : MU.IsFiniteType := inferInstance
  letI : MU.IsQuasicoherent := inferInstance
  obtain ⟨b, hb⟩ :=
    eventually_relativeProjectiveSerreTwist_sheafH_subsingleton
      Γ(S, U) h.chosenDimension i
      (hpushforward U hU) MU
  refine ⟨b, fun n hn q hq => ?_⟩
  let e :=
    Classical.choice (hrestrict U hU n)
  let eSheaf :=
    (Scheme.Modules.toUnderlyingSheaf
      ((f ⁻¹ᵁ U).toScheme)).mapIso e
  let E :
      (((relativeProjectiveSerreTwistEquivalence
        k h.chosenDimension h.chosenProjectiveMap
        (n : ℤ)).functor.obj M).restrict
          (f ⁻¹ᵁ U).ι).sheaf.H q ≃+
        ((relativeProjectiveSerreTwistEquivalence
          Γ(S, U) h.chosenDimension
          (h.chosenAffineProjectiveEmbedding U hU)
          (n : ℤ)).functor.obj
            (M.restrict (f ⁻¹ᵁ U).ι)).sheaf.H q :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction.postcompIsoAddEquiv
      eSheaf q
  have hTarget := hb n hn q hq
  exact
    ⟨fun x y =>
      E.injective
        (hTarget.elim (E x) (E y))⟩

end IsRelativeProjectiveFactorization
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
