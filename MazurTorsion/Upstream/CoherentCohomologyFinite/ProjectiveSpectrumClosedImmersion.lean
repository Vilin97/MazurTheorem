/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions induced on `Proj`

Mathlib provides the functorial morphism
`Proj.map : Proj ℬ ⟶ Proj 𝒜`, but at this pin it does not package the
standard fact that a componentwise-surjective graded ring map induces a
closed immersion on `Proj`.

The proof is affine-local.  On a standard open it is the spectrum map
induced by the corresponding map of degree-zero homogeneous
localizations.
-/

open CategoryTheory AlgebraicGeometry
open HomogeneousLocalization
open HomogeneousIdeal

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable {A B σ τ : Type u}
  [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- Surjectivity of a graded ring map descends to every homogeneous
component. -/
lemma gradedAddHom_surjective_of_surjective
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f)
    (d : ℕ) :
    Function.Surjective (f.gradedAddHom d) := by
  intro y
  obtain ⟨x, hx⟩ := hf (y : B)
  refine ⟨DirectSum.decompose 𝒜 x d, ?_⟩
  apply Subtype.ext
  change f (DirectSum.decompose 𝒜 x d : 𝒜 d) = (y : B)
  rw [GradedRingHom.map_directSumDecompose, hx,
    DirectSum.decompose_of_mem_same ℬ y.2]

/-- Componentwise surjectivity supplies the irrelevant-ideal
hypothesis required by `Proj.map`. -/
lemma irrelevant_le_map_of_componentwise_surjective
    (f : 𝒜 →+*ᵍ ℬ)
    (hcomponent :
      ∀ d : ℕ,
        Function.Surjective (f.gradedAddHom d)) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro d hd x hx
  obtain ⟨y, hy⟩ :=
    hcomponent d ⟨x, hx⟩
  have hy' : f (y : A) = x :=
    congrArg Subtype.val hy
  rw [← hy']
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem
      𝒜 hd y.2)

/-- Surjectivity supplies the irrelevant-ideal hypothesis required by
`Proj.map`. -/
lemma irrelevant_le_map_of_surjective
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f :=
  irrelevant_le_map_of_componentwise_surjective f
    (gradedAddHom_surjective_of_surjective f hf)

/-- A componentwise-surjective graded ring map remains surjective after
passing to the degree-zero homogeneous localization away from a
homogeneous element. -/
lemma awayMap_surjective_of_componentwise_surjective
    (f : 𝒜 →+*ᵍ ℬ)
    (hcomponent :
      ∀ d : ℕ,
        Function.Surjective (f.gradedAddHom d))
    {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective ℬ (GradedRingHom.map_mem f hs) z
  obtain ⟨a', ha'⟩ :=
    hcomponent (n • d) ⟨a, ha⟩
  refine ⟨Away.mk 𝒜 hs n a' a'.2, ?_⟩
  rw [Away.map_mk]
  congr
  exact Subtype.ext_iff.mp ha'

/-- The standard affine square associated to a graded ring map is a
pullback square. -/
lemma isPullback_awayMap_projMap
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f)
    {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    IsPullback
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Away.map f s)))
      (AlgebraicGeometry.Proj.awayι
        ℬ (f s) (GradedRingHom.map_mem f hs) hd)
      (AlgebraicGeometry.Proj.awayι 𝒜 s hs hd)
      (AlgebraicGeometry.Proj.map f hf) := by
  apply IsOpenImmersion.isPullback
  · exact AlgebraicGeometry.Proj.awayι_comp_map
      f hf hd s hs
  · rw [AlgebraicGeometry.Proj.opensRange_awayι,
      AlgebraicGeometry.Proj.map_preimage_basicOpen,
      AlgebraicGeometry.Proj.opensRange_awayι]

/-- A componentwise-surjective graded ring map induces a closed
immersion in the contravariant direction on `Proj`. -/
theorem isClosedImmersion_projMap_of_componentwise_surjective
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hcomponent :
      ∀ d : ℕ,
        Function.Surjective (f.gradedAddHom d)) :
    IsClosedImmersion (AlgebraicGeometry.Proj.map f hf) := by
  let I := Σ i : PNat, 𝒜 i
  let U : I → (AlgebraicGeometry.Proj 𝒜).Opens :=
    fun s =>
      AlgebraicGeometry.Proj.basicOpen 𝒜 (s.2 : A)
  have hU : iSup U = ⊤ := by
    classical
    apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
    intro z hz
    rw [← DirectSum.sum_support_decompose 𝒜 z]
    refine Ideal.sum_mem _ fun c hc ↦
      if hc0 : c = 0 then ?_ else ?_
    · convert Ideal.zero_mem _
      subst hc0
      exact hz
    · exact Ideal.subset_span
        ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := @IsClosedImmersion) U hU]
  intro s
  let sourceAwayι :=
    AlgebraicGeometry.Proj.awayι
      ℬ (f (s.2 : A)) (GradedRingHom.map_mem f s.2.2)
        (PNat.pos s.1)
  let targetAwayι :=
    AlgebraicGeometry.Proj.awayι 𝒜 (s.2 : A) s.2.2
      (PNat.pos s.1)
  let eSource :
      ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U s).toScheme ≅
        AlgebraicGeometry.Spec
          (CommRingCat.of <| Away ℬ (f (s.2 : A))) :=
    IsOpenImmersion.isoOfRangeEq
      (((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U s).ι)
      sourceAwayι (by
        rw [Scheme.Opens.range_ι,
          ← Scheme.Hom.coe_opensRange]
        rw [show sourceAwayι.opensRange =
              AlgebraicGeometry.Proj.basicOpen
                ℬ (f (s.2 : A)) by
              exact AlgebraicGeometry.Proj.opensRange_awayι
                ℬ (f (s.2 : A))
                  (GradedRingHom.map_mem f s.2.2)
                    (PNat.pos s.1)]
        exact congrArg SetLike.coe
          (AlgebraicGeometry.Proj.map_preimage_basicOpen
            f hf (s.2 : A)))
  let eTarget :=
    AlgebraicGeometry.Proj.basicOpenIsoSpec
      𝒜 (s.2 : A) s.2.2 (PNat.pos s.1)
  have hTarget :
      eTarget.hom ≫ targetAwayι = (U s).ι := by
    dsimp only [eTarget, targetAwayι, U]
    simp only [AlgebraicGeometry.Proj.awayι,
      Iso.hom_inv_id_assoc]
  have hSource :
      eSource.inv ≫
          ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U s).ι =
        sourceAwayι := by
    exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have hlocal :
      eSource.inv ≫
          (AlgebraicGeometry.Proj.map f hf ∣_ U s) ≫
            eTarget.hom =
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Away.map f (s.2 : A))) := by
    rw [← cancel_mono targetAwayι]
    calc
      (eSource.inv ≫
              (AlgebraicGeometry.Proj.map f hf ∣_ U s) ≫
                eTarget.hom) ≫ targetAwayι =
          eSource.inv ≫
            (AlgebraicGeometry.Proj.map f hf ∣_ U s) ≫
              (U s).ι := by simp only [Category.assoc, hTarget]
      _ = eSource.inv ≫
            ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U s).ι ≫
              AlgebraicGeometry.Proj.map f hf := by
        rw [AlgebraicGeometry.morphismRestrict_ι]
      _ = sourceAwayι ≫
            AlgebraicGeometry.Proj.map f hf := by
        rw [← Category.assoc, hSource]
      _ = AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (Away.map f (s.2 : A))) ≫
            targetAwayι := by
        exact AlgebraicGeometry.Proj.awayι_comp_map
          f hf (PNat.pos s.1) (s.2 : A) s.2.2
  rw [← MorphismProperty.cancel_right_of_respectsIso
      (P := @IsClosedImmersion) _ eTarget.hom,
    ← MorphismProperty.cancel_left_of_respectsIso
      (P := @IsClosedImmersion) eSource.inv,
    hlocal]
  exact IsClosedImmersion.spec_of_surjective _
    (awayMap_surjective_of_componentwise_surjective
      f hcomponent s.2.2)

/-- In particular, a surjective graded ring map induces a closed
immersion in the contravariant direction on `Proj`. -/
theorem isClosedImmersion_projMap_of_surjective
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hsurjective : Function.Surjective f) :
    IsClosedImmersion (AlgebraicGeometry.Proj.map f hf) :=
  isClosedImmersion_projMap_of_componentwise_surjective
    f hf
    (gradedAddHom_surjective_of_surjective f hsurjective)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
