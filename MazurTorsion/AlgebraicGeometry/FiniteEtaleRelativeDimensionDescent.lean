/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Descent of strict relative dimension through a finite étale cover

The existing smoothness API descends smoothness, but the natural-number-valued relative-dimension
predicate needs an additional rank argument.  This file computes the rank of the module of Kähler
differentials on standard-smooth neighbourhoods, transports that rank through a formally étale
faithfully flat cover, and reconstructs local standard-smooth presentations of the same dimension.
It then applies the ring theorem on affine opens to descend `SmoothOfRelativeDimension n` through
an affine, étale, surjective cover.
-/

noncomputable section

open TensorProduct
open CategoryTheory
open AlgebraicGeometry

universe u

namespace MazurTorsion.AlgebraicGeometry

private lemma rankAtStalk_kaehler_eq_of_locally_isStandardSmoothOfRelativeDimension
    (n : ℕ) (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap R S)) (p : PrimeSpectrum S) :
    Module.rankAtStalk Ω[S⁄R] p = n := by
  obtain ⟨s, hs, hstd⟩ := h
  have hnot : ¬ s ⊆ (p.asIdeal : Set S) := by
    intro hsub
    apply p.isPrime.ne_top
    rw [eq_top_iff, ← hs]
    exact Ideal.span_le.mpr hsub
  obtain ⟨t, hts, htp⟩ := Set.not_subset.mp hnot
  let T := Localization.Away t
  have hdisj : Disjoint (Submonoid.powers t : Set S) (p.asIdeal : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr htp
  letI : (p.asIdeal.map (algebraMap S T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers t) T p.asIdeal p.isPrime hdisj
  let q : PrimeSpectrum T := ⟨p.asIdeal.map (algebraMap S T), inferInstance⟩
  have hq : q.comap (algebraMap S T) = p := by
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers t) T p.isPrime hdisj
  letI : Nontrivial T := q.nontrivial
  have hstd' : (algebraMap R T).IsStandardSmoothOfRelativeDimension n := by
    simpa only [IsScalarTower.algebraMap_eq R S T] using hstd t hts
  letI : Algebra.IsStandardSmoothOfRelativeDimension n R T :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mp hstd'
  have hrank : Module.rank T Ω[T⁄R] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have hfinrank : Module.finrank T Ω[T⁄R] = n :=
    Module.finrank_eq_of_rank_eq hrank
  have hsmoothHom : RingHom.Smooth (algebraMap R S) :=
    RingHom.smooth_iff_locally_isStandardSmooth.mpr
      (RingHom.locally_of_locally
        (P := RingHom.IsStandardSmoothOfRelativeDimension n)
        (Q := RingHom.IsStandardSmooth)
        (fun {R S} _ _ {f} hrel ↦
          RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth n f hrel)
        ⟨s, hs, hstd⟩)
  letI : Algebra.Smooth R S := RingHom.smooth_algebraMap.mp hsmoothHom
  letI : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hbc : Module.rankAtStalk Ω[T⁄R] q = Module.rankAtStalk Ω[S⁄R] p := by
    rw [Module.rankAtStalk_isBaseChange
      (KaehlerDifferential.isBaseChange_of_formallyEtale R S T) q, hq]
  rw [← hbc]
  calc
    Module.rankAtStalk Ω[T⁄R] q = Module.finrank T Ω[T⁄R] :=
      congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := T) (M := Ω[T⁄R])) q
    _ = n := hfinrank

private lemma rankAtStalk_kaehler_eq_of_formallyEtale_faithfullyFlat_cover
    (n : ℕ) (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.Smooth R A] [Algebra.FormallyEtale A B]
    [Module.FaithfullyFlat A B]
    (hB : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap R B)) (p : PrimeSpectrum A) :
    Module.rankAtStalk Ω[A⁄R] p = n := by
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := A) (B := B) p
  rw [← hq, ← Module.rankAtStalk_isBaseChange
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B) q]
  exact rankAtStalk_kaehler_eq_of_locally_isStandardSmoothOfRelativeDimension
    n R B hB q

private lemma
    locally_isStandardSmoothOfRelativeDimension_of_smooth_of_formallyEtale_faithfullyFlat
    (n : ℕ) (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.Smooth R A] [Algebra.FormallyEtale A B]
    [Module.FaithfullyFlat A B]
    (hB : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap R B)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap R A) := by
  choose a ha hstd using Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R (S := A)
  refine ⟨Set.range (fun p : PrimeSpectrum A ↦ a p.asIdeal), ?_, ?_⟩
  · simp [← PrimeSpectrum.iSup_basicOpen_eq_top_iff,
      TopologicalSpace.Opens.ext_iff, Set.ext_iff]
    grind
  · rintro t ⟨p, rfl⟩
    let T := Localization.Away (a p.asIdeal)
    have hdisj : Disjoint (Submonoid.powers (a p.asIdeal) : Set A)
        (p.asIdeal : Set A) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime (a p.asIdeal)).mpr (ha p.asIdeal)
    letI : (p.asIdeal.map (algebraMap A T)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers (a p.asIdeal)) T p.asIdeal p.isPrime hdisj
    let q : PrimeSpectrum T := ⟨p.asIdeal.map (algebraMap A T), inferInstance⟩
    have hq : q.comap (algebraMap A T) = p := by
      apply PrimeSpectrum.ext
      exact IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers (a p.asIdeal)) T p.isPrime hdisj
    letI : Nontrivial T := q.nontrivial
    letI : Algebra.IsStandardSmooth R T := hstd p.asIdeal
    have hbc : Module.rankAtStalk Ω[T⁄R] q = Module.rankAtStalk Ω[A⁄R] p := by
      rw [Module.rankAtStalk_isBaseChange
        (KaehlerDifferential.isBaseChange_of_formallyEtale R A T) q, hq]
    have hfinrank : Module.finrank T Ω[T⁄R] = n := by
      calc
        Module.finrank T Ω[T⁄R] = Module.rankAtStalk Ω[T⁄R] q :=
          (congrFun (Module.rankAtStalk_eq_finrank_of_free
            (R := T) (M := Ω[T⁄R])) q).symm
        _ = Module.rankAtStalk Ω[A⁄R] p := hbc
        _ = n := rankAtStalk_kaehler_eq_of_formallyEtale_faithfullyFlat_cover
          n R A B hB p
    have hrank : Module.rank T Ω[T⁄R] = n := by
      rw [← Module.finrank_eq_rank T Ω[T⁄R], hfinrank]
    have hrel : Algebra.IsStandardSmoothOfRelativeDimension n R T :=
      (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr hrank
    have hrel' : (algebraMap R T).IsStandardSmoothOfRelativeDimension n :=
      (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr hrel
    simpa only [IsScalarTower.algebraMap_eq R A T] using hrel'

/-- Strict relative dimension descends through an affine, étale, surjective cover of the source.
The assumption that the target morphism is smooth supplies standard-smooth neighbourhoods on
which the rank of Kähler differentials determines the relative dimension. -/
theorem smoothOfRelativeDimension_of_etale_surjective_comp
    (n : ℕ) {X Y S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S)
    [AlgebraicGeometry.IsAffineHom f]
    [AlgebraicGeometry.Etale f]
    [AlgebraicGeometry.Surjective f]
    [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.SmoothOfRelativeDimension n (f ≫ g)] :
    AlgebraicGeometry.SmoothOfRelativeDimension n g := by
  rw [HasRingHomProperty.iff_appLE (P := @SmoothOfRelativeDimension n)]
  intro U V e
  let W : X.affineOpens :=
    ⟨f ⁻¹ᵁ V.1,
      (inferInstance : AlgebraicGeometry.IsAffineHom f).isAffine_preimage V.1 V.2⟩
  let ecomp : W.1 ≤ (f ≫ g) ⁻¹ᵁ U.1 := by
    dsimp only [W]
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact f.preimage_mono e
  have hcomp : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      ((f.appLE V.1 W.1 le_rfl).hom.comp (g.appLE U.1 V.1 e).hom) := by
    have h := AlgebraicGeometry.HasRingHomProperty.appLE
      (P := @AlgebraicGeometry.SmoothOfRelativeDimension n)
      (f ≫ g)
      (inferInstance : AlgebraicGeometry.SmoothOfRelativeDimension n (f ≫ g))
      U W ecomp
    simpa only [← CommRingCat.hom_comp,
      AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE] using h
  have hsmooth : RingHom.Smooth (g.appLE U.1 V.1 e).hom :=
    AlgebraicGeometry.HasRingHomProperty.appLE
      (P := @AlgebraicGeometry.Smooth) g
      (inferInstance : AlgebraicGeometry.Smooth g) U V e
  have hetale : RingHom.Etale (f.appLE V.1 W.1 le_rfl).hom :=
    AlgebraicGeometry.HasRingHomProperty.appLE
      (P := @AlgebraicGeometry.Etale) f
      (inferInstance : AlgebraicGeometry.Etale f) V W le_rfl
  let fV : W.1.toScheme ⟶ V.1.toScheme := f ∣_ V.1
  letI : AlgebraicGeometry.IsAffine W.1.toScheme := W.2
  letI : AlgebraicGeometry.IsAffine V.1.toScheme := V.2
  letI : AlgebraicGeometry.Etale fV := by
    dsimp only [fV]
    exact CategoryTheory.MorphismProperty.of_isPullback
      (AlgebraicGeometry.isPullback_morphismRestrict f V.1).flip
      (inferInstance : AlgebraicGeometry.Etale f)
  letI : AlgebraicGeometry.Surjective fV := by
    refine ⟨?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := f.surjective y
    have hxV : x ∈ W.1 := by
      change f x ∈ V.1
      simpa only [hx] using hy
    refine ⟨⟨x, hxV⟩, ?_⟩
    apply Subtype.ext
    exact (AlgebraicGeometry.morphismRestrict_base_coe
      f V.1 ⟨x, hxV⟩).trans hx
  have hffTop : fV.appTop.hom.FaithfullyFlat :=
    (AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine fV).mp
      ⟨inferInstance, inferInstance⟩
  have hffRes : (f.resLE V.1 W.1 le_rfl).appTop.hom.FaithfullyFlat := by
    rw [AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict]
    dsimp only [fV] at hffTop
    exact hffTop
  have hff : (f.appLE V.1 W.1 le_rfl).hom.FaithfullyFlat :=
    (RingHom.FaithfullyFlat.respectsIso.arrow_mk_iso_iff
      (AlgebraicGeometry.arrowResLEAppIso f V.1 W.1 le_rfl)).mp hffRes
  algebraize [(g.appLE U.1 V.1 e).hom, (f.appLE V.1 W.1 le_rfl).hom,
    (f.appLE V.1 W.1 le_rfl).hom.comp (g.appLE U.1 V.1 e).hom]
  apply
    locally_isStandardSmoothOfRelativeDimension_of_smooth_of_formallyEtale_faithfullyFlat
      n Γ(S, U.1) Γ(Y, V.1) Γ(X, W.1)
  simpa only [RingHom.algebraMap_toAlgebra] using hcomp

end MazurTorsion.AlgebraicGeometry
