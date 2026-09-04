/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductDoubleInputOverlapCompatibility

/-!
# An actual addition-source cover of the infinity pair chart

The coarse regular cover uses all of `D(B∞)`, whereas the checked regular
addition morphism has the smaller source obtained by also inverting its output
`Y` coordinate.  This file sharpens the primewise argument: outside the exact
double-standard open and the secant output-`Z` open, both inputs reduce to the
point at infinity.  On every lift to `D(B∞)`, the regular output `Y` is then
`-1`, so the lift belongs to the genuine regular addition source.

The design boundary is an honest finite `Scheme.OpenCover` of the
infinity-by-infinity pair chart.  Its three named members are precisely the
sources of the downstream standard-pair, regular-neighborhood, and secant
addition morphisms; no non-additive doubling chart is admitted.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The three affine source maps -/

/-- The double-standard source in the affine presentation of the infinity
pair chart. -/
noncomputable def projectivePairDoubleOverlapToInfinityPairAffine
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      Spec (.of (projectiveInfinityPairCoordinateRing W)) :=
  projectivePairDoubleOverlapToInfinityPair W ≫
    (projectivePairChartIsoSpecTensor W (false, false)).hom

/-- The genuine regular addition source in the affine presentation of the
infinity pair chart. -/
noncomputable def projectiveInfinityPairOriginAdditionOpenAffine
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairNeighborhoodAdditionOutputRing W)) ⟶
      Spec (.of (projectiveInfinityPairCoordinateRing W)) :=
  projectiveInfinityPairOriginAdditionOpen W ≫
    (projectivePairChartIsoSpecTensor W (false, false)).hom

/-- The secant output-`Z` source in the affine presentation of the infinity
pair chart. -/
noncomputable def projectiveInfinityPairSecantZOpenAffine
    (W : WeierstrassCurve K) :
    Spec (.of
        (projectivePairChartAdditionOutputRing W (false, false) true)) ⟶
      Spec (.of (projectiveInfinityPairCoordinateRing W)) :=
  projectivePairChartAdditionOutputOpen W (false, false) true ≫
    (projectivePairChartIsoSpecTensor W (false, false)).hom

instance projectivePairDoubleOverlapToInfinityPairAffine_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectivePairDoubleOverlapToInfinityPairAffine W) := by
  dsimp only [projectivePairDoubleOverlapToInfinityPairAffine]
  infer_instance

instance projectiveInfinityPairOriginAdditionOpenAffine_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectiveInfinityPairOriginAdditionOpenAffine W) := by
  dsimp only [projectiveInfinityPairOriginAdditionOpenAffine]
  infer_instance

instance projectiveInfinityPairSecantZOpenAffine_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectiveInfinityPairSecantZOpenAffine W) := by
  dsimp only [projectiveInfinityPairSecantZOpenAffine]
  infer_instance

/-- The affine double-standard source has exactly the basic-open range where
the product of the two infinity input `Z` coordinates is nonzero. -/
theorem projectivePairDoubleOverlapToInfinityPairAffine_opensRange
    (W : WeierstrassCurve K) :
    (projectivePairDoubleOverlapToInfinityPairAffine W).opensRange =
      PrimeSpectrum.basicOpen
        (projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W) := by
  letI := (infinityPairToDoubleOverlapAlgHom W).toAlgebra
  haveI := projectivePairDoubleOverlap_isLocalization_infinityPair W
  simp only [projectivePairDoubleOverlapToInfinityPairAffine,
    projectivePairDoubleOverlapToInfinityPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
      (projectivePairDoubleChartOverlapCoordinateRing W)
      (projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W)

/-- The affine secant source has exactly the basic-open range where its raw
output `Z` coordinate is nonzero. -/
theorem projectiveInfinityPairSecantZOpenAffine_opensRange
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairSecantZOpenAffine W).opensRange =
      PrimeSpectrum.basicOpen
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)) := by
  simp only [projectiveInfinityPairSecantZOpenAffine,
    projectivePairChartAdditionOutputOpen, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (projectiveInfinityPairCoordinateRing W))
    (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3))

/-- In affine coordinates, the genuine regular source is the composite of
the output localization with the `B∞` localization. -/
theorem projectiveInfinityPairOriginAdditionOpenAffine_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginAdditionOpenAffine W =
      projectiveInfinityPairNeighborhoodAdditionOutputOpen W ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (projectiveInfinityPairCoordinateRing W)
            (projectiveInfinityPairNeighborhoodRing W))) := by
  simp [projectiveInfinityPairOriginAdditionOpenAffine,
    projectiveInfinityPairOriginAdditionOpen,
    projectiveInfinityPairNeighborhoodOpen]

/-! ## The residual prime lies in the genuine regular source -/

private theorem projectivePairChartAdditionCoordinates_map_to_quotient_again
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (ij : Bool × Bool)
    (f : projectivePairChartCoordinateRing W ij →ₐ[K] A) :
    f ∘ projectivePairChartAdditionCoordinates W ij =
      (W.map (algebraMap K A)).toProjective.addXYZ
        (f ∘ projectivePairChartFirstUniversalPoint W ij)
        (f ∘ projectivePairChartSecondUniversalPoint W ij) := by
  have h := WeierstrassCurve.Projective.map_addXYZ
    (W' := projectivePairChartMappedCurve W ij)
    (f := f.toRingHom)
    (P := projectivePairChartFirstUniversalPoint W ij)
    (Q := projectivePairChartSecondUniversalPoint W ij)
  have hf : f.toRingHom.comp
      (algebraMap K (projectivePairChartCoordinateRing W ij)) =
        algebraMap K A := by
    ext a
    exact f.commutes a
  change ((W.map
      (algebraMap K (projectivePairChartCoordinateRing W ij))).map
        f.toRingHom).toProjective.addXYZ _ _ = _ at h
  rw [WeierstrassCurve.map_map, hf] at h
  exact h.symm

private theorem projectiveInfinityPairAdditionB12_map_eq_one_again
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairCoordinateRing W →+* A)
    (hX₁ : f (projectiveInfinityPairX₁ W) = 0)
    (hZ₁ : f (projectiveInfinityPairZ₁ W) = 0)
    (hZ₂ : f (projectiveInfinityPairZ₂ W) = 0) :
    f (projectiveInfinityPairAdditionB12 W) = 1 := by
  simp [projectiveInfinityPairAdditionB12, hX₁, hZ₁, hZ₂]

private theorem projectiveInfinityPairAdditionA12_map_eq_zero_again
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairCoordinateRing W →+* A)
    (hX₁ : f (projectiveInfinityPairX₁ W) = 0)
    (hX₂ : f (projectiveInfinityPairX₂ W) = 0)
    (hZ₂ : f (projectiveInfinityPairZ₂ W) = 0) :
    f (projectiveInfinityPairAdditionA12 W) = 0 := by
  simp [projectiveInfinityPairAdditionA12, hX₁, hX₂, hZ₂]

private theorem projectiveInfinityPair_coordinates_mem_of_product_and_addZ_mem
    (W : WeierstrassCurve K)
    (p : PrimeSpectrum (projectiveInfinityPairCoordinateRing W))
    (hZZ : projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W ∈
      p.asIdeal)
    (hAddZ : projectivePairChartAdditionCoordinates W (false, false)
      (2 : Fin 3) ∈ p.asIdeal) :
    projectiveInfinityPairX₁ W ∈ p.asIdeal ∧
      projectiveInfinityPairZ₁ W ∈ p.asIdeal ∧
      projectiveInfinityPairX₂ W ∈ p.asIdeal ∧
      projectiveInfinityPairZ₂ W ∈ p.asIdeal := by
  let R := projectiveInfinityPairCoordinateRing W
  let Q := R ⧸ p.asIdeal
  letI : CommRing Q := Ideal.Quotient.commRing p.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let q : R →+* Q := Ideal.Quotient.mk p.asIdeal
  let g : K →+* Q := q.comp (algebraMap K R)
  letI : Algebra K Q := g.toAlgebra
  let qAlg : R →ₐ[K] Q :=
    { __ := q
      commutes' := fun _ ↦ rfl }
  let P₁ : Fin 3 → Q := q ∘
    projectivePairChartFirstUniversalPoint W (false, false)
  let P₂ : Fin 3 → Q := q ∘
    projectivePairChartSecondUniversalPoint W (false, false)
  have hP₁ : (W.map g).toProjective.Equation P₁ := by
    simpa [g, P₁, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartFirstUniversalPoint_equation W
        (false, false)).map q
  have hP₂ : (W.map g).toProjective.Equation P₂ := by
    simpa [g, P₂, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartSecondUniversalPoint_equation W
        (false, false)).map q
  have hP₁Y : P₁ (1 : Fin 3) = 1 := by
    change q (projectivePairChartFirstUniversalPoint W (false, false)
      (coveringCoordinate false)) = 1
    rw [projectivePairChartFirstUniversalPoint_normalized, map_one]
  have hP₂Y : P₂ (1 : Fin 3) = 1 := by
    change q (projectivePairChartSecondUniversalPoint W (false, false)
      (coveringCoordinate false)) = 1
    rw [projectivePairChartSecondUniversalPoint_normalized, map_one]
  have hproduct : P₁ (2 : Fin 3) * P₂ (2 : Fin 3) = 0 := by
    change q (projectiveInfinityPairZ₁ W *
      projectiveInfinityPairZ₂ W) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hZZ
  have hmap := projectivePairChartAdditionCoordinates_map_to_quotient_again
    W (false, false) qAlg
  have hmapCoordinate := congrFun hmap (2 : Fin 3)
  change q (projectivePairChartAdditionCoordinates W (false, false)
      (2 : Fin 3)) =
    (W.map g).toProjective.addXYZ P₁ P₂ (2 : Fin 3) at hmapCoordinate
  have hAddZero : q
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hAddZ
  have hbothZ : P₁ (2 : Fin 3) = 0 ∧ P₂ (2 : Fin 3) = 0 := by
    rcases mul_eq_zero.mp hproduct with hP₁Z | hP₂Z
    · refine ⟨hP₁Z, ?_⟩
      by_contra hP₂Z
      have hformula := (W.map g).toProjective.addXYZ_of_Z_eq_zero_left
        (P := P₁) (Q := P₂) hP₁ hP₁Z
      have hcoordinate := hmapCoordinate.trans
        (congrFun hformula (2 : Fin 3))
      rw [Pi.smul_apply, hP₁Y, one_pow, one_mul, smul_eq_mul]
        at hcoordinate
      exact hP₂Z (mul_self_eq_zero.mp
        (hcoordinate.symm.trans hAddZero))
    · refine ⟨?_, hP₂Z⟩
      by_contra hP₁Z
      have hformula := (W.map g).toProjective.addXYZ_of_Z_eq_zero_right
        (P := P₁) (Q := P₂) hP₂ hP₂Z
      have hcoordinate := hmapCoordinate.trans
        (congrFun hformula (2 : Fin 3))
      rw [Pi.smul_apply, hP₂Y, one_pow, one_mul, smul_eq_mul,
        neg_mul] at hcoordinate
      have hsquare : P₁ (2 : Fin 3) ^ 2 = 0 := by
        simpa only [pow_two, neg_eq_zero] using
          hcoordinate.symm.trans hAddZero
      exact hP₁Z (sq_eq_zero_iff.mp hsquare)
  have hP₁X : P₁ (0 : Fin 3) = 0 :=
    (W.map g).toProjective.X_eq_zero_of_Z_eq_zero hP₁ hbothZ.1
  have hP₂X : P₂ (0 : Fin 3) = 0 :=
    (W.map g).toProjective.X_eq_zero_of_Z_eq_zero hP₂ hbothZ.2
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp hP₁X,
    Ideal.Quotient.eq_zero_iff_mem.mp hbothZ.1,
    Ideal.Quotient.eq_zero_iff_mem.mp hP₂X,
    Ideal.Quotient.eq_zero_iff_mem.mp hbothZ.2⟩

private theorem projectiveInfinityPairNeighborhoodThirdD_map_eq_one
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairNeighborhoodRing W →+* A)
    (hSlope : f (projectiveInfinityPairNeighborhoodSlope W) = 0) :
    f (projectiveInfinityPairNeighborhoodThirdD W) = 1 := by
  rw [projectiveInfinityPairNeighborhoodThirdD]
  simp only [f.map_add, f.map_mul, f.map_pow, f.map_one]
  rw [hSlope]
  ring

private theorem projectiveInfinityPairNeighborhoodSlope_map_eq_zero
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairNeighborhoodRing W →+* A)
    (hA : f (projectiveInfinityPairNeighborhoodA12 W) = 0) :
    f (projectiveInfinityPairNeighborhoodSlope W) = 0 := by
  change f (projectiveInfinityPairNeighborhoodA12 W *
    IsLocalization.Away.invSelf
      (projectiveInfinityPairAdditionB12 W)) = 0
  rw [f.map_mul, hA, zero_mul]

private theorem projectiveInfinityPairNeighborhoodIntercept_map_eq_zero
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairNeighborhoodRing W →+* A)
    (hZ₁ : f (projectiveInfinityPairNeighborhoodZ₁ W) = 0)
    (hSlope : f (projectiveInfinityPairNeighborhoodSlope W) = 0)
    (hX₁ : f (projectiveInfinityPairNeighborhoodX₁ W) = 0) :
    f (projectiveInfinityPairNeighborhoodIntercept W) = 0 := by
  change f (projectiveInfinityPairNeighborhoodZ₁ W -
    projectiveInfinityPairNeighborhoodSlope W *
      projectiveInfinityPairNeighborhoodX₁ W) = 0
  rw [f.map_sub, f.map_mul, hZ₁, hSlope, hX₁]
  ring

private theorem projectiveInfinityPairNeighborhoodThirdE_map_eq_zero
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairNeighborhoodRing W →+* A)
    (hSlope : f (projectiveInfinityPairNeighborhoodSlope W) = 0)
    (hIntercept : f (projectiveInfinityPairNeighborhoodIntercept W) = 0) :
    f (projectiveInfinityPairNeighborhoodThirdE W) = 0 := by
  rw [projectiveInfinityPairNeighborhoodThirdE]
  simp only [f.map_sub, f.map_add, f.map_mul, f.map_pow]
  rw [hSlope, hIntercept]
  ring

private theorem projectiveInfinityPairNeighborhoodThirdN_map_eq_zero
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairNeighborhoodRing W →+* A)
    (hE : f (projectiveInfinityPairNeighborhoodThirdE W) = 0)
    (hD : f (projectiveInfinityPairNeighborhoodThirdD W) = 1)
    (hX₁ : f (projectiveInfinityPairNeighborhoodX₁ W) = 0)
    (hX₂ : f (projectiveInfinityPairNeighborhoodX₂ W) = 0) :
    f (projectiveInfinityPairNeighborhoodThirdN W) = 0 := by
  rw [projectiveInfinityPairNeighborhoodThirdN,
    f.map_sub, f.map_mul, f.map_add, hE, hD, hX₁, hX₂]
  ring

private theorem projectiveInfinityPairNeighborhoodThirdM_map_eq_zero
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairNeighborhoodRing W →+* A)
    (hSlope : f (projectiveInfinityPairNeighborhoodSlope W) = 0)
    (hN : f (projectiveInfinityPairNeighborhoodThirdN W) = 0)
    (hIntercept : f (projectiveInfinityPairNeighborhoodIntercept W) = 0)
    (hD : f (projectiveInfinityPairNeighborhoodThirdD W) = 1) :
    f (projectiveInfinityPairNeighborhoodThirdM W) = 0 := by
  rw [projectiveInfinityPairNeighborhoodThirdM,
    f.map_add, f.map_mul, f.map_mul, hSlope, hN, hIntercept, hD]
  ring

private theorem
    projectiveInfinityPairNeighborhoodAdditionOutputY_map_eq_neg_one
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairNeighborhoodRing W →+* A)
    (hD : f (projectiveInfinityPairNeighborhoodThirdD W) = 1)
    (hN : f (projectiveInfinityPairNeighborhoodThirdN W) = 0)
    (hM : f (projectiveInfinityPairNeighborhoodThirdM W) = 0) :
    f (projectiveInfinityPairNeighborhoodAdditionCoordinates W
      (1 : Fin 3)) = -1 := by
  change f (-projectiveInfinityPairNeighborhoodThirdD W -
    (projectiveInfinityPairNeighborhoodMappedCurve W).a₁ *
      projectiveInfinityPairNeighborhoodThirdN W -
    (projectiveInfinityPairNeighborhoodMappedCurve W).a₃ *
      projectiveInfinityPairNeighborhoodThirdM W) = -1
  rw [f.map_sub, f.map_sub, f.map_neg, f.map_mul, f.map_mul,
    hD, hN, hM]
  ring

private theorem projectiveInfinityPairNeighborhoodAdditionOutputY_not_mem
    (W : WeierstrassCurve K)
    (s : PrimeSpectrum (projectiveInfinityPairNeighborhoodRing W))
    (hX₁ : projectiveInfinityPairX₁ W ∈
      (PrimeSpectrum.comap
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)) s).asIdeal)
    (hZ₁ : projectiveInfinityPairZ₁ W ∈
      (PrimeSpectrum.comap
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)) s).asIdeal)
    (hX₂ : projectiveInfinityPairX₂ W ∈
      (PrimeSpectrum.comap
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)) s).asIdeal)
    (hZ₂ : projectiveInfinityPairZ₂ W ∈
      (PrimeSpectrum.comap
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)) s).asIdeal) :
    projectiveInfinityPairNeighborhoodAdditionCoordinates W
      (1 : Fin 3) ∉ s.asIdeal := by
  let R := projectiveInfinityPairCoordinateRing W
  let S := projectiveInfinityPairNeighborhoodRing W
  let Q := S ⧸ s.asIdeal
  letI : CommRing Q := Ideal.Quotient.commRing s.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime s.asIdeal).mpr inferInstance
  let qS : S →+* Q := Ideal.Quotient.mk s.asIdeal
  let g : R →+* Q := qS.comp (algebraMap R S)
  have hgX₁ : g (projectiveInfinityPairX₁ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hX₁
  have hgZ₁ : g (projectiveInfinityPairZ₁ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hZ₁
  have hgX₂ : g (projectiveInfinityPairX₂ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hX₂
  have hgZ₂ : g (projectiveInfinityPairZ₂ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hZ₂
  have hqSX₁ : qS (projectiveInfinityPairNeighborhoodX₁ W) = 0 :=
    hgX₁
  have hqSZ₁ : qS (projectiveInfinityPairNeighborhoodZ₁ W) = 0 :=
    hgZ₁
  have hqSX₂ : qS (projectiveInfinityPairNeighborhoodX₂ W) = 0 :=
    hgX₂
  have hqSZ₂ : qS (projectiveInfinityPairNeighborhoodZ₂ W) = 0 :=
    hgZ₂
  have hqSA : qS (projectiveInfinityPairNeighborhoodA12 W) = 0 := by
    change g (projectiveInfinityPairAdditionA12 W) = 0
    exact projectiveInfinityPairAdditionA12_map_eq_zero_again
      W g hgX₁ hgX₂ hgZ₂
  have hqSSlope :
      qS (projectiveInfinityPairNeighborhoodSlope W) = 0 := by
    exact projectiveInfinityPairNeighborhoodSlope_map_eq_zero W qS hqSA
  have hqSIntercept :
      qS (projectiveInfinityPairNeighborhoodIntercept W) = 0 := by
    exact projectiveInfinityPairNeighborhoodIntercept_map_eq_zero
      W qS hqSZ₁ hqSSlope hqSX₁
  have hqSThirdD :
      qS (projectiveInfinityPairNeighborhoodThirdD W) = 1 := by
    exact projectiveInfinityPairNeighborhoodThirdD_map_eq_one
      W qS hqSSlope
  have hqSThirdE :
      qS (projectiveInfinityPairNeighborhoodThirdE W) = 0 := by
    exact projectiveInfinityPairNeighborhoodThirdE_map_eq_zero
      W qS hqSSlope hqSIntercept
  have hqSThirdN :
      qS (projectiveInfinityPairNeighborhoodThirdN W) = 0 := by
    exact projectiveInfinityPairNeighborhoodThirdN_map_eq_zero
      W qS hqSThirdE hqSThirdD hqSX₁ hqSX₂
  have hqSThirdM :
      qS (projectiveInfinityPairNeighborhoodThirdM W) = 0 := by
    exact projectiveInfinityPairNeighborhoodThirdM_map_eq_zero
      W qS hqSSlope hqSThirdN hqSIntercept hqSThirdD
  have hqSOutputY : qS
      (projectiveInfinityPairNeighborhoodAdditionCoordinates W
        (1 : Fin 3)) = -1 := by
    exact projectiveInfinityPairNeighborhoodAdditionOutputY_map_eq_neg_one
      W qS hqSThirdD hqSThirdN hqSThirdM
  intro h
  have hzero : qS
      (projectiveInfinityPairNeighborhoodAdditionCoordinates W
        (1 : Fin 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h
  exact neg_ne_zero.mpr one_ne_zero (hqSOutputY.symm.trans hzero)

private theorem projectiveInfinityPairOriginAdditionOpenAffine_mem_of_residual
    (W : WeierstrassCurve K)
    (p : PrimeSpectrum (projectiveInfinityPairCoordinateRing W))
    (hZZ : projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W ∈
      p.asIdeal)
    (hAddZ : projectivePairChartAdditionCoordinates W (false, false)
      (2 : Fin 3) ∈ p.asIdeal) :
    p ∈ (projectiveInfinityPairOriginAdditionOpenAffine W).opensRange := by
  let R := projectiveInfinityPairCoordinateRing W
  let S := projectiveInfinityPairNeighborhoodRing W
  rcases projectiveInfinityPair_coordinates_mem_of_product_and_addZ_mem
    W p hZZ hAddZ with ⟨hX₁, hZ₁, hX₂, hZ₂⟩
  let Q₀ := R ⧸ p.asIdeal
  letI : CommRing Q₀ := Ideal.Quotient.commRing p.asIdeal
  letI : IsDomain Q₀ :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let q : R →+* Q₀ := Ideal.Quotient.mk p.asIdeal
  have hqX₁ : q (projectiveInfinityPairX₁ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hX₁
  have hqZ₁ : q (projectiveInfinityPairZ₁ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hZ₁
  have hqX₂ : q (projectiveInfinityPairX₂ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hX₂
  have hqZ₂ : q (projectiveInfinityPairZ₂ W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hZ₂
  have hqB : q (projectiveInfinityPairAdditionB12 W) = 1 := by
    exact projectiveInfinityPairAdditionB12_map_eq_one_again
      W q hqX₁ hqZ₁ hqZ₂
  have hB : projectiveInfinityPairAdditionB12 W ∉ p.asIdeal := by
    intro h
    have hzero : q (projectiveInfinityPairAdditionB12 W) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact one_ne_zero (hqB.symm.trans hzero)
  have hpRange : p ∈ Set.range
      (PrimeSpectrum.comap
        (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S
      (projectiveInfinityPairAdditionB12 W)]
    exact hB
  rcases hpRange with ⟨s, hs⟩
  have hX₁s : projectiveInfinityPairX₁ W ∈
      (PrimeSpectrum.comap (algebraMap R S) s).asIdeal := by
    rw [hs]
    exact hX₁
  have hZ₁s : projectiveInfinityPairZ₁ W ∈
      (PrimeSpectrum.comap (algebraMap R S) s).asIdeal := by
    rw [hs]
    exact hZ₁
  have hX₂s : projectiveInfinityPairX₂ W ∈
      (PrimeSpectrum.comap (algebraMap R S) s).asIdeal := by
    rw [hs]
    exact hX₂
  have hZ₂s : projectiveInfinityPairZ₂ W ∈
      (PrimeSpectrum.comap (algebraMap R S) s).asIdeal := by
    rw [hs]
    exact hZ₂
  have hOutputY :=
    projectiveInfinityPairNeighborhoodAdditionOutputY_not_mem
      W s hX₁s hZ₁s hX₂s hZ₂s
  let y : S := projectiveInfinityPairNeighborhoodAdditionCoordinates W
    (1 : Fin 3)
  let T := Localization.Away y
  letI : Algebra S T := inferInstance
  letI : IsLocalization.Away y T := inferInstance
  have hy : y ∉ s.asIdeal := hOutputY
  have hsRange : s ∈ Set.range
      (PrimeSpectrum.comap (algebraMap S T)) := by
    have hrange : Set.range (PrimeSpectrum.comap (algebraMap S T)) =
        PrimeSpectrum.basicOpen y :=
      PrimeSpectrum.localization_away_comap_range T y
    exact hrange.symm ▸ hy
  rcases hsRange with ⟨t, ht⟩
  change p ∈ Set.range (projectiveInfinityPairOriginAdditionOpenAffine W)
  refine ⟨t, ?_⟩
  rw [projectiveInfinityPairOriginAdditionOpenAffine_eq]
  change Spec.map (CommRingCat.ofHom (algebraMap R S))
      (PrimeSpectrum.comap
        (algebraMap S T) t) = p
  rw [ht]
  exact hs

/-! ## The resulting affine and scheme open covers -/

/-- The three actual addition sources cover the affine presentation of the
infinity pair chart. -/
theorem projectiveInfinityPairActualAdditionOpens_cover
    (W : WeierstrassCurve K) :
    (projectivePairDoubleOverlapToInfinityPairAffine W).opensRange ⊔
      ((projectiveInfinityPairOriginAdditionOpenAffine W).opensRange ⊔
        (projectiveInfinityPairSecantZOpenAffine W).opensRange) = ⊤ := by
  apply top_unique
  intro p _
  rw [projectivePairDoubleOverlapToInfinityPairAffine_opensRange,
    projectiveInfinityPairSecantZOpenAffine_opensRange]
  change projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W ∉
      p.asIdeal ∨
    p ∈ (projectiveInfinityPairOriginAdditionOpenAffine W).opensRange ∨
    projectivePairChartAdditionCoordinates W (false, false)
      (2 : Fin 3) ∉ p.asIdeal
  by_cases hZZ : projectiveInfinityPairZ₁ W *
      projectiveInfinityPairZ₂ W ∈ p.asIdeal
  · by_cases hAddZ : projectivePairChartAdditionCoordinates W
        (false, false) (2 : Fin 3) ∈ p.asIdeal
    · exact Or.inr (Or.inl
        (projectiveInfinityPairOriginAdditionOpenAffine_mem_of_residual
          W p hZZ hAddZ))
    · exact Or.inr (Or.inr hAddZ)
  · exact Or.inl hZZ

/-- Labels for the three genuine addition sources on the infinity pair. -/
inductive ProjectiveInfinityPairAdditionCoverIndex
  | doubleStandard
  | originNeighborhood
  | secantZ
  deriving DecidableEq

/-- Source scheme selected by an infinity-pair addition-cover label. -/
abbrev projectiveInfinityPairAdditionCoverSource
    (W : WeierstrassCurve K) :
    ProjectiveInfinityPairAdditionCoverIndex → Scheme
  | .doubleStandard => projectivePairDoubleChartOverlapScheme W
  | .originNeighborhood =>
      Spec (.of (projectiveInfinityPairNeighborhoodAdditionOutputRing W))
  | .secantZ =>
      Spec (.of
        (projectivePairChartAdditionOutputRing W (false, false) true))

/-- Map selected by an infinity-pair addition-cover label. -/
noncomputable def projectiveInfinityPairAdditionCoverMap
    (W : WeierstrassCurve K) :
    (i : ProjectiveInfinityPairAdditionCoverIndex) →
      projectiveInfinityPairAdditionCoverSource W i ⟶
        projectivePairChartScheme W (false, false)
  | .doubleStandard => projectivePairDoubleOverlapToInfinityPair W
  | .originNeighborhood => projectiveInfinityPairOriginAdditionOpen W
  | .secantZ =>
      projectivePairChartAdditionOutputOpen W (false, false) true

instance projectiveInfinityPairAdditionCoverMap_isOpenImmersion
    (W : WeierstrassCurve K)
    (i : ProjectiveInfinityPairAdditionCoverIndex) :
    IsOpenImmersion (projectiveInfinityPairAdditionCoverMap W i) := by
  cases i <;> dsimp [projectiveInfinityPairAdditionCoverMap] <;>
    infer_instance

/-- The double-standard, genuine origin-neighborhood, and secant-`Z` sources
form an actual open cover of the infinity-by-infinity pair chart. -/
noncomputable def projectiveInfinityPairAdditionOpenCover
    (W : WeierstrassCurve K) :
    (projectivePairChartScheme W (false, false)).OpenCover :=
  Scheme.Cover.mkOfCovers
    ProjectiveInfinityPairAdditionCoverIndex
    (projectiveInfinityPairAdditionCoverSource W)
    (projectiveInfinityPairAdditionCoverMap W) (by
      intro x
      let e : projectivePairChartScheme W (false, false) ≅
          Spec (.of (projectiveInfinityPairCoordinateRing W)) :=
        projectivePairChartIsoSpecTensor W (false, false)
      have hx : e.hom x ∈ (⊤ :
          (Spec (.of (projectiveInfinityPairCoordinateRing W))).Opens) :=
        trivial
      rw [← projectiveInfinityPairActualAdditionOpens_cover W] at hx
      rcases hx with hx | hx | hx
      · change e.hom x ∈ Set.range
          (projectivePairDoubleOverlapToInfinityPairAffine W) at hx
        rcases hx with ⟨y, hy⟩
        refine ⟨ProjectiveInfinityPairAdditionCoverIndex.doubleStandard,
          y, ?_⟩
        change projectivePairDoubleOverlapToInfinityPair W y = x
        apply e.hom.homeomorph.injective
        simpa [projectivePairDoubleOverlapToInfinityPairAffine,
          Scheme.Hom.comp_apply] using hy
      · change e.hom x ∈ Set.range
          (projectiveInfinityPairOriginAdditionOpenAffine W) at hx
        rcases hx with ⟨y, hy⟩
        refine ⟨ProjectiveInfinityPairAdditionCoverIndex.originNeighborhood,
          y, ?_⟩
        change projectiveInfinityPairOriginAdditionOpen W y = x
        apply e.hom.homeomorph.injective
        simpa [projectiveInfinityPairOriginAdditionOpenAffine,
          Scheme.Hom.comp_apply] using hy
      · change e.hom x ∈ Set.range
          (projectiveInfinityPairSecantZOpenAffine W) at hx
        rcases hx with ⟨y, hy⟩
        refine ⟨ProjectiveInfinityPairAdditionCoverIndex.secantZ,
          y, ?_⟩
        change projectivePairChartAdditionOutputOpen W
          (false, false) true y = x
        apply e.hom.homeomorph.injective
        simpa [projectiveInfinityPairSecantZOpenAffine,
          Scheme.Hom.comp_apply] using hy)

/-- The genuine addition morphism selected on each member of the
infinity-pair addition cover.  The double-standard member transports the
checked standard-pair law; the other two members use the regular and secant
formulas already constructed on their exact source rings. -/
noncomputable def projectiveInfinityPairAdditionCoverMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (i : ProjectiveInfinityPairAdditionCoverIndex) →
      projectiveInfinityPairAdditionCoverSource W i ⟶ scheme W
  | .doubleStandard =>
      projectivePairDoubleOverlapToStandardPair W ≫
        standardPairAdditionMorphism W
  | .originNeighborhood => projectiveInfinityPairOriginAdditionMorphism W
  | .secantZ =>
      projectivePairChartAdditionOutputMorphism W (false, false) true

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
