/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, AINTLIB ModularCurves contributors,
  OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveChartPoints

/-!
# Coordinate readout on overlaps of projective Weierstrass charts

The coordinate `Xⱼ/Xᵢ` on chart `i` is the canonical homogeneous-localization
element.  Consequently a point represented in chart `i` also factors through chart
`j` exactly when that element has nonzero value.

The declarations are adapted from AINTLIB's
`projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean` at commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, exact source blob
`0cea4fbbcd8f0976b8cb0949755ecacec6e58b26` (Chris Birkbeck, Apache-2.0).
The source's backward-definitional-equality option is not retained: factorization and
nonvanishing are related through two explicitly typed basic-open membership lemmas,
with quotient-coordinate representatives normalized explicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdeal HomogeneousLocalization

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

private theorem mem_basicOpen_comap_iff_ne_zero
    {A K : Type*} [CommRing A] [Field K]
    (φ : A →+* K) (a : A) (x : PrimeSpectrum K) :
    PrimeSpectrum.comap φ x ∈ PrimeSpectrum.basicOpen a ↔ φ a ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hx : x.asIdeal = ⊥ :=
    (IsSimpleOrder.eq_bot_or_eq_top x.asIdeal).resolve_right x.2.ne_top
  rw [hx, Ideal.mem_bot]

/-- The chart coordinate `Xⱼ/Xᵢ` is the canonical localization element associated to
the two homogeneous coordinate classes. -/
theorem chartCoordEquiv_mk_X (W : WeierstrassCurve R) (i : Fin 3)
    (j : {j : Fin 3 // j ≠ i}) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial.X j)) =
      Away.isLocalizationElem
        (coordinateClass_mem_degreeOne W i)
        (coordinateClass_mem_degreeOne W j.1) := by
  rw [chartCoordEquiv_mk]
  have hhomogenize : MvPolynomial.homogenizeAt R i (MvPolynomial.X j) =
      MvPolynomial.awayVar R i j :=
    MvPolynomial.eval₂Hom_X' _ _ _
  rw [hhomogenize]
  apply val_injective
  rw [MvPolynomial.awayVar, Away.map_mk, Away.val_mk, Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by ring⟩

private theorem point_factors_through_chart_iff_mem_basicOpen
    (W : WeierstrassCurve R) (j : Fin 3) {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ model W) :
    (∃ h' : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X j)))),
      h' ≫ Proj.awayι (quotientGrading (ideal W)) _
        (coordinateClass_mem_degreeOne W j) one_pos = g) ↔
      g default ∈ (Proj.basicOpen (quotientGrading (ideal W))
        (Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X j)) :
          Set (Proj (quotientGrading (ideal W)))) := by
  constructor
  · rintro ⟨h', hfac⟩
    have hpoint : g default =
        (Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W j) one_pos) (h' default) := by
      rw [← hfac]
      exact Scheme.Hom.comp_apply _ _ _
    rw [hpoint]
    have hrange : Set.range ⇑(Proj.awayι (quotientGrading (ideal W)) _
        (coordinateClass_mem_degreeOne W j) one_pos) =
        (Proj.basicOpen (quotientGrading (ideal W))
          (Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X j)) :
            Set (Proj (quotientGrading (ideal W)))) := by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
      rfl
    rw [← hrange]
    exact ⟨h' default, rfl⟩
  · intro hmem
    have hrange : Set.range ⇑g ⊆
        Set.range ⇑(Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W j) one_pos) := by
      rw [show Set.range ⇑(Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W j) one_pos) =
          (Proj.basicOpen (quotientGrading (ideal W))
            (Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X j)) :
              Set (Proj (quotientGrading (ideal W)))) from by
        rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
        rfl]
      rw [show Set.range ⇑g = {g default} from Set.range_unique]
      rw [Set.singleton_subset_iff]
      exact hmem
    exact ⟨IsOpenImmersion.lift _ _ hrange,
      IsOpenImmersion.lift_fac _ _ hrange⟩

private theorem chartHomEquiv_symm_mem_basicOpen_iff
    (W : WeierstrassCurve R) (i j : Fin 3)
    {K : Type u} [Field K] [Algebra R K]
    (φ : {φ : Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (ideal W) 0))
          (Away (quotientGrading (ideal W))
            ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0))) =
        algebraMap R K}) :
    ((chartHomEquiv W i K).symm φ).1.1 default ∈
        (Proj.basicOpen (quotientGrading (ideal W))
          (Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X j)) :
            Set (Proj (quotientGrading (ideal W)))) ↔
      φ.1 (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne W i)
        (coordinateClass_mem_degreeOne W j)) ≠ 0 := by
  have hread : chartHomEquiv W i K ((chartHomEquiv W i K).symm φ) = φ :=
    (chartHomEquiv W i K).apply_symm_apply φ
  have hfac := chartHomEquiv_specMap_factors W i ((chartHomEquiv W i K).symm φ)
  rw [hread] at hfac
  have hbase : ((chartHomEquiv W i K).symm φ).1.1 default =
      (Proj.awayι (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i))
        (coordinateClass_mem_degreeOne W i) one_pos)
        ((Spec.map (CommRingCat.ofHom φ.1)) default) := by
    rw [← hfac]
    exact Scheme.Hom.comp_apply _ _ _
  rw [hbase]
  have hcoord : (quotientGradingHom (ideal W)) (MvPolynomial.X j) =
      Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X j) :=
    quotientGradingHom_apply (ideal W) _
  rw [← hcoord]
  change (Spec.map (CommRingCat.ofHom φ.1)) default ∈
      (Proj.awayι (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i))
        (coordinateClass_mem_degreeOne W i) one_pos ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X j))) ↔ _
  rw [Proj.awayι_preimage_basicOpen (quotientGrading (ideal W))
    (coordinateClass_mem_degreeOne W i) one_pos
    (coordinateClass_mem_degreeOne W j) one_pos]
  let xK : PrimeSpectrum K := default
  have hpoint :
      (Spec.map (CommRingCat.ofHom φ.1)) (default : Spec (.of K)) =
        PrimeSpectrum.comap φ.1 xK := by
    rw [Spec.map_apply, CommRingCat.hom_ofHom]
    congr 1
    exact Subsingleton.elim _ _
  rw [hpoint]
  exact mem_basicOpen_comap_iff_ne_zero φ.1
    (Away.isLocalizationElem
      (coordinateClass_mem_degreeOne W i)
      (coordinateClass_mem_degreeOne W j)) xK

/-- A point represented in chart `i` also factors through chart `j` exactly when its
`j`-th homogeneous localization coordinate is nonzero. -/
theorem chartPointOfHom_factors_iff (W : WeierstrassCurve R) (i j : Fin 3)
    {K : Type u} [Field K] [Algebra R K]
    (φ : {φ : Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (ideal W) 0))
          (Away (quotientGrading (ideal W))
            ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0))) =
        algebraMap R K}) :
    (∃ h' : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X j)))),
      h' ≫ Proj.awayι (quotientGrading (ideal W)) _
        (coordinateClass_mem_degreeOne W j) one_pos =
        ((chartHomEquiv W i K).symm φ).1.1) ↔
      φ.1 (Away.isLocalizationElem
        (coordinateClass_mem_degreeOne W i)
        (coordinateClass_mem_degreeOne W j)) ≠ 0 :=
  (point_factors_through_chart_iff_mem_basicOpen W j
    ((chartHomEquiv W i K).symm φ).1.1).trans
      (chartHomEquiv_symm_mem_basicOpen_iff W i j φ)

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
