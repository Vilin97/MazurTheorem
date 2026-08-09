/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, AINTLIB ModularCurves contributors,
  OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveChartTransition
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Explicit field points of projective Weierstrass models

For an elliptic Weierstrass curve, this file identifies the field-valued points of its
constructed projective model with Mathlib's affine Weierstrass points.  Points in the
`Z`-chart are read through the two dehomogenized coordinates; the unique point outside
that chart is the constructed section `[0 : 1 : 0]`, which maps to the group identity.

The point dichotomy and explicit equivalence are selectively adapted from AINTLIB's
`projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean` at commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, exact source blob
`0cea4fbbcd8f0976b8cb0949755ecacec6e58b26` (Chris Birkbeck, Apache-2.0).
No choice-normalized wrapper, smoothness result, group law, or `Over` equivalence is
ported here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdeal HomogeneousLocalization

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- A field-valued model point lies in the affine `Z = X₂` chart. -/
abbrev InZChart (W : WeierstrassCurve R) {K : Type u} [CommRing K] [Algebra R K]
    (g : SpecPoints (model W) (projection W) K) : Prop :=
  ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
      ((quotientGradingHom (ideal W)) (MvPolynomial.X 2)))),
    h ≫ Proj.awayι (quotientGrading (ideal W)) _
      (coordinateClass_mem_degreeOne W 2) one_pos = g.1

private theorem infinity_eval_polynomial (W : WeierstrassCurve R) :
    MvPolynomial.eval ![0, 1, 0] W.toProjective.polynomial = 0 := by
  change W.toProjective.Equation ![0, 1, 0]
  exact W.toProjective.equation_zero

/-- The constructed section at infinity `[0 : 1 : 0]` for a generic projective
Weierstrass model. -/
noncomputable def infinitySection (W : WeierstrassCurve R) :
    Spec (.of R) ⟶ model W :=
  normalizedSection W ![0, 1, 0] (infinity_eval_polynomial W) 1 (by simp)

@[reassoc (attr := simp)]
theorem infinitySection_projection (W : WeierstrassCurve R) :
    infinitySection W ≫ projection W = 𝟙 _ :=
  normalizedSection_projection W ![0, 1, 0]
    (infinity_eval_polynomial W) 1 (by simp)

/-- On the universal Tate family, the generic infinity section is the already
constructed zero section. -/
theorem infinitySection_tateCurveLocOver (A : CommRingCat.{u}) :
    infinitySection (tateCurveLocOver A) = zeroSection A := by
  rfl

/-- The `K`-point obtained from the constructed infinity section. -/
noncomputable def infinityPoint (W : WeierstrassCurve R) (K : Type u)
    [Field K] [Algebra R K] : SpecPoints (model W) (projection W) K :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ infinitySection W, by
    rw [Category.assoc, infinitySection_projection, Category.comp_id]⟩

private theorem infinitySection_preimage_zChart (W : WeierstrassCurve R) :
    infinitySection W ⁻¹ᵁ (Proj.basicOpen (quotientGrading (ideal W))
      ((quotientGradingHom (ideal W)) (MvPolynomial.X 2))) = ⊥ := by
  unfold infinitySection normalizedSection
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (hn := one_pos)
    (hr := coordinateClass_mem_degreeOne W 2)]
  have heval : coordinateEval W ![0, 1, 0] (infinity_eval_polynomial W)
      ((quotientGradingHom (ideal W)) (MvPolynomial.X 2)) = 0 := by
    rw [quotientGradingHom_apply, coordinateEval_mk]
    simp
  have hglobal : ((Scheme.ΓSpecIso (.of R)).inv.hom.comp
      (coordinateEval W ![0, 1, 0] (infinity_eval_polynomial W)))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X 2)) = 0 := by
    rw [RingHom.comp_apply, heval, map_zero]
  rw [hglobal]
  simp

/-- The constructed infinity point is outside the affine `Z`-chart. -/
theorem infinityPoint_not_inZ (W : WeierstrassCurve R) (K : Type u)
    [Field K] [Algebra R K] : ¬ InZChart W (infinityPoint W K) := by
  rintro ⟨h, hfac⟩
  have hpoint : (infinityPoint W K).1 default =
      (Proj.awayι (quotientGrading (ideal W)) _
        (coordinateClass_mem_degreeOne W 2) one_pos) (h default) := by
    rw [← hfac]
    exact Scheme.Hom.comp_apply _ _ _
  have hrange : Set.range ⇑(Proj.awayι (quotientGrading (ideal W)) _
      (coordinateClass_mem_degreeOne W 2) one_pos) =
      (Proj.basicOpen (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X 2)) :
          Set (Proj (quotientGrading (ideal W)))) := by
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  have hin : (infinityPoint W K).1 default ∈
      (Proj.basicOpen (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X 2)) :
          Set (Proj (quotientGrading (ideal W)))) := by
    rw [hpoint, ← hrange]
    exact ⟨h default, rfl⟩
  change (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
    infinitySection W) default ∈ _ at hin
  rw [Scheme.Hom.comp_apply] at hin
  have hpre : Spec.map (CommRingCat.ofHom (algebraMap R K)) default ∈
      (infinitySection W ⁻¹ᵁ Proj.basicOpen (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X 2))) := hin
  rw [infinitySection_preimage_zChart] at hpre
  exact hpre

private theorem aeval_dehomog_two (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 2} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) =
      v ⟨1, by decide⟩ ^ 2 + algebraMap R K W.a₁ * v ⟨0, by decide⟩ * v ⟨1, by decide⟩
        + algebraMap R K W.a₃ * v ⟨1, by decide⟩
        - (v ⟨0, by decide⟩ ^ 3 + algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2
          + algebraMap R K W.a₄ * v ⟨0, by decide⟩ + algebraMap R K W.a₆) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow]

private def zCoordsEquiv (K : Type u) : ({j : Fin 3 // j ≠ 2} → K) ≃ K × K where
  toFun v := (v ⟨0, by decide⟩, v ⟨1, by decide⟩)
  invFun p j := if j.1 = 0 then p.1 else p.2
  left_inv v := by
    funext j
    rcases j with ⟨j, hj⟩
    fin_cases j
    · simp
    · simp
    · exact absurd rfl hj
  right_inv p := by
    ext <;> simp

private noncomputable def zSolutionsToAffine (W : WeierstrassCurve R)
    (K : Type u) [Field K] [Algebra R K] :
    {v : {j : Fin 3 // j ≠ 2} → K //
      MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) = 0} ≃
    {p : K × K // (W.baseChange K).toAffine.Equation p.1 p.2} :=
  Equiv.subtypeEquiv (zCoordsEquiv K) (fun v => by
    rw [aeval_dehomog_two, WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, zCoordsEquiv, Equiv.coe_fn_mk]
    constructor <;> intro h <;> linear_combination h)

private noncomputable def affinePointSplit (W : WeierstrassCurve R)
    (hell : W.IsElliptic) (K : Type u) [Field K] [Algebra R K] :
    (W.baseChange K).toAffine.Point ≃
      {p : K × K // (W.baseChange K).toAffine.Equation p.1 p.2} ⊕ PUnit.{u + 1} where
  toFun P := match P with
    | .zero => Sum.inr PUnit.unit
    | .some x y h => Sum.inl ⟨(x, y), h.1⟩
  invFun s := match s with
    | .inl p => .some p.1.1 p.1.2 (by
        haveI := hell
        haveI : ((W.baseChange K).toAffine).IsElliptic :=
          inferInstanceAs ((W.map (algebraMap R K)).IsElliptic)
        exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp p.2)
    | .inr _ => .zero
  left_inv P := by cases P <;> rfl
  right_inv s := by rcases s with p | punit <;> rfl

private theorem aeval_dehomog_one (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 1} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial) =
      v ⟨2, by decide⟩ + algebraMap R K W.a₁ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨2, by decide⟩ ^ 2
        - (v ⟨0, by decide⟩ ^ 3
          + algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2 * v ⟨2, by decide⟩
          + algebraMap R K W.a₄ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩ ^ 2
          + algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 3) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 1 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow, one_mul]

private theorem aeval_dehomog_zero (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 0} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial) =
      v ⟨1, by decide⟩ ^ 2 * v ⟨2, by decide⟩
        + algebraMap R K W.a₁ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩ ^ 2
        - (1 + algebraMap R K W.a₂ * v ⟨2, by decide⟩
          + algebraMap R K W.a₄ * v ⟨2, by decide⟩ ^ 2
          + algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 3) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 0 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_one, mul_one, one_pow]

private theorem zero_y_chart_solution (W : WeierstrassCurve R) (K : Type u)
    [Field K] [Algebra R K] :
    MvPolynomial.aeval (fun _ : {j : Fin 3 // j ≠ 1} => (0 : K))
      (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial) = 0 := by
  rw [aeval_dehomog_one]
  simp

private def yZeroSolution (W : WeierstrassCurve R) (K : Type u)
    [Field K] [Algebra R K] :
    {v : {j : Fin 3 // j ≠ 1} → K //
      MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial) = 0} :=
  ⟨fun _ => 0, zero_y_chart_solution W K⟩

private noncomputable def chartInfinityPoint (W : WeierstrassCurve R) (K : Type u)
    [Field K] [Algebra R K] : SpecPoints (model W) (projection W) K :=
  ((chartHomEquiv W 1 K).symm
    ((chartSolutionsEquiv W 1 K).symm (yZeroSolution W K))).1

private theorem chartInfinityPoint_not_inZ (W : WeierstrassCurve R) (K : Type u)
    [Field K] [Algebra R K] : ¬ InZChart W (chartInfinityPoint W K) := by
  intro hfac
  have hne := (chartPointOfHom_factors_iff W 1 2
    ((chartSolutionsEquiv W 1 K).symm (yZeroSolution W K))).mp (by
      simpa only [chartInfinityPoint] using hfac)
  apply hne
  rw [← chartCoordEquiv_mk_X W 1 ⟨2, by decide⟩]
  have hv : ((chartSolutionsEquiv W 1 K)
      ((chartSolutionsEquiv W 1 K).symm (yZeroSolution W K))).1
        ⟨2, by decide⟩ = 0 := by
    rw [Equiv.apply_symm_apply]
    rfl
  exact hv

private theorem eq_chartInfinityPoint_of_not_inZ (W : WeierstrassCurve R)
    (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (model W) (projection W) K) (hg : ¬ InZChart W g) :
    g = chartInfinityPoint W K := by
  obtain ⟨i, h, hfac⟩ := specPoint_factors_through_chart W g.1
  let gi : {g : SpecPoints (model W) (projection W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W i) one_pos = g.1} :=
    ⟨g, ⟨h, hfac⟩⟩
  let φ := chartHomEquiv W i K gi
  have hback : (chartHomEquiv W i K).symm φ = gi := by
    exact (chartHomEquiv W i K).symm_apply_apply gi
  have gproj : ((chartHomEquiv W i K).symm φ).1 = g :=
    congrArg Subtype.val hback
  have hgφ : ¬ InZChart W ((chartHomEquiv W i K).symm φ).1 := by
    intro hZ
    apply hg
    rw [← gproj]
    exact hZ
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hi with rfl | rfl | rfl
  · exfalso
    have hz : φ.1 (chartCoordEquiv W 0 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 0})))) = 0 := by
      rw [chartCoordEquiv_mk_X W 0 ⟨2, by decide⟩]
      by_contra hne
      exact hgφ ((chartPointOfHom_factors_iff W 0 2 φ).mpr hne)
    have hv := ((chartSolutionsEquiv W 0 K) φ).2
    have hcomp : ((chartSolutionsEquiv W 0 K) φ).1 =
        fun j : {j : Fin 3 // j ≠ 0} => φ.1 (chartCoordEquiv W 0
          (Ideal.Quotient.mk _ (MvPolynomial.X j))) := rfl
    rw [hcomp, aeval_dehomog_zero] at hv
    simp only [hz, mul_zero, add_zero, zero_add] at hv
    simp at hv
  · have hz : φ.1 (chartCoordEquiv W 1 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 1})))) = 0 := by
      rw [chartCoordEquiv_mk_X W 1 ⟨2, by decide⟩]
      by_contra hne
      exact hgφ ((chartPointOfHom_factors_iff W 1 2 φ).mpr hne)
    have hv := ((chartSolutionsEquiv W 1 K) φ).2
    have hcomp : ((chartSolutionsEquiv W 1 K) φ).1 =
        fun j : {j : Fin 3 // j ≠ 1} => φ.1 (chartCoordEquiv W 1
          (Ideal.Quotient.mk _ (MvPolynomial.X j))) := rfl
    rw [hcomp, aeval_dehomog_one, hz] at hv
    have hu3 : φ.1 (chartCoordEquiv W 1 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 1})))) ^ 3 = 0 := by
      linear_combination -hv
    have hu : φ.1 (chartCoordEquiv W 1 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 1})))) = 0 :=
      pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hu3
    have hsol : (chartSolutionsEquiv W 1 K) φ = yZeroSolution W K := by
      refine Subtype.ext ?_
      rw [hcomp]
      funext j
      rcases j with ⟨j, hj⟩
      fin_cases j
      · exact hu
      · exact absurd rfl hj
      · exact hz
    have hφ0 : φ = (chartSolutionsEquiv W 1 K).symm (yZeroSolution W K) := by
      rw [← hsol, Equiv.symm_apply_apply]
    calc
      g = ((chartHomEquiv W 1 K).symm φ).1 := gproj.symm
      _ = chartInfinityPoint W K := by rw [hφ0]; rfl
  · exact (hg ⟨h, hfac⟩).elim

/-- Every point outside the `Z`-chart is the point obtained from the constructed
infinity section. -/
theorem eq_infinityPoint_of_not_inZ (W : WeierstrassCurve R) (K : Type u)
    [Field K] [Algebra R K] (g : SpecPoints (model W) (projection W) K)
    (hg : ¬ InZChart W g) : g = infinityPoint W K :=
  (eq_chartInfinityPoint_of_not_inZ W K g hg).trans
    (eq_chartInfinityPoint_of_not_inZ W K (infinityPoint W K)
      (infinityPoint_not_inZ W K)).symm

/-- The explicit pointed equivalence between field-valued model points and affine
Weierstrass points. -/
noncomputable def modelPointsEquivAffine (W : WeierstrassCurve R)
    (hell : W.IsElliptic) (K : Type u) [Field K] [Algebra R K] :
    SpecPoints (model W) (projection W) K ≃ (W.baseChange K).toAffine.Point := by
  classical
  exact (Equiv.sumCompl (InZChart W (K := K))).symm.trans
    ((((chartHomEquiv W 2 K).trans ((chartSolutionsEquiv W 2 K).trans
        (zSolutionsToAffine W K))).sumCongr
      ({ toFun := fun _ => PUnit.unit
         invFun := fun _ => ⟨infinityPoint W K, infinityPoint_not_inZ W K⟩
         left_inv := fun g =>
           Subtype.ext (eq_infinityPoint_of_not_inZ W K g.1 g.2).symm
         right_inv := fun _ => rfl } :
        {g : SpecPoints (model W) (projection W) K // ¬ InZChart W g} ≃
          PUnit.{u + 1})).trans
      (affinePointSplit W hell K).symm)

/-- Every off-`Z` point maps to the affine point at infinity. -/
theorem modelPointsEquivAffine_infinity (W : WeierstrassCurve R)
    (hell : W.IsElliptic) (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (model W) (projection W) K) (hg : ¬ InZChart W g) :
    modelPointsEquivAffine W hell K g = 0 := by
  classical
  unfold modelPointsEquivAffine
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hg,
    Equiv.sumCongr_apply, Sum.map_inr]
  rfl

/-- The point supplied by the constructed infinity section maps to zero. -/
theorem modelPointsEquivAffine_zero (W : WeierstrassCurve R)
    (hell : W.IsElliptic) (K : Type u) [Field K] [Algebra R K] :
    modelPointsEquivAffine W hell K (infinityPoint W K) = 0 :=
  modelPointsEquivAffine_infinity W hell K _ (infinityPoint_not_inZ W K)

/-- A `Z`-chart point maps to the affine point given by its two dehomogenized
coordinates. -/
theorem modelPointsEquivAffine_some (W : WeierstrassCurve R)
    (hell : W.IsElliptic) (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (model W) (projection W) K) (hZ : InZChart W g)
    (x y : K) (hxy : (W.baseChange K).toAffine.Nonsingular x y)
    (hx : x = (chartSolutionsEquiv W 2 K
      (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨0, by decide⟩)
    (hy : y = (chartSolutionsEquiv W 2 K
      (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨1, by decide⟩) :
    modelPointsEquivAffine W hell K g =
      WeierstrassCurve.Affine.Point.some x y hxy := by
  classical
  subst hx hy
  unfold modelPointsEquivAffine
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hZ,
    Equiv.sumCongr_apply, Sum.map_inl]
  rfl

/-- The coordinates read from a `Z`-chart point satisfy the nonsingularity condition. -/
theorem nonsingular_chartSolution (W : WeierstrassCurve R) (hell : W.IsElliptic)
    {K : Type u} [Field K] [Algebra R K]
    (g : SpecPoints (model W) (projection W) K) (hZ : InZChart W g) :
    (W.baseChange K).toAffine.Nonsingular
      ((chartSolutionsEquiv W 2 K
        (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨0, by decide⟩)
      ((chartSolutionsEquiv W 2 K
        (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨1, by decide⟩) := by
  haveI := hell
  haveI : ((W.baseChange K).toAffine).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap R K)).IsElliptic)
  exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (zSolutionsToAffine W K
      (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩))).2

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
