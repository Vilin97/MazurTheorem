/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductAdditionCoordinates

/-!
# Output charts for homogeneous Weierstrass formulas

This file turns a normalized homogeneous solution of a mapped Weierstrass
equation into a homomorphism from either quotient coordinate chart.  It then
applies that interface after localizing a projective-pair chart at one output
coordinate of the checked secant triple.

The resulting morphisms are honest addition formulas on principal opens of
the affine tensor-product presentations.  Covering the base loci and comparing
the formulas on intersections remain separate downstream steps.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Evaluate the polynomial presentation of the `i`th projective coordinate
chart at a homogeneous point whose `i`th coordinate is normalized to one. -/
noncomputable def coordinateChartEvaluationRingHom
    {A : Type u} [CommRing A] [Algebra K A]
    (i : Fin 3) (P : Fin 3 → A) :
    HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X i) →+* A :=
  (MvPolynomial.eval₂Hom (algebraMap K A)
    ![P (Equiv.swap i 2 1), P (Equiv.swap i 2 0)]).comp
      (coordinateChartPolynomialEquiv i).symm.toRingHom

@[simp]
theorem coordinateChartEvaluationRingHom_constant
    {A : Type u} [CommRing A] [Algebra K A]
    (i : Fin 3) (P : Fin 3 → A) (a : K) :
    coordinateChartEvaluationRingHom i P
        (coordinateChartConstantHom (K := K) i a) = algebraMap K A a := by
  rw [coordinateChartEvaluationRingHom, RingHom.comp_apply]
  have hc : (coordinateChartPolynomialEquiv (K := K) i).symm
      (coordinateChartConstantHom i a) = MvPolynomial.C a := by
    apply (coordinateChartPolynomialEquiv (K := K) i).injective
    simp
  change (MvPolynomial.eval₂Hom (algebraMap K A)
    ![P (Equiv.swap i 2 1), P (Equiv.swap i 2 0)])
      ((coordinateChartPolynomialEquiv (K := K) i).symm
        (coordinateChartConstantHom i a)) = _
  rw [hc]
  simp

private theorem coordinateChartEvaluationRingHom_ratio_self
    {A : Type u} [CommRing A] [Algebra K A]
    (i : Fin 3) (P : Fin 3 → A) (hPi : P i = 1) :
    coordinateChartEvaluationRingHom i P
        (coordinateChartRatio (K := K) i i) = P i := by
  rw [coordinateChartRatio_self (K := K), map_one, hPi]

private theorem coordinateChartEvaluationRingHom_ratio_zero
    {A : Type u} [CommRing A] [Algebra K A]
    (i : Fin 3) (P : Fin 3 → A) :
    coordinateChartEvaluationRingHom i P
        (coordinateChartRatio (K := K) i (Equiv.swap i 2 1)) =
      P (Equiv.swap i 2 1) := by
  rw [coordinateChartEvaluationRingHom, RingHom.comp_apply]
  have hr : (coordinateChartPolynomialEquiv (K := K) i).symm
      (coordinateChartRatio i (Equiv.swap i 2 1)) = MvPolynomial.X 0 := by
    apply (coordinateChartPolynomialEquiv (K := K) i).injective
    simp
  change (MvPolynomial.eval₂Hom (algebraMap K A)
    ![P (Equiv.swap i 2 1), P (Equiv.swap i 2 0)])
      ((coordinateChartPolynomialEquiv (K := K) i).symm
        (coordinateChartRatio i (Equiv.swap i 2 1))) = _
  rw [hr]
  simp

private theorem coordinateChartEvaluationRingHom_ratio_one
    {A : Type u} [CommRing A] [Algebra K A]
    (i : Fin 3) (P : Fin 3 → A) :
    coordinateChartEvaluationRingHom i P
        (coordinateChartRatio (K := K) i (Equiv.swap i 2 0)) =
      P (Equiv.swap i 2 0) := by
  rw [coordinateChartEvaluationRingHom, RingHom.comp_apply]
  have hr : (coordinateChartPolynomialEquiv (K := K) i).symm
      (coordinateChartRatio i (Equiv.swap i 2 0)) = MvPolynomial.X 1 := by
    apply (coordinateChartPolynomialEquiv (K := K) i).injective
    simp
  change (MvPolynomial.eval₂Hom (algebraMap K A)
    ![P (Equiv.swap i 2 1), P (Equiv.swap i 2 0)])
      ((coordinateChartPolynomialEquiv (K := K) i).symm
        (coordinateChartRatio i (Equiv.swap i 2 0))) = _
  rw [hr]
  simp

/-- Evaluation sends every normalized coordinate ratio `X_j / X_i` to the
corresponding coordinate of the normalized point. -/
@[simp]
theorem coordinateChartEvaluationRingHom_ratio
    {A : Type u} [CommRing A] [Algebra K A]
    (i : Fin 3) (P : Fin 3 → A) (hPi : P i = 1) (j : Fin 3) :
    coordinateChartEvaluationRingHom i P
        (coordinateChartRatio (K := K) i j) = P j := by
  fin_cases i
  · fin_cases j
    · exact coordinateChartEvaluationRingHom_ratio_self (K := K) 0 P hPi
    · simpa [Equiv.swap_apply_def] using
        coordinateChartEvaluationRingHom_ratio_zero (K := K) 0 P
    · simpa [Equiv.swap_apply_def] using
        coordinateChartEvaluationRingHom_ratio_one (K := K) 0 P
  · fin_cases j
    · simpa [Equiv.swap_apply_def] using
        coordinateChartEvaluationRingHom_ratio_one (K := K) 1 P
    · exact coordinateChartEvaluationRingHom_ratio_self (K := K) 1 P hPi
    · simpa [Equiv.swap_apply_def] using
        coordinateChartEvaluationRingHom_ratio_zero (K := K) 1 P
  · fin_cases j
    · simpa [Equiv.swap_apply_def] using
        coordinateChartEvaluationRingHom_ratio_one (K := K) 2 P
    · simpa [Equiv.swap_apply_def] using
        coordinateChartEvaluationRingHom_ratio_zero (K := K) 2 P
    · exact coordinateChartEvaluationRingHom_ratio_self (K := K) 2 P hPi

/-- The equation cutting out either covering chart is the homogeneous cubic
evaluated at its normalized coordinate ratios. -/
theorem coveringChartEquation_eq_eval₂Hom
    (W : WeierstrassCurve K) (b : Bool) :
    coveringChartEquation W b =
      MvPolynomial.eval₂Hom
        (coordinateChartConstantHom (coveringCoordinate b))
        (coordinateChartRatio (coveringCoordinate b))
        W.toProjective.polynomial := by
  cases b
  · change infinityLocalizedEquation W =
      MvPolynomial.eval₂ (coordinateChartConstantHom 1)
        (coordinateChartRatio 1) W.toProjective.polynomial
    simpa [infinityLocalizedEquation] using
      (coordinateChartAwayMk_eq_eval₂Hom (K := K) 1
        W.toProjective.polynomial (polynomial_mem_degree_three W))
  · change standardChartEquation W =
      MvPolynomial.eval₂ (coordinateChartConstantHom 2)
        (coordinateChartRatio 2) W.toProjective.polynomial
    simpa [standardChartEquation] using
      (coordinateChartAwayMk_eq_eval₂Hom (K := K) 2
        W.toProjective.polynomial (polynomial_mem_degree_three W))

private theorem eval₂Hom_polynomial_eq_zero_of_equation
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) {P : Fin 3 → A}
    (hP : (W.map (algebraMap K A)).toProjective.Equation P) :
    MvPolynomial.eval₂Hom (algebraMap K A) P
      W.toProjective.polynomial = 0 := by
  rw [WeierstrassCurve.Projective.Equation,
    WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map] at hP
  exact hP

/-- A normalized homogeneous solution of the mapped cubic induces a ring
homomorphism from the corresponding quotient coordinate chart. -/
noncomputable def coveringChartCoordinateRingHomOfNormalizedPoint
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (b : Bool) (P : Fin 3 → A)
    (hP : (W.map (algebraMap K A)).toProjective.Equation P)
    (hPi : P (coveringCoordinate b) = 1) :
    coveringChartCoordinateRing W b →+* A :=
  Ideal.Quotient.lift (coveringChartIdeal W b)
    (coordinateChartEvaluationRingHom (coveringCoordinate b) P) <| by
      intro a ha
      have hker : coveringChartIdeal W b ≤
          RingHom.ker (coordinateChartEvaluationRingHom
            (coveringCoordinate b) P) := by
        rw [coveringChartIdeal]
        apply Ideal.span_le.2
        rw [Set.singleton_subset_iff]
        change coordinateChartEvaluationRingHom (coveringCoordinate b) P
          (coveringChartEquation W b) = 0
        rw [coveringChartEquation_eq_eval₂Hom,
          MvPolynomial.map_eval₂Hom]
        have hc : (coordinateChartEvaluationRingHom
            (coveringCoordinate b) P).comp
              (coordinateChartConstantHom (coveringCoordinate b)) =
            algebraMap K A := by
          ext x
          exact coordinateChartEvaluationRingHom_constant
            (coveringCoordinate b) P x
        have hr : (fun j ↦ coordinateChartEvaluationRingHom
            (coveringCoordinate b) P
              (coordinateChartRatio (K := K) (coveringCoordinate b) j)) = P := by
          funext j
          exact coordinateChartEvaluationRingHom_ratio (K := K)
            (coveringCoordinate b) P hPi j
        rw [hc, hr]
        exact eval₂Hom_polynomial_eq_zero_of_equation W hP
      exact hker ha

@[simp]
theorem coveringChartCoordinateRingHomOfNormalizedPoint_mk
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (b : Bool) (P : Fin 3 → A)
    (hP : (W.map (algebraMap K A)).toProjective.Equation P)
    (hPi : P (coveringCoordinate b) = 1)
    (x : HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X (coveringCoordinate b))) :
    coveringChartCoordinateRingHomOfNormalizedPoint W b P hP hPi
        (Ideal.Quotient.mk (coveringChartIdeal W b) x) =
      coordinateChartEvaluationRingHom (coveringCoordinate b) P x := by
  exact Ideal.Quotient.lift_mk _ _ _

/-- The normalized-point quotient map is a `K`-algebra homomorphism. -/
noncomputable def coveringChartCoordinateRingAlgHomOfNormalizedPoint
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (b : Bool) (P : Fin 3 → A)
    (hP : (W.map (algebraMap K A)).toProjective.Equation P)
    (hPi : P (coveringCoordinate b) = 1) :
    coveringChartCoordinateRing W b →ₐ[K] A where
  __ := coveringChartCoordinateRingHomOfNormalizedPoint W b P hP hPi
  commutes' a := by
    rw [coveringChartCoordinateRing_algebraMap,
      coveringChartStructureRingHom]
    exact coordinateChartEvaluationRingHom_constant
      (coveringCoordinate b) P a

/-- The normalized-point algebra map sends every quotient coordinate ratio
to the selected homogeneous coordinate. -/
@[simp]
theorem coveringChartCoordinateRingAlgHomOfNormalizedPoint_ratio
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (b : Bool) (P : Fin 3 → A)
    (hP : (W.map (algebraMap K A)).toProjective.Equation P)
    (hPi : P (coveringCoordinate b) = 1) (j : Fin 3) :
    coveringChartCoordinateRingAlgHomOfNormalizedPoint W b P hP hPi
        (Ideal.Quotient.mk (coveringChartIdeal W b)
          (coordinateChartRatio (coveringCoordinate b) j)) = P j := by
  exact coordinateChartEvaluationRingHom_ratio
    (coveringCoordinate b) P hPi j

/-! ## Secant output principal opens -/

/-- The coordinate ring obtained by inverting one selected output coordinate
of the universal secant triple. -/
abbrev projectivePairChartAdditionOutputRing
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :=
  Localization.Away
    (projectivePairChartAdditionCoordinates W ij (coveringCoordinate out))

/-- The selected secant output coordinate as a unit in its principal
localization. -/
noncomputable def projectivePairChartAdditionOutputUnit
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    (projectivePairChartAdditionOutputRing W ij out)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (projectivePairChartAdditionCoordinates W ij
      (coveringCoordinate out))).unit

/-- The universal secant triple, mapped to an output-coordinate localization
and normalized by the inverse of the selected coordinate. -/
noncomputable def projectivePairChartAdditionOutputPoint
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    Fin 3 → projectivePairChartAdditionOutputRing W ij out :=
  fun j ↦
    ↑(projectivePairChartAdditionOutputUnit W ij out)⁻¹ *
      algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputRing W ij out)
        (projectivePairChartAdditionCoordinates W ij j)

/-- The selected coordinate of the localized secant output point is one. -/
@[simp]
theorem projectivePairChartAdditionOutputPoint_normalized
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    projectivePairChartAdditionOutputPoint W ij out
      (coveringCoordinate out) = 1 := by
  rw [projectivePairChartAdditionOutputPoint]
  rw [← (IsLocalization.Away.algebraMap_isUnit
    (projectivePairChartAdditionCoordinates W ij
      (coveringCoordinate out))).unit_spec]
  exact Units.inv_mul _

/-- The normalized secant output point satisfies the mapped cubic equation on
its output-coordinate principal localization. -/
theorem projectivePairChartAdditionOutputPoint_equation
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    (W.map (algebraMap K
      (projectivePairChartAdditionOutputRing W ij out))).toProjective.Equation
        (projectivePairChartAdditionOutputPoint W ij out) := by
  let R := projectivePairChartCoordinateRing W ij
  let S := projectivePairChartAdditionOutputRing W ij out
  let f : R →+* S := algebraMap R S
  have hmap : ((projectivePairChartMappedCurve W ij).map f).toProjective.Equation
      (f ∘ projectivePairChartAdditionCoordinates W ij) :=
    (projectivePairChartAdditionCoordinates_equation W ij).map f
  have hscaled :=
    (((projectivePairChartMappedCurve W ij).map f).toProjective.equation_smul
      (f ∘ projectivePairChartAdditionCoordinates W ij)
      (projectivePairChartAdditionOutputUnit W ij out)⁻¹.isUnit).mpr hmap
  have hf : f.comp (algebraMap K R) = algebraMap K S :=
    (IsScalarTower.algebraMap_eq K R S).symm
  rw [projectivePairChartMappedCurve, WeierstrassCurve.map_map, hf] at hscaled
  have hp : (↑(projectivePairChartAdditionOutputUnit W ij out)⁻¹ : S) •
      (f ∘ projectivePairChartAdditionCoordinates W ij) =
        projectivePairChartAdditionOutputPoint W ij out := by
    funext j
    rfl
  rw [hp] at hscaled
  exact hscaled

/-- The normalized secant output point induces a `K`-algebra map from the
selected quotient chart into the output-coordinate localization. -/
noncomputable def projectivePairChartAdditionOutputAlgHom
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    coveringChartCoordinateRing W out →ₐ[K]
      projectivePairChartAdditionOutputRing W ij out :=
  coveringChartCoordinateRingAlgHomOfNormalizedPoint W out
    (projectivePairChartAdditionOutputPoint W ij out)
    (projectivePairChartAdditionOutputPoint_equation W ij out)
    (projectivePairChartAdditionOutputPoint_normalized W ij out)

/-- On coordinate ratios, the localized output-chart algebra map is exactly
the selected secant coordinate divided by the inverted output coordinate. -/
@[simp]
theorem projectivePairChartAdditionOutputAlgHom_ratio
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) (j : Fin 3) :
    projectivePairChartAdditionOutputAlgHom W ij out
        (Ideal.Quotient.mk (coveringChartIdeal W out)
          (coordinateChartRatio (coveringCoordinate out) j)) =
      projectivePairChartAdditionOutputPoint W ij out j := by
  exact coveringChartCoordinateRingAlgHomOfNormalizedPoint_ratio W out
    (projectivePairChartAdditionOutputPoint W ij out)
    (projectivePairChartAdditionOutputPoint_equation W ij out)
    (projectivePairChartAdditionOutputPoint_normalized W ij out) j

/-- The selected output-coordinate principal open, mapped back into its
projective-pair chart through the affine tensor-product presentation. -/
noncomputable def projectivePairChartAdditionOutputOpen
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    Spec (.of (projectivePairChartAdditionOutputRing W ij out)) ⟶
      projectivePairChartScheme W ij :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputRing W ij out))) ≫
    (projectivePairChartIsoSpecTensor W ij).inv

instance projectivePairChartAdditionOutputOpen_isOpenImmersion
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    IsOpenImmersion (projectivePairChartAdditionOutputOpen W ij out) := by
  dsimp only [projectivePairChartAdditionOutputOpen,
    projectivePairChartAdditionOutputRing]
  infer_instance

/-- Under the affine presentation, the selected source is precisely the basic
open obtained by inverting the chosen secant output coordinate. -/
@[reassoc]
theorem projectivePairChartAdditionOutputOpen_comp_iso_hom
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    projectivePairChartAdditionOutputOpen W ij out ≫
        (projectivePairChartIsoSpecTensor W ij).hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputRing W ij out))) := by
  simp [projectivePairChartAdditionOutputOpen]

/-- The regular secant formula on the principal open where the selected output
coordinate is invertible. -/
noncomputable def projectivePairChartAdditionOutputMorphism
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    Spec (.of (projectivePairChartAdditionOutputRing W ij out)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom
      (projectivePairChartAdditionOutputAlgHom W ij out).toRingHom) ≫
    coveringChartMap W out

/-- Every localized secant formula is an actual morphism over `Spec K`. -/
@[reassoc]
theorem projectivePairChartAdditionOutputMorphism_comp_structureMap
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    projectivePairChartAdditionOutputMorphism W ij out ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (algebraMap K (projectivePairChartAdditionOutputRing W ij out))) := by
  rw [projectivePairChartAdditionOutputMorphism, Category.assoc,
    coveringChartMap_comp_structureMap, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  ext a
  exact (projectivePairChartAdditionOutputAlgHom W ij out).commutes a

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
