/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck

The quotient/tensor equivalence adapts AINTLIB's
`EllipticCurve/AdditionChartTensor.lean`, exact source blob
`8934898a972e7abe51cadbd34942849d1d0dc629`, from its Apache-2.0 licensed
commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The secant chart of Weierstrass addition

This file records the first genuine coordinate-chart prerequisite for the multiplication morphism
on the concrete projective Weierstrass cubic.  Over an arbitrary commutative ring, two affine
points together with an element inverse to their difference of abscissas determine the usual
secant slope.  The checked polynomial identity below shows that the chord-and-tangent formula
lands on the same Weierstrass equation without using field division or a supplied group-object
structure.

The induced quotient-ring map is consumed by `XZeroWeierstrassSecantAdditionMorphism`, where it
defines an actual morphism from the explicit principal-open presentation into the concrete
projective cubic and identifies the presentation with the corresponding open of the affine scheme
product.  Global multiplication still requires the tangent and infinity charts, their overlap
proofs, and scheme-level gluing.
-/

noncomputable section

open scoped WeierstrassCurve.Affine
open TensorProduct

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {R : Type u} [CommRing R]

/-- The secant-line factorization of the affine Weierstrass cubic.  Unlike the field-level
addition theorem, the slope is characterized by its denominator-cleared equation, which is the
form needed on a localized affine product chart. -/
private theorem addPolynomial_secant_factorization
    (W : WeierstrassCurve R) (x₁ x₂ y₁ y₂ ℓ : R)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂)
    (hunit : IsUnit (x₁ - x₂)) :
    W.toAffine.addPolynomial x₁ y₁ ℓ =
      -((Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂) *
        (Polynomial.X - Polynomial.C (W.toAffine.addX x₁ x₂ ℓ))) := by
  rw [WeierstrassCurve.Affine.addPolynomial_eq, neg_inj,
    Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  rw [WeierstrassCurve.Affine.equation_iff] at h₁ h₂
  ext
  · rfl
  · simp only [WeierstrassCurve.Affine.addX]
    ring
  · simp only [WeierstrassCurve.Affine.addX]
    apply hunit.mul_left_cancel
    linear_combination
      (-W.a₁ * x₂ - W.a₃ + ℓ * x₁ - ℓ * x₂ - y₁ - y₂) * hℓ - h₁ + h₂
  · simp only [WeierstrassCurve.Affine.addX]
    apply hunit.mul_left_cancel
    linear_combination
      -x₁ * (-W.a₁ * x₂ - W.a₃ + ℓ * x₁ - ℓ * x₂ - y₁ - y₂) * hℓ +
        x₂ * h₁ - x₁ * h₂

/-- The denominator-cleared secant formula lands on the affine Weierstrass equation over an
arbitrary commutative ring.  This is the algebraic input for the corresponding morphism from the
principal open in the affine product. -/
private theorem equation_add_of_secant
    (W : WeierstrassCurve R) (x₁ x₂ y₁ y₂ ℓ : R)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂)
    (hunit : IsUnit (x₁ - x₂)) :
    W.toAffine.Equation
      (W.toAffine.addX x₁ x₂ ℓ)
      (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  apply (W.toAffine.equation_neg _ _).mpr
  rw [WeierstrassCurve.Affine.equation_add_iff,
    addPolynomial_secant_factorization W x₁ x₂ y₁ y₂ ℓ h₁ h₂ hℓ hunit]
  simp

/-! ## The principal-open coordinate ring -/

/-- Four affine coordinates for an ordered pair of Weierstrass points. -/
private abbrev secantPairPolynomialRing (K : Type u) [CommRing K] :=
  MvPolynomial (Fin 4) K

private abbrev secantX₁ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 0

private abbrev secantY₁ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 1

private abbrev secantX₂ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 2

private abbrev secantY₂ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 3

/-- The affine Weierstrass equation evaluated at two elements of a coefficient algebra. -/
private def affineEquationExpression {K A : Type u} [CommRing K] [CommRing A]
    (W : WeierstrassCurve K) (c : K →+* A) (x y : A) : A :=
  y ^ 2 + c W.a₁ * x * y + c W.a₃ * y -
    (x ^ 3 + c W.a₂ * x ^ 2 + c W.a₄ * x + c W.a₆)

/-- The two equations cutting out the affine product `E × E` in four-space. -/
private def secantPairIdeal {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    Ideal (secantPairPolynomialRing K) :=
  Ideal.span {
    affineEquationExpression W MvPolynomial.C secantX₁ secantY₁,
    affineEquationExpression W MvPolynomial.C secantX₂ secantY₂ }

/-- Coordinate ring of the affine product before restricting to the secant locus. -/
abbrev secantPairCoordinateRing {K : Type u} [CommRing K] (W : WeierstrassCurve K) :=
  secantPairPolynomialRing K ⧸ secantPairIdeal W

/-- Structural coefficient map of the affine-pair coordinate ring. -/
def secantPairCoefficientHom {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : K →+* secantPairCoordinateRing W :=
  (Ideal.Quotient.mk (secantPairIdeal W)).comp MvPolynomial.C

/-- First universal abscissa in the affine-pair coordinate ring. -/
def secantPairX₁ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  Ideal.Quotient.mk (secantPairIdeal W) secantX₁

/-- First universal ordinate in the affine-pair coordinate ring. -/
def secantPairY₁ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  Ideal.Quotient.mk (secantPairIdeal W) secantY₁

/-- Second universal abscissa in the affine-pair coordinate ring. -/
def secantPairX₂ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  Ideal.Quotient.mk (secantPairIdeal W) secantX₂

/-- Second universal ordinate in the affine-pair coordinate ring. -/
def secantPairY₂ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  Ideal.Quotient.mk (secantPairIdeal W) secantY₂

/-- Difference of the two universal abscissas in the affine product coordinate ring. -/
def secantDenominator {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  secantPairX₁ W - secantPairX₂ W

/-- The affine coordinate ring of one Weierstrass factor. -/
abbrev secantTargetCoordinateRing {K : Type u} [CommRing K] (W : WeierstrassCurve K) :=
  Polynomial (Polynomial K) ⧸ Ideal.span {W.toAffine.polynomial}

/-- The structural coefficient map of the affine Weierstrass target. -/
def secantTargetCoefficientHom {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    K →+* secantTargetCoordinateRing W :=
  (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})).comp
    ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
      (Polynomial.C : K →+* Polynomial K))

/-- The explicit target coefficient map is its canonical algebra map. -/
theorem secantTargetCoefficientHom_eq_algebraMap
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantTargetCoefficientHom W = algebraMap K (secantTargetCoordinateRing W) := by
  rfl

/-- Tensor-product coordinate ring of the affine Weierstrass product chart. -/
abbrev secantPairTensorRing {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :=
  secantTargetCoordinateRing W ⊗[K] secantTargetCoordinateRing W

/-- Universal abscissa on one affine Weierstrass factor. -/
def secantTargetX {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W :=
  Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) (Polynomial.C Polynomial.X)

/-- Universal ordinate on one affine Weierstrass factor. -/
def secantTargetY {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W :=
  Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) Polynomial.X

private theorem secantTargetPolynomialEvaluation_eq_expression
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    Polynomial.eval₂
        (Polynomial.eval₂RingHom (secantTargetCoefficientHom W) (secantTargetX W))
        (secantTargetY W) W.toAffine.polynomial =
      affineEquationExpression W (secantTargetCoefficientHom W)
        (secantTargetX W) (secantTargetY W) := by
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial,
    (W.map (secantTargetCoefficientHom W)).toAffine.evalEval_polynomial]
  rfl

private theorem secantTarget_equation {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    affineEquationExpression W (secantTargetCoefficientHom W)
      (secantTargetX W) (secantTargetY W) = 0 := by
  rw [← secantTargetPolynomialEvaluation_eq_expression]
  change (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (secantTargetCoefficientHom W) (secantTargetX W))
      (secantTargetY W)) W.toAffine.polynomial = 0
  rw [show Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (secantTargetCoefficientHom W) (secantTargetX W))
        (secantTargetY W) =
      Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) by
    apply Polynomial.ringHom_ext
    · intro p
      have hinner : Polynomial.eval₂RingHom
          (secantTargetCoefficientHom W) (secantTargetX W) =
          (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})).comp Polynomial.C := by
        apply Polynomial.ringHom_ext
        · intro a
          simp [secantTargetCoefficientHom]
        · simp [secantTargetX]
      simpa using RingHom.congr_fun hinner p
    · simp [secantTargetY]]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

private noncomputable def secantPairToTensorAux {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairPolynomialRing K →ₐ[K] secantPairTensorRing W :=
  MvPolynomial.aeval ![
    secantTargetX W ⊗ₜ[K] (1 : secantTargetCoordinateRing W),
    secantTargetY W ⊗ₜ[K] (1 : secantTargetCoordinateRing W),
    (1 : secantTargetCoordinateRing W) ⊗ₜ[K] secantTargetX W,
    (1 : secantTargetCoordinateRing W) ⊗ₜ[K] secantTargetY W]

private theorem secantPairToTensorAux_equation_left {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairToTensorAux W
      (affineEquationExpression W MvPolynomial.C secantX₁ secantY₁) = 0 := by
  simp only [secantPairToTensorAux, affineEquationExpression, map_sub, map_add,
    map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rw [Algebra.TensorProduct.algebraMap_apply]
  let L : secantTargetCoordinateRing W →ₐ[K] secantPairTensorRing W :=
    Algebra.TensorProduct.includeLeft
  have h : L (affineEquationExpression W (secantTargetCoefficientHom W)
      (secantTargetX W) (secantTargetY W)) = 0 := by
    simpa only [map_zero] using congrArg L (secantTarget_equation W)
  simp only [affineEquationExpression, map_sub, map_add, map_mul, map_pow] at h
  simpa [L, secantTargetCoefficientHom_eq_algebraMap,
    Algebra.TensorProduct.includeLeft_apply] using h

private theorem secantPairToTensorAux_equation_right {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairToTensorAux W
      (affineEquationExpression W MvPolynomial.C secantX₂ secantY₂) = 0 := by
  simp only [secantPairToTensorAux, affineEquationExpression, map_sub, map_add,
    map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  let R : secantTargetCoordinateRing W →ₐ[K] secantPairTensorRing W :=
    Algebra.TensorProduct.includeRight
  have h : R (affineEquationExpression W (secantTargetCoefficientHom W)
      (secantTargetX W) (secantTargetY W)) = 0 := by
    simpa only [map_zero] using congrArg R (secantTarget_equation W)
  simp only [affineEquationExpression, map_sub, map_add, map_mul, map_pow] at h
  simpa [R, secantTargetCoefficientHom_eq_algebraMap,
    Algebra.TensorProduct.includeRight_apply] using h

private noncomputable def secantPairToTensor {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairCoordinateRing W →ₐ[K] secantPairTensorRing W :=
  Ideal.Quotient.liftₐ _ (secantPairToTensorAux W) <| by
    intro p hp
    refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
      (fun c x _ hx => by simp [hx]) hp
    rintro p (rfl | rfl)
    · exact secantPairToTensorAux_equation_left W
    · exact secantPairToTensorAux_equation_right W

private noncomputable def secantPairPolynomialEvaluation {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (x y : secantPairCoordinateRing W) :
    Polynomial (Polynomial K) →ₐ[K] secantPairCoordinateRing W :=
  Polynomial.eval₂AlgHom
    (Polynomial.eval₂AlgHom (Algebra.ofId K _) x (fun _ => Commute.all _ _))
    y (fun _ => Commute.all _ _)

private theorem secantPair_algebraMap {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (a : K) :
    algebraMap K (secantPairCoordinateRing W) a =
      Ideal.Quotient.mk (secantPairIdeal W) (MvPolynomial.C a) := by
  rw [IsScalarTower.algebraMap_apply K (secantPairPolynomialRing K),
    Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]

/-- The explicit coefficient map of the affine-pair presentation is its
canonical algebra map. -/
theorem secantPairCoefficientHom_eq_algebraMap
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantPairCoefficientHom W =
      algebraMap K (secantPairCoordinateRing W) := by
  ext a
  exact (secantPair_algebraMap W a).symm

private theorem secantPairPolynomialEvaluation_polynomial {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (x y : secantPairPolynomialRing K)
    (h : affineEquationExpression W MvPolynomial.C x y ∈ secantPairIdeal W) :
    secantPairPolynomialEvaluation W
      (Ideal.Quotient.mk (secantPairIdeal W) x)
      (Ideal.Quotient.mk (secantPairIdeal W) y) W.toAffine.polynomial = 0 := by
  have hz : Ideal.Quotient.mk (secantPairIdeal W)
      (affineEquationExpression W MvPolynomial.C x y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap K (secantPairCoordinateRing W))
        (Ideal.Quotient.mk (secantPairIdeal W) x))
      (Ideal.Quotient.mk (secantPairIdeal W) y) W.toAffine.polynomial = 0
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial,
    (W.map (algebraMap K (secantPairCoordinateRing W))).toAffine.evalEval_polynomial]
  simpa only [affineEquationExpression, Ideal.Quotient.algebraMap_eq,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, secantPair_algebraMap,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.map_C] using hz

private noncomputable def secantPairFromLeft {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →ₐ[K] secantPairCoordinateRing W :=
  Ideal.Quotient.liftₐ _
    (secantPairPolynomialEvaluation W
      (Ideal.Quotient.mk (secantPairIdeal W) secantX₁)
      (Ideal.Quotient.mk (secantPairIdeal W) secantY₁)) <| by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul]
    rw [secantPairPolynomialEvaluation_polynomial W secantX₁ secantY₁
      (Ideal.subset_span (Set.mem_insert _ _)), zero_mul]

private noncomputable def secantPairFromRight {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →ₐ[K] secantPairCoordinateRing W :=
  Ideal.Quotient.liftₐ _
    (secantPairPolynomialEvaluation W
      (Ideal.Quotient.mk (secantPairIdeal W) secantX₂)
      (Ideal.Quotient.mk (secantPairIdeal W) secantY₂)) <| by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul]
    rw [secantPairPolynomialEvaluation_polynomial W secantX₂ secantY₂
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)), zero_mul]

private noncomputable def secantPairFromTensor {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairTensorRing W →ₐ[K] secantPairCoordinateRing W :=
  Algebra.TensorProduct.lift (secantPairFromLeft W) (secantPairFromRight W)
    fun _ _ => Commute.all _ _

private theorem secantPairToTensor_mk {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (p : secantPairPolynomialRing K) :
    secantPairToTensor W (Ideal.Quotient.mk (secantPairIdeal W) p) =
      secantPairToTensorAux W p := rfl

private theorem secantPairFromLeft_mk {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (p : Polynomial (Polynomial K)) :
    secantPairFromLeft W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) p) =
      secantPairPolynomialEvaluation W
        (Ideal.Quotient.mk (secantPairIdeal W) secantX₁)
        (Ideal.Quotient.mk (secantPairIdeal W) secantY₁) p := rfl

private theorem secantPairFromRight_mk {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (p : Polynomial (Polynomial K)) :
    secantPairFromRight W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) p) =
      secantPairPolynomialEvaluation W
        (Ideal.Quotient.mk (secantPairIdeal W) secantX₂)
        (Ideal.Quotient.mk (secantPairIdeal W) secantY₂) p := rfl

private theorem secantPairFromLeft_targetX {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairFromLeft W (secantTargetX W) =
      Ideal.Quotient.mk (secantPairIdeal W) secantX₁ := by
  rw [secantTargetX, secantPairFromLeft_mk]
  simp [secantPairPolynomialEvaluation]

private theorem secantPairFromLeft_targetY {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairFromLeft W (secantTargetY W) =
      Ideal.Quotient.mk (secantPairIdeal W) secantY₁ := by
  rw [secantTargetY, secantPairFromLeft_mk]
  simp [secantPairPolynomialEvaluation]

private theorem secantPairFromRight_targetX {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairFromRight W (secantTargetX W) =
      Ideal.Quotient.mk (secantPairIdeal W) secantX₂ := by
  rw [secantTargetX, secantPairFromRight_mk]
  simp [secantPairPolynomialEvaluation]

private theorem secantPairFromRight_targetY {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairFromRight W (secantTargetY W) =
      Ideal.Quotient.mk (secantPairIdeal W) secantY₂ := by
  rw [secantTargetY, secantPairFromRight_mk]
  simp [secantPairPolynomialEvaluation]

private theorem secantPairToTensor_comp_fromLeft {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (secantPairToTensor W).comp (secantPairFromLeft W) =
      Algebra.TensorProduct.includeLeft (S := K) := by
  apply Ideal.Quotient.algHom_ext K
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    change secantPairToTensor W (secantPairFromLeft W (secantTargetX W)) =
      Algebra.TensorProduct.includeLeft (secantTargetX W)
    rw [secantPairFromLeft_targetX, secantPairToTensor_mk]
    simp [secantPairToTensorAux, secantTargetX,
      Algebra.TensorProduct.includeLeft_apply]
  · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    change secantPairToTensor W (secantPairFromLeft W (secantTargetY W)) =
      Algebra.TensorProduct.includeLeft (secantTargetY W)
    rw [secantPairFromLeft_targetY, secantPairToTensor_mk]
    simp [secantPairToTensorAux, secantTargetY,
      Algebra.TensorProduct.includeLeft_apply]

private theorem secantPairToTensor_comp_fromRight {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (secantPairToTensor W).comp (secantPairFromRight W) =
      Algebra.TensorProduct.includeRight := by
  apply Ideal.Quotient.algHom_ext K
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    change secantPairToTensor W (secantPairFromRight W (secantTargetX W)) =
      Algebra.TensorProduct.includeRight (secantTargetX W)
    rw [secantPairFromRight_targetX, secantPairToTensor_mk]
    simp [secantPairToTensorAux, secantTargetX,
      Algebra.TensorProduct.includeRight_apply]
  · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    change secantPairToTensor W (secantPairFromRight W (secantTargetY W)) =
      Algebra.TensorProduct.includeRight (secantTargetY W)
    rw [secantPairFromRight_targetY, secantPairToTensor_mk]
    simp [secantPairToTensorAux, secantTargetY,
      Algebra.TensorProduct.includeRight_apply]

/-- The four-coordinate presentation of a pair of affine Weierstrass points is canonically the
tensor product of the two affine coordinate rings. -/
noncomputable def secantPairTensorEquiv {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairCoordinateRing W ≃ₐ[K] secantPairTensorRing W :=
  AlgEquiv.ofAlgHom (secantPairToTensor W) (secantPairFromTensor W)
    (by
      refine Algebra.TensorProduct.ext' fun a b => ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply, secantPairFromTensor,
        Algebra.TensorProduct.lift_tmul, map_mul]
      rw [← AlgHom.comp_apply, secantPairToTensor_comp_fromLeft,
        ← AlgHom.comp_apply, secantPairToTensor_comp_fromRight]
      simp [Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply])
    (by
      refine Ideal.Quotient.algHom_ext K (MvPolynomial.algHom_ext fun i => ?_)
      fin_cases i <;>
        simp [secantPairToTensor_mk, secantPairToTensorAux, secantPairFromTensor,
          secantPairFromLeft_targetX, secantPairFromLeft_targetY,
          secantPairFromRight_targetX, secantPairFromRight_targetY])

/-- The first affine-pair abscissa is the left tensor-factor abscissa. -/
theorem secantPairTensorEquiv_X₁ {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairTensorEquiv W (secantPairX₁ W) =
      secantTargetX W ⊗ₜ[K] (1 : secantTargetCoordinateRing W) := by
  change secantPairToTensor W
      (Ideal.Quotient.mk (secantPairIdeal W) secantX₁) = _
  rw [secantPairToTensor_mk]
  simp [secantPairToTensorAux]

/-- The first affine-pair ordinate is the left tensor-factor ordinate. -/
theorem secantPairTensorEquiv_Y₁ {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairTensorEquiv W (secantPairY₁ W) =
      secantTargetY W ⊗ₜ[K] (1 : secantTargetCoordinateRing W) := by
  change secantPairToTensor W
      (Ideal.Quotient.mk (secantPairIdeal W) secantY₁) = _
  rw [secantPairToTensor_mk]
  simp [secantPairToTensorAux]

/-- The second affine-pair abscissa is the right tensor-factor abscissa. -/
theorem secantPairTensorEquiv_X₂ {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairTensorEquiv W (secantPairX₂ W) =
      (1 : secantTargetCoordinateRing W) ⊗ₜ[K] secantTargetX W := by
  change secantPairToTensor W
      (Ideal.Quotient.mk (secantPairIdeal W) secantX₂) = _
  rw [secantPairToTensor_mk]
  simp [secantPairToTensorAux]

/-- The second affine-pair ordinate is the right tensor-factor ordinate. -/
theorem secantPairTensorEquiv_Y₂ {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairTensorEquiv W (secantPairY₂ W) =
      (1 : secantTargetCoordinateRing W) ⊗ₜ[K] secantTargetY W := by
  change secantPairToTensor W
      (Ideal.Quotient.mk (secantPairIdeal W) secantY₂) = _
  rw [secantPairToTensor_mk]
  simp [secantPairToTensorAux]

/-- Under the affine-product identification, the secant denominator is exactly
`x₁ ⊗ 1 - 1 ⊗ x₂`. -/
theorem secantPairTensorEquiv_denominator {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantPairTensorEquiv W (secantDenominator W) =
      secantTargetX W ⊗ₜ[K] (1 : secantTargetCoordinateRing W) -
        (1 : secantTargetCoordinateRing W) ⊗ₜ[K] secantTargetX W := by
  change secantPairToTensor W
      (Ideal.Quotient.mk (secantPairIdeal W) (secantX₁ - secantX₂)) = _
  rw [secantPairToTensor_mk]
  simp [secantPairToTensorAux]

/-- Coordinate ring of the principal open in `E × E` where `x₁ - x₂` is invertible. -/
abbrev secantChartCoordinateRing {K : Type u} [CommRing K] (W : WeierstrassCurve K) :=
  Localization.Away (secantDenominator W)

private def secantCoordinate {K : Type u} [CommRing K] (W : WeierstrassCurve K)
    (q : secantPairPolynomialRing K) : secantChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
    (Ideal.Quotient.mk (secantPairIdeal W) q)

/-- The structural coefficient map of the secant chart. -/
def secantCoefficientHom {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    K →+* secantChartCoordinateRing W :=
  (algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)).comp
    ((Ideal.Quotient.mk (secantPairIdeal W)).comp MvPolynomial.C)

/-- The explicit coefficient map of the secant chart is its canonical algebra map. -/
theorem secantCoefficientHom_eq_algebraMap
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantCoefficientHom W = algebraMap K (secantChartCoordinateRing W) := by
  ext a
  change algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
      (Ideal.Quotient.mk (secantPairIdeal W) (MvPolynomial.C a)) =
    algebraMap K (secantChartCoordinateRing W) a
  rw [← secantPair_algebraMap W a]
  exact (IsScalarTower.algebraMap_apply K (secantPairCoordinateRing W)
    (secantChartCoordinateRing W) a).symm

/-- First universal abscissa on the secant chart. -/
def secantChartX₁ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantX₁

/-- First universal ordinate on the secant chart. -/
def secantChartY₁ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantY₁

/-- Second universal abscissa on the secant chart. -/
def secantChartX₂ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantX₂

/-- Second universal ordinate on the secant chart. -/
def secantChartY₂ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantY₂

/-- The universal secant slope on the principal open. -/
def secantChartSlope {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W :=
  (secantChartY₁ W - secantChartY₂ W) *
    IsLocalization.Away.invSelf (secantDenominator W)

private theorem secantPairEquation_mem_left {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    affineEquationExpression W MvPolynomial.C secantX₁ secantY₁ ∈
      secantPairIdeal W := by
  apply Ideal.subset_span
  simp

private theorem secantPairEquation_mem_right {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    affineEquationExpression W MvPolynomial.C secantX₂ secantY₂ ∈
      secantPairIdeal W := by
  apply Ideal.subset_span
  simp

/-- The first universal point of the affine-pair presentation satisfies the
base-changed Weierstrass equation. -/
theorem secantPair_equation_left {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (W.map (secantPairCoefficientHom W)).toAffine.Equation
      (secantPairX₁ W) (secantPairY₁ W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change affineEquationExpression W (secantPairCoefficientHom W)
      (secantPairX₁ W) (secantPairY₁ W) = 0
  have hzero : Ideal.Quotient.mk (secantPairIdeal W)
      (affineEquationExpression W MvPolynomial.C secantX₁ secantY₁) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (secantPairEquation_mem_left W)
  simpa [affineEquationExpression, secantPairCoefficientHom,
    secantPairX₁, secantPairY₁] using hzero

/-- The second universal point of the affine-pair presentation satisfies the
base-changed Weierstrass equation. -/
theorem secantPair_equation_right {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (W.map (secantPairCoefficientHom W)).toAffine.Equation
      (secantPairX₂ W) (secantPairY₂ W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change affineEquationExpression W (secantPairCoefficientHom W)
      (secantPairX₂ W) (secantPairY₂ W) = 0
  have hzero : Ideal.Quotient.mk (secantPairIdeal W)
      (affineEquationExpression W MvPolynomial.C secantX₂ secantY₂) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (secantPairEquation_mem_right W)
  simpa [affineEquationExpression, secantPairCoefficientHom,
    secantPairX₂, secantPairY₂] using hzero

/-- The first universal point satisfies the base-changed Weierstrass equation. -/
private theorem secantChart_equation_left {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (W.map (secantCoefficientHom W)).toAffine.Equation
      (secantChartX₁ W) (secantChartY₁ W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change affineEquationExpression W (secantCoefficientHom W)
      (secantChartX₁ W) (secantChartY₁ W) = 0
  have hzero : secantCoordinate W
      (affineEquationExpression W MvPolynomial.C secantX₁ secantY₁) = 0 := by
    rw [secantCoordinate,
      Ideal.Quotient.eq_zero_iff_mem.mpr (secantPairEquation_mem_left W), map_zero]
  simpa [affineEquationExpression, secantChartX₁, secantChartY₁,
    secantCoordinate, secantCoefficientHom] using hzero

/-- The second universal point satisfies the base-changed Weierstrass equation. -/
private theorem secantChart_equation_right {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (W.map (secantCoefficientHom W)).toAffine.Equation
      (secantChartX₂ W) (secantChartY₂ W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change affineEquationExpression W (secantCoefficientHom W)
      (secantChartX₂ W) (secantChartY₂ W) = 0
  have hzero : secantCoordinate W
      (affineEquationExpression W MvPolynomial.C secantX₂ secantY₂) = 0 := by
    rw [secantCoordinate,
      Ideal.Quotient.eq_zero_iff_mem.mpr (secantPairEquation_mem_right W), map_zero]
  simpa [affineEquationExpression, secantChartX₂, secantChartY₂,
    secantCoordinate, secantCoefficientHom] using hzero

private theorem secantChartX₁_sub_X₂ {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantChartX₁ W - secantChartX₂ W =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (secantDenominator W) := by
  simp [secantChartX₁, secantChartX₂, secantCoordinate, secantDenominator,
    secantPairX₁, secantPairX₂]

/-- The first secant-chart abscissa is pulled back from the affine-pair
coordinate ring. -/
@[simp]
theorem secantChartX₁_eq_algebraMap_pairX₁
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartX₁ W =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (secantPairX₁ W) := by
  rfl

/-- The first secant-chart ordinate is pulled back from the affine-pair
coordinate ring. -/
@[simp]
theorem secantChartY₁_eq_algebraMap_pairY₁
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartY₁ W =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (secantPairY₁ W) := by
  rfl

/-- The second secant-chart abscissa is pulled back from the affine-pair
coordinate ring. -/
@[simp]
theorem secantChartX₂_eq_algebraMap_pairX₂
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartX₂ W =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (secantPairX₂ W) := by
  rfl

/-- The second secant-chart ordinate is pulled back from the affine-pair
coordinate ring. -/
@[simp]
theorem secantChartY₂_eq_algebraMap_pairY₂
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartY₂ W =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (secantPairY₂ W) := by
  rfl

/-- The universal slope satisfies its denominator-cleared secant equation. -/
theorem secantChartSlope_mul_sub {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantChartSlope W * (secantChartX₁ W - secantChartX₂ W) =
      secantChartY₁ W - secantChartY₂ W := by
  rw [secantChartSlope, mul_assoc]
  rw [secantChartX₁_sub_X₂]
  change (secantChartY₁ W - secantChartY₂ W) *
      (IsLocalization.Away.invSelf (secantDenominator W) *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (secantDenominator W)) = _
  rw [mul_comm (IsLocalization.Away.invSelf (secantDenominator W)),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- The universal secant formula is an actual point of the base-changed affine cubic. -/
theorem secantChart_equation_add {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    let W' := W.map (secantCoefficientHom W)
    W'.toAffine.Equation
      (W'.toAffine.addX (secantChartX₁ W) (secantChartX₂ W)
        (secantChartSlope W))
      (W'.toAffine.addY (secantChartX₁ W) (secantChartX₂ W)
        (secantChartY₁ W) (secantChartSlope W)) := by
  dsimp only
  apply equation_add_of_secant
  · exact secantChart_equation_left W
  · exact secantChart_equation_right W
  · exact secantChartSlope_mul_sub W
  · rw [secantChartX₁_sub_X₂]
    exact IsLocalization.Away.algebraMap_isUnit (secantDenominator W)

/-! ## The induced affine morphism -/

/-- The universal output abscissa of the secant formula. -/
def secantChartAddX {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W :=
  let W' := W.map (secantCoefficientHom W)
  W'.toAffine.addX (secantChartX₁ W) (secantChartX₂ W) (secantChartSlope W)

/-- The universal output ordinate of the secant formula. -/
def secantChartAddY {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W :=
  let W' := W.map (secantCoefficientHom W)
  W'.toAffine.addY (secantChartX₁ W) (secantChartX₂ W)
    (secantChartY₁ W) (secantChartSlope W)

private def secantAdditionPolynomialEvaluation {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    Polynomial (Polynomial K) →+* secantChartCoordinateRing W :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (secantCoefficientHom W) (secantChartAddX W))
    (secantChartAddY W)

private theorem secantAdditionPolynomialEvaluation_eq_zero
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantAdditionPolynomialEvaluation W W.toAffine.polynomial = 0 := by
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom (secantCoefficientHom W) (secantChartAddX W))
      (secantChartAddY W) W.toAffine.polynomial = 0
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial]
  simpa [secantChartAddX, secantChartAddY,
    WeierstrassCurve.Affine.Equation] using secantChart_equation_add W

/-- The contravariant coordinate-ring map of secant addition on the principal open
`x₁ - x₂ ≠ 0` in the affine product. -/
def secantAdditionToAffineRing {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →+* secantChartCoordinateRing W :=
  Ideal.Quotient.lift (Ideal.span {W.toAffine.polynomial})
    (secantAdditionPolynomialEvaluation W) (by
      intro p hp
      apply (show Ideal.span {W.toAffine.polynomial} ≤
          RingHom.ker (secantAdditionPolynomialEvaluation W) by
        apply Ideal.span_le.mpr
        intro q hq
        rw [Set.mem_singleton_iff.mp hq]
        exact secantAdditionPolynomialEvaluation_eq_zero W) hp)

/-- The affine target's abscissa pulls back to the universal secant abscissa. -/
theorem secantAdditionToAffineRing_abscissa {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantAdditionToAffineRing W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
          (Polynomial.C Polynomial.X)) =
      secantChartAddX W := by
  simp [secantAdditionToAffineRing, secantAdditionPolynomialEvaluation]

/-- The affine target's ordinate pulls back to the universal secant ordinate. -/
theorem secantAdditionToAffineRing_ordinate {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantAdditionToAffineRing W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) Polynomial.X) =
      secantChartAddY W := by
  simp [secantAdditionToAffineRing, secantAdditionPolynomialEvaluation]

/-- Secant addition respects the structural coefficient maps. -/
@[simp]
theorem secantAdditionToAffineRing_coefficient {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (a : K) :
    secantAdditionToAffineRing W (secantTargetCoefficientHom W a) =
      secantCoefficientHom W a := by
  simp [secantAdditionToAffineRing, secantAdditionPolynomialEvaluation,
    secantTargetCoefficientHom, secantCoefficientHom]

/-- Ring-hom form of compatibility with the base coefficients. -/
theorem secantAdditionToAffineRing_comp_coefficient {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (secantAdditionToAffineRing W).comp (secantTargetCoefficientHom W) =
      secantCoefficientHom W := by
  ext a
  exact secantAdditionToAffineRing_coefficient W a

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
