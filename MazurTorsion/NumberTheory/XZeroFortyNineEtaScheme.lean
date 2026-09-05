/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.XZeroFortyNineEtaModel
import MazurTorsion.NumberTheory.XZeroFortyNineRationalCuspAffineChart

/-!
# A scheme-level eta-equation chart for `X₀(49)`

This file upgrades the checked rational eta-equation calculation to an
honest affine scheme.  Its coordinate ring is the quotient of `ℚ[x, y]` by
the eta equation.  The coordinate change to the represented Weierstrass
cubic contains the denominator `x² + 7x + 7`, so over arbitrary schemes its
regular domain is the principal open

`D(x (x² + 7x + 7))`.

On this open the formulas

`X = 4x`,

`Y = (8y - 28x(x² + 5x + 7)) / (x² + 7x + 7)`

define a scheme morphism into the explicit affine presentation of the
rational-cusp-avoiding open `D(X)` and hence into that actual open subscheme.

The design boundary is equation-side and target-side: no eta functions on a
modular curve, modular classifying map, or comparison isomorphism are
constructed here.  The immediate named downstream consumer is
`openScheme_rationalPoints_isEmpty`; a modular application must separately
construct a map into this eta-equation chart.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

namespace MazurTorsion.XZeroFortyNine.EtaSchemeModel

/-- The eta-plane equation as a ring expression over an arbitrary
commutative ring. -/
def equationExpression {R : Type*} [CommRing R] (x y : R) : R :=
  y ^ 2 - 7 * x * y * (x ^ 2 + 5 * x + 7) -
    x * (x ^ 6 + 7 * x ^ 5 + 21 * x ^ 4 + 49 * x ^ 3 +
      147 * x ^ 2 + 343 * x + 343)

/-- The bivariate eta-equation polynomial over `ℚ`. -/
def polynomial : MvPolynomial (Fin 2) ℚ :=
  equationExpression (MvPolynomial.X 0) (MvPolynomial.X 1)

/-- The principal ideal cutting out the eta-equation plane curve. -/
def ideal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {polynomial}

/-- The affine coordinate ring `ℚ[x, y] / (F)` of the eta equation. -/
abbrev coordinateRing := MvPolynomial (Fin 2) ℚ ⧸ ideal

/-- The eta-equation affine scheme. -/
abbrev scheme : Scheme := Spec (.of coordinateRing)

/-- The universal `x` coordinate on the eta-equation scheme. -/
def x : coordinateRing := Ideal.Quotient.mk ideal (MvPolynomial.X 0)

/-- The universal `y` coordinate on the eta-equation scheme. -/
def y : coordinateRing := Ideal.Quotient.mk ideal (MvPolynomial.X 1)

/-- The earlier rational eta-point equation is the specialization of the
universal ring expression. -/
theorem etaPlaneEquation_iff_equationExpression (a b : ℚ) :
    etaPlaneEquation a b ↔ equationExpression a b = 0 := by
  rfl

/-- The universal coordinates satisfy the eta equation. -/
theorem equation : equationExpression x y = 0 := by
  have h : Ideal.Quotient.mk ideal polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton polynomial))
  simpa only [polynomial, equationExpression, x, y, map_sub, map_add,
    map_mul, map_pow, map_ofNat] using h

/-- The denominator of the eta-to-Weierstrass coordinate change. -/
def denominator : coordinateRing := x ^ 2 + 7 * x + 7

/-- The element inverted on the scheme-theoretic regularity domain. -/
def openElement : coordinateRing := x * denominator

/-- The coordinate ring of `D(x (x² + 7x + 7))` in the eta-equation
scheme. -/
abbrev openCoordinateRing := Localization.Away openElement

/-- The regularity domain of the eta-to-Weierstrass coordinate change. -/
abbrev openScheme : Scheme := Spec (.of openCoordinateRing)

/-- The principal-open localization morphism into the eta-equation scheme. -/
def openInclusion : openScheme ⟶ scheme :=
  Spec.map (CommRingCat.ofHom
    (algebraMap coordinateRing openCoordinateRing))

instance openInclusion_isOpenImmersion : IsOpenImmersion openInclusion := by
  dsimp only [openInclusion, openScheme, openCoordinateRing]
  infer_instance

/-- The localization morphism has exactly the expected principal-open
range. -/
theorem openInclusion_opensRange :
    openInclusion.opensRange = PrimeSpectrum.basicOpen openElement := by
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of coordinateRing) openElement

/-- The localized universal `x` coordinate. -/
def openX : openCoordinateRing :=
  algebraMap coordinateRing openCoordinateRing x

/-- The localized universal `y` coordinate. -/
def openY : openCoordinateRing :=
  algebraMap coordinateRing openCoordinateRing y

/-- The localized coordinate-change denominator. -/
def openDenominator : openCoordinateRing :=
  algebraMap coordinateRing openCoordinateRing denominator

/-- The localized denominator retains its defining quadratic formula. -/
theorem openDenominator_eq :
    openDenominator = openX ^ 2 + 7 * openX + 7 := by
  simp only [openDenominator, denominator, openX, map_add, map_mul,
    map_pow, map_ofNat]

/-- The localized universal coordinates still satisfy the eta equation. -/
theorem openEquation : equationExpression openX openY = 0 := by
  have h := congrArg (algebraMap coordinateRing openCoordinateRing) equation
  simpa only [equationExpression, openX, openY, map_sub, map_add,
    map_mul, map_pow, map_ofNat, map_zero] using h

private theorem openElement_isUnit :
    IsUnit (algebraMap coordinateRing openCoordinateRing openElement) :=
  IsLocalization.map_units openCoordinateRing
    (⟨openElement, by simp⟩ : Submonoid.powers openElement)

/-- The coordinate `x` is a unit on the chosen regularity domain. -/
theorem openX_isUnit : IsUnit openX := by
  have hprod : IsUnit (openX * openDenominator) := by
    simpa [openElement, openX, openDenominator, map_mul] using openElement_isUnit
  exact IsUnit.mul_iff.mp hprod |>.1

/-- The coordinate-change denominator is a unit on the chosen regularity
domain. -/
theorem openDenominator_isUnit : IsUnit openDenominator := by
  have hprod : IsUnit (openX * openDenominator) := by
    simpa [openElement, openX, openDenominator, map_mul] using openElement_isUnit
  exact IsUnit.mul_iff.mp hprod |>.2

/-- The inverse of the coordinate-change denominator on the regularity
domain. -/
def openDenominatorInverse : openCoordinateRing :=
  ↑(openDenominator_isUnit.unit⁻¹)

/-- The chosen denominator inverse is a right inverse. -/
theorem openDenominator_mul_inverse :
    openDenominator * openDenominatorInverse = 1 := by
  rw [← openDenominator_isUnit.unit_spec]
  simp [openDenominatorInverse]

/-- The transformed Weierstrass abscissa `X = 4x`. -/
def openCurveX : openCoordinateRing := 4 * openX

/-- The transformed Weierstrass ordinate on the denominator-open locus. -/
def openCurveY : openCoordinateRing :=
  (8 * openY - 28 * openX * (openX ^ 2 + 5 * openX + 7)) *
    openDenominatorInverse

/-- The transformed coordinates satisfy the level-49 Weierstrass
equation. -/
theorem openCurveY_sq :
    openCurveY ^ 2 =
      openCurveX * (openCurveX ^ 2 + 21 * openCurveX + 112) := by
  apply (openDenominator_isUnit.pow 2).mul_left_cancel
  rw [show openDenominator ^ 2 * openCurveY ^ 2 =
      (openDenominator * openCurveY) ^ 2 by ring]
  have hymul : openDenominator * openCurveY =
      8 * openY - 28 * openX * (openX ^ 2 + 5 * openX + 7) := by
    rw [openCurveY]
    calc
      openDenominator *
          ((8 * openY - 28 * openX * (openX ^ 2 + 5 * openX + 7)) *
            openDenominatorInverse) =
        (8 * openY - 28 * openX * (openX ^ 2 + 5 * openX + 7)) *
          (openDenominator * openDenominatorInverse) := by ring
      _ = _ := by rw [openDenominator_mul_inverse, mul_one]
  rw [hymul, openDenominator_eq]
  unfold openCurveX
  have heta := openEquation
  unfold equationExpression at heta
  linear_combination 64 * heta

/-- The coefficient embedding into the eta-equation coordinate ring. -/
def coefficientHom : ℚ →+* coordinateRing :=
  (Ideal.Quotient.mk ideal).comp
    (MvPolynomial.C : ℚ →+* MvPolynomial (Fin 2) ℚ)

/-- The coefficient embedding into the localized eta-equation coordinate
ring. -/
def openCoefficientHom : ℚ →+* openCoordinateRing :=
  (algebraMap coordinateRing openCoordinateRing).comp coefficientHom

/-- The explicit coefficient map is the canonical algebra map. -/
theorem coefficientHom_eq_algebraMap :
    coefficientHom = algebraMap ℚ coordinateRing := by
  rfl

/-- The localized coefficient map is the canonical algebra map. -/
theorem openCoefficientHom_eq_algebraMap :
    openCoefficientHom = algebraMap ℚ openCoordinateRing := by
  rfl

private def curvePolynomialEvaluation :
    Polynomial (Polynomial ℚ) →+* openCoordinateRing :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom openCoefficientHom openCurveX) openCurveY

private theorem curvePolynomialEvaluation_eq_zero :
    curvePolynomialEvaluation curve.toAffine.polynomial = 0 := by
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom openCoefficientHom openCurveX)
      openCurveY curve.toAffine.polynomial = 0
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial,
    (curve.map openCoefficientHom).toAffine.evalEval_polynomial]
  have hcurve : openCurveY ^ 2 =
      openCurveX ^ 3 + 21 * openCurveX ^ 2 + 112 * openCurveX := by
    calc
      openCurveY ^ 2 =
          openCurveX * (openCurveX ^ 2 + 21 * openCurveX + 112) :=
        openCurveY_sq
      _ = openCurveX ^ 3 + 21 * openCurveX ^ 2 + 112 * openCurveX := by
        ring
  simpa [curve, map_ofNat] using sub_eq_zero.mpr hcurve

/-- Evaluation at the transformed coordinates as a map out of the affine
Weierstrass coordinate ring. -/
def affineCurveToOpenRing :
    affineWeierstrassCoordinateRing curve →+* openCoordinateRing :=
  Ideal.Quotient.lift (Ideal.span {curve.toAffine.polynomial})
    curvePolynomialEvaluation (by
      intro p hp
      apply (show Ideal.span {curve.toAffine.polynomial} ≤
          RingHom.ker curvePolynomialEvaluation by
        apply Ideal.span_le.mpr
        intro q hq
        rw [Set.mem_singleton_iff.mp hq]
        exact curvePolynomialEvaluation_eq_zero) hp)

/-- The affine Weierstrass abscissa maps to `4x`. -/
theorem affineCurveToOpenRing_abscissa :
    affineCurveToOpenRing
        (Ideal.Quotient.mk (Ideal.span {curve.toAffine.polynomial})
          (Polynomial.C Polynomial.X)) =
      openCurveX := by
  simp [affineCurveToOpenRing, curvePolynomialEvaluation]

/-- The affine Weierstrass ordinate maps to the regular transformed
ordinate. -/
theorem affineCurveToOpenRing_ordinate :
    affineCurveToOpenRing
        (Ideal.Quotient.mk (Ideal.span {curve.toAffine.polynomial})
          Polynomial.X) =
      openCurveY := by
  simp [affineCurveToOpenRing, curvePolynomialEvaluation]

private def coveringChartToAffine :
    standardAmbientChartRing ℚ →+* Polynomial (Polynomial ℚ) :=
  standardChartToAffine

private def standardAmbientEvaluation :
    standardAmbientChartRing ℚ →+* openCoordinateRing :=
  curvePolynomialEvaluation.comp coveringChartToAffine

private theorem standardAmbientEvaluation_equation_eq_zero :
    standardAmbientEvaluation (standardChartEquation curve) = 0 := by
  change curvePolynomialEvaluation
    (standardChartToAffine (standardChartEquation curve)) = 0
  rw [standardChartEquation_eq_affineToStandardChart]
  rw [show standardChartToAffine
      (affineToStandardChart curve.toAffine.polynomial) =
        curve.toAffine.polynomial from
    DFunLike.congr_fun standardChartToAffine_comp_affineToStandardChart _]
  exact curvePolynomialEvaluation_eq_zero

private theorem standardAmbientEvaluation_eq_zero_of_mem
    (p : standardAmbientChartRing ℚ) (hp : p ∈ standardChartIdeal curve) :
    standardAmbientEvaluation p = 0 := by
  apply (show standardChartIdeal curve ≤
      RingHom.ker standardAmbientEvaluation by
    apply Ideal.span_le.mpr
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact standardAmbientEvaluation_equation_eq_zero) hp

/-- The transformed coordinates define a map from the represented standard
Weierstrass-chart ring. -/
def standardChartToOpenRing :
    SchemeModel.rationalCuspStandardChartRing →+* openCoordinateRing := by
  change (standardAmbientChartRing ℚ ⧸ standardChartIdeal curve) →+*
    openCoordinateRing
  exact Ideal.Quotient.lift (standardChartIdeal curve)
    standardAmbientEvaluation standardAmbientEvaluation_eq_zero_of_mem

@[simp]
theorem standardChartToOpenRing_mk (a : standardAmbientChartRing ℚ) :
    standardChartToOpenRing
        (Ideal.Quotient.mk (standardChartIdeal curve) a) =
      standardAmbientEvaluation a := by
  exact Ideal.Quotient.lift_mk _ _ _

/-- The standard-chart abscissa maps to the transformed coordinate `4x`. -/
theorem standardChartToOpenRing_X :
    standardChartToOpenRing SchemeModel.rationalCuspStandardChartX =
      openCurveX := by
  change (Ideal.Quotient.lift (standardChartIdeal curve)
      standardAmbientEvaluation _)
      (Ideal.Quotient.mk (standardChartIdeal curve)
        (coordinateChartRatio (K := ℚ) 2 0)) = openCurveX
  rw [Ideal.Quotient.lift_mk]
  change curvePolynomialEvaluation
    (standardChartToAffine (coordinateChartRatio (K := ℚ) 2 0)) =
      openCurveX
  rw [standardChartToAffine_coordinateChartRatio_zero]
  simp [curvePolynomialEvaluation]

/-- The standard-chart ordinate maps to the regular transformed ordinate. -/
theorem standardChartToOpenRing_Y :
    standardChartToOpenRing
        (Ideal.Quotient.mk (standardChartIdeal curve)
          (coordinateChartRatio (K := ℚ) 2 1)) =
      openCurveY := by
  change (Ideal.Quotient.lift (standardChartIdeal curve)
      standardAmbientEvaluation _)
      (Ideal.Quotient.mk (standardChartIdeal curve)
        (coordinateChartRatio (K := ℚ) 2 1)) = openCurveY
  rw [Ideal.Quotient.lift_mk]
  change curvePolynomialEvaluation
    (standardChartToAffine (coordinateChartRatio (K := ℚ) 2 1)) =
      openCurveY
  rw [standardChartToAffine_coordinateChartRatio_one]
  simp [curvePolynomialEvaluation]

/-- The transformed target abscissa is a unit on the eta regularity domain. -/
theorem openCurveX_isUnit : IsUnit openCurveX := by
  have hfour : IsUnit (4 : openCoordinateRing) := by
    have h : IsUnit (4 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using h.map openCoefficientHom
  exact hfour.mul openX_isUnit

/-- The coordinate map extended across the target localization at `X`. -/
def affinePresentationToOpenRing :
    SchemeModel.rationalCuspAffinePresentationRing →+* openCoordinateRing :=
  IsLocalization.Away.lift SchemeModel.rationalCuspStandardChartX
    (standardChartToOpenRing_X ▸ openCurveX_isUnit)

@[simp]
theorem affinePresentationToOpenRing_algebraMap
    (a : SchemeModel.rationalCuspStandardChartRing) :
    affinePresentationToOpenRing
        (algebraMap SchemeModel.rationalCuspStandardChartRing
          SchemeModel.rationalCuspAffinePresentationRing a) =
      standardChartToOpenRing a := by
  exact IsLocalization.Away.lift_eq
    (x := SchemeModel.rationalCuspStandardChartX)
    (g := standardChartToOpenRing)
    (standardChartToOpenRing_X ▸ openCurveX_isUnit) a

/-- The scheme morphism from the eta regularity domain to the explicit
affine presentation of `D(X)`. -/
def toAffinePresentation :
    openScheme ⟶ SchemeModel.rationalCuspAffinePresentationScheme :=
  Spec.map (CommRingCat.ofHom affinePresentationToOpenRing)

/-- The scheme-level eta coordinate change into the actual
rational-cusp-avoiding open. -/
def toRationalCuspOpen :
    openScheme ⟶ SchemeModel.rationalCuspAvoidingScheme :=
  toAffinePresentation ≫ SchemeModel.rationalCuspAffinePresentationIso.hom

/-- After inclusion into the projective cubic, the eta coordinate change is
the explicit affine-presentation morphism. -/
@[reassoc]
theorem toRationalCuspOpen_comp_inclusion :
    toRationalCuspOpen ≫ SchemeModel.rationalCuspAvoidingInclusion =
      toAffinePresentation ≫ SchemeModel.rationalCuspAffinePresentationMap := by
  rw [toRationalCuspOpen, Category.assoc,
    SchemeModel.rationalCuspAffinePresentationIso_hom_comp_inclusion]

/-- The denominator-open eta-equation scheme has no rational scheme-valued
points, since it maps into the already-classified rational-cusp-avoiding
open. -/
theorem openScheme_rationalPoints_isEmpty :
    IsEmpty (Spec (.of ℚ) ⟶ openScheme) := by
  constructor
  intro g
  exact SchemeModel.rationalCuspAvoidingScheme_rationalPoints_isEmpty.false
    (g ≫ toRationalCuspOpen)

/-- Equivalently, the localized eta-equation coordinate ring admits no ring
homomorphism to `ℚ`. -/
theorem openCoordinateRing_hom_rat_isEmpty :
    IsEmpty (CommRingCat.of openCoordinateRing ⟶ CommRingCat.of ℚ) := by
  constructor
  intro f
  exact openScheme_rationalPoints_isEmpty.false (Spec.map f)

end MazurTorsion.XZeroFortyNine.EtaSchemeModel
