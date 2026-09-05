/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.XZeroFortyNineEtaScheme

/-!
# The eta chart as an open of the represented level-49 cubic

The scheme-level eta coordinate change constructed in
`XZeroFortyNineEtaScheme` lands in the explicit `D(X)` chart.  This file
computes its exact geometric image.  On the target chart put

`x = X / 4`,  `d = x² + 7x + 7`.

After localizing at `d`, the inverse ordinate is

`y = (Yd + 28x(x² + 5x + 7)) / 8`.

The two coordinate maps are inverse ring homomorphisms.  Consequently the
eta regularity domain `D(x(x² + 7x + 7))` is isomorphic to the target open
`D(d)` inside the explicit presentation of `D(X)`.  In particular, the
previously constructed eta-to-`D(X)` morphism is an open immersion whose
range is exactly this open.

The design boundary remains equation-side: this proves no modular
interpretation of the eta coordinates and constructs no eta functions on a
coarse modular curve.  The named downstream consumer is
`toRationalCuspOpen_opensRange`, which records the exact target open that a
future modular eta comparison must reach.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

namespace MazurTorsion.XZeroFortyNine.EtaSchemeModel

private theorem inverseCoordinateEquation
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (X Y : R) (h : Y ^ 2 = X * (X ^ 2 + 21 * X + 112)) :
    let x := algebraMap ℚ R (1 / 4) * X
    let d := x ^ 2 + 7 * x + 7
    let y := algebraMap ℚ R (1 / 8) *
      (Y * d + 28 * x * (x ^ 2 + 5 * x + 7))
    equationExpression x y = 0 := by
  dsimp only
  rw [show equationExpression
      (algebraMap ℚ R (1 / 4) * X)
      (algebraMap ℚ R (1 / 8) *
        (Y * ((algebraMap ℚ R (1 / 4) * X) ^ 2 +
            7 * (algebraMap ℚ R (1 / 4) * X) + 7) +
          28 * (algebraMap ℚ R (1 / 4) * X) *
            ((algebraMap ℚ R (1 / 4) * X) ^ 2 +
              5 * (algebraMap ℚ R (1 / 4) * X) + 7))) =
        algebraMap ℚ R (1 / 64) *
          ((algebraMap ℚ R (1 / 4) * X) ^ 2 +
            7 * (algebraMap ℚ R (1 / 4) * X) + 7) ^ 2 *
          (Y ^ 2 - X * (X ^ 2 + 21 * X + 112)) by
    unfold equationExpression
    algebra with ℚ]
  rw [sub_eq_zero.mpr h, mul_zero]

private def targetStandardX : standardAffineChartCoordinateRing curve :=
  Ideal.Quotient.mk (standardChartIdeal curve)
    (coordinateChartRatio (K := ℚ) 2 0)

private def targetStandardY : standardAffineChartCoordinateRing curve :=
  Ideal.Quotient.mk (standardChartIdeal curve)
    (coordinateChartRatio (K := ℚ) 2 1)

private def targetStandardYForPresentation :
    SchemeModel.rationalCuspStandardChartRing := by
  change standardAffineChartCoordinateRing curve
  exact targetStandardY

private def targetAffineX : affineWeierstrassCoordinateRing curve :=
  Ideal.Quotient.mk (Ideal.span {curve.toAffine.polynomial})
    (Polynomial.C Polynomial.X)

private def targetAffineY : affineWeierstrassCoordinateRing curve :=
  Ideal.Quotient.mk (Ideal.span {curve.toAffine.polynomial}) Polynomial.X

private theorem targetAffine_equation :
    targetAffineY ^ 2 =
      targetAffineX * (targetAffineX ^ 2 + 21 * targetAffineX + 112) := by
  have h : Ideal.Quotient.mk (Ideal.span {curve.toAffine.polynomial})
      curve.toAffine.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton curve.toAffine.polynomial))
  norm_num [curve, WeierstrassCurve.Affine.polynomial] at h
  simp only [map_ofNat] at h
  unfold targetAffineX targetAffineY
  linear_combination h

private theorem targetAffine_equiv_X :
    affineEquationToStandardChartRingEquiv curve targetAffineX =
      targetStandardX := by
  change Ideal.Quotient.mk (standardChartIdeal curve)
      (affineToStandardChart (Polynomial.C Polynomial.X)) =
    Ideal.Quotient.mk (standardChartIdeal curve)
      (coordinateChartRatio (K := ℚ) 2 0)
  rw [affineToStandardChart_C_X]

private theorem targetAffine_equiv_Y :
    affineEquationToStandardChartRingEquiv curve targetAffineY =
      targetStandardY := by
  change Ideal.Quotient.mk (standardChartIdeal curve)
      (affineToStandardChart Polynomial.X) =
    Ideal.Quotient.mk (standardChartIdeal curve)
      (coordinateChartRatio (K := ℚ) 2 1)
  rw [affineToStandardChart_X]

private theorem targetStandard_equation :
    targetStandardY ^ 2 =
      targetStandardX *
        (targetStandardX ^ 2 + 21 * targetStandardX + 112) := by
  let e := affineEquationToStandardChartRingEquiv curve
  have e21 : e (21 : affineWeierstrassCoordinateRing curve) = 21 := by
    simpa using map_ofNat e 21
  have e112 : e (112 : affineWeierstrassCoordinateRing curve) = 112 := by
    simpa using map_ofNat e 112
  calc
    targetStandardY ^ 2 = (e targetAffineY) ^ 2 := by
      rw [targetAffine_equiv_Y]
    _ = e (targetAffineY ^ 2) := by rw [map_pow]
    _ = e (targetAffineX *
        (targetAffineX ^ 2 + 21 * targetAffineX + 112)) := by
      rw [targetAffine_equation]
    _ = e targetAffineX *
        (e targetAffineX ^ 2 + 21 * e targetAffineX + 112) := by
      rw [map_mul, map_add, map_add, map_pow, map_mul, e21, e112]
    _ = targetStandardX *
        (targetStandardX ^ 2 + 21 * targetStandardX + 112) := by
      rw [targetAffine_equiv_X]

private theorem targetStandardForPresentation_equation :
    targetStandardYForPresentation ^ 2 =
      SchemeModel.rationalCuspStandardChartX *
        (SchemeModel.rationalCuspStandardChartX ^ 2 +
          21 * SchemeModel.rationalCuspStandardChartX + 112) := by
  exact targetStandard_equation

private abbrev targetRing :=
  SchemeModel.rationalCuspAffinePresentationRing

private def targetStandardCoefficientHom :
    ℚ →+* SchemeModel.rationalCuspStandardChartRing :=
  coveringChartStructureRingHom curve true

private def targetCoefficientHom : ℚ →+* targetRing :=
  (algebraMap SchemeModel.rationalCuspStandardChartRing targetRing).comp
    targetStandardCoefficientHom

private instance targetRing_algebra_rat : Algebra ℚ targetRing :=
  targetCoefficientHom.toAlgebra

private def targetX : targetRing :=
  algebraMap SchemeModel.rationalCuspStandardChartRing targetRing
    SchemeModel.rationalCuspStandardChartX

private def targetY : targetRing :=
  algebraMap SchemeModel.rationalCuspStandardChartRing targetRing
    targetStandardYForPresentation

private theorem targetY_sq :
    targetY ^ 2 = targetX * (targetX ^ 2 + 21 * targetX + 112) := by
  have h := congrArg (algebraMap
    SchemeModel.rationalCuspStandardChartRing targetRing)
    targetStandardForPresentation_equation
  simpa only [targetX, targetY, map_pow, map_mul, map_add, map_ofNat] using h

private theorem targetX_isUnit : IsUnit targetX :=
  IsLocalization.map_units targetRing
    (⟨SchemeModel.rationalCuspStandardChartX, by simp⟩ :
      Submonoid.powers SchemeModel.rationalCuspStandardChartX)

/-- The eta abscissa `x = X / 4` in the explicit target `D(X)` coordinate
ring. -/
def targetEtaX : SchemeModel.rationalCuspAffinePresentationRing :=
  targetCoefficientHom (1 / 4) * targetX

/-- The target-side quadratic denominator expressed in the eta abscissa. -/
def targetDenominator : SchemeModel.rationalCuspAffinePresentationRing :=
  targetEtaX ^ 2 + 7 * targetEtaX + 7

/-- The coordinate ring of the exact target image, obtained by inverting the
eta coordinate-change denominator inside the explicit `D(X)` chart. -/
abbrev targetOpenRing := Localization.Away targetDenominator

private def targetOpenCoefficientHom : ℚ →+* targetOpenRing :=
  (algebraMap targetRing targetOpenRing).comp targetCoefficientHom

private instance targetOpenRing_algebra_rat : Algebra ℚ targetOpenRing :=
  targetOpenCoefficientHom.toAlgebra

private theorem targetOpenCoefficientHom_eq_algebraMap :
    targetOpenCoefficientHom = algebraMap ℚ targetOpenRing := by
  rfl

private def targetOpenX : targetOpenRing :=
  algebraMap targetRing targetOpenRing targetX

private def targetOpenY : targetOpenRing :=
  algebraMap targetRing targetOpenRing targetY

private def inverseX : targetOpenRing :=
  targetOpenCoefficientHom (1 / 4) * targetOpenX

private def inverseDenominator : targetOpenRing :=
  inverseX ^ 2 + 7 * inverseX + 7

private def inverseY : targetOpenRing :=
  targetOpenCoefficientHom (1 / 8) *
    (targetOpenY * inverseDenominator +
      28 * inverseX * (inverseX ^ 2 + 5 * inverseX + 7))

private theorem inverseX_eq_map_targetEtaX :
    inverseX = algebraMap targetRing targetOpenRing targetEtaX := by
  simp only [inverseX, targetEtaX, targetOpenX,
    (algebraMap targetRing targetOpenRing).map_mul,
    targetOpenCoefficientHom, RingHom.coe_comp, Function.comp_apply]

private theorem inverseDenominator_eq_map :
    inverseDenominator =
      algebraMap targetRing targetOpenRing targetDenominator := by
  calc
    inverseDenominator =
        (algebraMap targetRing targetOpenRing targetEtaX) ^ 2 +
          7 * algebraMap targetRing targetOpenRing targetEtaX + 7 := by
      rw [inverseDenominator, inverseX_eq_map_targetEtaX]
    _ = algebraMap targetRing targetOpenRing
        (targetEtaX ^ 2 + 7 * targetEtaX + 7) := by
      simp only [(algebraMap targetRing targetOpenRing).map_add,
        (algebraMap targetRing targetOpenRing).map_mul,
        (algebraMap targetRing targetOpenRing).map_pow,
        map_ofNat (algebraMap targetRing targetOpenRing) 7]
    _ = algebraMap targetRing targetOpenRing targetDenominator := by
      rfl

private theorem inverseDenominator_isUnit : IsUnit inverseDenominator := by
  rw [inverseDenominator_eq_map]
  exact IsLocalization.map_units targetOpenRing
    (⟨targetDenominator, by simp⟩ : Submonoid.powers targetDenominator)

private theorem inverseX_isUnit : IsUnit inverseX := by
  rw [inverseX_eq_map_targetEtaX, targetEtaX,
    (algebraMap targetRing targetOpenRing).map_mul]
  apply IsUnit.mul
  · have h : IsUnit (targetOpenCoefficientHom (1 / 4)) :=
      (isUnit_iff_ne_zero.mpr (by norm_num : (1 / 4 : ℚ) ≠ 0)).map
        targetOpenCoefficientHom
    exact h
  · exact targetX_isUnit.map (algebraMap targetRing targetOpenRing)

private theorem inverseY_etaEquation :
    equationExpression inverseX inverseY = 0 := by
  have hcurve : targetOpenY ^ 2 =
      targetOpenX * (targetOpenX ^ 2 + 21 * targetOpenX + 112) := by
    have h := congrArg (algebraMap targetRing targetOpenRing) targetY_sq
    simpa only [targetOpenY, targetOpenX,
      (algebraMap targetRing targetOpenRing).map_pow,
      (algebraMap targetRing targetOpenRing).map_mul,
      (algebraMap targetRing targetOpenRing).map_add,
      map_ofNat (algebraMap targetRing targetOpenRing) 21,
      map_ofNat (algebraMap targetRing targetOpenRing) 112] using h
  have h := inverseCoordinateEquation targetOpenX targetOpenY hcurve
  rw [← targetOpenCoefficientHom_eq_algebraMap] at h
  simpa only [inverseX, inverseDenominator, inverseY] using h

private def etaPolynomialEvaluation :
    MvPolynomial (Fin 2) ℚ →+* targetOpenRing :=
  MvPolynomial.eval₂Hom targetOpenCoefficientHom ![inverseX, inverseY]

private theorem etaPolynomialEvaluation_eq_zero :
    etaPolynomialEvaluation polynomial = 0 := by
  simpa [etaPolynomialEvaluation, polynomial, equationExpression] using
    inverseY_etaEquation

private theorem etaPolynomialEvaluation_eq_zero_of_mem
    (p : MvPolynomial (Fin 2) ℚ) (hp : p ∈ ideal) :
    etaPolynomialEvaluation p = 0 := by
  apply (show ideal ≤ RingHom.ker etaPolynomialEvaluation by
    apply Ideal.span_le.mpr
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact etaPolynomialEvaluation_eq_zero) hp

private def coordinateRingToTargetOpen :
    coordinateRing →+* targetOpenRing :=
  Ideal.Quotient.lift ideal etaPolynomialEvaluation
    etaPolynomialEvaluation_eq_zero_of_mem

@[simp]
private theorem coordinateRingToTargetOpen_x :
    coordinateRingToTargetOpen x = inverseX := by
  simp [coordinateRingToTargetOpen, etaPolynomialEvaluation, x]

@[simp]
private theorem coordinateRingToTargetOpen_y :
    coordinateRingToTargetOpen y = inverseY := by
  simp [coordinateRingToTargetOpen, etaPolynomialEvaluation, y]

private theorem coordinateRingToTargetOpen_denominator :
    coordinateRingToTargetOpen denominator = inverseDenominator := by
  simp only [denominator, coordinateRingToTargetOpen.map_add,
    coordinateRingToTargetOpen.map_mul, coordinateRingToTargetOpen.map_pow,
    map_ofNat coordinateRingToTargetOpen 7,
    coordinateRingToTargetOpen_x, inverseDenominator]

private theorem coordinateRingToTargetOpen_openElement :
    coordinateRingToTargetOpen openElement =
      inverseX * inverseDenominator := by
  simp only [openElement, coordinateRingToTargetOpen.map_mul,
    coordinateRingToTargetOpen_x,
    coordinateRingToTargetOpen_denominator]

private def sourceToTargetOpen : openCoordinateRing →+* targetOpenRing :=
  IsLocalization.Away.lift openElement
    (coordinateRingToTargetOpen_openElement ▸
      inverseX_isUnit.mul inverseDenominator_isUnit)

@[simp]
private theorem sourceToTargetOpen_algebraMap (a : coordinateRing) :
    sourceToTargetOpen (algebraMap coordinateRing openCoordinateRing a) =
      coordinateRingToTargetOpen a := by
  exact IsLocalization.Away.lift_eq
    (x := openElement) (g := coordinateRingToTargetOpen)
    (coordinateRingToTargetOpen_openElement ▸
      inverseX_isUnit.mul inverseDenominator_isUnit) a

@[simp]
private theorem sourceToTargetOpen_openX :
    sourceToTargetOpen openX = inverseX := by
  rw [openX, sourceToTargetOpen_algebraMap, coordinateRingToTargetOpen_x]

@[simp]
private theorem sourceToTargetOpen_openY :
    sourceToTargetOpen openY = inverseY := by
  rw [openY, sourceToTargetOpen_algebraMap, coordinateRingToTargetOpen_y]

private def targetToSourceRing : targetRing →+* openCoordinateRing := by
  exact affinePresentationToOpenRing

private theorem targetToSourceRing_X :
    targetToSourceRing targetX = openCurveX := by
  change affinePresentationToOpenRing
      (algebraMap SchemeModel.rationalCuspStandardChartRing
        SchemeModel.rationalCuspAffinePresentationRing
        SchemeModel.rationalCuspStandardChartX) = openCurveX
  rw [affinePresentationToOpenRing_algebraMap, standardChartToOpenRing_X]

private theorem targetToSourceRing_Y :
    targetToSourceRing targetY = openCurveY := by
  change affinePresentationToOpenRing
      (algebraMap SchemeModel.rationalCuspStandardChartRing
        SchemeModel.rationalCuspAffinePresentationRing
        targetStandardYForPresentation) = openCurveY
  rw [affinePresentationToOpenRing_algebraMap]
  change standardChartToOpenRing
      (Ideal.Quotient.mk (standardChartIdeal curve)
        (coordinateChartRatio (K := ℚ) 2 1)) = openCurveY
  exact standardChartToOpenRing_Y

private theorem targetToSourceRing_coefficient (a : ℚ) :
    targetToSourceRing (targetCoefficientHom a) = openCoefficientHom a := by
  have h : targetToSourceRing.comp targetCoefficientHom =
      openCoefficientHom := Subsingleton.elim _ _
  exact DFunLike.congr_fun h a

private theorem targetToSourceRing_targetEtaX :
    targetToSourceRing targetEtaX = openX := by
  rw [targetEtaX, targetToSourceRing.map_mul,
    targetToSourceRing_coefficient,
    targetToSourceRing_X, openCoefficientHom_eq_algebraMap]
  unfold openCurveX
  algebra with ℚ

private theorem targetToSourceRing_denominator :
    targetToSourceRing targetDenominator = openDenominator := by
  rw [targetDenominator, targetToSourceRing.map_add,
    targetToSourceRing.map_add, targetToSourceRing.map_pow,
    targetToSourceRing.map_mul, map_ofNat targetToSourceRing 7,
    targetToSourceRing_targetEtaX, openDenominator_eq]

private def targetOpenToSource : targetOpenRing →+* openCoordinateRing :=
  IsLocalization.Away.lift targetDenominator
    (targetToSourceRing_denominator ▸ openDenominator_isUnit)

@[simp]
private theorem targetOpenToSource_algebraMap (a : targetRing) :
    targetOpenToSource (algebraMap targetRing targetOpenRing a) =
      targetToSourceRing a := by
  exact IsLocalization.Away.lift_eq
    (x := targetDenominator) (g := targetToSourceRing)
    (targetToSourceRing_denominator ▸ openDenominator_isUnit) a

@[simp]
private theorem targetOpenToSource_targetOpenX :
    targetOpenToSource targetOpenX = openCurveX := by
  rw [targetOpenX, targetOpenToSource_algebraMap, targetToSourceRing_X]

@[simp]
private theorem targetOpenToSource_targetOpenY :
    targetOpenToSource targetOpenY = openCurveY := by
  rw [targetOpenY, targetOpenToSource_algebraMap, targetToSourceRing_Y]

private theorem targetOpenToSource_coefficient (a : ℚ) :
    targetOpenToSource (targetOpenCoefficientHom a) =
      openCoefficientHom a := by
  have h : targetOpenToSource.comp targetOpenCoefficientHom =
      openCoefficientHom := Subsingleton.elim _ _
  exact DFunLike.congr_fun h a

private theorem targetOpenToSource_inverseX :
    targetOpenToSource inverseX = openX := by
  rw [inverseX_eq_map_targetEtaX, targetOpenToSource_algebraMap,
    targetToSourceRing_targetEtaX]

private theorem targetOpenToSource_inverseDenominator :
    targetOpenToSource inverseDenominator = openDenominator := by
  rw [inverseDenominator_eq_map, targetOpenToSource_algebraMap,
    targetToSourceRing_denominator]

private theorem targetOpenToSource_inverseY :
    targetOpenToSource inverseY = openY := by
  simp only [inverseY, targetOpenToSource.map_mul,
    targetOpenToSource.map_add, targetOpenToSource.map_pow,
    map_ofNat targetOpenToSource 28,
    map_ofNat targetOpenToSource 5, map_ofNat targetOpenToSource 7,
    targetOpenToSource_coefficient,
    targetOpenToSource_targetOpenY,
    targetOpenToSource_inverseDenominator,
    targetOpenToSource_inverseX,
    openCoefficientHom_eq_algebraMap]
  unfold openCurveY
  calc
    algebraMap ℚ openCoordinateRing (1 / 8) *
        (((8 * openY - 28 * openX * (openX ^ 2 + 5 * openX + 7)) *
            openDenominatorInverse) * openDenominator +
          28 * openX * (openX ^ 2 + 5 * openX + 7)) =
      algebraMap ℚ openCoordinateRing (1 / 8) *
        ((8 * openY - 28 * openX * (openX ^ 2 + 5 * openX + 7)) *
            (openDenominator * openDenominatorInverse) +
          28 * openX * (openX ^ 2 + 5 * openX + 7)) := by ring
    _ = algebraMap ℚ openCoordinateRing (1 / 8) *
        ((8 * openY - 28 * openX * (openX ^ 2 + 5 * openX + 7)) +
          28 * openX * (openX ^ 2 + 5 * openX + 7)) := by
      rw [openDenominator_mul_inverse, mul_one]
    _ = openY := by algebra with ℚ

private theorem sourceToTargetOpen_coefficient (a : ℚ) :
    sourceToTargetOpen (openCoefficientHom a) =
      targetOpenCoefficientHom a := by
  have h : sourceToTargetOpen.comp openCoefficientHom =
      targetOpenCoefficientHom := Subsingleton.elim _ _
  exact DFunLike.congr_fun h a

private theorem sourceToTargetOpen_openCurveX :
    sourceToTargetOpen openCurveX = targetOpenX := by
  rw [openCurveX, sourceToTargetOpen.map_mul,
    map_ofNat sourceToTargetOpen 4, sourceToTargetOpen_openX]
  unfold inverseX
  rw [targetOpenCoefficientHom_eq_algebraMap]
  algebra with ℚ

private theorem sourceToTargetOpen_openDenominator :
    sourceToTargetOpen openDenominator = inverseDenominator := by
  rw [openDenominator_eq, sourceToTargetOpen.map_add,
    sourceToTargetOpen.map_add, sourceToTargetOpen.map_pow,
    sourceToTargetOpen.map_mul, map_ofNat sourceToTargetOpen 7,
    sourceToTargetOpen_openX]
  rfl

private theorem sourceToTargetOpen_denominatorInverse_mul :
    sourceToTargetOpen openDenominatorInverse * inverseDenominator = 1 := by
  have h := congrArg sourceToTargetOpen openDenominator_mul_inverse
  rw [sourceToTargetOpen.map_mul, sourceToTargetOpen.map_one,
    sourceToTargetOpen_openDenominator] at h
  calc
    sourceToTargetOpen openDenominatorInverse * inverseDenominator =
        inverseDenominator * sourceToTargetOpen openDenominatorInverse := by
      ring
    _ = 1 := h

private theorem sourceToTargetOpen_openCurveY :
    sourceToTargetOpen openCurveY = targetOpenY := by
  have hnum :
      8 * inverseY - 28 * inverseX *
          (inverseX ^ 2 + 5 * inverseX + 7) =
        targetOpenY * inverseDenominator := by
    unfold inverseY
    rw [targetOpenCoefficientHom_eq_algebraMap]
    algebra with ℚ
  simp only [openCurveY, sourceToTargetOpen.map_mul,
    sourceToTargetOpen.map_sub, sourceToTargetOpen.map_add,
    sourceToTargetOpen.map_pow,
    map_ofNat sourceToTargetOpen 8, map_ofNat sourceToTargetOpen 28,
    map_ofNat sourceToTargetOpen 5, map_ofNat sourceToTargetOpen 7,
    sourceToTargetOpen_openX, sourceToTargetOpen_openY, hnum]
  calc
    targetOpenY * inverseDenominator *
        sourceToTargetOpen openDenominatorInverse =
      targetOpenY *
        (sourceToTargetOpen openDenominatorInverse * inverseDenominator) := by
      ring
    _ = targetOpenY := by
      rw [sourceToTargetOpen_denominatorInverse_mul, mul_one]

private theorem targetOpenToSource_comp_sourceToTargetOpen :
    targetOpenToSource.comp sourceToTargetOpen = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers openElement)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change targetOpenToSource
        (sourceToTargetOpen (openCoefficientHom a)) =
      openCoefficientHom a
    rw [sourceToTargetOpen_coefficient, targetOpenToSource_coefficient]
  · intro i
    fin_cases i
    · change targetOpenToSource (sourceToTargetOpen openX) = openX
      rw [sourceToTargetOpen_openX, targetOpenToSource_inverseX]
    · change targetOpenToSource (sourceToTargetOpen openY) = openY
      rw [sourceToTargetOpen_openY, targetOpenToSource_inverseY]

private theorem sourceToTargetOpen_comp_targetOpenToSource :
    sourceToTargetOpen.comp targetOpenToSource = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers targetDenominator)
  apply IsLocalization.ringHom_ext
    (Submonoid.powers SchemeModel.rationalCuspStandardChartX)
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := ℚ) (coveringCoordinate true)
  · ext a
    change sourceToTargetOpen
        (targetOpenToSource (targetOpenCoefficientHom a)) =
      targetOpenCoefficientHom a
    rw [targetOpenToSource_coefficient, sourceToTargetOpen_coefficient]
  · intro j
    fin_cases j
    · change sourceToTargetOpen
          (targetOpenToSource targetOpenX) = targetOpenX
      rw [targetOpenToSource_targetOpenX, sourceToTargetOpen_openCurveX]
    · change sourceToTargetOpen
          (targetOpenToSource targetOpenY) = targetOpenY
      rw [targetOpenToSource_targetOpenY, sourceToTargetOpen_openCurveY]
    · rw [show (⟨2, by omega⟩ : Fin 3) = coveringCoordinate true by rfl]
      rw [coordinateChartRatio_self]
      simp

/-- The localized eta-equation ring is explicitly isomorphic to the target
`D(d)` coordinate ring. -/
def openRingEquivTargetOpen : openCoordinateRing ≃+* targetOpenRing :=
  RingEquiv.ofRingHom sourceToTargetOpen targetOpenToSource
    sourceToTargetOpen_comp_targetOpenToSource
    targetOpenToSource_comp_sourceToTargetOpen

private instance openCoordinateRing_algebra_targetRing :
    Algebra targetRing openCoordinateRing :=
  targetToSourceRing.toAlgebra

private def targetOpenAlgEquivSource :
    targetOpenRing ≃ₐ[targetRing] openCoordinateRing where
  __ := openRingEquivTargetOpen.symm
  commutes' := targetOpenToSource_algebraMap

private instance openCoordinateRing_isLocalization_targetDenominator :
    IsLocalization.Away targetDenominator openCoordinateRing :=
  IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers targetDenominator) targetOpenAlgEquivSource

/-- The target-side denominator-open affine scheme. -/
abbrev targetOpenScheme : Scheme := Spec (.of targetOpenRing)

/-- The principal open `D(d)` inside the explicit affine presentation of
the rational-cusp-avoiding locus. -/
def targetDenominatorOpen :
    SchemeModel.rationalCuspAffinePresentationScheme.Opens := by
  change (Spec (.of targetRing)).Opens
  exact PrimeSpectrum.basicOpen targetDenominator

/-- The localization morphism from `D(d)` into the explicit `D(X)`
presentation. -/
def targetOpenInclusion :
    targetOpenScheme ⟶ SchemeModel.rationalCuspAffinePresentationScheme := by
  change Spec (.of targetOpenRing) ⟶ Spec (.of targetRing)
  exact Spec.map (CommRingCat.ofHom
    (algebraMap targetRing targetOpenRing))

instance targetOpenInclusion_isOpenImmersion :
    IsOpenImmersion targetOpenInclusion := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap targetRing targetOpenRing)))
  infer_instance

/-- The target localization has exactly the principal-open range `D(d)`. -/
theorem targetOpenInclusion_opensRange :
    targetOpenInclusion.opensRange = targetDenominatorOpen := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap targetRing targetOpenRing))).opensRange =
    PrimeSpectrum.basicOpen targetDenominator
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of targetRing) targetDenominator

/-- The eta regularity domain is isomorphic to the target denominator-open
scheme. -/
def openSchemeIsoTargetOpen : openScheme ≅ targetOpenScheme :=
  Scheme.Spec.mapIso
    openRingEquivTargetOpen.toCommRingCatIso.symm.op

/-- The open-scheme isomorphism followed by target inclusion is the original
eta coordinate morphism. -/
@[reassoc]
theorem openSchemeIsoTargetOpen_hom_comp_inclusion :
    openSchemeIsoTargetOpen.hom ≫ targetOpenInclusion =
      toAffinePresentation := by
  change Spec.map (CommRingCat.ofHom targetOpenToSource) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap targetRing targetOpenRing)) =
    Spec.map (CommRingCat.ofHom targetToSourceRing)
  rw [← Spec.map_comp, Spec.map_inj]
  ext a
  exact targetOpenToSource_algebraMap a

instance toAffinePresentation_isOpenImmersion :
    IsOpenImmersion toAffinePresentation := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap targetRing openCoordinateRing)))
  exact IsOpenImmersion.of_isLocalization (S := openCoordinateRing)
    targetDenominator

instance toRationalCuspOpen_isOpenImmersion :
    IsOpenImmersion toRationalCuspOpen := by
  dsimp only [toRationalCuspOpen]
  infer_instance

/-- The eta morphism into the explicit affine presentation has exact range
`D(d)`. -/
theorem toAffinePresentation_opensRange :
    toAffinePresentation.opensRange = targetDenominatorOpen := by
  have hrange : toAffinePresentation.opensRange =
      targetOpenInclusion.opensRange := by
    apply SetLike.ext'
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange,
      ← openSchemeIsoTargetOpen_hom_comp_inclusion]
    ext p
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨openSchemeIsoTargetOpen.hom q, hq⟩
    · rintro ⟨q, hq⟩
      obtain ⟨p, hp⟩ := openSchemeIsoTargetOpen.hom.surjective q
      refine ⟨p, ?_⟩
      simpa [hp] using hq
  exact hrange.trans targetOpenInclusion_opensRange

/-- In the actual rational-cusp-avoiding subscheme, the eta morphism has the
image of `D(d)` under the explicit-presentation isomorphism. -/
theorem toRationalCuspOpen_opensRange :
    toRationalCuspOpen.opensRange =
      SchemeModel.rationalCuspAffinePresentationIso.hom ''ᵁ
        targetDenominatorOpen := by
  change (toAffinePresentation ≫
    SchemeModel.rationalCuspAffinePresentationIso.hom).opensRange = _
  rw [Scheme.Hom.opensRange_comp,
    toAffinePresentation_opensRange]

end MazurTorsion.XZeroFortyNine.EtaSchemeModel
