/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The level-35 quotient map on the cusp chart in characteristic eleven

Let `x,y` be the coordinates on the standard affine hyperelliptic model

`y² = x⁸ - 4x⁷ - 6x⁶ - 4x⁵ - 9x⁴ + 4x³ - 6x² + 4x + 1`

of `X₀(35)`.  Put `D = x² + x - 1`.  On the open chart where `D` is invertible, the rational
coordinates of the quotient by `w₅` become the regular functions

`W = (x² - 6x - 1) / D`,
`Z = (7y - D²) / (2D²)`.

This file constructs both hypersurface coordinate rings over `F₁₁`, localizes the source away
from `D`, and constructs the contravariant coordinate-ring map to the source chart.  In
particular it proves the exact identity

`W - 1 = (-7 / D) x`.

The coefficient `-7 / D` is exhibited as an actual unit of the localized source ring.  Thus the
first-order relation needed at the cusp is derived from the explicit quotient formula; no
nonvanishing or formal-immersion premise is used.

The affine model and quotient formulas are those recorded in B. Cais, "Universal Families and
Ruling out Small Primes", pp. 8--10,
<https://math.stanford.edu/~conrad/vigregroup/vigre03/kubert.pdf>, following Galbraith and Kubert.
This is bibliographic guidance only: the file verifies the algebra internally, retains no external
source text, code, or data, and is released under Apache-2.0.  Identifying a represented integral
modular curve with this explicit hypersurface remains a separate geometric obligation.
-/

noncomputable section

namespace MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven

open MvPolynomial

/-- The residue field at the auxiliary prime eleven. -/
abbrev ResidueField := ZMod 11

local instance primeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The level-35 hyperelliptic polynomial, over any commutative ring. -/
def sourcePolynomial {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 +
    4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1

/-- The polynomial on the selected elliptic quotient model. -/
def targetPolynomial {R : Type*} [CommRing R] (w : R) : R :=
  w ^ 3 + w ^ 2 + 9 * w + 1

/-- The source hypersurface equation, with `x = X 0` and `y = X 1`. -/
def sourceEquation : MvPolynomial (Fin 2) ResidueField :=
  X 1 ^ 2 - sourcePolynomial (X 0)

/-- The principal ideal defining the source hypersurface. -/
def sourceIdeal : Ideal (MvPolynomial (Fin 2) ResidueField) :=
  Ideal.span {sourceEquation}

/-- The affine source hypersurface coordinate ring over `F₁₁`. -/
abbrev SourceCoordinateRing :=
  MvPolynomial (Fin 2) ResidueField ⧸ sourceIdeal

/-- The quotient map to the source coordinate ring. -/
def sourceMk : MvPolynomial (Fin 2) ResidueField →+* SourceCoordinateRing :=
  Ideal.Quotient.mk sourceIdeal

/-- The source abscissa. -/
def sourceX : SourceCoordinateRing := sourceMk (X 0)

/-- The source ordinate. -/
def sourceY : SourceCoordinateRing := sourceMk (X 1)

/-- The checked hypersurface relation in the source coordinate ring. -/
theorem source_relation :
    sourceY ^ 2 = sourcePolynomial sourceX := by
  have hzero : sourceMk sourceEquation = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton sourceEquation)
  simpa [sourceEquation, sourceMk, sourceX, sourceY, sourcePolynomial] using
    sub_eq_zero.mp hzero

/-- The denominator which is nonzero at the cusp `x=0`. -/
def sourceDenominator : SourceCoordinateRing :=
  sourceX ^ 2 + sourceX - 1

/-- The source open chart on which the quotient formulas are regular. -/
abbrev SourceChart := Localization.Away sourceDenominator

/-- The structure map into the localized source chart. -/
def sourceChartMap : SourceCoordinateRing →+* SourceChart :=
  algebraMap SourceCoordinateRing SourceChart

/-- The local source coordinate `t=x`. -/
def t : SourceChart := sourceChartMap sourceX

/-- The source ordinate on the local chart. -/
def y : SourceChart := sourceChartMap sourceY

/-- The denominator on the local chart. -/
def D : SourceChart := sourceChartMap sourceDenominator

/-- The denominator written in the local coordinate. -/
theorem D_eq : D = t ^ 2 + t - 1 := by
  simp [D, sourceDenominator, sourceChartMap, t]

/-- The denominator is an actual unit on the localized source chart. -/
noncomputable def denominatorUnit : SourceChartˣ :=
  (IsLocalization.Away.algebraMap_isUnit sourceDenominator).unit

@[simp]
theorem denominatorUnit_val :
    (denominatorUnit : SourceChart) = D := by
  exact IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit sourceDenominator)

/-- The inverse of `D`, expressed through the checked localization unit. -/
def denominatorInverse : SourceChart :=
  (denominatorUnit⁻¹ : SourceChartˣ)

@[simp]
theorem denominator_mul_inverse :
    D * denominatorInverse = 1 := by
  change (denominatorUnit : SourceChart) * (denominatorUnit⁻¹ : SourceChartˣ) = 1
  simp

/-- Matching powers of the denominator and its inverse cancel. -/
theorem denominator_pow_mul_inverse_pow (n : ℕ) :
    D ^ n * denominatorInverse ^ n = 1 := by
  rw [← mul_pow, denominator_mul_inverse, one_pow]

/-- The source equation after passage to the open chart. -/
theorem source_relation_on_chart :
    y ^ 2 = sourcePolynomial t := by
  simpa only [sourceChartMap, y, t, sourcePolynomial, map_pow, map_sub,
    map_add, map_mul, map_one, map_ofNat] using
    congrArg sourceChartMap source_relation

/-- The regularized quotient abscissa on the source chart. -/
def quotientW : SourceChart :=
  (t ^ 2 - 6 * t - 1) * denominatorInverse

/-- The regularized quotient ordinate on the source chart.  In `F₁₁`, `6 = 1/2`. -/
def quotientZ : SourceChart :=
  6 * (7 * y - D ^ 2) * denominatorInverse ^ 2

/-- The exact quotient-coordinate identity at the cusp. -/
theorem quotientW_sub_one :
    quotientW - 1 = (-7 * denominatorInverse) * t := by
  calc
    quotientW - 1 =
        (t ^ 2 - 6 * t - 1) * denominatorInverse -
          D * denominatorInverse := by rw [quotientW, denominator_mul_inverse]
    _ = (-7 * denominatorInverse) * t := by rw [D_eq]; ring

/-- The coefficient `-7/D` in the exact first-order identity, as a unit. -/
noncomputable def cotangentScaleUnit : SourceChartˣ :=
  Units.map (algebraMap ResidueField SourceChart).toMonoidHom
      (Units.mk0 (-7 : ResidueField) (by decide)) *
    denominatorUnit⁻¹

@[simp]
theorem cotangentScaleUnit_val :
    (cotangentScaleUnit : SourceChart) = -7 * denominatorInverse := by
  simp [cotangentScaleUnit, denominatorInverse, map_ofNat]

/-- The quotient parameter `W-1` is exactly a unit multiple of the source parameter `t`. -/
theorem quotientW_sub_one_eq_unit_mul_t :
    quotientW - 1 = (cotangentScaleUnit : SourceChart) * t := by
  rw [cotangentScaleUnit_val]
  exact quotientW_sub_one

/-- The target affine hypersurface equation, with `W = X 0` and `Z = X 1`. -/
def targetEquation : MvPolynomial (Fin 2) ResidueField :=
  X 1 ^ 2 + X 1 - targetPolynomial (X 0)

/-- The principal ideal defining the target affine elliptic curve. -/
def targetIdeal : Ideal (MvPolynomial (Fin 2) ResidueField) :=
  Ideal.span {targetEquation}

/-- The affine target hypersurface coordinate ring over `F₁₁`. -/
abbrev TargetCoordinateRing :=
  MvPolynomial (Fin 2) ResidueField ⧸ targetIdeal

/-- The target coordinate `W`. -/
def targetW : TargetCoordinateRing :=
  Ideal.Quotient.mk targetIdeal (X 0)

/-- The target coordinate `Z`. -/
def targetZ : TargetCoordinateRing :=
  Ideal.Quotient.mk targetIdeal (X 1)

/-- The denominator-cleared quotient equation.  This is a polynomial identity over `F₁₁`;
the right side is four times the source hypersurface equation. -/
theorem cleared_quotient_identity :
    (6 * (7 * y - D ^ 2)) ^ 2 +
          6 * (7 * y - D ^ 2) * D ^ 2 -
        ((t ^ 2 - 6 * t - 1) ^ 3 * D +
          (t ^ 2 - 6 * t - 1) ^ 2 * D ^ 2 +
          9 * (t ^ 2 - 6 * t - 1) * D ^ 3 + D ^ 4) =
      4 * (y ^ 2 - sourcePolynomial t) := by
  rw [D_eq]
  simp only [sourcePolynomial]
  have h11 : (11 : SourceChart) = 0 := by
    rw [← map_ofNat (algebraMap ResidueField SourceChart)]
    have hbase : (11 : ResidueField) = 0 := by decide
    rw [hbase, map_zero]
  linear_combination
    (2 * t ^ 8 + 14 * t ^ 7 + 10 * t ^ 6 - 19 * t ^ 5 -
      42 * t ^ 4 * y - 7 * t ^ 4 - 84 * t ^ 3 * y + 19 * t ^ 3 +
      42 * t ^ 2 * y + 10 * t ^ 2 + 84 * t * y - 14 * t +
      160 * y ^ 2 - 42 * y + 2) * h11

/-- The two regularized quotient coordinates satisfy the target elliptic equation. -/
theorem quotient_coordinates_relation :
    quotientZ ^ 2 + quotientZ = targetPolynomial quotientW := by
  let a : SourceChart := 7 * y - D ^ 2
  let n : SourceChart := t ^ 2 - 6 * t - 1
  let e : SourceChart := denominatorInverse
  have hde4 : D ^ 4 * e ^ 4 = 1 := denominator_pow_mul_inverse_pow 4
  have hde3 : D ^ 4 * e ^ 3 = D := by
    calc
      D ^ 4 * e ^ 3 = D * (D ^ 3 * e ^ 3) := by ring
      _ = D := by rw [denominator_pow_mul_inverse_pow 3]; ring
  have hde2 : D ^ 4 * e ^ 2 = D ^ 2 := by
    calc
      D ^ 4 * e ^ 2 = D ^ 2 * (D ^ 2 * e ^ 2) := by ring
      _ = D ^ 2 := by rw [denominator_pow_mul_inverse_pow 2]; ring
  have hde1 : D ^ 4 * e = D ^ 3 := by
    calc
      D ^ 4 * e = D ^ 3 * (D * e) := by ring
      _ = D ^ 3 := by rw [denominator_mul_inverse]; ring
  have hleft :
      D ^ 4 * (quotientZ ^ 2 + quotientZ) =
        (6 * a) ^ 2 + 6 * a * D ^ 2 := by
    dsimp only [quotientZ, a, e]
    linear_combination (6 * (7 * y - D ^ 2)) ^ 2 * hde4 +
      6 * (7 * y - D ^ 2) * hde2
  have hright :
      D ^ 4 * targetPolynomial quotientW =
        n ^ 3 * D + n ^ 2 * D ^ 2 + 9 * n * D ^ 3 + D ^ 4 := by
    dsimp only [targetPolynomial, quotientW, n, e]
    linear_combination
      (t ^ 2 - 6 * t - 1) ^ 3 * hde3 +
      (t ^ 2 - 6 * t - 1) ^ 2 * hde2 +
      9 * (t ^ 2 - 6 * t - 1) * hde1
  have hnumerators :
      (6 * a) ^ 2 + 6 * a * D ^ 2 =
        n ^ 3 * D + n ^ 2 * D ^ 2 + 9 * n * D ^ 3 + D ^ 4 := by
    have h := cleared_quotient_identity
    rw [source_relation_on_chart, sub_self, mul_zero] at h
    dsimp only [a, n]
    exact sub_eq_zero.mp h
  have hD4 : IsUnit (D ^ 4) := by
    have hD : IsUnit D := by
      rw [← denominatorUnit_val]
      exact denominatorUnit.isUnit
    exact hD.pow 4
  apply hD4.mul_left_cancel
  calc
    D ^ 4 * (quotientZ ^ 2 + quotientZ) =
        (6 * a) ^ 2 + 6 * a * D ^ 2 := hleft
    _ = n ^ 3 * D + n ^ 2 * D ^ 2 + 9 * n * D ^ 3 + D ^ 4 := hnumerators
    _ = D ^ 4 * targetPolynomial quotientW := hright.symm

/-- The two images assigned to the target variables. -/
def targetCoordinates : Fin 2 → SourceChart :=
  Fin.cases quotientW (Fin.cases quotientZ Fin.elim0)

@[simp]
theorem targetCoordinates_zero : targetCoordinates 0 = quotientW := rfl

@[simp]
theorem targetCoordinates_one : targetCoordinates 1 = quotientZ := rfl

/-- Evaluation of target polynomials at the regularized quotient coordinates. -/
def targetEvaluation : MvPolynomial (Fin 2) ResidueField →+* SourceChart :=
  MvPolynomial.eval₂Hom (algebraMap ResidueField SourceChart) targetCoordinates

/-- The target equation vanishes after evaluation at the quotient coordinates. -/
theorem targetEvaluation_equation :
    targetEvaluation targetEquation = 0 := by
  simpa [targetEvaluation, targetEquation, targetPolynomial] using
    sub_eq_zero.mpr quotient_coordinates_relation

/-- The contravariant coordinate-ring map from the target hypersurface to the localized
level-35 source chart. -/
noncomputable def quotientCoordinateMap : TargetCoordinateRing →+* SourceChart :=
  Ideal.Quotient.lift targetIdeal targetEvaluation (by
    intro p hp
    have hle : targetIdeal ≤ RingHom.ker targetEvaluation := by
      rw [targetIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact targetEvaluation_equation
    exact RingHom.mem_ker.mp (hle hp))

@[simp]
theorem quotientCoordinateMap_targetW :
    quotientCoordinateMap targetW = quotientW := by
  simp [quotientCoordinateMap, targetW, targetEvaluation]

@[simp]
theorem quotientCoordinateMap_targetZ :
    quotientCoordinateMap targetZ = quotientZ := by
  simp [quotientCoordinateMap, targetZ, targetEvaluation]

/-- The exact identity stated intrinsically as the pullback of the target parameter `W-1`. -/
theorem quotientCoordinateMap_targetW_sub_one :
    quotientCoordinateMap (targetW - 1) =
      (cotangentScaleUnit : SourceChart) * t := by
  rw [map_sub, quotientCoordinateMap_targetW, map_one,
    quotientW_sub_one_eq_unit_mul_t]

end MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven
