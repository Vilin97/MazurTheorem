/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Polynomial.RingDivision
import MazurTorsion.NumberTheory.XOneThirteenMumfordCoordinates

/-!
# Explicit two-point Mumford composition for `X₁(13)`

This file extends the existing normalized rational `AffineMumford` interface
for the fixed genus-two model

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

No divisor-class quotient or general Jacobian library is introduced.  The
main operation-level result is `AffineMumford.ofDistinctPoints`: two affine
curve points with distinct abscissae produce a genuine normalized quadratic
Mumford record.  Its support is `(X-x₁)(X-x₂)` and its ordinate is the explicit
interpolation line.

The construction factors through `coprime_support_product_dvd`, the
polynomial certificate behind coprime Cantor composition.  A converse to the
existing symbolic division certificate then exposes the two scalar remainder
equalities required by coefficientwise finite-field verification.

The next operation-level obligation is separate and explicit: handle shared
support (including tangent doubling), then reduce a coprime product of two
quadratic supports from degree four back to degree at most two.  Neither step
is claimed here.
-/

namespace MazurTorsion.XOneThirteenMumford

open Polynomial

noncomputable section

namespace AffineMumford

/-! ## Coprime-support polynomial composition -/

/-- A polynomial congruent to an ordinate modulo a support polynomial has
the same square modulo that support. -/
private theorem dvd_square_sub_square_of_dvd_sub
    (u w v : ℚ[X]) (h : u ∣ w - v) : u ∣ w ^ 2 - v ^ 2 := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q * (w + v), ?_⟩
  calc
    w ^ 2 - v ^ 2 = (w - v) * (w + v) := by ring
    _ = (u * q) * (w + v) := by rw [hq]
    _ = u * (q * (w + v)) := by ring

/-- Coprime-support composition at the polynomial-certificate level.

If `w` interpolates the two ordinate polynomials modulo coprime supports,
then the product support divides `f - w²`.  This is the algebraic closure step
of coprime Cantor composition, before any degree reduction. -/
theorem coprime_support_product_dvd
    (D E : AffineMumford) (w : ℚ[X])
    (hcoprime : IsCoprime D.u E.u)
    (hD : D.u ∣ w - D.v) (hE : E.u ∣ w - E.v) :
    D.u * E.u ∣ sexticPolynomial - w ^ 2 := by
  have hDsquare : D.u ∣ w ^ 2 - D.v ^ 2 :=
    dvd_square_sub_square_of_dvd_sub D.u w D.v hD
  have hEsquare : E.u ∣ w ^ 2 - E.v ^ 2 :=
    dvd_square_sub_square_of_dvd_sub E.u w E.v hE
  have hDtarget : D.u ∣ sexticPolynomial - w ^ 2 := by
    convert D.equation_mod_u.sub hDsquare using 1
    all_goals ring
  have hEtarget : E.u ∣ sexticPolynomial - w ^ 2 := by
    convert E.equation_mod_u.sub hEsquare using 1
    all_goals ring
  exact hcoprime.mul_dvd hDtarget hEtarget

/-! ## Explicit interpolation of two distinct points -/

/-- Slope of the line through two points with distinct abscissae. -/
def interpolationSlope (x₁ y₁ x₂ y₂ : ℚ) : ℚ :=
  (y₁ - y₂) / (x₁ - x₂)

/-- Constant coefficient of the line through two points. -/
def interpolationConstant (x₁ y₁ x₂ y₂ : ℚ) : ℚ :=
  (x₁ * y₂ - x₂ * y₁) / (x₁ - x₂)

/-- The explicit line through two affine points. -/
def interpolationLine (x₁ y₁ x₂ y₂ : ℚ) : ℚ[X] :=
  C (interpolationSlope x₁ y₁ x₂ y₂) * X +
    C (interpolationConstant x₁ y₁ x₂ y₂)

/-- The interpolation line has the prescribed value at its first point. -/
theorem eval_interpolationLine_left
    (x₁ y₁ x₂ y₂ : ℚ) (hx : x₁ ≠ x₂) :
    (interpolationLine x₁ y₁ x₂ y₂).eval x₁ = y₁ := by
  simp only [interpolationLine, interpolationSlope, interpolationConstant,
    eval_add, eval_mul, eval_C, eval_X]
  field_simp [sub_ne_zero.mpr hx]
  ring

/-- The interpolation line has the prescribed value at its second point. -/
theorem eval_interpolationLine_right
    (x₁ y₁ x₂ y₂ : ℚ) (hx : x₁ ≠ x₂) :
    (interpolationLine x₁ y₁ x₂ y₂).eval x₂ = y₂ := by
  simp only [interpolationLine, interpolationSlope, interpolationConstant,
    eval_add, eval_mul, eval_C, eval_X]
  field_simp [sub_ne_zero.mpr hx]
  ring

/-- A linear factor divides the difference between the interpolation line and
the corresponding constant ordinate. -/
private theorem point_factor_dvd_interpolation_sub
    (x₁ y₁ x₂ y₂ x y : ℚ)
    (heval : (interpolationLine x₁ y₁ x₂ y₂).eval x = y) :
    X - C x ∣ interpolationLine x₁ y₁ x₂ y₂ - C y := by
  rw [dvd_iff_isRoot]
  simp only [IsRoot, eval_sub, eval_C, heval, sub_self]

/-- Compose two affine points with distinct abscissae into normalized
degree-two Mumford data.

The pointwise curve equations give divisibility by the two linear supports;
their coprimality gives divisibility by the monic quadratic product. -/
def ofDistinctPoints
    (x₁ y₁ x₂ y₂ : ℚ)
    (hcurve₁ : y₁ ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x₁)
    (hcurve₂ : y₂ ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x₂)
    (hx : x₁ ≠ x₂) : AffineMumford where
  u := (X - C x₁) * (X - C x₂)
  v := interpolationLine x₁ y₁ x₂ y₂
  u_monic := (monic_X_sub_C x₁).mul (monic_X_sub_C x₂)
  u_natDegree_le := by
    compute_degree
  v_degree_lt := by
    have huDegree :
        ((X - C x₁) * (X - C x₂) : ℚ[X]).degree = 2 := by
      compute_degree <;> norm_num
    rw [huDegree]
    simp only [interpolationLine]
    compute_degree
    all_goals norm_num
  equation_mod_u := by
    apply coprime_support_product_dvd
        (ofPoint x₁ y₁ hcurve₁) (ofPoint x₂ y₂ hcurve₂)
    · exact isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr hx).isUnit
    · exact point_factor_dvd_interpolation_sub x₁ y₁ x₂ y₂ x₁ y₁
        (eval_interpolationLine_left x₁ y₁ x₂ y₂ hx)
    · exact point_factor_dvd_interpolation_sub x₁ y₁ x₂ y₂ x₂ y₂
        (eval_interpolationLine_right x₁ y₁ x₂ y₂ hx)

@[simp]
theorem ofDistinctPoints_u
    (x₁ y₁ x₂ y₂ : ℚ) (hcurve₁ hcurve₂) (hx : x₁ ≠ x₂) :
    (ofDistinctPoints x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ hx).u =
      (X - C x₁) * (X - C x₂) := rfl

@[simp]
theorem ofDistinctPoints_v
    (x₁ y₁ x₂ y₂ : ℚ) (hcurve₁ hcurve₂) (hx : x₁ ≠ x₂) :
    (ofDistinctPoints x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ hx).v =
      interpolationLine x₁ y₁ x₂ y₂ := rfl

/-- Coefficient form of the monic quadratic support. -/
theorem two_point_support_coefficients (x₁ x₂ : ℚ) :
    (X - C x₁) * (X - C x₂) =
      monicQuadratic (x₁ * x₂) (-(x₁ + x₂)) := by
  simp only [monicQuadratic, C_neg, C_add, C_mul]
  ring

/-- Coefficient form of the interpolating ordinate. -/
theorem interpolationLine_coefficients (x₁ y₁ x₂ y₂ : ℚ) :
    interpolationLine x₁ y₁ x₂ y₂ =
      linearPolynomial (interpolationConstant x₁ y₁ x₂ y₂)
        (interpolationSlope x₁ y₁ x₂ y₂) := by
  rfl

end AffineMumford

/-! ## Scalar verification of the symbolic division certificate -/

/-- Genuine divisibility by a monic quadratic forces both displayed scalar
remainders to vanish.  Together with
`isMumfordPair_of_remainders_eq_zero`, this makes the coefficient verifier
exact over `ℚ`. -/
theorem remainders_eq_zero_of_isMumfordPair
    (u₀ u₁ v₀ v₁ : ℚ) (hpair : IsMumfordPair u₀ u₁ v₀ v₁) :
    mumfordRemainderConstant u₀ u₁ v₀ v₁ = 0 ∧
      mumfordRemainderLinear u₀ u₁ v₀ v₁ = 0 := by
  have hu : (monicQuadratic u₀ u₁).Monic := by
    simp only [monicQuadratic]
    monicity <;> norm_num
  let rem : ℚ[X] :=
    C (mumfordRemainderConstant u₀ u₁ v₀ v₁) +
      C (mumfordRemainderLinear u₀ u₁ v₀ v₁) * X
  have hsub : monicQuadratic u₀ u₁ ∣
      (sexticPolynomial - linearPolynomial v₀ v₁ ^ 2) - rem := by
    refine ⟨mumfordQuotient u₀ u₁ v₁, ?_⟩
    calc
      (sexticPolynomial - linearPolynomial v₀ v₁ ^ 2) - rem =
          (monicQuadratic u₀ u₁ * mumfordQuotient u₀ u₁ v₁ +
            C (mumfordRemainderConstant u₀ u₁ v₀ v₁) +
            C (mumfordRemainderLinear u₀ u₁ v₀ v₁) * X) - rem := by
              rw [mumford_division_certificate]
      _ = monicQuadratic u₀ u₁ * mumfordQuotient u₀ u₁ v₁ := by
        simp only [rem]
        ring
  have hmod := modByMonic_eq_of_dvd_sub hu hsub
  have hpmod :
      (sexticPolynomial - linearPolynomial v₀ v₁ ^ 2) %ₘ
          monicQuadratic u₀ u₁ = 0 :=
    (modByMonic_eq_zero_iff_dvd hu).2 hpair
  have hrdeg : rem.degree < (monicQuadratic u₀ u₁).degree := by
    have huDegree : (monicQuadratic u₀ u₁).degree = 2 := by
      simp only [monicQuadratic]
      compute_degree <;> norm_num
    rw [huDegree]
    dsimp only [rem]
    compute_degree
    all_goals norm_num
  have hrmod : rem %ₘ monicQuadratic u₀ u₁ = rem :=
    (modByMonic_eq_self_iff hu).2 hrdeg
  rw [hpmod, hrmod] at hmod
  have hz : rem = 0 := hmod.symm
  constructor
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 0) hz
    simpa [rem] using hc
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hz
    simpa [rem] using hc

/-- The two scalar equations are exactly the quadratic Mumford divisibility
condition over `ℚ`. -/
theorem isMumfordPair_iff_remainders_eq_zero
    (u₀ u₁ v₀ v₁ : ℚ) :
    IsMumfordPair u₀ u₁ v₀ v₁ ↔
      mumfordRemainderConstant u₀ u₁ v₀ v₁ = 0 ∧
        mumfordRemainderLinear u₀ u₁ v₀ v₁ = 0 := by
  constructor
  · exact remainders_eq_zero_of_isMumfordPair u₀ u₁ v₀ v₁
  · rintro ⟨h₀, h₁⟩
    exact isMumfordPair_of_remainders_eq_zero u₀ u₁ v₀ v₁ h₀ h₁

namespace AffineMumford

/-- The explicit coefficients produced by two-point composition pass both
scalar remainder checks.  This has the coefficient-level shape used by the
existing finite-field Mumford verifiers. -/
theorem ofDistinctPoints_remainders_eq_zero
    (x₁ y₁ x₂ y₂ : ℚ)
    (hcurve₁ : y₁ ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x₁)
    (hcurve₂ : y₂ ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x₂)
    (hx : x₁ ≠ x₂) :
    mumfordRemainderConstant
        (x₁ * x₂) (-(x₁ + x₂))
        (interpolationConstant x₁ y₁ x₂ y₂)
        (interpolationSlope x₁ y₁ x₂ y₂) = 0 ∧
      mumfordRemainderLinear
        (x₁ * x₂) (-(x₁ + x₂))
        (interpolationConstant x₁ y₁ x₂ y₂)
        (interpolationSlope x₁ y₁ x₂ y₂) = 0 := by
  apply remainders_eq_zero_of_isMumfordPair
  change monicQuadratic (x₁ * x₂) (-(x₁ + x₂)) ∣
    sexticPolynomial -
      linearPolynomial (interpolationConstant x₁ y₁ x₂ y₂)
          (interpolationSlope x₁ y₁ x₂ y₂) ^ 2
  rw [← two_point_support_coefficients,
    ← interpolationLine_coefficients]
  exact (ofDistinctPoints x₁ y₁ x₂ y₂ hcurve₁ hcurve₂ hx).equation_mod_u

/-! ## Concrete rational cusp composition -/

private theorem cusp_zero_curve :
    (1 : ℚ) ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial 0 := by
  norm_num [MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]

private theorem cusp_neg_one_curve :
    (1 : ℚ) ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial (-1) := by
  norm_num [MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]

/-- The normalized record obtained by composing the two affine cusps. -/
def cuspComposition : AffineMumford :=
  ofDistinctPoints 0 1 (-1) 1 cusp_zero_curve cusp_neg_one_curve
    (by norm_num)

/-- The composed cusp support is the expected `X² + X`. -/
@[simp]
theorem cuspComposition_u : cuspComposition.u = monicQuadratic 0 1 := by
  rw [cuspComposition, ofDistinctPoints_u,
    two_point_support_coefficients]
  norm_num

/-- The composed cusp ordinate polynomial is the constant `1`. -/
@[simp]
theorem cuspComposition_v : cuspComposition.v = linearPolynomial 1 0 := by
  rw [cuspComposition, ofDistinctPoints_v,
    interpolationLine_coefficients]
  norm_num [interpolationSlope, interpolationConstant]

/-- The operation-level cusp construction recovers the existing fixed
quadratic certificate. -/
theorem cuspComposition_isMumfordPair : IsMumfordPair 0 1 1 0 := by
  change monicQuadratic 0 1 ∣
    sexticPolynomial - linearPolynomial 1 0 ^ 2
  rw [← cuspComposition_u, ← cuspComposition_v]
  exact cuspComposition.equation_mod_u

end AffineMumford

end

end MazurTorsion.XOneThirteenMumford
