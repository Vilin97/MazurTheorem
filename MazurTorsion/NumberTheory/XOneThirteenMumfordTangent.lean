/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenMumfordComposition
import MazurTorsion.NumberTheory.XOneThirteenRationalMumfordReduction

/-!
# Tangent Mumford certificates for `X₁(13)`

This file handles the first shared-support case left open by
`XOneThirteenMumfordComposition`.  For an affine point `(x,y)` with `y ≠ 0`,
the explicit tangent slope

`m = f'(x) / (2y)`

gives a line whose squared difference from the fixed sextic is divisible by
`(X-x)²`.  The quotient is displayed coefficient by coefficient, so the
result is a checked normalized `AffineMumford` record rather than an appeal to
a general Jacobian implementation.

The concrete consumer doubles the affine cusp `(0,1)` at the coordinate
level.  Its coefficients are `(u₀,u₁,v₀,v₁) = (0,0,1,2)`.  A denominator-one
cleared record then reduces to the corresponding existing balanced record
over `𝔽₅`.  No divisor-class quotient or group law is claimed.

The remaining shared-support boundary is the Weierstrass case `y = 0`; the
remaining general composition boundary is reduction of degree-four support
arising from two coprime quadratic inputs.
-/

namespace MazurTorsion.XOneThirteenMumford

open Polynomial

noncomputable section

namespace AffineMumford

/-! ## Symbolic tangent division -/

/-- The scalar derivative of the fixed sextic. -/
def sexticDerivativeValue (x : ℚ) : ℚ :=
  6 * x ^ 5 + 10 * x ^ 4 + 4 * x ^ 3 + 6 * x ^ 2 + 12 * x + 4

/-- Evaluation of the polynomial derivative agrees with the displayed scalar
formula. -/
theorem eval_derivative_sexticPolynomial (x : ℚ) :
    sexticPolynomial.derivative.eval x = sexticDerivativeValue x := by
  simp [sexticPolynomial, sexticDerivativeValue, derivative_add,
    derivative_mul, derivative_pow]
  ring

/-- A line through `(x,y)` with a supplied slope. -/
def tangentLineWithSlope (x y m : ℚ) : ℚ[X] :=
  C m * (X - C x) + C y

/-- Quotient of `f - tangentLine²` by `(X-x)²`, assuming the curve and
tangency equations.  It is written in powers of the local parameter
`T = X-x`. -/
def tangentQuotientWithSlope (x m : ℚ) : ℚ[X] :=
  let T := X - C x
  T ^ 4 + C (6 * x + 2) * T ^ 3 +
    C (15 * x ^ 2 + 10 * x + 1) * T ^ 2 +
    C (20 * x ^ 3 + 20 * x ^ 2 + 4 * x + 2) * T +
    C (15 * x ^ 4 + 20 * x ^ 3 + 6 * x ^ 2 + 6 * x + 6 - m ^ 2)

/-- Exact Taylor-division certificate for an arbitrary supplied tangent
slope.  Both scalar premises are exposed: the point lies on the curve, and
the supplied slope satisfies `2ym = f'(x)`. -/
theorem tangent_division_certificate
    (x y m : ℚ)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x)
    (htangent : 2 * y * m = sexticDerivativeValue x) :
    sexticPolynomial - tangentLineWithSlope x y m ^ 2 =
      (X - C x) ^ 2 * tangentQuotientWithSlope x m := by
  apply Polynomial.funext
  intro z
  simp only [sexticPolynomial, tangentLineWithSlope,
    tangentQuotientWithSlope, eval_sub, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, eval_ofNat, eval_one]
  dsimp [MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial] at hcurve
  dsimp [sexticDerivativeValue] at htangent
  linear_combination -hcurve - (z - x) * htangent

/-- The tangent slope at a non-Weierstrass affine point. -/
def tangentSlope (x y : ℚ) : ℚ :=
  sexticDerivativeValue x / (2 * y)

/-- The only denominator required by the tangent construction is nonzero
when `y ≠ 0`. -/
theorem tangentSlope_spec (x y : ℚ) (hy : y ≠ 0) :
    2 * y * tangentSlope x y = sexticDerivativeValue x := by
  simp only [tangentSlope]
  field_simp [hy]

/-- The canonical tangent line at a non-Weierstrass affine point. -/
def tangentLine (x y : ℚ) : ℚ[X] :=
  tangentLineWithSlope x y (tangentSlope x y)

/-- The tangent line passes through its point. -/
@[simp]
theorem eval_tangentLine (x y : ℚ) : (tangentLine x y).eval x = y := by
  simp [tangentLine, tangentLineWithSlope]

/-- Tangent doubling of a non-Weierstrass affine point, at the coordinate
certificate level.

The result has repeated support `(X-x)²`, degree at most two, and ordinate the
explicit tangent line.  The premise `y ≠ 0` is retained because it is exactly
what makes the tangent slope defined by division. -/
def ofTangentPoint
    (x y : ℚ)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x)
    (hy : y ≠ 0) : AffineMumford where
  u := (X - C x) ^ 2
  v := tangentLine x y
  u_monic := (monic_X_sub_C x).pow 2
  u_natDegree_le := by
    compute_degree
  v_degree_lt := by
    have huDegree : ((X - C x) ^ 2 : ℚ[X]).degree = 2 := by
      compute_degree <;> norm_num
    rw [huDegree]
    simp only [tangentLine, tangentLineWithSlope]
    compute_degree
    all_goals norm_num
  equation_mod_u := by
    refine ⟨tangentQuotientWithSlope x (tangentSlope x y), ?_⟩
    exact tangent_division_certificate x y (tangentSlope x y) hcurve
      (tangentSlope_spec x y hy)

@[simp]
theorem ofTangentPoint_u (x y : ℚ) (hcurve) (hy : y ≠ 0) :
    (ofTangentPoint x y hcurve hy).u = (X - C x) ^ 2 := rfl

@[simp]
theorem ofTangentPoint_v (x y : ℚ) (hcurve) (hy : y ≠ 0) :
    (ofTangentPoint x y hcurve hy).v = tangentLine x y := rfl

/-- Coefficient form of the repeated monic support. -/
theorem tangent_support_coefficients (x : ℚ) :
    (X - C x) ^ 2 = monicQuadratic (x ^ 2) (-2 * x) := by
  apply Polynomial.funext
  intro z
  simp only [monicQuadratic, eval_pow, eval_sub, eval_X, eval_C,
    eval_add, eval_mul]
  ring

/-- Coefficient form of a line through `(x,y)` with slope `m`. -/
theorem tangentLineWithSlope_coefficients (x y m : ℚ) :
    tangentLineWithSlope x y m = linearPolynomial (y - m * x) m := by
  simp only [tangentLineWithSlope, linearPolynomial, C_sub, C_mul]
  ring

/-- Tangent-point coefficients satisfy both exact scalar remainder equations.
This is the finite-verifier form of the polynomial divisibility certificate. -/
theorem ofTangentPoint_remainders_eq_zero
    (x y : ℚ)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x)
    (hy : y ≠ 0) :
    mumfordRemainderConstant
        (x ^ 2) (-2 * x) (y - tangentSlope x y * x)
        (tangentSlope x y) = 0 ∧
      mumfordRemainderLinear
        (x ^ 2) (-2 * x) (y - tangentSlope x y * x)
        (tangentSlope x y) = 0 := by
  apply remainders_eq_zero_of_isMumfordPair
  change monicQuadratic (x ^ 2) (-2 * x) ∣
    sexticPolynomial -
      linearPolynomial (y - tangentSlope x y * x)
          (tangentSlope x y) ^ 2
  rw [← tangent_support_coefficients,
    ← tangentLineWithSlope_coefficients]
  exact (ofTangentPoint x y hcurve hy).equation_mod_u

/-! ## The tangent certificate at the affine cusp `(0,1)` -/

private theorem cusp_zero_curve :
    (1 : ℚ) ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial 0 := by
  norm_num [MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]

/-- Coordinate-level tangent doubling at the affine cusp `(0,1)`. -/
def cuspZeroTangent : AffineMumford :=
  ofTangentPoint 0 1 cusp_zero_curve one_ne_zero

@[simp]
theorem cuspZeroTangent_slope : tangentSlope 0 1 = 2 := by
  norm_num [tangentSlope, sexticDerivativeValue]

@[simp]
theorem cuspZeroTangent_u : cuspZeroTangent.u = monicQuadratic 0 0 := by
  rw [cuspZeroTangent, ofTangentPoint_u,
    tangent_support_coefficients]
  norm_num

@[simp]
theorem cuspZeroTangent_v : cuspZeroTangent.v = linearPolynomial 1 2 := by
  rw [cuspZeroTangent, ofTangentPoint_v, tangentLine,
    tangentLineWithSlope_coefficients, cuspZeroTangent_slope]
  norm_num

/-- The tangent construction yields the explicit coefficient certificate
`(u₀,u₁,v₀,v₁) = (0,0,1,2)`. -/
theorem cuspZeroTangent_isMumfordPair : IsMumfordPair 0 0 1 2 := by
  change monicQuadratic 0 0 ∣
    sexticPolynomial - linearPolynomial 1 2 ^ 2
  rw [← cuspZeroTangent_u, ← cuspZeroTangent_v]
  exact cuspZeroTangent.equation_mod_u

end AffineMumford

/-! ## Denominator-one reduction of the cusp tangent certificate -/

open XOneThirteenRationalMumfordReduction
open XOneThirteenFiniteMumfordFive

local instance : NeZero 5 := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The integral coefficient record underlying the cusp tangent pair. -/
def cuspZeroTangentCleared : ClearedDegreeTwo where
  u₀Numerator := 0
  u₁Numerator := 0
  v₀Numerator := 1
  v₁Numerator := 2
  denominator := 1
  denominator_ne_zero := by norm_num
  cleared_constant := by
    norm_num [clearedRemainderConstant]
  cleared_linear := by
    norm_num [clearedRemainderLinear]

/-- The denominator-cleared record recovers the tangent construction over
`ℚ`. -/
theorem cuspZeroTangentCleared_toAffineMumford :
    cuspZeroTangentCleared.toAffineMumford =
      AffineMumford.cuspZeroTangent := by
  apply AffineMumford.ext <;>
    simp [cuspZeroTangentCleared, ClearedDegreeTwo.toAffineMumford,
      ClearedDegreeTwo.u₀, ClearedDegreeTwo.u₁,
      ClearedDegreeTwo.v₀, ClearedDegreeTwo.v₁]

/-- The cusp tangent certificate viewed through the existing cleared-record
sum. -/
def cuspZeroTangentClearedMumford : ClearedMumford :=
  .inr cuspZeroTangentCleared

private theorem cuspZeroTangent_denominator_good_F5 :
    ¬(5 : ℤ) ∣ cuspZeroTangentClearedMumford.denominator := by
  norm_num [cuspZeroTangentClearedMumford, ClearedMumford.denominator,
    cuspZeroTangentCleared]

/-- Existing coefficientwise reduction sends the rational cusp tangent
certificate into the balanced `𝔽₅` record set. -/
def cuspZeroTangentReductionF5 : BalancedMumfordF5 :=
  cuspZeroTangentClearedMumford.reduceF5
    cuspZeroTangent_denominator_good_F5

/-- The reduced record has exactly the first degree-two coefficient tuple in
the existing eight-entry `𝔽₅` table. -/
theorem cuspZeroTangentReductionF5_value :
    cuspZeroTangentReductionF5.1 = rawDegreeTwoF5 0 0 1 2 := by
  simp [cuspZeroTangentReductionF5,
    cuspZeroTangentClearedMumford, cuspZeroTangentCleared,
    ClearedMumford.reduceF5, ClearedMumford.reduceRawF5,
    ClearedMumford.degreeTwoRawF5, ClearedMumford.fractionF5]

/-- The reduced tangent coefficients are literally entry zero of the checked
eight-element degree-two table modulo `5`. -/
theorem cuspZeroTangentReductionF5_table_entry :
    (degreeTwoRecordOfIndexF5 0).1 = (0, 0, 1, 2) ∧
      cuspZeroTangentReductionF5.1 = rawDegreeTwoF5 0 0 1 2 :=
  ⟨rfl, cuspZeroTangentReductionF5_value⟩

/-- The existing local verifier supplies reducedness and genuine polynomial
divisibility for the tangent cusp record modulo `5`. -/
theorem cuspZeroTangentReductionF5_spec :
    IsReducedEncodingF5 cuspZeroTangentReductionF5.1 ∧
      recordUF5 cuspZeroTangentReductionF5.1 ∣
        sexticF5 - recordVF5 cuspZeroTangentReductionF5.1 ^ 2 :=
  balancedMumfordF5_spec cuspZeroTangentReductionF5

end

end MazurTorsion.XOneThirteenMumford
