/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenFiniteMumfordFive
import Mathlib.Algebra.Field.ZMod

/-!
# Denominator-cleared reduction of fixed `X₁(13)` Mumford data

This file connects actual rational Mumford coordinate records for the fixed
sextic

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`

to the checked balanced coordinate sets over `𝔽₃` and `𝔽₅`.

The rational input is deliberately small and explicit.  A degree-one record
stores integer numerators for `(x,y)` and one common nonzero denominator.  A
degree-two record stores integer numerators for `(u₀,u₁,v₀,v₁)`, again with one
common nonzero denominator, together with the two degree-five homogeneous
remainder identities obtained by clearing that denominator.

Each input first gives genuine `AffineMumford` data over `ℚ`.  If `3`,
respectively `5`, does not divide the common denominator, coefficientwise
reduction gives an existing raw balanced record.  The cleared identities prove
its finite-field validity, so only then do we package it as a
`BalancedMumfordF3` or `BalancedMumfordF5`.  The downstream specifications state
actual polynomial divisibility and reducedness.

No Jacobian reduction map, divisor-class quotient, or injectivity of reduction
is asserted here.
-/

namespace MazurTorsion.XOneThirteenRationalMumfordReduction

open Polynomial
open XOneThirteenMumford
open XOneThirteenFiniteField
open XOneThirteenFiniteMumford
open XOneThirteenFiniteMumfordFive

local instance : NeZero 3 := ⟨by norm_num⟩
local instance : NeZero 5 := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ## Homogeneous cleared identities -/

/-- The degree-six homogenization of the fixed affine sextic. -/
def clearedSextic {R : Type*} [CommRing R] (x d : R) : R :=
  x ^ 6 + 2 * x ^ 5 * d + x ^ 4 * d ^ 2 + 2 * x ^ 3 * d ^ 3 +
    6 * x ^ 2 * d ^ 4 + 4 * x * d ^ 5 + d ^ 6

/-- The degree-five homogenization of the constant Mumford remainder. -/
def clearedRemainderConstant {R : Type*} [CommRing R]
    (u₀ u₁ v₀ v₁ d : R) : R :=
  -u₀ ^ 3 * d ^ 2 + 3 * u₀ ^ 2 * u₁ ^ 2 * d -
    4 * u₀ ^ 2 * u₁ * d ^ 2 + u₀ ^ 2 * d ^ 3 - u₀ * u₁ ^ 4 +
    2 * u₀ * u₁ ^ 3 * d - u₀ * u₁ ^ 2 * d ^ 2 +
    2 * u₀ * u₁ * d ^ 3 + u₀ * v₁ ^ 2 * d ^ 2 -
    6 * u₀ * d ^ 4 - v₀ ^ 2 * d ^ 3 + d ^ 5

/-- The degree-five homogenization of the linear Mumford remainder. -/
def clearedRemainderLinear {R : Type*} [CommRing R]
    (u₀ u₁ v₀ v₁ d : R) : R :=
  -3 * u₀ ^ 2 * u₁ * d ^ 2 + 2 * u₀ ^ 2 * d ^ 3 +
    4 * u₀ * u₁ ^ 3 * d - 6 * u₀ * u₁ ^ 2 * d ^ 2 +
    2 * u₀ * u₁ * d ^ 3 - 2 * u₀ * d ^ 4 - u₁ ^ 5 +
    2 * u₁ ^ 4 * d - u₁ ^ 3 * d ^ 2 + 2 * u₁ ^ 2 * d ^ 3 +
    u₁ * v₁ ^ 2 * d ^ 2 - 6 * u₁ * d ^ 4 -
    2 * v₀ * v₁ * d ^ 3 + 4 * d ^ 5

private theorem degreeOne_division_of_cleared
    {K : Type*} [Field K] (x y d : K) (hd : d ≠ 0)
    (h : y ^ 2 * d ^ 4 = clearedSextic x d) :
    (y / d) ^ 2 =
      (x / d) ^ 6 + 2 * (x / d) ^ 5 + (x / d) ^ 4 +
        2 * (x / d) ^ 3 + 6 * (x / d) ^ 2 + 4 * (x / d) + 1 := by
  field_simp [hd]
  simp only [clearedSextic] at h ⊢
  linear_combination h

private theorem remainderConstant_division_of_cleared
    {K : Type*} [Field K] (u₀ u₁ v₀ v₁ d : K) (hd : d ≠ 0)
    (h : clearedRemainderConstant u₀ u₁ v₀ v₁ d = 0) :
    -(u₀ / d) ^ 3 + 3 * (u₀ / d) ^ 2 * (u₁ / d) ^ 2 -
        4 * (u₀ / d) ^ 2 * (u₁ / d) + (u₀ / d) ^ 2 -
        (u₀ / d) * (u₁ / d) ^ 4 + 2 * (u₀ / d) * (u₁ / d) ^ 3 -
        (u₀ / d) * (u₁ / d) ^ 2 + 2 * (u₀ / d) * (u₁ / d) +
        (u₀ / d) * (v₁ / d) ^ 2 - 6 * (u₀ / d) -
        (v₀ / d) ^ 2 + 1 = 0 := by
  field_simp [hd]
  simp only [clearedRemainderConstant] at h ⊢
  linear_combination h

private theorem remainderLinear_division_of_cleared
    {K : Type*} [Field K] (u₀ u₁ v₀ v₁ d : K) (hd : d ≠ 0)
    (h : clearedRemainderLinear u₀ u₁ v₀ v₁ d = 0) :
    -3 * (u₀ / d) ^ 2 * (u₁ / d) + 2 * (u₀ / d) ^ 2 +
        4 * (u₀ / d) * (u₁ / d) ^ 3 -
        6 * (u₀ / d) * (u₁ / d) ^ 2 +
        2 * (u₀ / d) * (u₁ / d) - 2 * (u₀ / d) -
        (u₁ / d) ^ 5 + 2 * (u₁ / d) ^ 4 - (u₁ / d) ^ 3 +
        2 * (u₁ / d) ^ 2 + (u₁ / d) * (v₁ / d) ^ 2 -
        6 * (u₁ / d) - 2 * (v₀ / d) * (v₁ / d) + 4 = 0 := by
  field_simp [hd]
  simp only [clearedRemainderLinear] at h ⊢
  linear_combination h

/-! ## Actual rational coordinate records -/

/-- A denominator-cleared rational affine point, hence degree-one Mumford
data for the fixed sextic. -/
structure ClearedDegreeOne where
  xNumerator : ℤ
  yNumerator : ℤ
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0
  cleared_equation :
    yNumerator ^ 2 * denominator ^ 4 =
      clearedSextic xNumerator denominator

namespace ClearedDegreeOne

/-- Rational abscissa represented by a cleared degree-one record. -/
def x (D : ClearedDegreeOne) : ℚ :=
  (D.xNumerator : ℚ) / (D.denominator : ℚ)

/-- Rational ordinate represented by a cleared degree-one record. -/
def y (D : ClearedDegreeOne) : ℚ :=
  (D.yNumerator : ℚ) / (D.denominator : ℚ)

/-- The cleared identity gives the actual rational curve equation. -/
theorem curve_equation (D : ClearedDegreeOne) :
    D.y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial D.x := by
  have hd : (D.denominator : ℚ) ≠ 0 := by
    exact_mod_cast D.denominator_ne_zero
  have hcast :
      (D.yNumerator : ℚ) ^ 2 * (D.denominator : ℚ) ^ 4 =
        clearedSextic (D.xNumerator : ℚ) (D.denominator : ℚ) := by
    simpa [clearedSextic] using
      congrArg (Int.castRingHom ℚ) D.cleared_equation
  simpa [x, y,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial] using
      degreeOne_division_of_cleared
        (D.xNumerator : ℚ) (D.yNumerator : ℚ)
        (D.denominator : ℚ) hd hcast

/-- Genuine rational degree-one `AffineMumford` data. -/
noncomputable def toAffineMumford (D : ClearedDegreeOne) :
    XOneThirteenMumford.AffineMumford :=
  XOneThirteenMumford.AffineMumford.ofPoint D.x D.y D.curve_equation

end ClearedDegreeOne

/-- Denominator-cleared rational monic-quadratic Mumford coefficients. -/
structure ClearedDegreeTwo where
  u₀Numerator : ℤ
  u₁Numerator : ℤ
  v₀Numerator : ℤ
  v₁Numerator : ℤ
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0
  cleared_constant :
    clearedRemainderConstant u₀Numerator u₁Numerator
      v₀Numerator v₁Numerator denominator = 0
  cleared_linear :
    clearedRemainderLinear u₀Numerator u₁Numerator
      v₀Numerator v₁Numerator denominator = 0

namespace ClearedDegreeTwo

def u₀ (D : ClearedDegreeTwo) : ℚ :=
  (D.u₀Numerator : ℚ) / (D.denominator : ℚ)

def u₁ (D : ClearedDegreeTwo) : ℚ :=
  (D.u₁Numerator : ℚ) / (D.denominator : ℚ)

def v₀ (D : ClearedDegreeTwo) : ℚ :=
  (D.v₀Numerator : ℚ) / (D.denominator : ℚ)

def v₁ (D : ClearedDegreeTwo) : ℚ :=
  (D.v₁Numerator : ℚ) / (D.denominator : ℚ)

/-- The two cleared identities imply the rational scalar remainder
conditions. -/
theorem rational_remainders (D : ClearedDegreeTwo) :
    mumfordRemainderConstant D.u₀ D.u₁ D.v₀ D.v₁ = 0 ∧
      mumfordRemainderLinear D.u₀ D.u₁ D.v₀ D.v₁ = 0 := by
  have hd : (D.denominator : ℚ) ≠ 0 := by
    exact_mod_cast D.denominator_ne_zero
  have hconstant :
      clearedRemainderConstant
        (D.u₀Numerator : ℚ) (D.u₁Numerator : ℚ)
        (D.v₀Numerator : ℚ) (D.v₁Numerator : ℚ)
        (D.denominator : ℚ) = 0 := by
    simpa [clearedRemainderConstant] using
      congrArg (Int.castRingHom ℚ) D.cleared_constant
  have hlinear :
      clearedRemainderLinear
        (D.u₀Numerator : ℚ) (D.u₁Numerator : ℚ)
        (D.v₀Numerator : ℚ) (D.v₁Numerator : ℚ)
        (D.denominator : ℚ) = 0 := by
    simpa [clearedRemainderLinear] using
      congrArg (Int.castRingHom ℚ) D.cleared_linear
  constructor
  · simpa [u₀, u₁, v₀, v₁, mumfordRemainderConstant] using
      remainderConstant_division_of_cleared
        (D.u₀Numerator : ℚ) (D.u₁Numerator : ℚ)
        (D.v₀Numerator : ℚ) (D.v₁Numerator : ℚ)
        (D.denominator : ℚ) hd hconstant
  · simpa [u₀, u₁, v₀, v₁, mumfordRemainderLinear] using
      remainderLinear_division_of_cleared
        (D.u₀Numerator : ℚ) (D.u₁Numerator : ℚ)
        (D.v₀Numerator : ℚ) (D.v₁Numerator : ℚ)
        (D.denominator : ℚ) hd hlinear

/-- The cleared record is a genuine rational Mumford pair. -/
theorem isMumfordPair (D : ClearedDegreeTwo) :
    IsMumfordPair D.u₀ D.u₁ D.v₀ D.v₁ :=
  isMumfordPair_of_remainders_eq_zero D.u₀ D.u₁ D.v₀ D.v₁
    D.rational_remainders.1 D.rational_remainders.2

/-- Genuine rational degree-two `AffineMumford` data. -/
noncomputable def toAffineMumford (D : ClearedDegreeTwo) :
    XOneThirteenMumford.AffineMumford where
  u := monicQuadratic D.u₀ D.u₁
  v := linearPolynomial D.v₀ D.v₁
  u_monic := by
    simp only [monicQuadratic]
    monicity <;> norm_num
  u_natDegree_le := by
    simp only [monicQuadratic]
    compute_degree
  v_degree_lt := by
    have huDegree : (monicQuadratic D.u₀ D.u₁).degree = 2 := by
      simp only [monicQuadratic]
      compute_degree <;> norm_num
    rw [huDegree]
    simp only [linearPolynomial]
    compute_degree
    all_goals norm_num
  equation_mod_u := D.isMumfordPair

end ClearedDegreeTwo

/-- The two supported affine degrees of denominator-cleared rational Mumford
data considered by this interface. -/
def ClearedMumford := ClearedDegreeOne ⊕ ClearedDegreeTwo

namespace ClearedMumford

/-- Common denominator of either supported degree. -/
def denominator : ClearedMumford → ℤ
  | .inl D => D.denominator
  | .inr D => D.denominator

/-- Every cleared record produces genuine rational `AffineMumford` data. -/
noncomputable def toAffineMumford : ClearedMumford →
    XOneThirteenMumford.AffineMumford
  | .inl D => D.toAffineMumford
  | .inr D => D.toAffineMumford

/-! ## Coefficientwise reduction modulo `3` -/

def fractionF3 (n d : ℤ) : F3 :=
  (n : F3) / (d : F3)

private theorem denominator_ne_zero_F3 {d : ℤ}
    (hgood : ¬(3 : ℤ) ∣ d) : (d : F3) ≠ 0 := by
  intro hzero
  exact hgood ((ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp hzero)

def degreeOneRawF3 (D : ClearedDegreeOne) : RawBalancedMumfordF3 :=
  rawDegreeOne (fractionF3 D.xNumerator D.denominator)
    (fractionF3 D.yNumerator D.denominator) 1

def degreeTwoRawF3 (D : ClearedDegreeTwo) : RawBalancedMumfordF3 :=
  rawDegreeTwo (fractionF3 D.u₀Numerator D.denominator)
    (fractionF3 D.u₁Numerator D.denominator)
    (fractionF3 D.v₀Numerator D.denominator)
    (fractionF3 D.v₁Numerator D.denominator)

theorem degreeOneRawF3_valid (D : ClearedDegreeOne)
    (hgood : ¬(3 : ℤ) ∣ D.denominator) :
    IsValid (degreeOneRawF3 D) := by
  have hd := denominator_ne_zero_F3 hgood
  have hcast :
      (D.yNumerator : F3) ^ 2 * (D.denominator : F3) ^ 4 =
        clearedSextic (D.xNumerator : F3) (D.denominator : F3) := by
    simpa [clearedSextic] using
      congrArg (Int.castRingHom F3) D.cleared_equation
  change (fractionF3 D.yNumerator D.denominator) ^ 2 =
    sexticValue (fractionF3 D.xNumerator D.denominator)
  simpa [fractionF3, sexticValue] using
    degreeOne_division_of_cleared
      (D.xNumerator : F3) (D.yNumerator : F3)
      (D.denominator : F3) hd hcast

theorem degreeTwoRawF3_valid (D : ClearedDegreeTwo)
    (hgood : ¬(3 : ℤ) ∣ D.denominator) :
    IsValid (degreeTwoRawF3 D) := by
  have hd := denominator_ne_zero_F3 hgood
  have hconstant :
      clearedRemainderConstant
        (D.u₀Numerator : F3) (D.u₁Numerator : F3)
        (D.v₀Numerator : F3) (D.v₁Numerator : F3)
        (D.denominator : F3) = 0 := by
    simpa [clearedRemainderConstant] using
      congrArg (Int.castRingHom F3) D.cleared_constant
  have hlinear :
      clearedRemainderLinear
        (D.u₀Numerator : F3) (D.u₁Numerator : F3)
        (D.v₀Numerator : F3) (D.v₁Numerator : F3)
        (D.denominator : F3) = 0 := by
    simpa [clearedRemainderLinear] using
      congrArg (Int.castRingHom F3) D.cleared_linear
  change
    remainderConstantF3
      (fractionF3 D.u₀Numerator D.denominator)
      (fractionF3 D.u₁Numerator D.denominator)
      (fractionF3 D.v₀Numerator D.denominator)
      (fractionF3 D.v₁Numerator D.denominator) = 0 ∧
    remainderLinearF3
      (fractionF3 D.u₀Numerator D.denominator)
      (fractionF3 D.u₁Numerator D.denominator)
      (fractionF3 D.v₀Numerator D.denominator)
      (fractionF3 D.v₁Numerator D.denominator) = 0
  constructor
  · simpa [fractionF3, remainderConstantF3] using
      remainderConstant_division_of_cleared
        (D.u₀Numerator : F3) (D.u₁Numerator : F3)
        (D.v₀Numerator : F3) (D.v₁Numerator : F3)
        (D.denominator : F3) hd hconstant
  · simpa [fractionF3, remainderLinearF3] using
      remainderLinear_division_of_cleared
        (D.u₀Numerator : F3) (D.u₁Numerator : F3)
        (D.v₀Numerator : F3) (D.v₁Numerator : F3)
        (D.denominator : F3) hd hlinear

/-- Coefficientwise raw reduction modulo `3`. -/
def reduceRawF3 : ClearedMumford → RawBalancedMumfordF3
  | .inl D => degreeOneRawF3 D
  | .inr D => degreeTwoRawF3 D

theorem reduceRawF3_valid (D : ClearedMumford)
    (hgood : ¬(3 : ℤ) ∣ D.denominator) :
    IsValid D.reduceRawF3 := by
  rcases D with D | D
  · exact degreeOneRawF3_valid D hgood
  · exact degreeTwoRawF3_valid D hgood

/-- A balanced `𝔽₃` record is produced only after validity has been derived
from the cleared rational identity. -/
def reduceF3 (D : ClearedMumford)
    (hgood : ¬(3 : ℤ) ∣ D.denominator) : BalancedMumfordF3 :=
  ⟨D.reduceRawF3, D.reduceRawF3_valid hgood⟩

/-- Reduction modulo `3` preserves the explicit reducedness and polynomial
divisibility conditions. -/
theorem reduceF3_spec (D : ClearedMumford)
    (hgood : ¬(3 : ℤ) ∣ D.denominator) :
    IsReducedEncoding (D.reduceF3 hgood).1 ∧
      recordU (D.reduceF3 hgood).1 ∣
        sextic - recordV (D.reduceF3 hgood).1 ^ 2 :=
  balancedMumfordF3_spec (D.reduceF3 hgood)

/-! ## Coefficientwise reduction modulo `5` -/

def fractionF5 (n d : ℤ) : F5 :=
  (n : F5) / (d : F5)

private theorem denominator_ne_zero_F5 {d : ℤ}
    (hgood : ¬(5 : ℤ) ∣ d) : (d : F5) ≠ 0 := by
  intro hzero
  exact hgood ((ZMod.intCast_zmod_eq_zero_iff_dvd d 5).mp hzero)

def degreeOneRawF5 (D : ClearedDegreeOne) : RawBalancedMumfordF5 :=
  rawDegreeOneF5 (fractionF5 D.xNumerator D.denominator)
    (fractionF5 D.yNumerator D.denominator) 1

def degreeTwoRawF5 (D : ClearedDegreeTwo) : RawBalancedMumfordF5 :=
  rawDegreeTwoF5 (fractionF5 D.u₀Numerator D.denominator)
    (fractionF5 D.u₁Numerator D.denominator)
    (fractionF5 D.v₀Numerator D.denominator)
    (fractionF5 D.v₁Numerator D.denominator)

theorem degreeOneRawF5_valid (D : ClearedDegreeOne)
    (hgood : ¬(5 : ℤ) ∣ D.denominator) :
    IsValidF5 (degreeOneRawF5 D) := by
  have hd := denominator_ne_zero_F5 hgood
  have hcast :
      (D.yNumerator : F5) ^ 2 * (D.denominator : F5) ^ 4 =
        clearedSextic (D.xNumerator : F5) (D.denominator : F5) := by
    simpa [clearedSextic] using
      congrArg (Int.castRingHom F5) D.cleared_equation
  change (fractionF5 D.yNumerator D.denominator) ^ 2 =
    sexticValueF5 (fractionF5 D.xNumerator D.denominator)
  simpa [fractionF5, sexticValueF5] using
    degreeOne_division_of_cleared
      (D.xNumerator : F5) (D.yNumerator : F5)
      (D.denominator : F5) hd hcast

theorem degreeTwoRawF5_valid (D : ClearedDegreeTwo)
    (hgood : ¬(5 : ℤ) ∣ D.denominator) :
    IsValidF5 (degreeTwoRawF5 D) := by
  have hd := denominator_ne_zero_F5 hgood
  have hconstant :
      clearedRemainderConstant
        (D.u₀Numerator : F5) (D.u₁Numerator : F5)
        (D.v₀Numerator : F5) (D.v₁Numerator : F5)
        (D.denominator : F5) = 0 := by
    simpa [clearedRemainderConstant] using
      congrArg (Int.castRingHom F5) D.cleared_constant
  have hlinear :
      clearedRemainderLinear
        (D.u₀Numerator : F5) (D.u₁Numerator : F5)
        (D.v₀Numerator : F5) (D.v₁Numerator : F5)
        (D.denominator : F5) = 0 := by
    simpa [clearedRemainderLinear] using
      congrArg (Int.castRingHom F5) D.cleared_linear
  change
    remainderConstantF5
      (fractionF5 D.u₀Numerator D.denominator)
      (fractionF5 D.u₁Numerator D.denominator)
      (fractionF5 D.v₀Numerator D.denominator)
      (fractionF5 D.v₁Numerator D.denominator) = 0 ∧
    remainderLinearF5
      (fractionF5 D.u₀Numerator D.denominator)
      (fractionF5 D.u₁Numerator D.denominator)
      (fractionF5 D.v₀Numerator D.denominator)
      (fractionF5 D.v₁Numerator D.denominator) = 0
  constructor
  · simpa [fractionF5, remainderConstantF5] using
      remainderConstant_division_of_cleared
        (D.u₀Numerator : F5) (D.u₁Numerator : F5)
        (D.v₀Numerator : F5) (D.v₁Numerator : F5)
        (D.denominator : F5) hd hconstant
  · simpa [fractionF5, remainderLinearF5] using
      remainderLinear_division_of_cleared
        (D.u₀Numerator : F5) (D.u₁Numerator : F5)
        (D.v₀Numerator : F5) (D.v₁Numerator : F5)
        (D.denominator : F5) hd hlinear

/-- Coefficientwise raw reduction modulo `5`. -/
def reduceRawF5 : ClearedMumford → RawBalancedMumfordF5
  | .inl D => degreeOneRawF5 D
  | .inr D => degreeTwoRawF5 D

theorem reduceRawF5_valid (D : ClearedMumford)
    (hgood : ¬(5 : ℤ) ∣ D.denominator) :
    IsValidF5 D.reduceRawF5 := by
  rcases D with D | D
  · exact degreeOneRawF5_valid D hgood
  · exact degreeTwoRawF5_valid D hgood

/-- A balanced `𝔽₅` record is produced only after validity has been derived
from the cleared rational identity. -/
def reduceF5 (D : ClearedMumford)
    (hgood : ¬(5 : ℤ) ∣ D.denominator) : BalancedMumfordF5 :=
  ⟨D.reduceRawF5, D.reduceRawF5_valid hgood⟩

/-- Reduction modulo `5` preserves the explicit reducedness and polynomial
divisibility conditions. -/
theorem reduceF5_spec (D : ClearedMumford)
    (hgood : ¬(5 : ℤ) ∣ D.denominator) :
    IsReducedEncodingF5 (D.reduceF5 hgood).1 ∧
      recordUF5 (D.reduceF5 hgood).1 ∣
        sexticF5 - recordVF5 (D.reduceF5 hgood).1 ^ 2 :=
  balancedMumfordF5_spec (D.reduceF5 hgood)

/-- The actual rational record and both finite reductions are available
simultaneously when the common denominator is prime to `15`. -/
theorem rational_and_two_reductions (D : ClearedMumford)
    (h3 : ¬(3 : ℤ) ∣ D.denominator)
    (h5 : ¬(5 : ℤ) ∣ D.denominator) :
    D.toAffineMumford.u ∣
        sexticPolynomial - D.toAffineMumford.v ^ 2 ∧
      (IsReducedEncoding (D.reduceF3 h3).1 ∧
        recordU (D.reduceF3 h3).1 ∣
          sextic - recordV (D.reduceF3 h3).1 ^ 2) ∧
      (IsReducedEncodingF5 (D.reduceF5 h5).1 ∧
        recordUF5 (D.reduceF5 h5).1 ∣
          sexticF5 - recordVF5 (D.reduceF5 h5).1 ^ 2) :=
  ⟨D.toAffineMumford.equation_mod_u, D.reduceF3_spec h3,
    D.reduceF5_spec h5⟩

end ClearedMumford

end MazurTorsion.XOneThirteenRationalMumfordReduction
