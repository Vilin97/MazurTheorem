/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit

/-!
# Affine Mumford coordinates for the `X₁(13)` sextic

This file records the small amount of Mumford-coordinate infrastructure needed
to state later computations on the fixed curve

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

`AffineMumford` is deliberately only a polynomial coordinate record.  In
particular, this file neither constructs a divisor-class quotient nor claims
that every such record determines a point of a Jacobian.  The checked
operation below is hyperelliptic conjugation `(u, v) ↦ (u, -v)`.
-/

namespace MazurTorsion.XOneThirteenDescent

open Polynomial

noncomputable section

/-- The `X₁(13)` sextic as a polynomial over `ℚ`. -/
def mumfordSextic : ℚ[X] :=
  X ^ 6 + C 2 * X ^ 5 + X ^ 4 + C 2 * X ^ 3 +
    C 6 * X ^ 2 + C 4 * X + 1

@[simp]
theorem eval_mumfordSextic (x : ℚ) :
    mumfordSextic.eval x =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x := by
  simp [mumfordSextic,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]

/-- Affine Mumford polynomial coordinates of support degree at most two.

The divisibility condition says that `v` interpolates the ordinate on the
affine support cut out by `u`.  This is a coordinate record, not a quotient by
principal divisors; for the even-degree model it also contains no choice of a
point at infinity. -/
@[ext]
structure AffineMumford where
  /-- The monic affine support polynomial. -/
  u : ℚ[X]
  /-- The interpolating ordinate polynomial. -/
  v : ℚ[X]
  u_monic : u.Monic
  u_natDegree_le : u.natDegree ≤ 2
  v_degree_lt : v.degree < u.degree
  equation_mod_u : u ∣ mumfordSextic - v ^ 2

namespace AffineMumford

/-- Empty affine support, represented by `(1, 0)`. -/
def empty : AffineMumford where
  u := 1
  v := 0
  u_monic := monic_one
  u_natDegree_le := by simp
  v_degree_lt := by simp
  equation_mod_u := by simp

/-- Hyperelliptic conjugation on affine Mumford coordinates. -/
def neg (D : AffineMumford) : AffineMumford where
  u := D.u
  v := -D.v
  u_monic := D.u_monic
  u_natDegree_le := D.u_natDegree_le
  v_degree_lt := by simpa using D.v_degree_lt
  equation_mod_u := by simpa using D.equation_mod_u

@[simp] theorem empty_u : empty.u = 1 := rfl

@[simp] theorem empty_v : empty.v = 0 := rfl

@[simp] theorem neg_u (D : AffineMumford) : (neg D).u = D.u := rfl

@[simp] theorem neg_v (D : AffineMumford) : (neg D).v = -D.v := rfl

@[simp]
theorem neg_empty : neg empty = empty := by
  rfl

@[simp]
theorem neg_neg (D : AffineMumford) : neg (neg D) = D := by
  apply AffineMumford.ext <;> simp

/-- The degree-one affine Mumford coordinates attached to a rational point on
the fixed sextic. -/
def ofPoint (x y : ℚ)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x) :
    AffineMumford where
  u := X - C x
  v := C y
  u_monic := monic_X_sub_C x
  u_natDegree_le := by simp
  v_degree_lt := by
    rw [degree_X_sub_C]
    exact degree_C_le.trans_lt (by norm_num)
  equation_mod_u := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_C,
      eval_mumfordSextic, hcurve]
    ring

@[simp]
theorem ofPoint_u (x y : ℚ) (hcurve) :
    (ofPoint x y hcurve).u = X - C x := rfl

@[simp]
theorem ofPoint_v (x y : ℚ) (hcurve) :
    (ofPoint x y hcurve).v = C y := rfl

/-- Hyperelliptic conjugation of a point record negates its ordinate. -/
theorem neg_ofPoint (x y : ℚ)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x) :
    neg (ofPoint x y hcurve) =
      ofPoint x (-y) (by simpa using hcurve) := by
  apply AffineMumford.ext <;> simp

end AffineMumford

end

end MazurTorsion.XOneThirteenDescent
