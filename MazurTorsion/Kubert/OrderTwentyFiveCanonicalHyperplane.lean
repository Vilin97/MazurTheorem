/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalMarked
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Coordinate-hyperplane intersections on the order-25 canonical carrier

The first canonical cyclic function is `r₀ = -z/w`.  Its divisor is therefore
the difference between the hyperplane sections `z = 0` and `w = 0`.  This
file computes both intersections in affine charts by exact elimination.

On the two charts covering `w = 0`, the residual univariate equations are

* `Y²(Y+1)` on `z = 1`, giving multiplicities two and one at cusps 3 and 1;
* `Y³` on `x = 1`, giving multiplicity three at cusp 4.

On the two charts covering `z = 0`, they are

* `Y³(Y-1)` on `w = 1`, giving multiplicities three and one at cusps 0 and 2;
* `Y²(Y-1)` on `x = 1`, giving multiplicities two and one at cusps 4 and 2.

The overlap point is cusp 2, so these certify the coordinate-section tables

`ord(z) = (3,0,1,0,2)` and `ord(w) = (0,1,0,2,3)`.

Their difference is exactly `(3,-1,1,-2,-1)`, the order vector consumed by
the determinant-71 Picard interface.  The named downstream consumer
`orderTwentyFiveCanonical_rootZero_cuspOrderVector` records this match.
Passing these checked affine intersection certificates to a global order
system for the represented projective curve remains the geometric boundary.
-/

namespace MazurTorsion.Kubert

/-- Elimination on the `z = 1` chart of the hyperplane `w = 0`. -/
theorem orderTwentyFiveCanonical_w_zChart_elimination
    {R : Type*} [CommRing R] (x y : R) :
    orderTwentyFiveCanonicalCubic x y 1 0 +
        y * orderTwentyFiveCanonicalQuadric x y 1 0 =
      y ^ 2 * (y + 1) := by
  simp only [orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic]
  ring

/-- Elimination on the `x = 1` chart of the hyperplane `w = 0`. -/
theorem orderTwentyFiveCanonical_w_xChart_elimination
    {R : Type*} [CommRing R] (y z : R) :
    y * orderTwentyFiveCanonicalQuadric 1 y z 0 -
        (y - 1) * orderTwentyFiveCanonicalCubic 1 y z 0 =
      y ^ 3 := by
  simp only [orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic]
  ring

/-- Elimination on the `w = 1` chart of the hyperplane `z = 0`. -/
theorem orderTwentyFiveCanonical_z_wChart_elimination
    {R : Type*} [CommRing R] (x y : R) :
    orderTwentyFiveCanonicalCubic x y 0 1 =
      y ^ 3 * (y - 1) +
        orderTwentyFiveCanonicalQuadric x y 0 1 *
          (-x - y ^ 2 + y) := by
  simp only [orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic]
  ring

/-- Elimination on the `x = 1` chart of the hyperplane `z = 0`. -/
theorem orderTwentyFiveCanonical_z_xChart_elimination
    {R : Type*} [CommRing R] (y w : R) :
    orderTwentyFiveCanonicalCubic 1 y 0 w + y ^ 2 * (y - 1) =
      (y - 1) * orderTwentyFiveCanonicalQuadric 1 y 0 w := by
  simp only [orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic]
  ring

/-- The `z = 1` chart of `w = 0` consists of cusps 3 and 1. -/
theorem orderTwentyFiveCanonical_w_zChart_locus
    {K : Type*} [Field K] (x y : K) :
    OrderTwentyFiveCanonicalOnCurve x y 1 0 ↔
      x = y ^ 2 + y ∧ (y = 0 ∨ y = -1) := by
  constructor
  · rintro ⟨hQ, hC⟩
    have hx : x = y ^ 2 + y := by
      simp only [orderTwentyFiveCanonicalQuadric] at hQ
      linear_combination -hQ
    have hfactor : y ^ 2 * (y + 1) = 0 := by
      rw [← orderTwentyFiveCanonical_w_zChart_elimination x y, hQ, hC]
      ring
    rcases mul_eq_zero.mp hfactor with hy | hy
    · exact ⟨hx, Or.inl (sq_eq_zero_iff.mp hy)⟩
    · exact ⟨hx, Or.inr (eq_neg_of_add_eq_zero_left hy)⟩
  · rintro ⟨hx, hy | hy⟩
    · subst y
      norm_num at hx
      subst x
      norm_num [OrderTwentyFiveCanonicalOnCurve,
        orderTwentyFiveCanonicalQuadric,
        orderTwentyFiveCanonicalCubic]
    · subst y
      norm_num at hx
      subst x
      norm_num [OrderTwentyFiveCanonicalOnCurve,
        orderTwentyFiveCanonicalQuadric,
        orderTwentyFiveCanonicalCubic]

/-- The `x = 1` chart of `w = 0` contains only cusp 4. -/
theorem orderTwentyFiveCanonical_w_xChart_locus
    {K : Type*} [Field K] (y z : K) :
    OrderTwentyFiveCanonicalOnCurve 1 y z 0 ↔ y = 0 ∧ z = 0 := by
  constructor
  · rintro ⟨hQ, hC⟩
    have hycube : y ^ 3 = 0 := by
      rw [← orderTwentyFiveCanonical_w_xChart_elimination y z, hQ, hC]
      ring
    have hy : y = 0 := by simpa using hycube
    have hz : z = 0 := by
      simp only [orderTwentyFiveCanonicalQuadric, hy, zero_mul] at hQ
      simpa using hQ.symm
    exact ⟨hy, hz⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [OrderTwentyFiveCanonicalOnCurve,
      orderTwentyFiveCanonicalQuadric,
      orderTwentyFiveCanonicalCubic]

/-- The `w = 1` chart of `z = 0` consists of cusps 0 and 2. -/
theorem orderTwentyFiveCanonical_z_wChart_locus
    {K : Type*} [Field K] (x y : K) :
    OrderTwentyFiveCanonicalOnCurve x y 0 1 ↔
      x = y ^ 2 ∧ (y = 0 ∨ y = 1) := by
  constructor
  · rintro ⟨hQ, hC⟩
    have hx : x = y ^ 2 := by
      simp only [orderTwentyFiveCanonicalQuadric] at hQ
      linear_combination -hQ
    have hfactor : y ^ 3 * (y - 1) = 0 := by
      rw [orderTwentyFiveCanonical_z_wChart_elimination x y, hQ] at hC
      simpa using hC
    rcases mul_eq_zero.mp hfactor with hy | hy
    · exact ⟨hx, Or.inl (by simpa using hy)⟩
    · exact ⟨hx, Or.inr (sub_eq_zero.mp hy)⟩
  · rintro ⟨hx, hy | hy⟩
    · subst y
      norm_num at hx
      subst x
      norm_num [OrderTwentyFiveCanonicalOnCurve,
        orderTwentyFiveCanonicalQuadric,
        orderTwentyFiveCanonicalCubic]
    · subst y
      norm_num at hx
      subst x
      norm_num [OrderTwentyFiveCanonicalOnCurve,
        orderTwentyFiveCanonicalQuadric,
        orderTwentyFiveCanonicalCubic]

/-- The `x = 1` chart of `z = 0` consists of cusps 4 and 2. -/
theorem orderTwentyFiveCanonical_z_xChart_locus
    {K : Type*} [Field K] (y w : K) :
    OrderTwentyFiveCanonicalOnCurve 1 y 0 w ↔
      w = y ^ 2 ∧ (y = 0 ∨ y = 1) := by
  constructor
  · rintro ⟨hQ, hC⟩
    have hw : w = y ^ 2 := by
      simp only [orderTwentyFiveCanonicalQuadric] at hQ
      linear_combination -hQ
    have hfactor : y ^ 2 * (y - 1) = 0 := by
      have hid := orderTwentyFiveCanonical_z_xChart_elimination y w
      rw [hQ, hC] at hid
      simpa using hid.symm
    rcases mul_eq_zero.mp hfactor with hy | hy
    · exact ⟨hw, Or.inl (sq_eq_zero_iff.mp hy)⟩
    · exact ⟨hw, Or.inr (sub_eq_zero.mp hy)⟩
  · rintro ⟨hw, hy | hy⟩
    · subst y
      norm_num at hw
      subst w
      norm_num [OrderTwentyFiveCanonicalOnCurve,
        orderTwentyFiveCanonicalQuadric,
        orderTwentyFiveCanonicalCubic]
    · subst y
      norm_num at hw
      subst w
      norm_num [OrderTwentyFiveCanonicalOnCurve,
        orderTwentyFiveCanonicalQuadric,
        orderTwentyFiveCanonicalCubic]

/-- The charts `z = 1` and `x = 1` cover the nonzero intersection with
`w = 0`. -/
theorem orderTwentyFiveCanonical_w_hyperplane_chart_cover
    (p : OrderTwentyFiveCanonicalCoordinates ℚ)
    (hnonzero : OrderTwentyFiveCanonicalCoordinatesNonzero p.x p.y p.z p.w)
    (hcurve : p.OnCurve) (hw : p.w = 0) :
    p.z ≠ 0 ∨ p.x ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  rcases h with ⟨hz, hx⟩
  have hy : p.y = 0 := by
    have hQ := hcurve.1
    simp only [orderTwentyFiveCanonicalQuadric, hx, hz, hw,
      mul_zero, sub_zero, add_zero] at hQ
    exact sq_eq_zero_iff.mp hQ
  exact hnonzero.elim (fun hx' ↦ hx' hx)
    (fun hy' ↦ hy'.elim (fun hy' ↦ hy' hy)
      (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw)))

/-- The charts `w = 1` and `x = 1` cover the nonzero intersection with
`z = 0`. -/
theorem orderTwentyFiveCanonical_z_hyperplane_chart_cover
    (p : OrderTwentyFiveCanonicalCoordinates ℚ)
    (hnonzero : OrderTwentyFiveCanonicalCoordinatesNonzero p.x p.y p.z p.w)
    (hcurve : p.OnCurve) (hz : p.z = 0) :
    p.w ≠ 0 ∨ p.x ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  rcases h with ⟨hw, hx⟩
  have hy : p.y = 0 := by
    have hQ := hcurve.1
    simp only [orderTwentyFiveCanonicalQuadric, hx, hz, hw,
      mul_zero, sub_zero, add_zero] at hQ
    exact sq_eq_zero_iff.mp hQ
  exact hnonzero.elim (fun hx' ↦ hx' hx)
    (fun hy' ↦ hy'.elim (fun hy' ↦ hy' hy)
      (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw)))

/-- Residual intersection polynomial for `w = 0` on `z = 1`. -/
noncomputable def orderTwentyFiveCanonicalWZIntersectionPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 * (Polynomial.X + Polynomial.C 1)

/-- Residual intersection polynomial for `w = 0` on `x = 1`. -/
noncomputable def orderTwentyFiveCanonicalWXIntersectionPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 3

/-- Residual intersection polynomial for `z = 0` on `w = 1`. -/
noncomputable def orderTwentyFiveCanonicalZWIntersectionPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 3 * (Polynomial.X - Polynomial.C 1)

/-- Residual intersection polynomial for `z = 0` on `x = 1`. -/
noncomputable def orderTwentyFiveCanonicalZXIntersectionPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C 1)

private theorem rootMultiplicity_pow_mul_distinct
    (r s : ℚ) (n : ℕ) (hrs : r ≠ s) :
    Polynomial.rootMultiplicity r
        ((Polynomial.X - Polynomial.C r) ^ n *
          (Polynomial.X - Polynomial.C s)) = n ∧
      Polynomial.rootMultiplicity s
        ((Polynomial.X - Polynomial.C r) ^ n *
          (Polynomial.X - Polynomial.C s)) = 1 := by
  constructor
  · rw [mul_comm]
    rw [Polynomial.rootMultiplicity_mul_X_sub_C_pow
      (Polynomial.X_sub_C_ne_zero s)]
    rw [Polynomial.rootMultiplicity_X_sub_C]
    simp [hrs]
  · rw [show Polynomial.X - Polynomial.C s =
        (Polynomial.X - Polynomial.C s) ^ 1 by ring]
    rw [Polynomial.rootMultiplicity_mul_X_sub_C_pow
      (pow_ne_zero n (Polynomial.X_sub_C_ne_zero r))]
    have hnot :
        ¬Polynomial.IsRoot ((Polynomial.X - Polynomial.C r) ^ n) s := by
      simp [Polynomial.IsRoot, sub_ne_zero.mpr hrs.symm]
    rw [Polynomial.rootMultiplicity_eq_zero hnot]

/-- Exact local multiplicities of `w = 0` on the `z = 1` chart. -/
theorem orderTwentyFiveCanonicalWZIntersectionPolynomial_rootMultiplicities :
    Polynomial.rootMultiplicity 0
        orderTwentyFiveCanonicalWZIntersectionPolynomial = 2 ∧
      Polynomial.rootMultiplicity (-1)
        orderTwentyFiveCanonicalWZIntersectionPolynomial = 1 := by
  have h := rootMultiplicity_pow_mul_distinct (0 : ℚ) (-1) 2 (by norm_num)
  simpa [orderTwentyFiveCanonicalWZIntersectionPolynomial] using h

/-- Exact local multiplicity of `w = 0` on the `x = 1` chart. -/
theorem orderTwentyFiveCanonicalWXIntersectionPolynomial_rootMultiplicity :
    Polynomial.rootMultiplicity 0
        orderTwentyFiveCanonicalWXIntersectionPolynomial = 3 := by
  simpa [orderTwentyFiveCanonicalWXIntersectionPolynomial] using
    (Polynomial.rootMultiplicity_X_sub_C_pow (R := ℚ) 0 3)

/-- Exact local multiplicities of `z = 0` on the `w = 1` chart. -/
theorem orderTwentyFiveCanonicalZWIntersectionPolynomial_rootMultiplicities :
    Polynomial.rootMultiplicity 0
        orderTwentyFiveCanonicalZWIntersectionPolynomial = 3 ∧
      Polynomial.rootMultiplicity 1
        orderTwentyFiveCanonicalZWIntersectionPolynomial = 1 := by
  have h := rootMultiplicity_pow_mul_distinct (0 : ℚ) 1 3 (by norm_num)
  simpa [orderTwentyFiveCanonicalZWIntersectionPolynomial] using h

/-- Exact local multiplicities of `z = 0` on the `x = 1` chart. -/
theorem orderTwentyFiveCanonicalZXIntersectionPolynomial_rootMultiplicities :
    Polynomial.rootMultiplicity 0
        orderTwentyFiveCanonicalZXIntersectionPolynomial = 2 ∧
      Polynomial.rootMultiplicity 1
        orderTwentyFiveCanonicalZXIntersectionPolynomial = 1 := by
  have h := rootMultiplicity_pow_mul_distinct (0 : ℚ) 1 2 (by norm_num)
  simpa [orderTwentyFiveCanonicalZXIntersectionPolynomial] using h

/-- Expected orders of the coordinate section `z` at the five cyclic cusps,
now certified by the affine intersection polynomials above. -/
def orderTwentyFiveCanonicalZCuspOrder : Fin 5 → ℤ :=
  ![3, 0, 1, 0, 2]

/-- Expected orders of the coordinate section `w` at the five cyclic cusps,
now certified by the affine intersection polynomials above. -/
def orderTwentyFiveCanonicalWCuspOrder : Fin 5 → ℤ :=
  ![0, 1, 0, 2, 3]

/-- The difference of the two certified coordinate-section tables is the
canonical cyclic-unit order vector `(3,-1,1,-2,-1)`. -/
theorem orderTwentyFiveCanonical_rootZero_cuspOrderVector (i : Fin 5) :
    orderTwentyFiveCanonicalZCuspOrder i -
        orderTwentyFiveCanonicalWCuspOrder i =
      orderTwentyFiveCuspOrder (0 : Fin 5) 1 2 3 4 i := by
  fin_cases i <;>
    simp [orderTwentyFiveCanonicalZCuspOrder,
      orderTwentyFiveCanonicalWCuspOrder,
      orderTwentyFiveCuspOrder, Matrix.cons_val_zero, Fin.ext_iff]

end MazurTorsion.Kubert
