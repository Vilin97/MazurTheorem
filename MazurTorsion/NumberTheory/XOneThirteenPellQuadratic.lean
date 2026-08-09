/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenMumfordCoordinates

/-!
# The fixed quadratic coordinate algebra for the `X₁(13)` Pell function

For the fixed equation `Y² = sexticPolynomial`, a polynomial function has a
normal-form pair `(A, B)`, representing `A + B Y`.  This file defines the
normal-form multiplication, conjugation, and norm directly on such pairs.
It does not construct a function field or a divisor group.

The degree-`19` Pell numerator and degree-`16` Pell denominator are lifted to
polynomials.  Their existing checked Pell identity becomes the polynomial
norm identity `H² - f K² = -4`, and hence supplies an explicit two-sided
inverse for `H + K Y`.  This is the affine unit certificate used by a later
calculation of its orders at the two points at infinity.
-/

namespace MazurTorsion.XOneThirteenMumford

open Polynomial

noncomputable section

/-- A normal-form expression `base + radical * Y` subject to the fixed
relation `Y² = sexticPolynomial`. -/
@[ext]
structure QuadraticCoordinate where
  base : ℚ[X]
  radical : ℚ[X]

namespace QuadraticCoordinate

/-- A polynomial regarded as an expression with zero `Y` coefficient. -/
def scalar (a : ℚ[X]) : QuadraticCoordinate :=
  ⟨a, 0⟩

/-- The multiplicative identity in fixed quadratic coordinates. -/
def one : QuadraticCoordinate :=
  scalar 1

/-- Multiplication reduced using `Y² = sexticPolynomial`. -/
def mul (q r : QuadraticCoordinate) : QuadraticCoordinate :=
  ⟨q.base * r.base + sexticPolynomial * q.radical * r.radical,
    q.base * r.radical + q.radical * r.base⟩

/-- Conjugation induced by the hyperelliptic involution `Y ↦ -Y`. -/
def conj (q : QuadraticCoordinate) : QuadraticCoordinate :=
  ⟨q.base, -q.radical⟩

/-- The polynomial norm `A² - sexticPolynomial * B²`. -/
def norm (q : QuadraticCoordinate) : ℚ[X] :=
  q.base ^ 2 - sexticPolynomial * q.radical ^ 2

/-- Polynomial scaling of both coordinates. -/
def scale (a : ℚ[X]) (q : QuadraticCoordinate) : QuadraticCoordinate :=
  ⟨a * q.base, a * q.radical⟩

@[simp] theorem scalar_base (a : ℚ[X]) : (scalar a).base = a := rfl

@[simp] theorem scalar_radical (a : ℚ[X]) : (scalar a).radical = 0 := rfl

@[simp] theorem one_base : one.base = 1 := rfl

@[simp] theorem one_radical : one.radical = 0 := rfl

@[simp] theorem mul_base (q r : QuadraticCoordinate) :
    (mul q r).base =
      q.base * r.base + sexticPolynomial * q.radical * r.radical := rfl

@[simp] theorem mul_radical (q r : QuadraticCoordinate) :
    (mul q r).radical =
      q.base * r.radical + q.radical * r.base := rfl

@[simp] theorem conj_base (q : QuadraticCoordinate) :
    (conj q).base = q.base := rfl

@[simp] theorem conj_radical (q : QuadraticCoordinate) :
    (conj q).radical = -q.radical := rfl

@[simp]
theorem conj_conj (q : QuadraticCoordinate) : conj (conj q) = q := by
  apply QuadraticCoordinate.ext <;> simp

theorem mul_comm (q r : QuadraticCoordinate) : mul q r = mul r q := by
  apply QuadraticCoordinate.ext <;> simp <;> ring

@[simp]
theorem one_mul (q : QuadraticCoordinate) : mul one q = q := by
  apply QuadraticCoordinate.ext <;> simp [mul, one, scalar]

@[simp]
theorem mul_one (q : QuadraticCoordinate) : mul q one = q := by
  rw [mul_comm]
  exact one_mul q

theorem mul_assoc (q r s : QuadraticCoordinate) :
    mul (mul q r) s = mul q (mul r s) := by
  apply QuadraticCoordinate.ext <;> simp <;> ring

/-- Multiplying an expression by its conjugate leaves its scalar norm. -/
theorem mul_conj (q : QuadraticCoordinate) :
    mul q (conj q) = scalar (norm q) := by
  apply QuadraticCoordinate.ext <;> simp [norm, scalar] <;> ring

/-- The fixed quadratic norm is multiplicative. -/
theorem norm_mul (q r : QuadraticCoordinate) :
    norm (mul q r) = norm q * norm r := by
  simp only [norm, mul_base, mul_radical]
  ring

theorem mul_scale_right (q r : QuadraticCoordinate) (a : ℚ[X]) :
    mul q (scale a r) = scale a (mul q r) := by
  apply QuadraticCoordinate.ext <;> simp [scale] <;> ring

/-- Evaluation of `A + B Y` at an affine pair `(x, y)`. -/
def evalOnCurve (x y : ℚ) (q : QuadraticCoordinate) : ℚ :=
  q.base.eval x + y * q.radical.eval x

@[simp]
theorem evalOnCurve_scalar (x y : ℚ) (a : ℚ[X]) :
    evalOnCurve x y (scalar a) = a.eval x := by
  simp [evalOnCurve, scalar]

@[simp]
theorem evalOnCurve_one (x y : ℚ) : evalOnCurve x y one = 1 := by
  simp [one]

/-- Evaluation respects the reduced multiplication at points of the fixed
sextic. -/
theorem evalOnCurve_mul
    (x y : ℚ)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x)
    (q r : QuadraticCoordinate) :
    evalOnCurve x y (mul q r) =
      evalOnCurve x y q * evalOnCurve x y r := by
  simp only [evalOnCurve, mul_base, mul_radical, eval_add, eval_mul,
    eval_sexticPolynomial]
  rw [← hcurve]
  ring

@[simp]
theorem evalOnCurve_conj (x y : ℚ) (q : QuadraticCoordinate) :
    evalOnCurve x y (conj q) = evalOnCurve x (-y) q := by
  simp [evalOnCurve]

end QuadraticCoordinate

/-! ## The fixed Pell unit -/

/-- Polynomial lift of the existing degree-`19` Pell numerator. -/
def pellHPolynomial : ℚ[X] :=
  X ^ 19 + 3 * X ^ 18 + 2 * X ^ 17 + 5 * X ^ 16 +
    22 * X ^ 15 + 22 * X ^ 14 + 10 * X ^ 13 +
    54 * X ^ 12 + 78 * X ^ 11 + 20 * X ^ 10 +
    51 * X ^ 9 + 113 * X ^ 8 + 36 * X ^ 7 +
    13 * X ^ 6 + 66 * X ^ 5 + 26 * X ^ 4 -
    2 * X ^ 3 + 12 * X ^ 2 + 4 * X

/-- Polynomial lift of the existing degree-`16` Pell denominator. -/
def pellKPolynomial : ℚ[X] :=
  X ^ 16 + 2 * X ^ 15 + 4 * X ^ 13 + 14 * X ^ 12 +
    4 * X ^ 11 + 2 * X ^ 10 + 32 * X ^ 9 +
    18 * X ^ 8 - 8 * X ^ 7 + 29 * X ^ 6 +
    24 * X ^ 5 - 10 * X ^ 4 + 10 * X ^ 3 +
    10 * X ^ 2 - 4 * X + 2

@[simp]
theorem eval_pellHPolynomial (x : ℚ) :
    pellHPolynomial.eval x =
      MazurTorsion.XOneThirteenDescent.pellH x := by
  simp [pellHPolynomial, MazurTorsion.XOneThirteenDescent.pellH]

@[simp]
theorem eval_pellKPolynomial (x : ℚ) :
    pellKPolynomial.eval x =
      MazurTorsion.XOneThirteenDescent.pellK x := by
  simp [pellKPolynomial, MazurTorsion.XOneThirteenDescent.pellK]

/-- The normal-form polynomial expression `H + K Y`. -/
def pellCoordinate : QuadraticCoordinate :=
  ⟨pellHPolynomial, pellKPolynomial⟩

@[simp]
theorem evalOnCurve_pellCoordinate (x y : ℚ) :
    QuadraticCoordinate.evalOnCurve x y pellCoordinate =
      MazurTorsion.XOneThirteenDescent.pellH x +
        y * MazurTorsion.XOneThirteenDescent.pellK x := by
  simp [QuadraticCoordinate.evalOnCurve, pellCoordinate]

/-- The scalar Pell identity upgraded to an equality of polynomials. -/
theorem pell_polynomial_identity :
    pellHPolynomial ^ 2 - sexticPolynomial * pellKPolynomial ^ 2 =
      C (-4) := by
  apply Polynomial.funext
  intro x
  simp only [eval_sub, eval_pow, eval_mul, eval_pellHPolynomial,
    eval_sexticPolynomial, eval_pellKPolynomial, eval_C]
  exact MazurTorsion.XOneThirteenDescent.pell_identity x

/-- The fixed Pell coordinate has constant norm `-4`. -/
@[simp]
theorem pellCoordinate_norm :
    QuadraticCoordinate.norm pellCoordinate = C (-4) := by
  simpa [QuadraticCoordinate.norm, pellCoordinate] using
    pell_polynomial_identity

/-- An explicit inverse for `H + K Y`, namely `(-1/4)(H - K Y)`. -/
def pellCoordinateInverse : QuadraticCoordinate :=
  QuadraticCoordinate.scale (C (-1 / 4 : ℚ))
    (QuadraticCoordinate.conj pellCoordinate)

theorem pellCoordinate_mul_inverse :
    QuadraticCoordinate.mul pellCoordinate pellCoordinateInverse =
      QuadraticCoordinate.one := by
  calc
    QuadraticCoordinate.mul pellCoordinate pellCoordinateInverse =
        QuadraticCoordinate.scale (C (-1 / 4 : ℚ))
          (QuadraticCoordinate.mul pellCoordinate
            (QuadraticCoordinate.conj pellCoordinate)) := by
      exact QuadraticCoordinate.mul_scale_right _ _ _
    _ = QuadraticCoordinate.scale (C (-1 / 4 : ℚ))
        (QuadraticCoordinate.scalar
          (QuadraticCoordinate.norm pellCoordinate)) := by
      rw [QuadraticCoordinate.mul_conj]
    _ = QuadraticCoordinate.one := by
      apply QuadraticCoordinate.ext
      · simp only [QuadraticCoordinate.scale, QuadraticCoordinate.scalar,
          QuadraticCoordinate.one]
        rw [pellCoordinate_norm, ← C_mul]
        norm_num
      · simp [QuadraticCoordinate.scale, QuadraticCoordinate.scalar,
          QuadraticCoordinate.one]

theorem pellCoordinate_inverse_mul :
    QuadraticCoordinate.mul pellCoordinateInverse pellCoordinate =
      QuadraticCoordinate.one := by
  rw [QuadraticCoordinate.mul_comm]
  exact pellCoordinate_mul_inverse

/-- The explicit two-sided unit certificate for the Pell coordinate. -/
theorem pellCoordinate_unit_relation :
    QuadraticCoordinate.mul pellCoordinate pellCoordinateInverse =
        QuadraticCoordinate.one ∧
      QuadraticCoordinate.mul pellCoordinateInverse pellCoordinate =
        QuadraticCoordinate.one :=
  ⟨pellCoordinate_mul_inverse, pellCoordinate_inverse_mul⟩

end

end MazurTorsion.XOneThirteenMumford
