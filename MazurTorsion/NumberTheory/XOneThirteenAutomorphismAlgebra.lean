/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit

/-!
# Algebraic certificates for an automorphism of the `X₁(13)` sextic

This file records elementary identities for the completed-square model

`Y² = X⁶ + 2X⁵ + X⁴ + 2X³ + 6X² + 4X + 1`.

The generalized model

`y² + (x³ + x² + 1)y = x² + x`

appears on page 3 of P. Bruin, M. Derickx, and M. Stoll, *Elliptic curves
with a point of order 13 defined over cyclic cubic fields* (2021),
<https://www.mathe2.uni-bayreuth.de/stoll/papers/cyc13-v6.pdf>.  The source is
used here only for provenance of the curve model.  The completed-square
change of variables and every formula below are independently expanded and
checked by Lean; no source code is copied from the paper or its ancillary
files.

The rational map

`(x, Y) ↦ (-1 / (x + 1), Y / (x + 1)³)`

preserves the completed-square equation on its affine domain.  Its third
iterate is the hyperelliptic sign change and its sixth iterate is the
identity wherever all displayed affine denominators are nonzero.

This is deliberately only an algebraic certificate module.  It does not
construct a curve automorphism as a scheme morphism, a Jacobian, or an
endomorphism of a Jacobian.
-/

namespace MazurTorsion.XOneThirteenAutomorphismAlgebra

/-! ## The square-plus-four-square decomposition -/

/-- The quadratic expression `D = x(x+1)` in the cyclic-cubic quotient. -/
def D (x : ℚ) : ℚ :=
  x ^ 2 + x

/-- The cubic expression `N = x³ - 3x - 1`. -/
def N (x : ℚ) : ℚ :=
  x ^ 3 - 3 * x - 1

/-- The sum `A = N + D`. -/
def A (x : ℚ) : ℚ :=
  N x + D x

/-- The affine sextic defining the completed-square `X₁(13)` model. -/
def F (x : ℚ) : ℚ :=
  MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x

/-- The sextic is a square plus four times a square. -/
theorem F_eq_A_sq_add_four_D_sq (x : ℚ) :
    F x = A x ^ 2 + 4 * D x ^ 2 := by
  simp only [F, A, N, D,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]
  ring

/-- The same decomposition expanded in terms of `N` and `D`. -/
theorem F_eq_N_sq_add_two_ND_add_five_D_sq (x : ℚ) :
    F x = N x ^ 2 + 2 * N x * D x + 5 * D x ^ 2 := by
  simp only [F, N, D,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]
  ring

/-! ## Homogeneous invariance -/

/-- The binary sextic obtained by homogenizing `F` to degree six. -/
def FHomogeneous (X Z : ℚ) : ℚ :=
  X ^ 6 + 2 * X ^ 5 * Z + X ^ 4 * Z ^ 2 +
    2 * X ^ 3 * Z ^ 3 + 6 * X ^ 2 * Z ^ 4 +
    4 * X * Z ^ 5 + Z ^ 6

/-- Dehomogenizing the binary sextic at `Z = 1` recovers `F`. -/
@[simp]
theorem FHomogeneous_at_one (x : ℚ) :
    FHomogeneous x 1 = F x := by
  simp only [FHomogeneous, F,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]
  ring

/-- The rational binary sextic is the cast of the integral homogeneous
sextic used by the checked Pell-power split. -/
theorem FHomogeneous_intCast (a b : ℤ) :
    FHomogeneous (a : ℚ) (b : ℚ) =
      (MazurTorsion.XOneThirteenDescent.integerSexticHomogeneous a b : ℚ) := by
  norm_num [FHomogeneous,
    MazurTorsion.XOneThirteenDescent.integerSexticHomogeneous]

/-- The order-three fractional-linear action preserves the binary sextic. -/
theorem FHomogeneous_neg_right_add (X Z : ℚ) :
    FHomogeneous (-Z) (X + Z) = FHomogeneous X Z := by
  simp only [FHomogeneous]
  ring

/-! ## The completed-square model and its rational symmetry -/

/-- The coefficient of `y` in the generalized affine model. -/
def generalizedH (x : ℚ) : ℚ :=
  x ^ 3 + x ^ 2 + 1

/-- Exact residual identity for the substitution `Y = 2y + h(x)`. -/
theorem completed_square_residual_identity (x y : ℚ) :
    (2 * y + generalizedH x) ^ 2 - F x =
      4 * (y ^ 2 + generalizedH x * y - (x ^ 2 + x)) := by
  simp only [generalizedH, F,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]
  ring

/-- The completed-square equation as a predicate on affine coordinates. -/
def IsOnCompletedSquareModel (x Y : ℚ) : Prop :=
  Y ^ 2 = F x

/-- The abscissa of the rational affine symmetry. -/
def automorphismX (x : ℚ) : ℚ :=
  -1 / (x + 1)

/-- The ordinate of the rational affine symmetry. -/
def automorphismY (x Y : ℚ) : ℚ :=
  Y / (x + 1) ^ 3

/-- The rational affine symmetry on pairs of completed-square coordinates. -/
def affineAutomorphism (P : ℚ × ℚ) : ℚ × ℚ :=
  (automorphismX P.1, automorphismY P.1 P.2)

/-- Transformation law for the affine sextic. -/
theorem F_automorphismX (x : ℚ) (hx : x + 1 ≠ 0) :
    F (automorphismX x) = F x / (x + 1) ^ 6 := by
  simp only [F, automorphismX,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial]
  field_simp [hx]
  ring

/-- The rational affine symmetry preserves the completed-square equation. -/
theorem affineAutomorphism_preserves
    (x Y : ℚ) (hx : x + 1 ≠ 0)
    (hP : IsOnCompletedSquareModel x Y) :
    IsOnCompletedSquareModel (automorphismX x) (automorphismY x Y) := by
  rw [IsOnCompletedSquareModel, automorphismY, F_automorphismX x hx]
  rw [IsOnCompletedSquareModel] at hP
  rw [← hP]
  field_simp [hx]

/-- Explicit second iterate on the common affine domain. -/
theorem affineAutomorphism_sq
    (x Y : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    affineAutomorphism (affineAutomorphism (x, Y)) =
    (-(x + 1) / x, Y / x ^ 3) := by
  apply Prod.ext
  · change -1 / (-1 / (x + 1) + 1) = -(x + 1) / x
    (field_simp [hx, hx1]; ring)
  · change (Y / (x + 1) ^ 3) / (-1 / (x + 1) + 1) ^ 3 =
      Y / x ^ 3
    (field_simp [hx, hx1]; ring)

/-- The third iterate is the hyperelliptic sign change. -/
theorem affineAutomorphism_cube
    (x Y : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    affineAutomorphism
        (affineAutomorphism (affineAutomorphism (x, Y))) =
      (x, -Y) := by
  rw [affineAutomorphism_sq x Y hx hx1]
  apply Prod.ext
  · change -1 / (-(x + 1) / x + 1) = x
    (field_simp [hx]; ring)
  · change (Y / x ^ 3) / (-(x + 1) / x + 1) ^ 3 = -Y
    (field_simp [hx]; ring)

/-- The sixth iterate is the identity on the common affine domain. -/
theorem affineAutomorphism_sixth
    (x Y : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    affineAutomorphism (affineAutomorphism (affineAutomorphism
      (affineAutomorphism (affineAutomorphism (affineAutomorphism (x, Y)))))) =
      (x, Y) := by
  rw [affineAutomorphism_cube x Y hx hx1]
  rw [affineAutomorphism_cube x (-Y) hx hx1]
  simp

/-! ## Pure coefficient-matrix arithmetic -/

/-- The coefficient matrix suggested by the pullback formulas
`ω₀ ↦ ω₀ + ω₁` and `ω₁ ↦ -ω₀`.

This definition records only a literal rational matrix.  It does not claim
that differentials or a Jacobian have been constructed. -/
def differentialCoefficientMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, -1; 1, 0]

/-- The coefficient matrix satisfies `M² - M + I = 0`. -/
theorem differentialCoefficientMatrix_quadratic :
    differentialCoefficientMatrix * differentialCoefficientMatrix -
        differentialCoefficientMatrix + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [differentialCoefficientMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

end MazurTorsion.XOneThirteenAutomorphismAlgebra
