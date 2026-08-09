/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveEisensteinIdealSupport

/-!
# The explicit quotient map from the level-35 hyperelliptic model

The standard affine model of `X₀(35)` is

`y² = x⁸ - 4x⁷ - 6x⁶ - 4x⁵ - 9x⁴ + 4x³ - 6x² + 4x + 1`.

On this model the Atkin--Lehner involution `w₅` is
`(x,y) ↦ (-1/x, y/x⁴)`.  Its invariant functions

`u = x - 1/x`, `v = y(1 + 1/x⁴)`

satisfy a genus-one equation.  The further rational change

`w = (u-6)/(u+1)`,
`z = 7v/(2(u²+2)(u+1)²) - 1/2`

lands on the already checked rank-zero model
`z² + z = w³ + w² + 9w + 1`.

The formulas and their modular interpretation are recorded in B. Cais,
"Universal Families and Ruling out Small Primes", pp. 8--10, following
Galbraith and Kubert.  This file checks the rational algebra, all denominator
conditions, invariance under the displayed involution, and the genuine
downstream rational-point classification using the existing unconditional
finiteness theorem for the target model.  It does not identify a represented
integral modular curve with this affine equation; that geometric classifying
comparison remains explicit.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

/-- The degree-eight polynomial in the standard affine model of `X₀(35)`. -/
def xZeroThirtyFivePolynomial (x : ℚ) : ℚ :=
  x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 +
    4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1

/-- The standard affine equation used for the explicit `w₅` quotient. -/
def IsXZeroThirtyFiveAffinePoint (x y : ℚ) : Prop :=
  y ^ 2 = xZeroThirtyFivePolynomial x

/-- The abscissa of the displayed `w₅` involution. -/
def wFiveX (x : ℚ) : ℚ :=
  -1 / x

/-- The ordinate of the displayed `w₅` involution. -/
def wFiveY (x y : ℚ) : ℚ :=
  y / x ^ 4

/-- The first `w₅`-invariant quotient coordinate. -/
def quotientU (x : ℚ) : ℚ :=
  x - 1 / x

/-- The second `w₅`-invariant quotient coordinate. -/
def quotientV (x y : ℚ) : ℚ :=
  y * (1 + 1 / x ^ 4)

/-- The abscissa on the selected Weierstrass quotient model. -/
def quotientW (x : ℚ) : ℚ :=
  (quotientU x - 6) / (quotientU x + 1)

/-- The ordinate on the selected Weierstrass quotient model. -/
def quotientZ (x y : ℚ) : ℚ :=
  7 * quotientV x y /
      (2 * (quotientU x ^ 2 + 2) * (quotientU x + 1) ^ 2) - 1 / 2

/-- The displayed Atkin--Lehner abscissa is an involution on its rational-function domain. -/
theorem wFiveX_wFiveX {x : ℚ} (_hx : x ≠ 0) :
    wFiveX (wFiveX x) = x := by
  simp [wFiveX]

/-- The displayed Atkin--Lehner formula preserves the affine equation. -/
theorem wFive_preserves_affineEquation {x y : ℚ}
    (hx : x ≠ 0) (hxy : IsXZeroThirtyFiveAffinePoint x y) :
    IsXZeroThirtyFiveAffinePoint (wFiveX x) (wFiveY x y) := by
  dsimp only [IsXZeroThirtyFiveAffinePoint, wFiveX, wFiveY,
    xZeroThirtyFivePolynomial] at hxy ⊢
  field_simp [hx] at hxy ⊢
  nlinarith

/-- The first quotient coordinate is invariant under the displayed `w₅`. -/
theorem quotientU_wFive {x : ℚ} (_hx : x ≠ 0) :
    quotientU (wFiveX x) = quotientU x := by
  simp [quotientU, wFiveX]
  ring

/-- The second quotient coordinate is invariant under the displayed `w₅`. -/
theorem quotientV_wFive {x y : ℚ} (hx : x ≠ 0) :
    quotientV (wFiveX x) (wFiveY x y) = quotientV x y := by
  simp [quotientV, wFiveX, wFiveY]
  field_simp [hx]
  ring

/-- A finite rational abscissa never reaches the exceptional value `u=-1`. -/
theorem quotientU_add_one_ne_zero (x : ℚ) :
    quotientU x + 1 ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    norm_num [quotientU]
  intro hu
  have hquad : x ^ 2 + x - 1 = 0 := by
    have hu' := congrArg (fun q : ℚ ↦ q * x) hu
    dsimp only [quotientU] at hu'
    field_simp [hx] at hu'
    nlinarith
  have hfive : ¬ IsSquare (5 : ℚ) := by norm_num
  apply hfive
  refine ⟨2 * x + 1, ?_⟩
  nlinarith

/-- The second denominator in the quotient transformation is nonzero over `ℚ`. -/
theorem quotientU_sq_add_two_ne_zero (x : ℚ) :
    quotientU x ^ 2 + 2 ≠ 0 := by
  nlinarith [sq_nonneg (quotientU x)]

/-- The two invariant functions satisfy the affine quotient equation. -/
theorem quotient_invariants_equation {x y : ℚ}
    (hx : x ≠ 0) (hxy : IsXZeroThirtyFiveAffinePoint x y) :
    quotientV x y ^ 2 =
      (quotientU x + 1) * (quotientU x ^ 2 + 2) ^ 2 *
        (quotientU x ^ 3 - 5 * quotientU x ^ 2 +
          3 * quotientU x - 19) := by
  dsimp only [IsXZeroThirtyFiveAffinePoint, xZeroThirtyFivePolynomial,
    quotientU, quotientV] at hxy ⊢
  field_simp [hx] at hxy ⊢
  nlinarith

/-- The explicit invariant-coordinate change lands on the selected rank-zero
Weierstrass model. -/
theorem quotient_coordinates_equation {x y : ℚ}
    (hx : x ≠ 0) (hxy : IsXZeroThirtyFiveAffinePoint x y) :
    quotientZ x y ^ 2 + quotientZ x y =
      quotientW x ^ 3 + quotientW x ^ 2 + 9 * quotientW x + 1 := by
  have hinv := quotient_invariants_equation hx hxy
  have hu := quotientU_add_one_ne_zero x
  have hu2 := quotientU_sq_add_two_ne_zero x
  dsimp only [quotientW, quotientZ]
  field_simp [hu, hu2]
  linear_combination 49 * hinv

/-- The explicit quotient coordinates define an actual affine point of the
selected rank-zero elliptic curve. -/
noncomputable def quotientPoint (x y : ℚ) (hx : x ≠ 0)
    (hxy : IsXZeroThirtyFiveAffinePoint x y) :
    optimalQuotientModel.toAffine.Point :=
  .some (quotientW x) (quotientZ x y) (by
    apply optimalQuotientModel.toAffine.equation_iff_nonsingular.mp
    simpa [WeierstrassCurve.Affine.equation_iff,
      optimalQuotientModel] using quotient_coordinates_equation hx hxy)

/-- Since the selected quotient has finite rational point group of order
three, every rational point is zero or one of the two visible nonzero points. -/
theorem optimalQuotientModel_point_eq_zero_or_visible
    (P : optimalQuotientModel.toAffine.Point) :
    P = 0 ∨ P = modelThreeTorsion ∨ P = -modelThreeTorsion := by
  letI : Finite optimalQuotientModel.toAffine.Point :=
    optimalQuotientModel_finite
  obtain ⟨n, hn⟩ := torsion_point_eq_zsmul_modelThreeTorsion P
    (isOfFinAddOrder_of_finite P)
  have hnonneg : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hreduce : (n % 3) • modelThreeTorsion = n • modelThreeTorsion := by
    simpa [addOrderOf_modelThreeTorsion] using
      mod_addOrderOf_zsmul modelThreeTorsion n
  have hthree : (3 : ℤ) • modelThreeTorsion = 0 := by
    change (3 : ℕ) • modelThreeTorsion = 0
    rw [← addOrderOf_modelThreeTorsion]
    exact addOrderOf_nsmul_eq_zero modelThreeTorsion
  have htwo : (2 : ℤ) • modelThreeTorsion = -modelThreeTorsion := by
    calc
      (2 : ℤ) • modelThreeTorsion =
          (3 : ℤ) • modelThreeTorsion - modelThreeTorsion := by abel
      _ = -modelThreeTorsion := by rw [hthree]; simp
  rcases hcases with hzero | hone | htwo'
  · left
    rw [hn, ← hreduce, hzero, zero_zsmul]
  · right; left
    rw [hn, ← hreduce, hone, one_zsmul]
  · right; right
    rw [hn, ← hreduce, htwo', htwo]

/-- Every affine source point away from `x=0` would map to one of the two
visible nonzero quotient points, and hence would have quotient abscissa one. -/
theorem quotientW_eq_one_of_affinePoint {x y : ℚ}
    (hx : x ≠ 0) (hxy : IsXZeroThirtyFiveAffinePoint x y) :
    quotientW x = 1 := by
  let P := quotientPoint x y hx hxy
  rcases optimalQuotientModel_point_eq_zero_or_visible P with hzero | hvisible | hvisible
  · exact (WeierstrassCurve.Affine.Point.some_ne_zero _ hzero).elim
  · have hcoords : quotientW x = 1 ∧ quotientZ x y = 3 := by
      simpa only [P, quotientPoint, modelThreeTorsion,
        WeierstrassCurve.Affine.Point.some.injEq] using hvisible
    exact hcoords.1
  · have hcoords : quotientW x = 1 ∧
        quotientZ x y =
          optimalQuotientModel.toAffine.negY 1 3 := by
      simpa only [P, quotientPoint, modelThreeTorsion,
        WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] using hvisible
    exact hcoords.1

/-- The quotient abscissa of a finite rational `u`-coordinate cannot be one. -/
theorem quotientW_ne_one (x : ℚ) :
    quotientW x ≠ 1 := by
  intro hw
  have hu := quotientU_add_one_ne_zero x
  dsimp only [quotientW] at hw
  field_simp [hu] at hw
  linarith

/-- The complete affine rational-point classification on the displayed
hyperelliptic model: every affine rational point has `x=0`. -/
theorem xZeroThirtyFive_affine_abscissa_eq_zero {x y : ℚ}
    (hxy : IsXZeroThirtyFiveAffinePoint x y) :
    x = 0 := by
  by_contra hx
  exact quotientW_ne_one x (quotientW_eq_one_of_affinePoint hx hxy)

/-- The two affine rational points on the displayed level-35 model are
exactly `(0,1)` and `(0,-1)`.  The two points at infinity are outside this
affine chart. -/
theorem xZeroThirtyFive_affine_rational_points {x y : ℚ}
    (hxy : IsXZeroThirtyFiveAffinePoint x y) :
    x = 0 ∧ (y = 1 ∨ y = -1) := by
  have hx := xZeroThirtyFive_affine_abscissa_eq_zero hxy
  subst x
  constructor
  · rfl
  dsimp only [IsXZeroThirtyFiveAffinePoint,
    xZeroThirtyFivePolynomial] at hxy
  norm_num at hxy
  exact hxy

end MazurTorsion.OrderThirtyFive
