/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenRealCubicQuotient

/-!
# The visible seven-torsion on the `X₁(18)` elliptic quotient

The point `(1,0)` on the real-cubic quotient has exact order seven.  This
file checks its first four multiples directly in the affine group law.  In
particular, every affine point in the generated subgroup has abscissa among
`1`, `3-τ²`, and `1-τ`.

No assertion that this subgroup exhausts the Mordell--Weil group is made
here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientSevenTorsion

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient

private theorem tau_ne_zero : tau ≠ 0 := by
  intro h
  have := tau_cubic
  rw [h] at this
  norm_num at this

private theorem tau_add_one_ne_zero : tau + 1 ≠ 0 := by
  intro h
  have ht : tau = -1 := by
    calc
      tau = tau + 1 - 1 := by ring
      _ = -1 := by rw [h]; ring
  have := tau_cubic
  rw [ht] at this
  norm_num at this

private theorem tau_sq_add_tau_ne_zero : tau ^ 2 + tau ≠ 0 := by
  rw [show tau ^ 2 + tau = tau * (tau + 1) by ring]
  exact mul_ne_zero tau_ne_zero tau_add_one_ne_zero

private theorem tau_sq_ne_two : tau ^ 2 ≠ 2 := by
  intro h
  have ht3 : tau ^ 3 = 2 * tau := by
    calc
      tau ^ 3 = tau * tau ^ 2 := by ring
      _ = 2 * tau := by rw [h]; ring
  have hadd : tau + 1 = 0 := by
    calc
      tau + 1 = (3 * tau + 1) - 2 * tau := by ring
      _ = tau ^ 3 - tau ^ 3 := by rw [← tau_cubic, ← ht3]
      _ = 0 := sub_self _
  exact tau_add_one_ne_zero hadd

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

private theorem nonsingular_of_equation {x y : K}
    (h : y ^ 2 + x * y + (tau ^ 2 + tau - 1) * y =
      x ^ 3 + (tau ^ 2 + tau - 3) * x ^ 2 +
        (-tau ^ 2 + 4) * x - tau - 2) :
    quotientCurve.toAffine.Nonsingular x y := by
  apply quotientCurve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa [quotientCurve, sub_eq_add_neg, add_assoc] using h

private theorem generator_nonsingular :
    quotientCurve.toAffine.Nonsingular 1 0 := by
  apply nonsingular_of_equation
  ring_nf

private theorem pointTwo_nonsingular :
    quotientCurve.toAffine.Nonsingular (3 - tau ^ 2) (2 - tau ^ 2) := by
  apply nonsingular_of_equation
  ring_nf
  simp only [tau_pow_five, tau_pow_four, tau_cubic]
  ring

private theorem pointThree_nonsingular :
    quotientCurve.toAffine.Nonsingular (1 - tau) (-tau ^ 2 + tau) := by
  apply nonsingular_of_equation
  ring_nf
  simp only [tau_pow_four, tau_cubic]
  ring

private theorem pointFour_nonsingular :
    quotientCurve.toAffine.Nonsingular (1 - tau) (-tau) := by
  apply nonsingular_of_equation
  ring_nf
  simp only [tau_pow_four, tau_cubic]
  ring

/-- The visible generator `(1,0)`. -/
def generator : quotientCurve.toAffine.Point :=
  .some 1 0 generator_nonsingular

/-- The displayed double of `generator`. -/
def pointTwo : quotientCurve.toAffine.Point :=
  .some (3 - tau ^ 2) (2 - tau ^ 2) pointTwo_nonsingular

/-- The displayed triple of `generator`. -/
def pointThree : quotientCurve.toAffine.Point :=
  .some (1 - tau) (-tau ^ 2 + tau) pointThree_nonsingular

/-- The displayed fourth multiple, equal to `-pointThree`. -/
def pointFour : quotientCurve.toAffine.Point :=
  .some (1 - tau) (-tau) pointFour_nonsingular

private theorem generator_not_vertical :
    ¬((1 : K) = 1 ∧
      (0 : K) = quotientCurve.toAffine.negY 1 0) := by
  rintro ⟨-, h⟩
  simp only [WeierstrassCurve.Affine.negY, quotientCurve] at h
  apply tau_sq_add_tau_ne_zero
  linear_combination h

private theorem two_add_generator_x_ne : (3 - tau ^ 2 : K) ≠ 1 := by
  intro h
  apply tau_sq_ne_two
  calc
    tau ^ 2 = 3 - (3 - tau ^ 2) := by ring
    _ = 3 - 1 := by rw [h]
    _ = 2 := by ring

private theorem three_add_generator_x_ne : (1 - tau : K) ≠ 1 := by
  intro h
  apply tau_ne_zero
  calc
    tau = 1 - (1 - tau) := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by ring

private theorem two_sub_tau_sq_ne_zero : (2 - tau ^ 2 : K) ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm tau_sq_ne_two)

private theorem generator_slope :
    quotientCurve.toAffine.slope 1 1 0 0 = tau ^ 2 - 2 := by
  rw [quotientCurve.toAffine.slope_of_Y_ne rfl (fun h ↦
    generator_not_vertical ⟨rfl, h⟩)]
  simp only [WeierstrassCurve.Affine.negY, quotientCurve,
    WeierstrassCurve.toAffine]
  rw [show 3 * (1 : K) ^ 2 + 2 * (tau ^ 2 + tau - 3) * 1 +
      (-tau ^ 2 + 4) - 1 * 0 = tau ^ 2 + 2 * tau + 1 by ring,
    show (0 : K) - (-0 - 1 * 1 - (tau ^ 2 + tau - 1)) =
      tau ^ 2 + tau by ring]
  rw [div_eq_iff tau_sq_add_tau_ne_zero]
  ring_nf
  simp only [tau_pow_four, tau_cubic]
  ring

private theorem pointTwo_generator_slope :
    quotientCurve.toAffine.slope (3 - tau ^ 2) 1 (2 - tau ^ 2) 0 = 1 := by
  rw [quotientCurve.toAffine.slope_of_X_ne two_add_generator_x_ne]
  rw [show (2 - tau ^ 2 : K) - 0 = 2 - tau ^ 2 by ring,
    show (3 - tau ^ 2 : K) - 1 = 2 - tau ^ 2 by ring]
  exact div_self two_sub_tau_sq_ne_zero

private theorem pointThree_generator_slope :
    quotientCurve.toAffine.slope (1 - tau) 1 (-tau ^ 2 + tau) 0 =
      tau - 1 := by
  rw [quotientCurve.toAffine.slope_of_X_ne three_add_generator_x_ne]
  rw [show (-tau ^ 2 + tau : K) - 0 = -tau ^ 2 + tau by ring,
    show (1 - tau : K) - 1 = -tau by ring]
  rw [div_eq_iff (neg_ne_zero.mpr tau_ne_zero)]
  ring

private theorem two_nsmul_generator : (2 : ℕ) • generator = pointTwo := by
  rw [two_nsmul]
  unfold generator pointTwo
  rw [WeierstrassCurve.Affine.Point.add_some generator_not_vertical]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve
  · rw [generator_slope]
    simp only [WeierstrassCurve.Affine.addX, quotientCurve,
      WeierstrassCurve.toAffine]
    ring_nf
    simp only [tau_pow_four]
    ring
  · rw [generator_slope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      quotientCurve, WeierstrassCurve.toAffine]
    ring_nf
    simp only [tau_pow_six, tau_pow_four, tau_cubic]
    ring

private theorem three_nsmul_generator : (3 : ℕ) • generator = pointThree := by
  rw [show (3 : ℕ) • generator = (2 : ℕ) • generator + generator by abel,
    two_nsmul_generator]
  unfold pointTwo generator pointThree
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne two_add_generator_x_ne]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve
  · rw [pointTwo_generator_slope]
    simp only [WeierstrassCurve.Affine.addX, quotientCurve,
      WeierstrassCurve.toAffine]
    ring_nf
  · rw [pointTwo_generator_slope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      quotientCurve, WeierstrassCurve.toAffine]
    ring_nf

private theorem four_nsmul_generator : (4 : ℕ) • generator = pointFour := by
  rw [show (4 : ℕ) • generator = (3 : ℕ) • generator + generator by abel,
    three_nsmul_generator]
  unfold pointThree generator pointFour
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne three_add_generator_x_ne]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve
  · rw [pointThree_generator_slope]
    simp only [WeierstrassCurve.Affine.addX, quotientCurve,
      WeierstrassCurve.toAffine]
    ring_nf
  · rw [pointThree_generator_slope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      quotientCurve, WeierstrassCurve.toAffine]
    ring_nf

private theorem pointFour_eq_neg_pointThree : pointFour = -pointThree := by
  unfold pointFour pointThree
  rw [WeierstrassCurve.Affine.Point.neg_some]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve rfl
  simp only [WeierstrassCurve.Affine.negY, quotientCurve,
    WeierstrassCurve.toAffine]
  ring

/-- The visible generator is killed by seven. -/
@[simp]
theorem seven_nsmul_generator : (7 : ℕ) • generator = 0 := by
  calc
    (7 : ℕ) • generator =
        (4 : ℕ) • generator + (3 : ℕ) • generator := by abel
    _ = pointFour + pointThree := by
      rw [four_nsmul_generator, three_nsmul_generator]
    _ = 0 := by rw [pointFour_eq_neg_pointThree]; exact neg_add_cancel _

/-- The displayed point `pointTwo` is twice the visible generator. -/
theorem two_nsmul_generator_eq_pointTwo :
    (2 : ℕ) • generator = pointTwo :=
  two_nsmul_generator

/-- The displayed point `pointThree` is three times the visible generator. -/
theorem three_nsmul_generator_eq_pointThree :
    (3 : ℕ) • generator = pointThree :=
  three_nsmul_generator

/-- The displayed point `pointFour` is four times the visible generator. -/
theorem four_nsmul_generator_eq_pointFour :
    (4 : ℕ) • generator = pointFour :=
  four_nsmul_generator

/-- The fifth multiple is the negative of the displayed double. -/
theorem five_nsmul_generator_eq_neg_pointTwo :
    (5 : ℕ) • generator = -pointTwo := by
  apply eq_neg_of_add_eq_zero_left
  rw [← two_nsmul_generator, ← add_nsmul]
  norm_num

/-- The sixth multiple is the negative of the visible generator. -/
theorem six_nsmul_generator_eq_neg_generator :
    (6 : ℕ) • generator = -generator := by
  apply eq_neg_of_add_eq_zero_left
  change (6 : ℕ) • generator + (1 : ℕ) • generator = 0
  rw [← add_nsmul]
  norm_num

/-- The visible generator has exact additive order seven. -/
theorem addOrderOf_generator : addOrderOf generator = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  apply addOrderOf_eq_prime seven_nsmul_generator
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

end

end MazurTorsion.XOneEighteenQuotientSevenTorsion
