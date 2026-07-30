/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.NumberTheory.FLT.Three

/-!
# Rational points of the Fermat cubic

The affine Fermat cubic `u³ + v³ = 1` has exactly the two rational
points `(1,0)` and `(0,1)`.  This is Euler's case of Fermat's last
theorem, available in mathlib as `fermatLastTheoremThree`; it is the
Diophantine core of the modular curve `X₀(27)`, which the order-27
exclusion reduces to.
-/

namespace MazurTorsion

/-- The affine Fermat cubic has only its two trivial rational points. -/
theorem fermat_cubic_rational_points (u v : ℚ)
    (h : u ^ 3 + v ^ 3 = 1) :
    (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 1) := by
  have hflt : FermatLastTheoremWith ℚ 3 :=
    ((fermatLastTheoremWith_nat_int_rat_tfae 3).out 0 2).mp
      fermatLastTheoremThree
  by_cases hu : u = 0
  · subst hu
    right
    refine ⟨rfl, ?_⟩
    have hv : v ^ 3 = 1 := by linarith
    have hfac : (v - 1) * (v ^ 2 + v + 1) = 0 := by
      linear_combination hv
    rcases mul_eq_zero.mp hfac with h1 | h2
    · linarith
    · exfalso
      nlinarith [sq_nonneg (2 * v + 1)]
  by_cases hv : v = 0
  · subst hv
    left
    refine ⟨?_, rfl⟩
    have hu3 : u ^ 3 = 1 := by linarith
    have hfac : (u - 1) * (u ^ 2 + u + 1) = 0 := by
      linear_combination hu3
    rcases mul_eq_zero.mp hfac with h1 | h2
    · linarith
    · exfalso
      nlinarith [sq_nonneg (2 * u + 1)]
  · exfalso
    exact hflt u v 1 hu hv one_ne_zero (by rw [h]; norm_num)

/-- The affine rational points of the minimal `X₀(27)` model
`y² + y = x³ - 7` are exactly `(3, 4)` and `(3, -5)`. -/
theorem x0_twentySeven_affine_points (x y : ℚ)
    (h : y ^ 2 + y = x ^ 3 - 7) :
    (x = 3 ∧ y = 4) ∨ (x = 3 ∧ y = -5) := by
  set X : ℚ := 4 * x with hX
  set Y : ℚ := 8 * y + 4 with hY
  have hW : Y ^ 2 = X ^ 3 - 432 := by
    rw [hX, hY]
    linear_combination 64 * h
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0] at hW
    nlinarith [sq_nonneg Y]
  have hu : ((36 + Y) / (6 * X)) ^ 3 + ((36 - Y) / (6 * X)) ^ 3 = 1 := by
    field_simp
    linear_combination 216 * hW
  have h6X : (6 : ℚ) * X ≠ 0 := by
    intro hz
    rcases mul_eq_zero.mp hz with hz | hz
    · norm_num at hz
    · exact hX0 hz
  rcases fermat_cubic_rational_points _ _ hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `u = 1, v = 0`: the point `(3, 4)`
    left
    have hYv : 36 - Y = 0 := by
      rcases div_eq_zero_iff.mp h2 with h' | h'
      · exact h'
      · exact absurd h' h6X
    have hXv : 36 + Y = 6 * X := by
      field_simp at h1
      linarith [h1]
    constructor
    · rw [hX] at hXv
      linarith
    · rw [hY] at hYv
      linarith
  · -- `u = 0, v = 1`: the point `(3, -5)`
    right
    have hYv : 36 + Y = 0 := by
      rcases div_eq_zero_iff.mp h1 with h' | h'
      · exact h'
      · exact absurd h' h6X
    have hXv : 36 - Y = 6 * X := by
      field_simp at h2
      linarith [h2]
    constructor
    · rw [hX] at hXv
      linarith
    · rw [hY] at hYv
      linarith

end MazurTorsion
