/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XZeroTwentySevenClassification

/-!
# The endgame of the order-twenty-seven tower

On the parametrized `X₁(9)` family the first two hauptmodul legs are
never cuspidal, and the first leg never takes the CM value `-243`: the
would-be CM parameter satisfies a monic integral polynomial of degree
nine with no root modulo two.  Combined with the classification of the
chained `X₀(9)` correspondence, any third leg completing the chain is
impossible.  Producing such a third leg from a rational point of exact
order twenty-seven is the remaining step of the exclusion.
-/

namespace MazurTorsion.Kubert

private lemma quadratic_pos (f : ℚ) : 0 < f ^ 2 - f + 1 := by
  nlinarith [sq_nonneg (2 * f - 1)]

private noncomputable def cmLegPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 9 - Polynomial.C 9 * Polynomial.X ^ 8 +
    Polynomial.C 27 * Polynomial.X ^ 7 + Polynomial.C 192 * Polynomial.X ^ 6 -
    Polynomial.C 666 * Polynomial.X ^ 5 + Polynomial.C 675 * Polynomial.X ^ 4 -
    Polynomial.C 213 * Polynomial.X ^ 3 - Polynomial.C 9 * Polynomial.X ^ 2 +
    Polynomial.C 1

private lemma cmLegPolynomial_monic :
    Polynomial.Monic cmLegPolynomial := by
  unfold cmLegPolynomial
  monicity!

private lemma cmLegPolynomial_no_root_mod_two :
    ∀ z : ZMod 2, z ^ 9 - 9 * z ^ 8 + 27 * z ^ 7 + 192 * z ^ 6 - 666 * z ^ 5 +
      675 * z ^ 4 - 213 * z ^ 3 - 9 * z ^ 2 + 1 ≠ 0 := by
  decide

/-- The first hauptmodul leg never takes the CM value `-243`. -/
private theorem firstLeg_ne_cm (f : ℚ) : a1legN f + 243 * a1legD f ≠ 0 := by
  intro h
  have hP : f ^ 9 - 9 * f ^ 8 + 27 * f ^ 7 + 192 * f ^ 6 - 666 * f ^ 5 +
      675 * f ^ 4 - 213 * f ^ 3 - 9 * f ^ 2 + 1 = 0 := by
    simp only [a1legN, a1legD] at h
    linear_combination h
  have hroot : Polynomial.aeval f cmLegPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [cmLegPolynomial]
    linear_combination hP
  obtain ⟨z, hfz, -⟩ :=
    exists_integer_of_is_root_of_monic cmLegPolynomial_monic hroot
  have hzrat : (z : ℚ) ^ 9 - 9 * (z : ℚ) ^ 8 + 27 * (z : ℚ) ^ 7 +
      192 * (z : ℚ) ^ 6 - 666 * (z : ℚ) ^ 5 + 675 * (z : ℚ) ^ 4 -
      213 * (z : ℚ) ^ 3 - 9 * (z : ℚ) ^ 2 + 1 = 0 := by
    have hzcast : (z : ℚ) = f := by
      simpa using hfz.symm
    rw [hzcast]
    linear_combination hP
  have hzint : z ^ 9 - 9 * z ^ 8 + 27 * z ^ 7 + 192 * z ^ 6 - 666 * z ^ 5 +
      675 * z ^ 4 - 213 * z ^ 3 - 9 * z ^ 2 + 1 = 0 := by
    exact_mod_cast hzrat
  apply cmLegPolynomial_no_root_mod_two (z : ZMod 2)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 2)) hzint

/-- No rational value can complete the two family legs to a chain of
the Fricke-twisted `X₀(9)` correspondence. -/
theorem legs_chain_impossible (f : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (s₃ : ℚ)
    (h2 : orderNineG9F (a2legN f / a2legD f) s₃ = 0) : False := by
  have hquad : f ^ 2 - f + 1 ≠ 0 := (quadratic_pos f).ne'
  have hD1 : a1legD f ≠ 0 := by
    simp only [a1legD]
    exact mul_ne_zero (pow_ne_zero 3 hf0)
      (pow_ne_zero 3 (sub_ne_zero.mpr hf1))
  have hD2 : a2legD f ≠ 0 := by
    simp only [a2legD]
    exact mul_ne_zero (mul_ne_zero hf0 (sub_ne_zero.mpr hf1))
      (pow_ne_zero 3 hquad)
  have hG1 : orderNineG9F (a1legN f / a1legD f) (a2legN f / a2legD f) = 0 := by
    simp only [orderNineG9F]
    field_simp
    linear_combination legs_G9F_relation f
  rcases XZeroTwentySeven.spaceCurve_classification hG1 h2 with
    ⟨hs1, -, -⟩ | ⟨hs1, -, -⟩
  · rcases div_eq_zero_iff.mp hs1 with h | h
    · simp only [a1legN] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact hquad (pow_eq_zero_iff (by norm_num) |>.mp h')
      · exact hK h'
    · exact hD1 h
  · have hcm : a1legN f + 243 * a1legD f = 0 := by
      rw [div_eq_iff hD1] at hs1
      linear_combination hs1
    exact firstLeg_ne_cm f hcm

end MazurTorsion.Kubert
