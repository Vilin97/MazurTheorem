/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree

/-!
# Rational nonvanishing factors for the order-seven resultant

The primitive resultant certificate for the order-seven backtracking
calculation has two factors not accounted for by the discriminant of the
Kubert family.  This file records them over `ℤ` and proves that neither has a
rational root.  Since both polynomials are monic with constant coefficient
one, the rational-root theorem reduces the proof to evaluation at `±1`.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

/-- The degree-six primitive factor in the order-seven resultant. -/
def resultantFactorSix : ℤ[X] :=
  X ^ 6 + C 229 * X ^ 5 + C 270 * X ^ 4 - C 1695 * X ^ 3 +
    C 1430 * X ^ 2 - C 235 * X + 1

/-- The degree-twelve primitive factor in the order-seven resultant. -/
def resultantFactorTwelve : ℤ[X] :=
  X ^ 12 - C 522 * X ^ 11 - C 8955 * X ^ 10 + C 37950 * X ^ 9 -
    C 70998 * X ^ 8 + C 131562 * X ^ 7 - C 253239 * X ^ 6 +
    C 316290 * X ^ 5 - C 218058 * X ^ 4 + C 80090 * X ^ 3 -
    C 14631 * X ^ 2 + C 510 * X + 1

private lemma resultantFactorSix_monic : resultantFactorSix.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 6 (by
    unfold resultantFactorSix
    compute_degree) (by
      norm_num [resultantFactorSix, coeff_X_pow, coeff_one, coeff_X])

private lemma resultantFactorTwelve_monic : resultantFactorTwelve.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 12 (by
    unfold resultantFactorTwelve
    compute_degree) (by
      norm_num [resultantFactorTwelve, coeff_X_pow, coeff_one, coeff_X])

private theorem monic_constant_one_eval_ne_zero
    {p : ℤ[X]} (hmonic : p.Monic) (hconstant : p.coeff 0 = 1)
    (hone : eval₂ (Int.castRingHom ℚ) 1 p ≠ 0)
    (hneg : eval₂ (Int.castRingHom ℚ) (-1) p ≠ 0)
    (d : ℚ) : eval₂ (Int.castRingHom ℚ) d p ≠ 0 := by
  intro h
  have hroot : aeval d p = 0 := by
    simpa [aeval_def] using h
  obtain ⟨z, hz, hdiv⟩ :=
    exists_integer_of_is_root_of_monic hmonic hroot
  rw [hconstant] at hdiv
  have hzunit : IsUnit z := isUnit_iff_dvd_one.mpr hdiv
  rcases Int.isUnit_iff.mp hzunit with rfl | rfl
  · apply hone
    rw [hz] at hroot
    simpa [aeval_def] using hroot
  · apply hneg
    rw [hz] at hroot
    simpa [aeval_def] using hroot

/-- The primitive degree-six resultant factor has no rational root. -/
theorem resultantFactorSix_eval_ne_zero (d : ℚ) :
    eval₂ (Int.castRingHom ℚ) d resultantFactorSix ≠ 0 :=
  monic_constant_one_eval_ne_zero resultantFactorSix_monic
    (by norm_num [resultantFactorSix])
    (by norm_num [resultantFactorSix])
    (by norm_num [resultantFactorSix]) d

/-- The primitive degree-twelve resultant factor has no rational root. -/
theorem resultantFactorTwelve_eval_ne_zero (d : ℚ) :
    eval₂ (Int.castRingHom ℚ) d resultantFactorTwelve ≠ 0 :=
  monic_constant_one_eval_ne_zero resultantFactorTwelve_monic
    (by norm_num [resultantFactorTwelve])
    (by norm_num [resultantFactorTwelve])
    (by norm_num [resultantFactorTwelve]) d

/-- The generic first backtracking resultant, factored over the parameter
ring.  The Bézout certificate has this polynomial as its scalar target. -/
def resultantFactorData : ℚ[X] :=
  X ^ 63 * (X - 1) ^ 51 *
    (X ^ 3 - C 8 * X ^ 2 + C 5 * X + 1) ^ 260 *
    (resultantFactorSix.map (Int.castRingHom ℚ)) ^ 2 *
    resultantFactorTwelve.map (Int.castRingHom ℚ)

/-- The factored generic resultant is nonzero away from the three singular
Kubert parameters. -/
theorem resultantFactorData_eval_ne_zero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    resultantFactorData.eval d ≠ 0 := by
  have hdsub : d - 1 ≠ 0 := sub_ne_zero.mpr hd1
  have hsix := resultantFactorSix_eval_ne_zero d
  have htwelve := resultantFactorTwelve_eval_ne_zero d
  unfold resultantFactorData
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one,
    eval_add, eval_C, eval_map]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero 63 hd0) (pow_ne_zero 51 hdsub))
        (pow_ne_zero 260 hcubic))
      (pow_ne_zero 2 hsix))
    htwelve

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
