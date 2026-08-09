/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrincipalSmallPrimes
import Mathlib.NumberTheory.KummerDedekind

/-!
# The triadic prime in the `X₁(18)` two-division compositum

We first identify the unique prime above `3` in the real cubic coefficient
field.  The normalized generator then has a relative cubic polynomial of
discriminant `-8`; its irreducible reduction at that coefficient prime gives
the unique prime above `3` in the degree-nine compositum.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicPrime

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The unique coefficient-field prime above `3` -/

/-- A uniformizer above `3` in the real cubic coefficient field. -/
def coefficientTriadicUniformizer : NumberField.RingOfIntegers Q.K :=
  coefficientInteger - 1

private def coefficientTriadicUnit : NumberField.RingOfIntegers Q.K :=
  2 * coefficientInteger - coefficientInteger ^ 2

private def coefficientTriadicUnitInverse : NumberField.RingOfIntegers Q.K :=
  coefficientInteger ^ 2 + coefficientInteger - 1

private theorem coefficientTriadicUnit_mul_inverse :
    coefficientTriadicUnit * coefficientTriadicUnitInverse = 1 := by
  apply RingOfIntegers.coe_injective
  change (2 * Q.tau - Q.tau ^ 2) *
      (Q.tau ^ 2 + Q.tau - 1) = 1
  linear_combination (1 - Q.tau) * Q.tau_cubic

private theorem coefficientTriadicUnit_isUnit :
    IsUnit coefficientTriadicUnit := by
  exact ⟨⟨coefficientTriadicUnit, coefficientTriadicUnitInverse,
    coefficientTriadicUnit_mul_inverse,
    by rw [mul_comm, coefficientTriadicUnit_mul_inverse]⟩, rfl⟩

private theorem coefficientTriadic_element_factorization :
    coefficientTriadicUniformizer ^ 3 =
      (3 : NumberField.RingOfIntegers Q.K) * coefficientTriadicUnit := by
  apply RingOfIntegers.coe_injective
  change (Q.tau - 1) ^ 3 = 3 * (2 * Q.tau - Q.tau ^ 2)
  linear_combination Q.tau_cubic

/-- The rational triadic ideal is the cube of the displayed coefficient
prime. -/
theorem coefficient_span_three_eq_uniformizer_cube :
    Ideal.span {(3 : NumberField.RingOfIntegers Q.K)} =
      Ideal.span {coefficientTriadicUniformizer} ^ 3 := by
  rw [Ideal.span_singleton_pow, coefficientTriadic_element_factorization,
    mul_comm (3 : NumberField.RingOfIntegers Q.K) coefficientTriadicUnit]
  exact (Ideal.span_singleton_mul_left_unit coefficientTriadicUnit_isUnit 3).symm

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim]

/-- The coefficient-field uniformizer ideal has absolute norm `3`. -/
theorem coefficientTriadicPrime_absNorm :
    Ideal.absNorm (Ideal.span {coefficientTriadicUniformizer}) = 3 := by
  have hthree : Ideal.absNorm
      (Ideal.span {(3 : NumberField.RingOfIntegers Q.K)}) = 27 := by
    calc
      Ideal.absNorm
          (Ideal.span {(3 : NumberField.RingOfIntegers Q.K)}) =
        3 ^ Module.finrank ℤ (NumberField.RingOfIntegers Q.K) := by
          simpa using
            (Ideal.absNorm_span_natCast
              (S := NumberField.RingOfIntegers Q.K) 3)
      _ = 27 := by
        rw [RingOfIntegers.rank, coefficientField_finrank]
        norm_num
  have h := congrArg Ideal.absNorm
    coefficient_span_three_eq_uniformizer_cube
  rw [hthree, map_pow] at h
  have hpow :
      Ideal.absNorm (Ideal.span {coefficientTriadicUniformizer}) ^ 3 =
        3 ^ 3 := by
    norm_num at h ⊢
    exact h.symm
  exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) hpow

/-- The displayed norm-three ideal is prime. -/
theorem coefficientTriadicPrime_isPrime :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [coefficientTriadicPrime_absNorm]
  exact (Nat.irreducible_iff_nat_prime 3).mpr Nat.prime_three

/-- The displayed coefficient ideal lies over the rational prime `3`. -/
theorem coefficientTriadicPrime_mem_primesOver :
    Ideal.span {coefficientTriadicUniformizer} ∈
      Ideal.primesOver (Ideal.span {(3 : ℤ)})
        (NumberField.RingOfIntegers Q.K) := by
  refine ⟨coefficientTriadicPrime_isPrime, ?_⟩
  letI : (Ideal.span {(3 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 3
  apply (Ideal.liesOver_iff_dvd_map
    coefficientTriadicPrime_isPrime.ne_top).mpr
  rw [Ideal.map_span, Set.image_singleton, map_ofNat,
    coefficient_span_three_eq_uniformizer_cube]
  exact dvd_pow_self _ (by norm_num)

private theorem eq_of_dvd_of_absNorm_eq_three
    {P I : Ideal (NumberField.RingOfIntegers Q.K)}
    (hdiv : P ∣ I) (hPne : P ≠ ⊤) (hI : I.absNorm = 3) : P = I := by
  have hle : I ≤ P := Ideal.dvd_iff_le.mp hdiv
  have hnormDvd : P.absNorm ∣ 3 := by
    rw [← hI]
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  have hPnorm : P.absNorm = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hnormDvd with hOne | hThree
    · exact False.elim (hPne (Ideal.absNorm_eq_one_iff.mp hOne))
    · exact hThree
  obtain ⟨J, hJ⟩ := hdiv
  have hnorm := congrArg Ideal.absNorm hJ
  rw [map_mul, hPnorm, hI] at hnorm
  have hJnorm : J.absNorm = 1 := by omega
  have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJnorm
  rw [hJtop, mul_top] at hJ
  exact hJ.symm

/-- The displayed ideal is the only coefficient-field prime above `3`. -/
theorem coefficient_prime_over_three_eq
    (P : Ideal (NumberField.RingOfIntegers Q.K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(3 : ℤ)})
      (NumberField.RingOfIntegers Q.K)) :
    P = Ideal.span {coefficientTriadicUniformizer} := by
  have hprime : Prime P :=
    Ideal.prime_of_mem_primesOver (by norm_num) hP
  letI : (Ideal.span {(3 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 3
  have hPthree : P ∣ Ideal.span
      {(3 : NumberField.RingOfIntegers Q.K)} := by
    have hmap := (Ideal.liesOver_iff_dvd_map hP.1.ne_top).mp hP.2
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hmap
  rw [coefficient_span_three_eq_uniformizer_cube] at hPthree
  have hPuniformizer : P ∣ Ideal.span {coefficientTriadicUniformizer} :=
    hprime.dvd_of_dvd_pow hPthree
  exact eq_of_dvd_of_absNorm_eq_three hPuniformizer hP.1.ne_top
    coefficientTriadicPrime_absNorm

end

end MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
