/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionTriadicLift

/-!
# Class number one for the `X₁(18)` two-division compositum

The exact Minkowski bound is less than `32`.  The primes over `2` are the
two displayed principal dyadic ideals, the unique prime over `3` is generated
by `rho`, and the checked inertia certificates exclude every rational prime
between `5` and `31`.  These facts prove that the full ring of integers is a
principal ideal ring.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionClassNumberOne

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionMinkowski
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicLift
open NumberField Ideal RingOfIntegers

/-- The full ring of integers of the degree-nine two-division compositum is
a principal ideal ring. -/
theorem compositumRingOfIntegers_isPrincipal :
    IsPrincipalIdealRing (NumberField.RingOfIntegers M) := by
  apply
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hpRange hpPrime P hP hpow
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces M *
          (Nat.factorial (Module.finrank ℚ M) /
            (Module.finrank ℚ M) ^ (Module.finrank ℚ M) *
              Real.sqrt |NumberField.discr M|)⌋₊ ≤ 31 := by
    change ⌊minkowskiBound⌋₊ ≤ 31
    have hlt : ⌊minkowskiBound⌋₊ < 32 :=
      (Nat.floor_lt' (by norm_num : 32 ≠ 0)).mpr
        minkowskiBound_lt_thirtytwo
    omega
  have hpUpper : p ≤ 31 :=
    (Finset.mem_Icc.mp hpRange).2.trans hfloor
  by_cases hpTwo : p = 2
  · subst p
    rcases prime_over_two_eq_span_alpha_or_beta P hP with hAlpha | hBeta
    · rw [hAlpha]
      infer_instance
    · rw [hBeta]
      infer_instance
  by_cases hpThree : p = 3
  · subst p
    rw [compositum_prime_over_three_eq_span_rho P hP]
    infer_instance
  have hpLower : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hpPrime.eq_two_or_odd'.resolve_left hpTwo
    have hpTwoLe : 2 ≤ p := hpPrime.two_le
    omega
  have hlarge := thirtyone_lt_absNorm_of_mem_primesOver p
    (Finset.mem_Icc.mpr ⟨hpLower, hpUpper⟩) hpPrime P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg p P] at hlarge
  omega

/-- The degree-nine two-division compositum has class number one. -/
theorem compositum_classNumber_eq_one :
    NumberField.classNumber M = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    compositumRingOfIntegers_isPrincipal

end

end MazurTorsion.XOneEighteenTwoDivisionClassNumberOne
