/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentUnitSquareclasses
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The Minkowski cutoff for the `X₁(13)` sextic field

This file isolates the numerical and ideal-theoretic end of the class-number
calculation.  An integral power basis of discriminant `-10816` gives the
field-discriminant bound `|D_K| ≤ 10816`; that concrete power-basis bridge is
kept separate.  Under precisely this bound, the Minkowski constant is less
than four.

Consequently a class-number-one proof only needs to rule out prime ideals of
norm two or three.  The final criterion below packages an especially small
way to do that: it suffices that every prime above `2` and `3` have inertia
degree at least three.  The reductions of the integral sextic give degrees
three and six, respectively.
-/

namespace MazurTorsion.XOneThirteenTwoDescentMinkowski

open Module NumberField NumberField.InfinitePlace Nat Real
open RingOfIntegers
open scoped NumberField
open XOneThirteenTwoDescentSextic
open XOneThirteenTwoDescentUnitSquareclasses

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The real expression in Minkowski's ideal-class bound. -/
def minkowskiClassBound : ℝ :=
  (4 / Real.pi) ^ nrComplexPlaces SexticField *
    ((finrank ℚ SexticField)! /
      (finrank ℚ SexticField) ^ (finrank ℚ SexticField) *
        Real.sqrt |NumberField.discr SexticField|)

/-- The only field-specific numerical input needed for the small Minkowski
cutoff is the discriminant bound supplied by an integral power basis. -/
theorem minkowskiClassBound_lt_four
    (hdisc : |NumberField.discr SexticField| ≤ 10816) :
    minkowskiClassBound < 4 := by
  have hsqrt : Real.sqrt (|NumberField.discr SexticField| : ℝ) ≤ 104 := by
    have hcast : (|NumberField.discr SexticField| : ℝ) ≤ 10816 := by
      exact_mod_cast hdisc
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num; exact hcast⟩
  rw [minkowskiClassBound, sexticField_finrank,
    sexticField_nrComplexPlaces]
  norm_num only [Nat.cast_ofNat, Nat.factorial]
  change (4 / Real.pi) ^ 3 * ((5 : ℝ) / 324 *
    Real.sqrt |NumberField.discr SexticField|) < 4
  calc
    (4 / Real.pi) ^ 3 * ((5 : ℝ) / 324 *
        Real.sqrt |NumberField.discr SexticField|) ≤
      (4 / (3.141592 : ℝ)) ^ 3 * ((5 : ℝ) / 324 * 104) := by
        gcongr
        exact Real.pi_gt_d6.le
    _ < 4 := by norm_num

/-- The natural-number floor of the Minkowski bound is at most three. -/
theorem floor_minkowskiClassBound_le_three
    (hdisc : |NumberField.discr SexticField| ≤ 10816) :
    ⌊minkowskiClassBound⌋₊ ≤ 3 := by
  have hnonneg : 0 ≤ minkowskiClassBound := by
    rw [minkowskiClassBound]
    positivity
  have hlt : ⌊minkowskiClassBound⌋₊ < 4 :=
    (Nat.floor_lt hnonneg).2 (minkowskiClassBound_lt_four hdisc)
  omega

/-- Once the discriminant is bounded, inertia degree at least three above
both `2` and `3` makes the small-prime part of the Minkowski criterion
vacuous. -/
theorem isPrincipalIdealRing_of_discr_le_of_small_prime_inertia
    (hdisc : |NumberField.discr SexticField| ≤ 10816)
    (h2 : ∀ (P : Ideal (𝓞 SexticField)),
      P ∈ Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (𝓞 SexticField) → 3 ≤ P.inertiaDeg ℤ)
    (h3 : ∀ (P : Ideal (𝓞 SexticField)),
      P ∈ Ideal.primesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))
        (𝓞 SexticField) → 3 ≤ P.inertiaDeg ℤ) :
    IsPrincipalIdealRing (𝓞 SexticField) := by
  apply
    isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hpInterval hpPrime P hP hpow
  have hfloor := floor_minkowskiClassBound_le_three hdisc
  change p ^ P.inertiaDeg ℤ ≤ ⌊minkowskiClassBound⌋₊ at hpow
  have hpLe : p ≤ 3 := le_trans (Finset.mem_Icc.mp hpInterval).2 hfloor
  interval_cases p
  · exact (Nat.not_prime_zero hpPrime).elim
  · exact (Nat.not_prime_one hpPrime).elim
  · have hinertia : 3 ≤ P.inertiaDeg ℤ := h2 P hP
    have heigth : 8 ≤ 2 ^ P.inertiaDeg ℤ := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ P.inertiaDeg ℤ := Nat.pow_le_pow_right (by norm_num) hinertia
    omega
  · have hinertia : 3 ≤ P.inertiaDeg ℤ := h3 P hP
    have heigth : 27 ≤ 3 ^ P.inertiaDeg ℤ := by
      calc
        27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ P.inertiaDeg ℤ := Nat.pow_le_pow_right (by norm_num) hinertia
    omega

/-- Class-number-one form of the same two finite obligations. -/
theorem classNumber_eq_one_of_discr_le_of_small_prime_inertia
    (hdisc : |NumberField.discr SexticField| ≤ 10816)
    (h2 : ∀ (P : Ideal (𝓞 SexticField)),
      P ∈ Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (𝓞 SexticField) → 3 ≤ P.inertiaDeg ℤ)
    (h3 : ∀ (P : Ideal (𝓞 SexticField)),
      P ∈ Ideal.primesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))
        (𝓞 SexticField) → 3 ≤ P.inertiaDeg ℤ) :
    NumberField.classNumber SexticField = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    (isPrincipalIdealRing_of_discr_le_of_small_prime_inertia hdisc h2 h3)

end

end MazurTorsion.XOneThirteenTwoDescentMinkowski
