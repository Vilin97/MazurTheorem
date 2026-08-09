/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCyclotomicResultants
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Minkowski cutoff for the thirteenth cyclotomic field

This file checks the numerical part of the class-number-one calculation for
`ℚ(ζ₁₃)`.  Its Minkowski expression is strictly less than `307`.  Consequently,
the ideal-class argument only has to inspect rational primes at most `306`.

The proof uses Mathlib's exact formulas for the degree, complex places, and
discriminant of a prime cyclotomic field, together with the certified lower
bound `3.141592 < π`.  It makes no principal-ideal or class-number claim.
-/

namespace MazurTorsion.XOneThirteenCyclotomic

open Module NumberField InfinitePlace Nat Real

noncomputable section

/-- The real expression occurring in Minkowski's ideal-class bound. -/
def minkowskiClassBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ nrComplexPlaces K *
    ((Module.finrank ℚ K)! /
      (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        Real.sqrt |NumberField.discr K|)

variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {13} ℚ K]

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- A thirteenth cyclotomic field has degree twelve. -/
theorem finrank_thirteen : Module.finrank ℚ K = 12 := by
  rw [IsCyclotomicExtension.Rat.finrank 13 K,
    Nat.totient_prime (by decide)]

/-- A thirteenth cyclotomic field has six complex places. -/
theorem nrComplexPlaces_thirteen : nrComplexPlaces K = 6 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 13,
    Nat.totient_prime (by decide)]

/-- The discriminant of a thirteenth cyclotomic field is `13^11`. -/
theorem discr_thirteen : NumberField.discr K = 13 ^ 11 := by
  rw [IsCyclotomicExtension.Rat.discr_prime 13 K]
  norm_num

/-- A rational upper bound for the square root of the discriminant. -/
private theorem sqrt_discr_thirteen_lt :
    Real.sqrt (1792160394037 : ℝ) < 1338716 := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

/-- The exact Minkowski class bound for `ℚ(ζ₁₃)` is strictly below `307`. -/
theorem minkowskiClassBound_lt : minkowskiClassBound K < 307 := by
  rw [minkowskiClassBound, finrank_thirteen K,
    nrComplexPlaces_thirteen K, discr_thirteen K]
  norm_num only [Int.reduceAbs, Int.cast_pow, Int.cast_ofNat,
    Nat.cast_ofNat, Nat.factorial]
  change (4 / Real.pi) ^ 6 *
    ((1925 : ℝ) / 35831808 * Real.sqrt 1792160394037) < 307
  calc
    (4 / Real.pi) ^ 6 *
        ((1925 : ℝ) / 35831808 * Real.sqrt 1792160394037) <
      (4 / (3.141592 : ℝ)) ^ 6 *
        ((1925 : ℝ) / 35831808 * 1338716) := by
          gcongr
          · exact Real.pi_gt_d6
          · exact sqrt_discr_thirteen_lt
    _ < 307 := by norm_num

/-- The natural-number floor used in the ideal-class argument is at most
`306`. -/
theorem floor_minkowskiClassBound_le :
    ⌊minkowskiClassBound K⌋₊ ≤ 306 := by
  have hnonneg : 0 ≤ minkowskiClassBound K := by
    rw [minkowskiClassBound, finrank_thirteen K,
      nrComplexPlaces_thirteen K, discr_thirteen K]
    positivity
  have hlt : ⌊minkowskiClassBound K⌋₊ < 307 :=
    (Nat.floor_lt hnonneg).2 (minkowskiClassBound_lt K)
  omega

end

end MazurTorsion.XOneThirteenCyclotomic
