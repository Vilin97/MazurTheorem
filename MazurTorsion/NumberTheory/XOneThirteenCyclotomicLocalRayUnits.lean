/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCyclotomicLambdaPowers
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement

/-!
# The local ray-unit quotient at `(1 - ζ₁₃)`

This file constructs the actual reduction map

`(𝓞 ℚ(ζ₁₃))ˣ → ((𝓞 ℚ(ζ₁₃)) / λ ^ n)ˣ`

and the quotient of the target by the image of global units.  For positive
`n`, its cardinality divides the already checked local unit cardinality
`12 * 13 ^ (n - 1)`.  Consequently it has cardinality prime to nineteen and
has no nontrivial element killed by nineteen.

This is only a concrete finite quotient of local units.  No identification
with a ray class group or a Galois group is asserted.
-/

namespace MazurTorsion.XOneThirteenCyclotomic

open scoped NumberField

noncomputable section

local notation "O₁₃" => 𝓞 ThirteenCyclotomicField

/-- Reduction of global units modulo `λ ^ n`. -/
def lambdaPowerUnitReduction (n : ℕ) :
    O₁₃ˣ →* (O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ :=
  Units.map (Ideal.Quotient.mk (lambdaThirteenIdeal ^ n)).toMonoidHom

@[simp]
theorem lambdaPowerUnitReduction_apply (n : ℕ) (u : O₁₃ˣ) :
    ((lambdaPowerUnitReduction n u :
        (O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ) :
      O₁₃ ⧸ lambdaThirteenIdeal ^ n) =
      Ideal.Quotient.mk (lambdaThirteenIdeal ^ n) (u : O₁₃) :=
  rfl

/-- The actual subgroup of local units obtained from global units. -/
def lambdaPowerGlobalUnitImage (n : ℕ) :
    Subgroup (O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ :=
  (lambdaPowerUnitReduction n).range

/-- The global-unit image is normal because the local unit group is
commutative. -/
instance lambdaPowerGlobalUnitImage_normal (n : ℕ) :
    (lambdaPowerGlobalUnitImage n).Normal := by
  letI : IsMulCommutative (O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ :=
    IsMulCommutative.of_comm mul_comm
  infer_instance

/-- The finite local ray-unit quotient at level `λ ^ n`.

The arithmetic results below use positive `n`; the definition also makes
sense at level zero. -/
abbrev LambdaPowerLocalRayUnitQuotient (n : ℕ) :=
  (O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ ⧸ lambdaPowerGlobalUnitImage n

/-- The local ray-unit quotient is an actual finite type. -/
noncomputable instance finite_lambdaPowerLocalRayUnitQuotient (n : ℕ) :
    Finite (LambdaPowerLocalRayUnitQuotient n) :=
  inferInstance

/-- The canonical projection from local units to the local ray-unit
quotient. -/
def lambdaPowerLocalRayUnitProjection (n : ℕ) :
    (O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ →*
      LambdaPowerLocalRayUnitQuotient n :=
  QuotientGroup.mk' (lambdaPowerGlobalUnitImage n)

@[simp]
theorem lambdaPowerLocalRayUnitProjection_apply (n : ℕ)
    (u : (O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ) :
    lambdaPowerLocalRayUnitProjection n u =
      QuotientGroup.mk (s := lambdaPowerGlobalUnitImage n) u :=
  rfl

@[simp]
theorem lambdaPowerLocalRayUnitProjection_ker (n : ℕ) :
    (lambdaPowerLocalRayUnitProjection n).ker =
      lambdaPowerGlobalUnitImage n :=
  QuotientGroup.ker_mk' (lambdaPowerGlobalUnitImage n)

/-- Every reduced global unit becomes trivial in the quotient. -/
@[simp]
theorem lambdaPowerLocalRayUnitProjection_reduction (n : ℕ) (u : O₁₃ˣ) :
    lambdaPowerLocalRayUnitProjection n (lambdaPowerUnitReduction n u) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [lambdaPowerLocalRayUnitProjection_ker]
  exact ⟨u, rfl⟩

/-- The cardinality of the quotient by global units divides the cardinality
of the full local unit group. -/
theorem natCard_lambdaPowerLocalRayUnitQuotient_dvd_localUnits (n : ℕ) :
    Nat.card (LambdaPowerLocalRayUnitQuotient n) ∣
      Nat.card ((O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ) := by
  change
    Nat.card
        ((O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ ⧸
          lambdaPowerGlobalUnitImage n) ∣
      Nat.card ((O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ)
  exact (lambdaPowerGlobalUnitImage n).card_quotient_dvd_card

/-- For positive `n`, the local ray-unit quotient has cardinality dividing
`12 * 13 ^ (n - 1)`. -/
theorem natCard_lambdaPowerLocalRayUnitQuotient_dvd
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (LambdaPowerLocalRayUnitQuotient n) ∣
      12 * 13 ^ (n - 1) := by
  rw [← natCard_units_quotient_lambdaThirteenIdeal_pow n hn]
  exact natCard_lambdaPowerLocalRayUnitQuotient_dvd_localUnits n

/-- For positive `n`, the local ray-unit quotient has cardinality prime to
nineteen. -/
theorem natCard_lambdaPowerLocalRayUnitQuotient_coprime_nineteen
    (n : ℕ) (hn : n ≠ 0) :
    (Nat.card (LambdaPowerLocalRayUnitQuotient n)).Coprime 19 :=
  Nat.Coprime.of_dvd_left
    (natCard_lambdaPowerLocalRayUnitQuotient_dvd_localUnits n)
    (natCard_units_quotient_lambdaThirteenIdeal_pow_coprime_nineteen n hn)

/-- There is no nontrivial element of the local ray-unit quotient killed by
nineteen. -/
theorem pow_nineteen_eq_one_iff_eq_one
    (n : ℕ) (hn : n ≠ 0) (x : LambdaPowerLocalRayUnitQuotient n) :
    x ^ 19 = 1 ↔ x = 1 := by
  constructor
  · intro hx
    have horderNineteen : orderOf x ∣ 19 :=
      orderOf_dvd_of_pow_eq_one hx
    have horderCard : orderOf x ∣
        Nat.card (LambdaPowerLocalRayUnitQuotient n) :=
      orderOf_dvd_natCard x
    have horderGcd : orderOf x ∣
        (Nat.card (LambdaPowerLocalRayUnitQuotient n)).gcd 19 :=
      Nat.dvd_gcd horderCard horderNineteen
    have hgcd :
        (Nat.card (LambdaPowerLocalRayUnitQuotient n)).gcd 19 = 1 :=
      (natCard_lambdaPowerLocalRayUnitQuotient_coprime_nineteen n hn).gcd_eq_one
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hgcd ▸ horderGcd))
  · rintro rfl
    simp

end

end MazurTorsion.XOneThirteenCyclotomic
