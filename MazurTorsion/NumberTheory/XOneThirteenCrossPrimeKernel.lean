/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.GroupTheory.IndexNSmulFG
import MazurTorsion.NumberTheory.XOneThirteenRationalMumfordReduction

/-!
# The honest cross-prime kernel boundary for `X₁(13)`

The checked finite-coordinate calculations give nineteen actual balanced
Mumford records over both `𝔽₃` and `𝔽₅`.  They do not themselves put a group
law on those record sets or construct reduction homomorphisms from a rational
Jacobian.

This file isolates exactly that remaining boundary.  A certificate consists
of two finite additive groups whose underlying carriers are equivalent to the
checked record sets, additive reduction homomorphisms from a finitely generated
abelian group, and the standard good-reduction kernel conclusions: the kernel
at `3` has 3-power cardinality and the kernel at `5` has 5-power cardinality.
For a torsion source these are the usual good-reduction conclusions.  For the
full Mordell--Weil group, finite kernel cardinality is an additional strong
premise and is not claimed to follow from good reduction alone.

The conclusion is nontrivial.  First-isomorphism counting shows that the
source cardinality divides both `3^a * 19` and `5^b * 19`; coprimality of `3`
and `5` then makes it divide `19`.  In particular the source is finite and is
either trivial or has cardinality nineteen.

No Jacobian, divisor-class group, reduction homomorphism, or injectivity
statement is manufactured here.  Constructing the certificate remains the
precise geometric/arithmetic premise needed to apply this result to `J(ℚ)`.
-/

namespace MazurTorsion.XOneThirteenCrossPrimeKernel

open XOneThirteenFiniteMumford
open XOneThirteenFiniteMumfordFive
open XOneThirteenRationalMumfordReduction

/-! ## The actual simultaneous coefficient reduction -/

/-- A denominator-cleared rational Mumford record with good denominators at
both checked primes. -/
structure TwoPrimeGoodMumford where
  record : XOneThirteenRationalMumfordReduction.ClearedMumford
  goodAtThree : ¬(3 : ℤ) ∣ record.denominator
  goodAtFive : ¬(5 : ℤ) ∣ record.denominator

/-- The actual pair of coefficientwise reductions constructed in
`XOneThirteenRationalMumfordReduction`. -/
def simultaneousReduction (D : TwoPrimeGoodMumford) :
    BalancedMumfordF3 × BalancedMumfordF5 :=
  (D.record.reduceF3 D.goodAtThree, D.record.reduceF5 D.goodAtFive)

/-- The checked simultaneous target has `19² = 361` elements. -/
theorem card_simultaneous_target :
    Fintype.card (BalancedMumfordF3 × BalancedMumfordF5) = 361 := by
  simp [card_balancedMumfordF3, card_balancedMumfordF5]

/-- Any finite family on which the actual simultaneous coefficient reduction
is injective has at most 361 elements.  The injectivity premise is deliberately
visible: it is not supplied by the finite enumeration. -/
theorem natCard_le_361_of_simultaneousReduction_injective
    {R : Type*} [Finite R] (representative : R → TwoPrimeGoodMumford)
    (hinjective :
      Function.Injective (fun r => simultaneousReduction (representative r))) :
    Nat.card R ≤ 361 := by
  calc
    Nat.card R ≤
        Nat.card (BalancedMumfordF3 × BalancedMumfordF5) :=
      Nat.card_le_card_of_injective
        (fun r => simultaneousReduction (representative r)) hinjective
    _ = Fintype.card (BalancedMumfordF3 × BalancedMumfordF5) :=
      Nat.card_eq_fintype_card
    _ = 361 := card_simultaneous_target

/-! ## Generic cardinality lemmas -/

/-- A number dividing two coprime-power multiples of the same core already
divides the core. -/
theorem dvd_core_of_two_coprime_power_bounds
    {n p q c a b : ℕ} (hpq : p.Coprime q)
    (hp : n ∣ p ^ a * c) (hq : n ∣ q ^ b * c) :
    n ∣ c := by
  have hcommon : n ∣ (p ^ a * c).gcd (q ^ b * c) :=
    Nat.dvd_gcd hp hq
  have hpowers : (p ^ a).Coprime (q ^ b) :=
    Nat.Coprime.pow a b hpq
  rw [Nat.gcd_mul_right, hpowers.gcd_eq_one, one_mul] at hcommon
  exact hcommon

/-- A homomorphism to a finite additive group with a nonzero prime-power
kernel has finite source. -/
theorem finite_of_primePower_kernel
    {G H : Type*} [AddGroup G] [AddGroup H] [Finite H]
    (reduction : G →+ H) {p a : ℕ} (hp : p ≠ 0)
    (hkernel : Nat.card reduction.ker = p ^ a) :
    Finite G := by
  apply Nat.finite_of_card_ne_zero
  rw [← reduction.card_ker_mul_card_range, hkernel]
  exact mul_ne_zero (pow_ne_zero a hp) Nat.card_pos.ne'

/-- Two homomorphisms with coprime prime-power kernels and equally bounded
finite targets force the source cardinality to divide the common target
cardinality. -/
theorem natCard_dvd_of_two_coprime_power_kernels
    {G H₁ H₂ : Type*}
    [AddGroup G] [AddGroup H₁] [AddGroup H₂]
    [Finite H₁] [Finite H₂]
    (reduction₁ : G →+ H₁) (reduction₂ : G →+ H₂)
    {p q c : ℕ} (hpq : p.Coprime q)
    (htarget₁ : Nat.card H₁ = c) (htarget₂ : Nat.card H₂ = c)
    (hkernel₁ : ∃ a, Nat.card reduction₁.ker = p ^ a)
    (hkernel₂ : ∃ b, Nat.card reduction₂.ker = q ^ b) :
    Nat.card G ∣ c := by
  obtain ⟨a, ha⟩ := hkernel₁
  obtain ⟨b, hb⟩ := hkernel₂
  have hrange₁ : Nat.card reduction₁.range ∣ c := by
    rw [← htarget₁]
    exact AddSubgroup.card_addSubgroup_dvd_card reduction₁.range
  have hrange₂ : Nat.card reduction₂.range ∣ c := by
    rw [← htarget₂]
    exact AddSubgroup.card_addSubgroup_dvd_card reduction₂.range
  have hbound₁ : Nat.card G ∣ p ^ a * c := by
    rw [← reduction₁.card_ker_mul_card_range, ha]
    exact Nat.mul_dvd_mul_left (p ^ a) hrange₁
  have hbound₂ : Nat.card G ∣ q ^ b * c := by
    rw [← reduction₂.card_ker_mul_card_range, hb]
    exact Nat.mul_dvd_mul_left (q ^ b) hrange₂
  exact dvd_core_of_two_coprime_power_bounds hpq hbound₁ hbound₂

/-! ## The `X₁(13)` certificate interface -/

/-- The remaining cross-prime reduction data for a candidate rational
Mordell--Weil group.

The equivalences remember that the finite group carriers are the actual
enumerated Mumford records, without imposing an invented group law on the
record types themselves.  The kernel hypotheses are the finite-kernel content
supplied by good reduction on torsion; for a full Mordell--Weil group they
explicitly include the remaining finiteness input. -/
structure Certificate
    (G H₃ H₅ : Type*)
    [AddCommGroup G] [AddGroup.FG G]
    [AddCommGroup H₃] [AddCommGroup H₅]
    [Finite H₃] [Finite H₅] where
  reductionAtThree : G →+ H₃
  reductionAtFive : G →+ H₅
  recordsAtThree : H₃ ≃ BalancedMumfordF3
  recordsAtFive : H₅ ≃ BalancedMumfordF5
  kernelAtThree_isThreePower :
    ∃ a, Nat.card reductionAtThree.ker = 3 ^ a
  kernelAtFive_isFivePower :
    ∃ b, Nat.card reductionAtFive.ker = 5 ^ b

namespace Certificate

variable
    {G H₃ H₅ : Type*}
    [AddCommGroup G] [AddGroup.FG G]
    [AddCommGroup H₃] [AddCommGroup H₅]
    [Finite H₃] [Finite H₅]
    (C : Certificate G H₃ H₅)

include C

/-- The group underlying the reduction at `3` has the checked cardinality
nineteen. -/
theorem targetThree_natCard : Nat.card H₃ = 19 := by
  calc
    Nat.card H₃ = Nat.card BalancedMumfordF3 :=
      Nat.card_congr (recordsAtThree C)
    _ = Fintype.card BalancedMumfordF3 := Nat.card_eq_fintype_card
    _ = 19 := card_balancedMumfordF3

/-- The group underlying the reduction at `5` has the checked cardinality
nineteen. -/
theorem targetFive_natCard : Nat.card H₅ = 19 := by
  calc
    Nat.card H₅ = Nat.card BalancedMumfordF5 :=
      Nat.card_congr (recordsAtFive C)
    _ = Fintype.card BalancedMumfordF5 := Nat.card_eq_fintype_card
    _ = 19 := card_balancedMumfordF5

/-- Either prime-power kernel hypothesis already makes the source finite. -/
theorem finite_source : Finite G := by
  obtain ⟨a, ha⟩ := kernelAtThree_isThreePower C
  exact finite_of_primePower_kernel (reductionAtThree C) (by norm_num) ha

/-- Main cross-prime consequence: the source cardinality divides nineteen. -/
theorem natCard_dvd_nineteen : Nat.card G ∣ 19 :=
  natCard_dvd_of_two_coprime_power_kernels
    (reductionAtThree C) (reductionAtFive C) (by norm_num)
    (targetThree_natCard C) (targetFive_natCard C)
    (kernelAtThree_isThreePower C) (kernelAtFive_isFivePower C)

/-- Consequently the source is either trivial or has cardinality nineteen. -/
theorem subsingleton_or_natCard_eq_nineteen :
    Subsingleton G ∨ Nat.card G = 19 := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 19)).mp
      (natCard_dvd_nineteen C) with hcard | hcard
  · exact Or.inl (Nat.card_eq_one_iff_unique.mp hcard).1
  · exact Or.inr hcard

/-- A nontrivial source satisfying the certificate has exactly nineteen
elements.  This is the downstream endpoint expected for a nontrivial rational
torsion group. -/
theorem natCard_eq_nineteen_of_nontrivial [Nontrivial G] :
    Nat.card G = 19 :=
  (subsingleton_or_natCard_eq_nineteen C).resolve_left (not_subsingleton G)

/-- The finite-generation rank is zero once the cross-prime finite-kernel
certificate is supplied. -/
theorem finrank_eq_zero : Module.finrank ℤ G = 0 := by
  letI : Finite G := finite_source C
  simp [Module.finrank, Module.rank_eq_zero_of_finite ℤ G]

/-- A compact consumer exposing all group-theoretic consequences needed by a
later rational Jacobian specialization. -/
theorem rational_group_endpoint :
    Finite G ∧ Module.finrank ℤ G = 0 ∧ Nat.card G ∣ 19 :=
  ⟨finite_source C, finrank_eq_zero C, natCard_dvd_nineteen C⟩

end Certificate

end MazurTorsion.XOneThirteenCrossPrimeKernel
