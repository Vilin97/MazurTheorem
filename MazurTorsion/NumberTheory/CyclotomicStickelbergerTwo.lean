/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# The corrected `b = 2` Stickelberger coefficient

This file isolates the elementary finite arithmetic behind the
`b = 2` integral Stickelberger element.  For a nonzero residue `a` modulo
an odd prime `p`, its corrected coefficient is

`floor (2 * a.val / p)`.

It is the indicator of the upper half of the nonzero residues.  The
corresponding weighted scalar is invertible modulo every prime `p ≥ 5`;
more precisely, eight times that scalar is one.
-/

open scoped BigOperators

namespace NumberTheory.CyclotomicCharacter

/-- The nonnegative coefficient of `σₐ⁻¹` in the negative of the corrected
`b = 2` Stickelberger element. -/
def stickelbergerTwoCoefficient (p : ℕ) (a : (ZMod p)ˣ) : ℕ :=
  (2 * (a : ZMod p).val) / p

variable {p : ℕ} [Fact p.Prime]

/-- The corrected `b = 2` coefficient is the upper-half indicator. -/
theorem stickelbergerTwoCoefficient_eq_ite (a : (ZMod p)ˣ) :
    stickelbergerTwoCoefficient p a =
      if p ≤ 2 * (a : ZMod p).val then 1 else 0 := by
  have hlt : (a : ZMod p).val < p := ZMod.val_lt _
  simp only [stickelbergerTwoCoefficient]
  split_ifs with h
  · have hquot_pos : 0 < (2 * (a : ZMod p).val) / p :=
      Nat.div_pos h (Fact.out : p.Prime).pos
    have hquot_lt : (2 * (a : ZMod p).val) / p < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos]
      omega
    omega
  · exact Nat.div_eq_of_lt (by omega)

/-- Below the upper half, the corrected coefficient vanishes. -/
theorem stickelbergerTwoCoefficient_eq_zero (a : (ZMod p)ˣ)
    (ha : 2 * (a : ZMod p).val < p) :
    stickelbergerTwoCoefficient p a = 0 := by
  rw [stickelbergerTwoCoefficient_eq_ite]
  rw [if_neg (Nat.not_le_of_lt ha)]

/-- On the upper half, the corrected coefficient is one. -/
theorem stickelbergerTwoCoefficient_eq_one (a : (ZMod p)ˣ)
    (ha : p ≤ 2 * (a : ZMod p).val) :
    stickelbergerTwoCoefficient p a = 1 := by
  rw [stickelbergerTwoCoefficient_eq_ite]
  simp [ha]

/-- The weighted scalar through which the corrected `b = 2` element acts
on the inverse-character component. -/
def stickelbergerTwoWeightedScalar (p : ℕ) [NeZero p] : ZMod p :=
  ∑ a : (ZMod p)ˣ,
    (stickelbergerTwoCoefficient p a : ZMod p) * (a : ZMod p)

/-- For prime modulus, taking the least positive representative identifies
the units with the interval from one through `p - 1`. -/
private def unitsEquivIcc :
    (ZMod p)ˣ ≃ {n : ℕ // n ∈ Finset.Icc 1 (p - 1)} where
  toFun a := ⟨(a : ZMod p).val, by
    rw [Finset.mem_Icc]
    constructor
    · exact ZMod.val_pos.mpr (Units.ne_zero a)
    · have := ZMod.val_lt (a : ZMod p)
      omega⟩
  invFun n :=
    ZMod.unitOfCoprime n.1 <|
      Nat.Coprime.symm <| (Fact.out : p.Prime).coprime_iff_not_dvd.mpr <| by
        intro hpn
        have hn := Finset.mem_Icc.mp n.2
        have hp_le_n := Nat.le_of_dvd (by omega) hpn
        omega
  left_inv a := by
    apply Units.ext
    exact ZMod.natCast_zmod_val (a : ZMod p)
  right_inv n := by
    apply Subtype.ext
    apply ZMod.val_natCast_of_lt
    have hn := Finset.mem_Icc.mp n.2
    omega

/-- Reindexing by least positive representatives turns the weighted scalar
into the sum of the upper-half representatives. -/
theorem stickelbergerTwoWeightedScalar_eq_upperHalfSum (hp5 : 5 ≤ p) :
    stickelbergerTwoWeightedScalar p =
      ∑ n ∈ Finset.Icc (p / 2 + 1) (p - 1), (n : ZMod p) := by
  classical
  have hp_ne_two : p ≠ 2 := by omega
  have hp_odd : p % 2 = 1 :=
    ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp_ne_two
  have hhalf : 2 * (p / 2) = p - 1 := Nat.two_mul_odd_div_two hp_odd
  let e := unitsEquivIcc (p := p)
  calc
    stickelbergerTwoWeightedScalar p =
        ∑ n : {n : ℕ // n ∈ Finset.Icc 1 (p - 1)},
          if p ≤ 2 * n.1 then (n.1 : ZMod p) else 0 := by
      unfold stickelbergerTwoWeightedScalar
      apply Fintype.sum_equiv e
      intro a
      rw [stickelbergerTwoCoefficient_eq_ite]
      change ((if p ≤ 2 * (a : ZMod p).val then 1 else 0 : ℕ) : ZMod p) *
          (a : ZMod p) =
        if p ≤ 2 * (a : ZMod p).val then
          ((a : ZMod p).val : ZMod p) else 0
      split_ifs <;> simp
    _ = ∑ n ∈ Finset.Icc 1 (p - 1),
          if p ≤ 2 * n then (n : ZMod p) else 0 := by
      exact Finset.sum_attach (Finset.Icc 1 (p - 1))
        (fun n : ℕ ↦ if p ≤ 2 * n then (n : ZMod p) else 0)
    _ = ∑ n ∈ Finset.Icc (p / 2 + 1) (p - 1), (n : ZMod p) := by
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega

/-- Closed natural-number formula for the upper-half interval.  The
division-free form is convenient for reduction modulo `p`. -/
theorem eight_mul_sum_upperHalf (hp5 : 5 ≤ p) :
    8 * (∑ n ∈ Finset.Icc (p / 2 + 1) (p - 1), n) =
      (p - 1) * (3 * p - 1) := by
  have hp_ne_two : p ≠ 2 := by omega
  have hp_odd : p % 2 = 1 :=
    ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp_ne_two
  have hhalf : 2 * (p / 2) = p - 1 := Nat.two_mul_odd_div_two hp_odd
  have hp_one_le : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hle : p / 2 + 1 ≤ p := by omega
  have hinterval :
      Finset.Ico (p / 2 + 1) p =
        Finset.Icc (p / 2 + 1) (p - 1) := by
    calc
      Finset.Ico (p / 2 + 1) p =
          Finset.Ico (p / 2 + 1) (p - 1 + 1) := by
        rw [Nat.sub_add_cancel hp_one_le]
      _ = Finset.Icc (p / 2 + 1) (p - 1) :=
        Finset.Ico_add_one_right_eq_Icc (p / 2 + 1) (p - 1)
  have hsplit :=
    Finset.sum_range_add_sum_Ico (fun n : ℕ ↦ n) hle
  rw [hinterval] at hsplit
  have htotal := Finset.sum_range_id_mul_two p
  have hlower := Finset.sum_range_id_mul_two (p / 2 + 1)
  have hp_eq : p = 2 * (p / 2) + 1 := by omega
  have hthree : 3 * p - 1 = 6 * (p / 2) + 2 := by omega
  have htotal' :
      (∑ n ∈ Finset.range p, n) * 2 =
        (2 * (p / 2) + 1) * (2 * (p / 2)) := by
    calc
      (∑ n ∈ Finset.range p, n) * 2 = p * (p - 1) := htotal
      _ = (2 * (p / 2) + 1) * (2 * (p / 2)) := by
        nlinarith [hp_eq, hhalf]
  have hlower' :
      (∑ n ∈ Finset.range (p / 2 + 1), n) * 2 =
        (p / 2 + 1) * (p / 2) := by
    simpa only [Nat.add_sub_cancel] using hlower
  conv_rhs => rw [← hhalf, hthree]
  nlinarith

/-- Eight times the upper-half sum is one modulo `p`. -/
theorem eight_mul_upperHalfSum (hp5 : 5 ≤ p) :
    (8 : ZMod p) *
        (∑ n ∈ Finset.Icc (p / 2 + 1) (p - 1), (n : ZMod p)) = 1 := by
  have h := congrArg (fun n : ℕ ↦ (n : ZMod p))
    (eight_mul_sum_upperHalf (p := p) hp5)
  push_cast at h
  rw [Nat.cast_sub (Fact.out : p.Prime).one_le,
    Nat.cast_sub (by have := (Fact.out : p.Prime).pos; omega),
    ZMod.natCast_self] at h
  norm_num at h ⊢
  exact h

/-- The exact inverse-character scalar identity for the corrected
`b = 2` coefficient. -/
theorem eight_mul_stickelbergerTwoWeightedScalar (hp5 : 5 ≤ p) :
    (8 : ZMod p) * stickelbergerTwoWeightedScalar p = 1 := by
  rw [stickelbergerTwoWeightedScalar_eq_upperHalfSum hp5]
  exact eight_mul_upperHalfSum (p := p) hp5

/-- The corrected `b = 2` weighted scalar is a unit modulo `p`. -/
theorem isUnit_stickelbergerTwoWeightedScalar (hp5 : 5 ≤ p) :
    IsUnit (stickelbergerTwoWeightedScalar p) := by
  apply IsUnit.of_mul_eq_one (8 : ZMod p)
  rw [mul_comm]
  exact eight_mul_stickelbergerTwoWeightedScalar (p := p) hp5

end NumberTheory.CyclotomicCharacter
