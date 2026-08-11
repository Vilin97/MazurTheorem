/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellLocalFiniteCertificate

/-!
# The three `191`-adic cusp branches of the `X₁(13)` Pell-power cover

The finite local certificate places every integral power-split solution in
one of `a = 0`, `b = 0`, or `a + b = 0` modulo `191`.  Primitivity makes
these branches exclusive.  This file then reduces the three split-cubic
equations, the ordinate equation, and both thirty-eighth-power equations in
each branch.

The result is an exact reusable branch interface for a later `191`-adic
descent.  Each displayed branch is locally populated, so no global
obstruction is claimed here.
-/

namespace MazurTorsion.XOneThirteenPellLocalBranches

open MazurTorsion.XOneThirteenDescent
open MazurTorsion.XOneThirteenPellLocalCertificate
open MazurTorsion.XOneThirteenPellLocalFiniteCertificate

local instance : NeZero 191 := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 191) := ⟨by norm_num⟩

/-- Congruence data in the branch `191 ∣ a`. -/
def PellCuspAtA191 (m n a b c r s : ℤ) : Prop :=
  (a : F191) = 0 ∧
    (b : F191) ≠ 0 ∧
    (a : F191) + (b : F191) ≠ 0 ∧
    (r : F191) ≠ 0 ∧
    (s : F191) ≠ 0 ∧
    (c : F191) = (n : F191) ^ 2 ∧
    (((m : F191) = (n : F191) ∧
        (n : F191) ^ 2 = -(b : F191) ^ 3 ∧
        (r : F191) ^ 38 = -(b : F191) ^ 19 ∧
        (s : F191) ^ 38 = -(b : F191) ^ 19) ∨
      ((m : F191) = -(n : F191) ∧
        (n : F191) ^ 2 = (b : F191) ^ 3 ∧
        (r : F191) ^ 38 = (b : F191) ^ 19 ∧
        (s : F191) ^ 38 = (b : F191) ^ 19))

/-- Congruence data in the branch `191 ∣ b`. -/
def PellCuspAtB191 (m n a b c r s : ℤ) : Prop :=
  (b : F191) = 0 ∧
    (a : F191) ≠ 0 ∧
    (a : F191) + (b : F191) ≠ 0 ∧
    (c : F191) = (n : F191) ^ 2 ∧
    (((m : F191) = (n : F191) ∧
        (n : F191) ^ 2 = (a : F191) ^ 3 ∧
        (s : F191) = 0 ∧
        (r : F191) ≠ 0 ∧
        (r : F191) ^ 38 = (a : F191) ^ 19) ∨
      ((m : F191) = -(n : F191) ∧
        (n : F191) ^ 2 = -(a : F191) ^ 3 ∧
        (r : F191) = 0 ∧
        (s : F191) ≠ 0 ∧
        (s : F191) ^ 38 = -(a : F191) ^ 19))

/-- Congruence data in the branch `191 ∣ a+b`. -/
def PellCuspAtAPlusB191 (m n a b c r s : ℤ) : Prop :=
  ((a : F191) + (b : F191)) = 0 ∧
    (a : F191) ≠ 0 ∧
    (b : F191) ≠ 0 ∧
    (r : F191) ≠ 0 ∧
    (s : F191) ≠ 0 ∧
    (c : F191) = (n : F191) ^ 2 ∧
    (((m : F191) = (n : F191) ∧
        (n : F191) ^ 2 = (b : F191) ^ 3 ∧
        (r : F191) ^ 38 = (b : F191) ^ 19 ∧
        (s : F191) ^ 38 = (b : F191) ^ 19) ∨
      ((m : F191) = -(n : F191) ∧
        (n : F191) ^ 2 = -(b : F191) ^ 3 ∧
        (r : F191) ^ 38 = -(b : F191) ^ 19 ∧
        (s : F191) ^ 38 = -(b : F191) ^ 19))

private theorem right_ne_zero_of_isCoprime
    {a b : ℤ} (hab : IsCoprime a b) (ha : (a : F191) = 0) :
    (b : F191) ≠ 0 := by
  intro hb
  have haDvd : (191 : ℤ) ∣ a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd a 191).mp ha
  have hbDvd : (191 : ℤ) ∣ b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd b 191).mp hb
  have hunit : IsUnit (191 : ℤ) := hab.isUnit_of_dvd' haDvd hbDvd
  exact absurd (Int.isUnit_iff.mp hunit) (by norm_num)

private theorem left_ne_zero_of_isCoprime
    {a b : ℤ} (hab : IsCoprime a b) (hb : (b : F191) = 0) :
    (a : F191) ≠ 0 := by
  exact right_ne_zero_of_isCoprime hab.symm hb

private theorem factors_ne_zero_of_product
    {b r s : ℤ} (hbSplit : b = r * s) (hb : (b : F191) ≠ 0) :
    (r : F191) ≠ 0 ∧ (s : F191) ≠ 0 := by
  have hbSplitMod : (b : F191) = (r : F191) * (s : F191) := by
    simpa using congrArg (Int.castRingHom F191) hbSplit
  constructor
  · intro hr
    apply hb
    rw [hbSplitMod, hr, zero_mul]
  · intro hs
    apply hb
    rw [hbSplitMod, hs, mul_zero]

private theorem eq_or_eq_neg_of_sq_eq_sq
    {x y : F191} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have hfactor : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hfactor with hxy | hxy
  · exact Or.inl (sub_eq_zero.mp hxy)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp hxy)

private theorem pellCuspAtA191_of_equations
    (m n a b c r s : ℤ)
    (ha : (a : F191) = 0)
    (hb : (b : F191) ≠ 0)
    (hlead : n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)))
    (htrace : m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3))
    (hpair : 2 * m ^ 2 - 4 * m * n - 2 * n ^ 2 =
      4 * (-a ^ 3 - 3 * a ^ 2 * b + b ^ 3))
    (htwice : 2 * c = m ^ 2 + n ^ 2)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    PellCuspAtA191 m n a b c r s := by
  have hrs := factors_ne_zero_of_product hbSplit hb
  have hleadMod :
      (n : F191) ^ 2 - (m : F191) ^ 2 =
        4 * ((a : F191) * (b : F191) * ((a : F191) + (b : F191))) := by
    simpa using congrArg (Int.castRingHom F191) hlead
  have htraceMod :
      (m : F191) ^ 2 + 4 * (m : F191) * (n : F191) - (n : F191) ^ 2 =
        4 * ((a : F191) ^ 3 - 3 * (a : F191) * (b : F191) ^ 2 -
          (b : F191) ^ 3) := by
    simpa using congrArg (Int.castRingHom F191) htrace
  have hpairMod :
      2 * (m : F191) ^ 2 - 4 * (m : F191) * (n : F191) -
          2 * (n : F191) ^ 2 =
        4 * (-(a : F191) ^ 3 - 3 * (a : F191) ^ 2 * (b : F191) +
          (b : F191) ^ 3) := by
    simpa using congrArg (Int.castRingHom F191) hpair
  have htwiceMod :
      2 * (c : F191) = (m : F191) ^ 2 + (n : F191) ^ 2 := by
    simpa using congrArg (Int.castRingHom F191) htwice
  have hsq : (m : F191) ^ 2 = (n : F191) ^ 2 := by
    rw [ha] at hleadMod
    ring_nf at hleadMod
    linear_combination -hleadMod
  have hplusMod :
      (pellHHomogeneous a b : F191) +
          (c : F191) * (pellKHomogeneous a b : F191) =
        2 * (r : F191) ^ 38 := by
    simpa [positivePellFactor] using
      congrArg (Int.castRingHom F191) hplus
  have hminusMod :
      (c : F191) * (pellKHomogeneous a b : F191) -
          (pellHHomogeneous a b : F191) =
        2 * (s : F191) ^ 38 := by
    simpa [negativePellFactorMagnitude] using
      congrArg (Int.castRingHom F191) hminus
  have hH : (pellHHomogeneous a b : F191) = 0 := by
    simp [pellHHomogeneous, ha]
  have hK : (pellKHomogeneous a b : F191) = 2 * (b : F191) ^ 16 := by
    simp [pellKHomogeneous, ha]
  have hsum : (a : F191) + (b : F191) ≠ 0 := by simpa [ha] using hb
  refine ⟨ha, hb, hsum, hrs.1, hrs.2, ?_⟩
  rcases eq_or_eq_neg_of_sq_eq_sq hsq with hm | hm
  · have hnSq : (n : F191) ^ 2 = -(b : F191) ^ 3 := by
      rw [ha, hm] at htraceMod
      ring_nf at htraceMod
      apply mul_right_cancel₀ (by decide : (4 : F191) ≠ 0)
      simpa only [neg_mul] using htraceMod
    have hc : (c : F191) = (n : F191) ^ 2 := by
      rw [hm] at htwiceMod
      ring_nf at htwiceMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact htwiceMod
    refine ⟨hc, Or.inl ⟨hm, hnSq, ?_, ?_⟩⟩
    · rw [hH, hK, hc, hnSq] at hplusMod
      ring_nf at hplusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      simpa only [neg_mul] using hplusMod.symm
    · rw [hH, hK, hc, hnSq] at hminusMod
      ring_nf at hminusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      simpa only [neg_mul] using hminusMod.symm
  · have hnSq : (n : F191) ^ 2 = (b : F191) ^ 3 := by
      rw [ha, hm] at hpairMod
      ring_nf at hpairMod
      apply mul_right_cancel₀ (by decide : (4 : F191) ≠ 0)
      exact hpairMod
    have hc : (c : F191) = (n : F191) ^ 2 := by
      rw [hm] at htwiceMod
      ring_nf at htwiceMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact htwiceMod
    refine ⟨hc, Or.inr ⟨hm, hnSq, ?_, ?_⟩⟩
    · rw [hH, hK, hc, hnSq] at hplusMod
      ring_nf at hplusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact hplusMod.symm
    · rw [hH, hK, hc, hnSq] at hminusMod
      ring_nf at hminusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact hminusMod.symm

private theorem pellCuspAtB191_of_equations
    (m n a b c r s : ℤ)
    (hb : (b : F191) = 0)
    (ha : (a : F191) ≠ 0)
    (hlead : n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)))
    (htrace : m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3))
    (hpair : 2 * m ^ 2 - 4 * m * n - 2 * n ^ 2 =
      4 * (-a ^ 3 - 3 * a ^ 2 * b + b ^ 3))
    (htwice : 2 * c = m ^ 2 + n ^ 2)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38) :
    PellCuspAtB191 m n a b c r s := by
  have hleadMod :
      (n : F191) ^ 2 - (m : F191) ^ 2 =
        4 * ((a : F191) * (b : F191) * ((a : F191) + (b : F191))) := by
    simpa using congrArg (Int.castRingHom F191) hlead
  have htraceMod :
      (m : F191) ^ 2 + 4 * (m : F191) * (n : F191) - (n : F191) ^ 2 =
        4 * ((a : F191) ^ 3 - 3 * (a : F191) * (b : F191) ^ 2 -
          (b : F191) ^ 3) := by
    simpa using congrArg (Int.castRingHom F191) htrace
  have hpairMod :
      2 * (m : F191) ^ 2 - 4 * (m : F191) * (n : F191) -
          2 * (n : F191) ^ 2 =
        4 * (-(a : F191) ^ 3 - 3 * (a : F191) ^ 2 * (b : F191) +
          (b : F191) ^ 3) := by
    simpa using congrArg (Int.castRingHom F191) hpair
  have htwiceMod :
      2 * (c : F191) = (m : F191) ^ 2 + (n : F191) ^ 2 := by
    simpa using congrArg (Int.castRingHom F191) htwice
  have hsq : (m : F191) ^ 2 = (n : F191) ^ 2 := by
    rw [hb] at hleadMod
    ring_nf at hleadMod
    linear_combination -hleadMod
  have hplusMod :
      (pellHHomogeneous a b : F191) +
          (c : F191) * (pellKHomogeneous a b : F191) =
        2 * (r : F191) ^ 38 := by
    simpa [positivePellFactor] using
      congrArg (Int.castRingHom F191) hplus
  have hminusMod :
      (c : F191) * (pellKHomogeneous a b : F191) -
          (pellHHomogeneous a b : F191) =
        2 * (s : F191) ^ 38 := by
    simpa [negativePellFactorMagnitude] using
      congrArg (Int.castRingHom F191) hminus
  have hH : (pellHHomogeneous a b : F191) = (a : F191) ^ 19 := by
    simp [pellHHomogeneous, hb]
  have hK : (pellKHomogeneous a b : F191) = (a : F191) ^ 16 := by
    simp [pellKHomogeneous, hb]
  have hsum : (a : F191) + (b : F191) ≠ 0 := by simpa [hb] using ha
  refine ⟨hb, ha, hsum, ?_⟩
  rcases eq_or_eq_neg_of_sq_eq_sq hsq with hm | hm
  · have hnSq : (n : F191) ^ 2 = (a : F191) ^ 3 := by
      rw [hb, hm] at htraceMod
      ring_nf at htraceMod
      apply mul_right_cancel₀ (by decide : (4 : F191) ≠ 0)
      exact htraceMod
    have hc : (c : F191) = (n : F191) ^ 2 := by
      rw [hm] at htwiceMod
      ring_nf at htwiceMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact htwiceMod
    have hsPow : (s : F191) ^ 38 = 0 := by
      rw [hH, hK, hc, hnSq] at hminusMod
      ring_nf at hminusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact hminusMod.symm
    have hsZero : (s : F191) = 0 :=
      (pow_eq_zero_iff (by norm_num : (38 : ℕ) ≠ 0)).mp hsPow
    have hrPow : (r : F191) ^ 38 = (a : F191) ^ 19 := by
      rw [hH, hK, hc, hnSq] at hplusMod
      ring_nf at hplusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact hplusMod.symm
    have hrNe : (r : F191) ≠ 0 := by
      intro hr
      apply pow_ne_zero 19 ha
      rw [← hrPow, hr]
      norm_num
    exact ⟨hc, Or.inl ⟨hm, hnSq, hsZero, hrNe, hrPow⟩⟩
  · have hnSq : (n : F191) ^ 2 = -(a : F191) ^ 3 := by
      rw [hb, hm] at hpairMod
      ring_nf at hpairMod
      apply mul_right_cancel₀ (by decide : (4 : F191) ≠ 0)
      simpa only [neg_mul] using hpairMod
    have hc : (c : F191) = (n : F191) ^ 2 := by
      rw [hm] at htwiceMod
      ring_nf at htwiceMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact htwiceMod
    have hrPow : (r : F191) ^ 38 = 0 := by
      rw [hH, hK, hc, hnSq] at hplusMod
      ring_nf at hplusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact hplusMod.symm
    have hrZero : (r : F191) = 0 :=
      (pow_eq_zero_iff (by norm_num : (38 : ℕ) ≠ 0)).mp hrPow
    have hsPow : (s : F191) ^ 38 = -(a : F191) ^ 19 := by
      rw [hH, hK, hc, hnSq] at hminusMod
      ring_nf at hminusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      simpa only [neg_mul] using hminusMod.symm
    have hsNe : (s : F191) ≠ 0 := by
      intro hs
      apply pow_ne_zero 19 ha
      have : -(a : F191) ^ 19 = 0 := by
        rw [← hsPow, hs]
        norm_num
      simpa using neg_eq_zero.mp this
    exact ⟨hc, Or.inr ⟨hm, hnSq, hrZero, hsNe, hsPow⟩⟩

private theorem pellCuspAtAPlusB191_of_equations
    (m n a b c r s : ℤ)
    (hab : IsCoprime a b)
    (hsum : (a : F191) + (b : F191) = 0)
    (hlead : n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)))
    (htrace : m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3))
    (hpair : 2 * m ^ 2 - 4 * m * n - 2 * n ^ 2 =
      4 * (-a ^ 3 - 3 * a ^ 2 * b + b ^ 3))
    (htwice : 2 * c = m ^ 2 + n ^ 2)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    PellCuspAtAPlusB191 m n a b c r s := by
  have haEq : (a : F191) = -(b : F191) :=
    eq_neg_of_add_eq_zero_left hsum
  have hb : (b : F191) ≠ 0 := by
    intro hbZero
    have haZero : (a : F191) = 0 := by rw [haEq, hbZero, neg_zero]
    exact (right_ne_zero_of_isCoprime hab haZero) hbZero
  have ha : (a : F191) ≠ 0 := by simpa [haEq] using hb
  have hrs := factors_ne_zero_of_product hbSplit hb
  have hleadMod :
      (n : F191) ^ 2 - (m : F191) ^ 2 =
        4 * ((a : F191) * (b : F191) * ((a : F191) + (b : F191))) := by
    simpa using congrArg (Int.castRingHom F191) hlead
  have htraceMod :
      (m : F191) ^ 2 + 4 * (m : F191) * (n : F191) - (n : F191) ^ 2 =
        4 * ((a : F191) ^ 3 - 3 * (a : F191) * (b : F191) ^ 2 -
          (b : F191) ^ 3) := by
    simpa using congrArg (Int.castRingHom F191) htrace
  have hpairMod :
      2 * (m : F191) ^ 2 - 4 * (m : F191) * (n : F191) -
          2 * (n : F191) ^ 2 =
        4 * (-(a : F191) ^ 3 - 3 * (a : F191) ^ 2 * (b : F191) +
          (b : F191) ^ 3) := by
    simpa using congrArg (Int.castRingHom F191) hpair
  have htwiceMod :
      2 * (c : F191) = (m : F191) ^ 2 + (n : F191) ^ 2 := by
    simpa using congrArg (Int.castRingHom F191) htwice
  have hsq : (m : F191) ^ 2 = (n : F191) ^ 2 := by
    rw [hsum] at hleadMod
    ring_nf at hleadMod
    linear_combination -hleadMod
  have hplusMod :
      (pellHHomogeneous a b : F191) +
          (c : F191) * (pellKHomogeneous a b : F191) =
        2 * (r : F191) ^ 38 := by
    simpa [positivePellFactor] using
      congrArg (Int.castRingHom F191) hplus
  have hminusMod :
      (c : F191) * (pellKHomogeneous a b : F191) -
          (pellHHomogeneous a b : F191) =
        2 * (s : F191) ^ 38 := by
    simpa [negativePellFactorMagnitude] using
      congrArg (Int.castRingHom F191) hminus
  have hH : (pellHHomogeneous a b : F191) = 0 := by
    simp [pellHHomogeneous, haEq]
    ring
  have hK : (pellKHomogeneous a b : F191) = 2 * (b : F191) ^ 16 := by
    simp [pellKHomogeneous, haEq]
    ring
  refine ⟨hsum, ha, hb, hrs.1, hrs.2, ?_⟩
  rcases eq_or_eq_neg_of_sq_eq_sq hsq with hm | hm
  · have hnSq : (n : F191) ^ 2 = (b : F191) ^ 3 := by
      rw [haEq, hm] at htraceMod
      ring_nf at htraceMod
      apply mul_right_cancel₀ (by decide : (4 : F191) ≠ 0)
      exact htraceMod
    have hc : (c : F191) = (n : F191) ^ 2 := by
      rw [hm] at htwiceMod
      ring_nf at htwiceMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact htwiceMod
    refine ⟨hc, Or.inl ⟨hm, hnSq, ?_, ?_⟩⟩
    · rw [hH, hK, hc, hnSq] at hplusMod
      ring_nf at hplusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact hplusMod.symm
    · rw [hH, hK, hc, hnSq] at hminusMod
      ring_nf at hminusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact hminusMod.symm
  · have hnSq : (n : F191) ^ 2 = -(b : F191) ^ 3 := by
      rw [haEq, hm] at hpairMod
      ring_nf at hpairMod
      apply mul_right_cancel₀ (by decide : (4 : F191) ≠ 0)
      simpa only [neg_mul] using hpairMod
    have hc : (c : F191) = (n : F191) ^ 2 := by
      rw [hm] at htwiceMod
      ring_nf at htwiceMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      exact htwiceMod
    refine ⟨hc, Or.inr ⟨hm, hnSq, ?_, ?_⟩⟩
    · rw [hH, hK, hc, hnSq] at hplusMod
      ring_nf at hplusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      simpa only [neg_mul] using hplusMod.symm
    · rw [hH, hK, hc, hnSq] at hminusMod
      ring_nf at hminusMod
      apply mul_right_cancel₀ (by decide : (2 : F191) ≠ 0)
      simpa only [neg_mul] using hminusMod.symm

/-- Exact three-way reduction of a primitive Pell-power split system modulo
`191`.  In particular, the nonvanishing fields make the three cusp branches
pairwise exclusive, while the inner alternatives record the two signs
`m = ±n` and their forced thirty-eighth-power residues. -/
theorem pell_power_split_mod_191_exact_branches
    (m n a b c r s : ℤ)
    (hab : IsCoprime a b)
    (hlead : n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)))
    (htrace : m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3))
    (hpair : 2 * m ^ 2 - 4 * m * n - 2 * n ^ 2 =
      4 * (-a ^ 3 - 3 * a ^ 2 * b + b ^ 3))
    (htwice : 2 * c = m ^ 2 + n ^ 2)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    PellCuspAtA191 m n a b c r s ∨
      PellCuspAtB191 m n a b c r s ∨
      PellCuspAtAPlusB191 m n a b c r s := by
  rcases pell_power_split_mod_191_cusp_divisor a b c r s
      hplus hminus hbSplit with haDvd | hbDvd | hsumDvd
  · have ha : (a : F191) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a 191).mpr haDvd
    have hb := right_ne_zero_of_isCoprime hab ha
    exact Or.inl (pellCuspAtA191_of_equations m n a b c r s
      ha hb hlead htrace hpair htwice hplus hminus hbSplit)
  · have hb : (b : F191) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd b 191).mpr hbDvd
    have ha := left_ne_zero_of_isCoprime hab hb
    exact Or.inr (Or.inl (pellCuspAtB191_of_equations m n a b c r s
      hb ha hlead htrace hpair htwice hplus hminus))
  · have hsumCast : ((a + b : ℤ) : F191) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 191).mpr hsumDvd
    have hsum : (a : F191) + (b : F191) = 0 := by
      simpa using hsumCast
    exact Or.inr (Or.inr (pellCuspAtAPlusB191_of_equations
      m n a b c r s hab hsum hlead htrace hpair htwice
      hplus hminus hbSplit))

end MazurTorsion.XOneThirteenPellLocalBranches
