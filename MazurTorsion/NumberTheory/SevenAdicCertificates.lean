/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Seven-adic certificates for the level-seven CM loci

The quadratic `t² + 245t + 2401` and the quartic
`t⁴ - 490t³ - 21609t² - 235298t - 823543` cut out the complex
multiplication fibres (over `j = 0` and `j = 1728`) of the degeneracy
loci of level-seven hauptmodul correspondences.  Neither has a rational
root: the quadratic dies modulo eight and the quartic modulo five.
Both facts are shared by the `X₀(21)` and `X₀(49)` transfer files.
-/

namespace MazurTorsion

private abbrev toTwo : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

private lemma quad_mod_eight :
    ∀ m n : ZMod 8, (toTwo m ≠ 0 ∨ toTwo n ≠ 0) →
      m ^ 2 + 245 * m * n + 2401 * n ^ 2 ≠ 0 := by
  decide

private lemma intCast_toTwo_ne_zero
    {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    toTwo (m : ZMod 8) ≠ 0 := by
  intro h
  apply hm
  have h2 : ((m : ZMod 2) : ZMod 2) = 0 := by
    simpa [toTwo] using h
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2

/-- The quadratic factor `t₇² + 245t₇ + 2401` has no rational root. -/
lemma levelSevenQuadratic_ne_zero (t₇ : ℚ) :
    t₇ ^ 2 + 245 * t₇ + 2401 ≠ 0 := by
  intro hq
  let m : ℤ := t₇.num
  let n : ℤ := (t₇.den : ℤ)
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast t₇.den_ne_zero
  have ht : t₇ = (m : ℚ) / n := t₇.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den t₇
  have hclearedQ :
      ((m ^ 2 + 245 * m * n + 2401 * n ^ 2 : ℤ) : ℚ) = 0 := by
    rw [ht] at hq
    field_simp at hq
    push_cast
    linear_combination hq
  have hcleared : m ^ 2 + 245 * m * n + 2401 * n ^ 2 = 0 := by
    exact_mod_cast hclearedQ
  have hodd : ¬ (2 : ℤ) ∣ m ∨ ¬ (2 : ℤ) ∣ n := by
    by_contra hcon
    push Not at hcon
    have : IsUnit (2 : ℤ) := hmn.isUnit_of_dvd' hcon.1 hcon.2
    norm_num [Int.isUnit_iff] at this
  apply quad_mod_eight (m : ZMod 8) (n : ZMod 8)
    (hodd.imp intCast_toTwo_ne_zero intCast_toTwo_ne_zero)
  have := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hcleared
  push_cast at this
  linear_combination this

private lemma quartic_mod_five :
    ∀ m n : ZMod 5, (m ≠ 0 ∨ n ≠ 0) →
      m ^ 4 - 490 * m ^ 3 * n - 21609 * m ^ 2 * n ^ 2 -
        235298 * m * n ^ 3 - 823543 * n ^ 4 ≠ 0 := by
  decide

/-- The quartic factor has no rational root. -/
lemma levelSevenQuartic_ne_zero (t₇ : ℚ) :
    t₇ ^ 4 - 490 * t₇ ^ 3 - 21609 * t₇ ^ 2 -
      235298 * t₇ - 823543 ≠ 0 := by
  intro hq
  let m : ℤ := t₇.num
  let n : ℤ := (t₇.den : ℤ)
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast t₇.den_ne_zero
  have ht : t₇ = (m : ℚ) / n := t₇.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den t₇
  have hclearedQ :
      ((m ^ 4 - 490 * m ^ 3 * n - 21609 * m ^ 2 * n ^ 2 -
        235298 * m * n ^ 3 - 823543 * n ^ 4 : ℤ) : ℚ) = 0 := by
    rw [ht] at hq
    field_simp at hq
    push_cast
    linear_combination hq
  have hcleared : m ^ 4 - 490 * m ^ 3 * n - 21609 * m ^ 2 * n ^ 2 -
      235298 * m * n ^ 3 - 823543 * n ^ 4 = 0 := by
    exact_mod_cast hclearedQ
  have hnotboth : ((m : ZMod 5) ≠ 0 ∨ (n : ZMod 5) ≠ 0) := by
    by_contra hcon
    push Not at hcon
    have h5m : (5 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 5).mp hcon.1
    have h5n : (5 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mp hcon.2
    have : IsUnit (5 : ℤ) := hmn.isUnit_of_dvd' h5m h5n
    norm_num [Int.isUnit_iff] at this
  apply quartic_mod_five (m : ZMod 5) (n : ZMod 5) hnotboth
  have := congrArg (fun z : ℤ ↦ (z : ZMod 5)) hcleared
  push_cast at this
  linear_combination this


end MazurTorsion
