/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenParametrization
import Mathlib.Data.ZMod.Basic

/-!
# The four exceptional `j`-invariants at level twenty-one

The four noncuspidal rational points of `X₀(21)` have

`j ∈ {3375/2, -140625/8, -189613868625/128, -1159088625/2097152}`.

Every numerator is divisible by `5³` while every denominator is a power of
two.  On the order-seven Tate family the invariant `c₄` is the value of the
binary form

`(m² - mn + n²)(m⁶ - 11m⁵n + 30m⁴n² - 15m³n³ - 10m²n⁴ + 5mn⁵ + n⁶)`,

which has no nontrivial zero modulo five.  Consequently
`c₄(d)³ = j₀·Δ(d)` is impossible for every rational `d` and each of the
four exceptional values: a curve carrying a rational point of order seven
never has one of the four exceptional `j`-invariants.
-/

namespace MazurTorsion.Kubert

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The homogenized `c₄` of the order-seven family, as a binary form. -/
private def sevenC₄Form (m n : ℤ) : ℤ :=
  (m ^ 2 - m * n + n ^ 2) *
    (m ^ 6 - 11 * m ^ 5 * n + 30 * m ^ 4 * n ^ 2 - 15 * m ^ 3 * n ^ 3 -
      10 * m ^ 2 * n ^ 4 + 5 * m * n ^ 5 + n ^ 6)

/-- The homogenized discriminant of the order-seven family. -/
private def sevenΔForm (m n : ℤ) : ℤ :=
  m ^ 7 * (m - n) ^ 7 *
    (m ^ 3 - 8 * m ^ 2 * n + 5 * m * n ^ 2 + n ^ 3) * n ^ 7

private lemma sevenC₄Form_cube_unit_mod_five :
    ∀ m n q : ZMod 5, q ≠ 0 → (m ≠ 0 ∨ n ≠ 0) →
      q * ((m ^ 2 - m * n + n ^ 2) *
        (m ^ 6 - 11 * m ^ 5 * n + 30 * m ^ 4 * n ^ 2 -
          15 * m ^ 3 * n ^ 3 - 10 * m ^ 2 * n ^ 4 +
          5 * m * n ^ 5 + n ^ 6)) ^ 3 ≠ 0 := by
  decide

/-- Homogenization of the family `c₄` at a reduced fraction. -/
private lemma c₄_homogenize (m n : ℤ) (hn : (n : ℚ) ≠ 0) :
    (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
        (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).c₄ * (n : ℚ) ^ 8 =
      ((sevenC₄Form m n : ℤ) : ℚ) := by
  rw [orderSeven_c₄]
  unfold sevenC₄Form
  push_cast
  field_simp

/-- Homogenization of the family discriminant at a reduced fraction. -/
private lemma Δ_homogenize (m n : ℤ) (hn : (n : ℚ) ≠ 0) :
    (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
        (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).Δ * (n : ℚ) ^ 24 =
      ((sevenΔForm m n : ℤ) : ℚ) := by
  rw [orderSeven_Δ]
  unfold sevenΔForm
  push_cast
  field_simp

/-- On the order-seven family, `q·c₄³ = p·Δ` is impossible whenever
`5 ∣ p` and `5 ∤ q`. -/
private lemma no_exceptional_j_of_five_dvd
    (p q : ℤ) (hp : (5 : ℤ) ∣ p) (hq : ¬ (5 : ℤ) ∣ q) (d : ℚ)
    (h : (q : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 =
      (p : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ) :
    False := by
  set m : ℤ := d.num with hm
  set n : ℤ := (d.den : ℤ) with hn
  have hn0 : (n : ℚ) ≠ 0 := by
    rw [hn]
    exact_mod_cast d.den_ne_zero
  have hd : d = (m : ℚ) / n := d.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [hm, hn] using Rat.isCoprime_num_den d
  rw [hd] at h
  -- clear denominators to the integral binary forms
  have hcleared :
      q * sevenC₄Form m n ^ 3 = p * sevenΔForm m n := by
    have hC := c₄_homogenize m n hn0
    have hD := Δ_homogenize m n hn0
    have h24 :
        (q : ℚ) *
            ((tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
              (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).c₄ * (n : ℚ) ^ 8) ^ 3 =
          (p : ℚ) *
            ((tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
              (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).Δ * (n : ℚ) ^ 24) := by
      calc
        (q : ℚ) * _ =
            ((q : ℚ) *
              (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
                (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).c₄ ^ 3) *
              (n : ℚ) ^ 24 := by ring
        _ = ((p : ℚ) *
              (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
                (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).Δ) *
              (n : ℚ) ^ 24 := by rw [h]
        _ = (p : ℚ) * _ := by ring
    rw [hC, hD] at h24
    exact_mod_cast h24
  -- reduce modulo five
  have hmod := congrArg (fun z : ℤ ↦ (z : ZMod 5)) hcleared
  simp only [Int.cast_mul, Int.cast_pow] at hmod
  have hp5 : ((p : ZMod 5)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd p 5).mpr hp
  have hq5 : ((q : ZMod 5)) ≠ 0 := by
    intro hz
    exact hq ((ZMod.intCast_zmod_eq_zero_iff_dvd q 5).mp hz)
  -- coprimality prevents both coordinates from vanishing modulo five
  have hnotboth : ((m : ZMod 5) ≠ 0 ∨ (n : ZMod 5) ≠ 0) := by
    by_contra hcon
    push Not at hcon
    have h5m : (5 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 5).mp hcon.1
    have h5n : (5 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mp hcon.2
    have : IsUnit (5 : ℤ) := hmn.isUnit_of_dvd' h5m h5n
    norm_num [Int.isUnit_iff] at this
  apply sevenC₄Form_cube_unit_mod_five (m : ZMod 5) (n : ZMod 5)
    (q : ZMod 5) hq5 hnotboth
  have hCcast : ((sevenC₄Form m n : ℤ) : ZMod 5) =
      ((m : ZMod 5) ^ 2 - (m : ZMod 5) * (n : ZMod 5) +
        (n : ZMod 5) ^ 2) *
      ((m : ZMod 5) ^ 6 - 11 * (m : ZMod 5) ^ 5 * (n : ZMod 5) +
        30 * (m : ZMod 5) ^ 4 * (n : ZMod 5) ^ 2 -
        15 * (m : ZMod 5) ^ 3 * (n : ZMod 5) ^ 3 -
        10 * (m : ZMod 5) ^ 2 * (n : ZMod 5) ^ 4 +
        5 * (m : ZMod 5) * (n : ZMod 5) ^ 5 + (n : ZMod 5) ^ 6) := by
    unfold sevenC₄Form
    push_cast
    ring
  rw [← hCcast, hmod, hp5, zero_mul]

/-- No curve in the order-seven Tate family has `j = 3375/2`. -/
theorem no_seven_family_j_first (d : ℚ) :
    (2 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (3375 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd 3375 2 (by norm_num) (by norm_num) d
    (by exact_mod_cast h)

/-- No curve in the order-seven Tate family has `j = -140625/8`. -/
theorem no_seven_family_j_second (d : ℚ) :
    (8 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (-140625 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd (-140625) 8
    (by norm_num) (by norm_num) d (by exact_mod_cast h)

/-- No curve in the order-seven Tate family has `j = -189613868625/128`. -/
theorem no_seven_family_j_third (d : ℚ) :
    (128 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (-189613868625 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd (-189613868625) 128
    (by norm_num) (by norm_num) d (by exact_mod_cast h)

/-- No curve in the order-seven Tate family has
`j = -1159088625/2097152`. -/
theorem no_seven_family_j_fourth (d : ℚ) :
    (2097152 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (-1159088625 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd (-1159088625) 2097152
    (by norm_num) (by norm_num) d (by exact_mod_cast h)

end MazurTorsion.Kubert
