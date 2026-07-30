/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.VariableChange
import MazurTorsion.NumberTheory.QuarticDifferenceDescent
import Mathlib.NumberTheory.FLT.Four

/-!
# Elimination of a rational point of order sixteen

The elementary part of the order-sixteen argument ends on the hyperelliptic
curve

`v² = (u² - 1)(u² + 1)(u² + 2u - 1)`.

This file first proves the arithmetic obstruction for this curve.  The proof
clears denominators and splits according to their parity.  Opposite parity
produces a nonzero square which is a difference of fourth powers; odd/odd
parity produces a forbidden solution of `a⁴ + b⁴ = c²`.

The second part records the duplication identities which connect an
order-sixteen chain

`R, 2R, 4R, 8R`

on a normalized Weierstrass equation `Y² = X³ + aX² + bX` to the displayed
curve.
-/

namespace MazurTorsion.Kubert

open scoped WeierstrassCurve.Affine

/-- The short model used after translating the final two-torsion point to
the origin and completing the square. -/
def normalizedCurve (a b : ℚ) : WeierstrassCurve ℚ :=
  ⟨0, a, 0, b, 0⟩

private lemma normalized_curve_equation
    {a b x y : ℚ}
    (h : (normalizedCurve a b).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + a * x ^ 2 + b * x := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simpa [normalizedCurve] using heq

private lemma normalized_duplication_identity_algebra
    {a b x y x₂ : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x)
    (hx₂ :
      x₂ =
        ((3 * x ^ 2 + 2 * a * x + b) / (2 * y)) ^ 2 -
          a - 2 * x) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2 := by
  rw [hx₂]
  field_simp [hy]
  linear_combination -4 * (a + 2 * x) * hcurve

/-- The denominator-free duplication identity on `normalizedCurve`. -/
lemma normalized_duplication_identity_of_double
    {a b x y x₂ y₂ : ℚ}
    [_hE : (normalizedCurve a b).IsElliptic]
    (hP : (normalizedCurve a b).toAffine.Nonsingular x y)
    (hP₂ : (normalizedCurve a b).toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) •
          WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2 := by
  let W := normalizedCurve a b
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hy
    simp [W, normalizedCurve, WeierstrassCurve.Affine.negY, hy0]
  let ℓ := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := W.toAffine) (h₁ := hP) hy
  have hx₂ : W.toAffine.addX x x ℓ = x₂ := by
    have hsum :
        WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP =
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
      simpa [two_nsmul] using hdouble
    exact (WeierstrassCurve.Affine.Point.some.inj
      (hadd.symm.trans hsum)).1
  have hℓ :
      ℓ = (3 * x ^ 2 + 2 * a * x + b) / (2 * y) := by
    dsimp [ℓ]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp only [WeierstrassCurve.Affine.negY]
    simp [W, normalizedCurve]
    ring
  apply normalized_duplication_identity_algebra hy0
    (normalized_curve_equation hP)
  rw [← hx₂]
  simp only [WeierstrassCurve.Affine.addX]
  rw [hℓ]
  simp [W, normalizedCurve]
  ring

private lemma isCoprime_sub_sq_left
    {m n : ℤ} (hmn : IsCoprime m n) :
    IsCoprime (m ^ 2 - n ^ 2) n := by
  have hsq : IsCoprime (m ^ 2) n := hmn.pow_left
  simpa only [pow_two, sub_eq_add_neg, mul_neg] using
    (hsq.add_mul_left_left (-n))

private lemma isCoprime_add_sq_left
    {m n : ℤ} (hmn : IsCoprime m n) :
    IsCoprime (m ^ 2 + n ^ 2) n := by
  have hsq : IsCoprime (m ^ 2) n := hmn.pow_left
  simpa [pow_two] using
    (hsq.add_mul_left_left n)

private lemma odd_sq_sub_sq_of_opposite_parity
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    Odd (m ^ 2 - n ^ 2) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · obtain ⟨m₀, hm₀⟩ := Int.dvd_of_emod_eq_zero hm
    obtain ⟨n₀, hn₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
    rw [sub_eq_iff_eq_add] at hn₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 - n ^ 2 =
          2 * (2 * m₀ ^ 2 - 2 * n₀ ^ 2 - 2 * n₀ - 1) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega
  · obtain ⟨n₀, hn₀⟩ := Int.dvd_of_emod_eq_zero hn
    obtain ⟨m₀, hm₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
    rw [sub_eq_iff_eq_add] at hm₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 - n ^ 2 =
          2 * (2 * m₀ ^ 2 + 2 * m₀ - 2 * n₀ ^ 2) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega

private lemma odd_sq_add_sq_of_opposite_parity
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    Odd (m ^ 2 + n ^ 2) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · obtain ⟨m₀, hm₀⟩ := Int.dvd_of_emod_eq_zero hm
    obtain ⟨n₀, hn₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
    rw [sub_eq_iff_eq_add] at hn₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 + n ^ 2 =
          2 * (2 * m₀ ^ 2 + 2 * n₀ ^ 2 + 2 * n₀) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega
  · obtain ⟨n₀, hn₀⟩ := Int.dvd_of_emod_eq_zero hn
    obtain ⟨m₀, hm₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
    rw [sub_eq_iff_eq_add] at hm₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 + n ^ 2 =
          2 * (2 * m₀ ^ 2 + 2 * m₀ + 2 * n₀ ^ 2) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega

private lemma odd_sub_of_opposite_parity
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    Odd (m - n) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · obtain ⟨m₀, hm₀⟩ := Int.dvd_of_emod_eq_zero hm
    obtain ⟨n₀, hn₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
    rw [sub_eq_iff_eq_add] at hn₀
    refine ⟨m₀ - n₀ - 1, ?_⟩
    rw [hm₀, hn₀]
    ring
  · obtain ⟨n₀, hn₀⟩ := Int.dvd_of_emod_eq_zero hn
    obtain ⟨m₀, hm₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
    rw [sub_eq_iff_eq_add] at hm₀
    refine ⟨m₀ - n₀, ?_⟩
    rw [hm₀, hn₀]
    ring

private lemma opposite_parity_pairwise_coprime
    {m n : ℤ} (hmn : IsCoprime m n)
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) ∧
      IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) ∧
      IsCoprime (m ^ 2 + n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) := by
  have hAq : IsCoprime (m ^ 2 - n ^ 2) n :=
    isCoprime_sub_sq_left hmn
  have hAp : IsCoprime (m ^ 2 - n ^ 2) m := by
    have h := isCoprime_sub_sq_left hmn.symm
    simpa only [neg_sub] using h.neg_left
  have hA2 : IsCoprime (m ^ 2 - n ^ 2) 2 :=
    Int.isCoprime_two_right.mpr
      (odd_sq_sub_sq_of_opposite_parity hpar)
  have hA2q2 : IsCoprime (m ^ 2 - n ^ 2) (2 * n ^ 2) :=
    hA2.mul_right hAq.pow_right
  have hAB : IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) := by
    have h := hA2q2.add_mul_left_right 1
    rw [show 2 * n ^ 2 + (m ^ 2 - n ^ 2) * 1 =
      m ^ 2 + n ^ 2 by ring] at h
    exact h
  have hA2mn : IsCoprime (m ^ 2 - n ^ 2) (2 * m * n) :=
    (hA2.mul_right hAp).mul_right hAq
  have hAC :
    IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) := by
    have h := hA2mn.add_mul_left_right 1
    rw [show 2 * m * n + (m ^ 2 - n ^ 2) * 1 =
      m ^ 2 + 2 * m * n - n ^ 2 by ring] at h
    exact h
  have hBq : IsCoprime (m ^ 2 + n ^ 2) n :=
    isCoprime_add_sq_left hmn
  have hB2 : IsCoprime (m ^ 2 + n ^ 2) 2 :=
    Int.isCoprime_two_right.mpr
      (odd_sq_add_sq_of_opposite_parity hpar)
  have hDq : IsCoprime (m - n) n := by
    have h := hmn.add_mul_left_left (-1)
    rw [show m + n * (-1) = m - n by ring] at h
    exact h
  have hD2 : IsCoprime (m - n) 2 :=
    Int.isCoprime_two_right.mpr (odd_sub_of_opposite_parity hpar)
  have hD2q2 : IsCoprime (m - n) (2 * n ^ 2) :=
    hD2.mul_right hDq.pow_right
  have hBD : IsCoprime (m ^ 2 + n ^ 2) (m - n) := by
    have h := hD2q2.symm.add_mul_left_left (m + n)
    rw [show 2 * n ^ 2 + (m - n) * (m + n) =
      m ^ 2 + n ^ 2 by ring] at h
    exact h
  have hB2qD : IsCoprime (m ^ 2 + n ^ 2) (2 * n * (m - n)) :=
    (hB2.mul_right hBq).mul_right hBD
  have hBC :
      IsCoprime (m ^ 2 + n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) := by
    have h := hB2qD.add_mul_left_right 1
    rw [show 2 * n * (m - n) + (m ^ 2 + n ^ 2) * 1 =
      m ^ 2 + 2 * m * n - n ^ 2 by ring] at h
    exact h
  exact ⟨hAB, hAC, hBC⟩

private theorem no_opposite_parity_certificate
    {m n z : ℤ} (hmn : IsCoprime m n) (hm : m ≠ 0) (hn : n ≠ 0)
    (hA : m ^ 2 - n ^ 2 ≠ 0)
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0))
    (hprod :
      (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) *
        (m ^ 2 + 2 * m * n - n ^ 2) = z ^ 2) :
    False := by
  obtain ⟨hAB, hAC, hBC⟩ :=
    opposite_parity_pairwise_coprime hmn hpar
  obtain ⟨a, ha⟩ : ∃ a : ℤ,
      m ^ 2 - n ^ 2 = a ^ 2 ∨ m ^ 2 - n ^ 2 = -a ^ 2 := by
    apply Int.sq_of_isCoprime (hAB.mul_right hAC) (c := z)
    linear_combination hprod
  obtain ⟨b, hb⟩ : ∃ b : ℤ,
      m ^ 2 + n ^ 2 = b ^ 2 ∨ m ^ 2 + n ^ 2 = -b ^ 2 := by
    apply Int.sq_of_isCoprime (hAB.symm.mul_right hBC) (c := z)
    linear_combination hprod
  have hBpos : 0 < m ^ 2 + n ^ 2 := by
    positivity
  have hbpos : m ^ 2 + n ^ 2 = b ^ 2 := by
    rcases hb with hb | hb
    · exact hb
    · nlinarith [sq_nonneg b]
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    rcases ha with ha | ha <;> norm_num at ha <;> exact hA ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    norm_num at hbpos
    nlinarith [sq_pos_of_ne_zero hm, sq_pos_of_ne_zero hn]
  have hmn0 : 2 * m * n ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm) hn
  apply MazurTorsion.QuarticDifference.sq_ne_quartic_sub_quartic
    hb0 ha0 hmn0
  calc
    b ^ 4 - a ^ 4 = (b ^ 2) ^ 2 - (a ^ 2) ^ 2 := by ring
    _ = (m ^ 2 + n ^ 2) ^ 2 - (m ^ 2 - n ^ 2) ^ 2 := by
      rcases ha with ha | ha
      · rw [← hbpos, ← ha]
      · rw [← hbpos, ha]
        ring
    _ = (2 * m * n) ^ 2 := by ring

private lemma opposite_parity_of_odd_sum
    {r s : ℤ} (hodd : Odd (r + s)) :
    (r % 2 = 0 ∧ s % 2 = 1) ∨
      (r % 2 = 1 ∧ s % 2 = 0) := by
  rw [Int.odd_iff] at hodd
  rcases Int.emod_two_eq_zero_or_one r with hr | hr <;>
    rcases Int.emod_two_eq_zero_or_one s with hs | hs <;> omega

private theorem no_odd_odd_certificate
    {m n z : ℤ} (hmn : IsCoprime m n)
    (hmOdd : Odd m) (hnOdd : Odd n)
    (hA : m ^ 2 - n ^ 2 ≠ 0)
    (hprod :
      (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) *
        (m ^ 2 + 2 * m * n - n ^ 2) = z ^ 2) :
    False := by
  obtain ⟨m₀, hm₀⟩ :=
    exists_eq_mul_left_of_dvd
      (Int.dvd_self_sub_of_emod_eq (Int.odd_iff.mp hmOdd))
  obtain ⟨n₀, hn₀⟩ :=
    exists_eq_mul_left_of_dvd
      (Int.dvd_self_sub_of_emod_eq (Int.odd_iff.mp hnOdd))
  rw [sub_eq_iff_eq_add] at hm₀ hn₀
  let r : ℤ := m₀ + n₀ + 1
  let s : ℤ := m₀ - n₀
  have hmrs : m = r + s := by
    rw [hm₀]
    simp only [r, s]
    ring
  have hnrs : n = r - s := by
    rw [hn₀]
    simp only [r, s]
    ring
  have hrs : IsCoprime r s := by
    obtain ⟨u, v, huv⟩ := hmn
    refine ⟨u + v, u - v, ?_⟩
    rw [hmrs, hnrs] at huv
    linear_combination huv
  have hrsParity :
      (r % 2 = 0 ∧ s % 2 = 1) ∨
        (r % 2 = 1 ∧ s % 2 = 0) := by
    apply opposite_parity_of_odd_sum
    rw [← hmrs]
    exact hmOdd
  have hpair := opposite_parity_pairwise_coprime hrs hrsParity
  have hKrs :
      IsCoprime (r ^ 2 + s ^ 2) (r * s) :=
    Int.isCoprime_of_sq_sum' hrs
  have hKr : IsCoprime (r ^ 2 + s ^ 2) r :=
    hKrs.of_mul_right_left
  have hKs : IsCoprime (r ^ 2 + s ^ 2) s :=
    hKrs.of_mul_right_right
  have hDr :
      IsCoprime (r ^ 2 + 2 * r * s - s ^ 2) r := by
    have h :=
      (hrs.symm.pow_left (m := 2)).neg_left.add_mul_left_left (r + 2 * s)
    rw [show -(s ^ 2) + r * (r + 2 * s) =
      r ^ 2 + 2 * r * s - s ^ 2 by ring] at h
    exact h
  have hDs :
      IsCoprime (r ^ 2 + 2 * r * s - s ^ 2) s := by
    have h := (hrs.pow_left (m := 2)).add_mul_left_left (2 * r - s)
    rw [show r ^ 2 + s * (2 * r - s) =
      r ^ 2 + 2 * r * s - s ^ 2 by ring] at h
    exact h
  have hKD :
      IsCoprime (r ^ 2 + s ^ 2) (r ^ 2 + 2 * r * s - s ^ 2) :=
    hpair.2.2
  have hscaled :
      16 * (r * s * (r ^ 2 + s ^ 2) *
        (r ^ 2 + 2 * r * s - s ^ 2)) = z ^ 2 := by
    rw [← hprod, hmrs, hnrs]
    ring
  have hfourPow : (4 : ℤ) ^ 2 ∣ z ^ 2 := by
    refine ⟨r * s * (r ^ 2 + s ^ 2) *
      (r ^ 2 + 2 * r * s - s ^ 2), ?_⟩
    rw [← hscaled]
    ring
  have hfour : (4 : ℤ) ∣ z :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp hfourPow
  obtain ⟨w, hw⟩ := hfour
  have hsmall :
      r * s * (r ^ 2 + s ^ 2) *
        (r ^ 2 + 2 * r * s - s ^ 2) = w ^ 2 := by
    rw [hw] at hscaled
    nlinarith
  have hrD :
      IsCoprime r (r ^ 2 + 2 * r * s - s ^ 2) :=
    hDr.symm
  have hsD :
      IsCoprime s (r ^ 2 + 2 * r * s - s ^ 2) :=
    hDs.symm
  have hrK : IsCoprime r (r ^ 2 + s ^ 2) := hKr.symm
  have hsK : IsCoprime s (r ^ 2 + s ^ 2) := hKs.symm
  obtain ⟨a, ha⟩ : ∃ a : ℤ, r = a ^ 2 ∨ r = -a ^ 2 := by
    apply Int.sq_of_isCoprime
      ((hrs.mul_right hrK).mul_right hrD) (c := w)
    linear_combination hsmall
  obtain ⟨b, hb⟩ : ∃ b : ℤ, s = b ^ 2 ∨ s = -b ^ 2 := by
    apply Int.sq_of_isCoprime
      ((hrs.symm.mul_right hsK).mul_right hsD) (c := w)
    linear_combination hsmall
  obtain ⟨c, hc⟩ : ∃ c : ℤ,
      r ^ 2 + s ^ 2 = c ^ 2 ∨ r ^ 2 + s ^ 2 = -c ^ 2 := by
    apply Int.sq_of_isCoprime
      ((hKr.mul_right hKs).mul_right hKD) (c := w)
    linear_combination hsmall
  have hrs0 : r * s ≠ 0 := by
    intro hrs0
    apply hA
    rw [hmrs, hnrs]
    rcases mul_eq_zero.mp hrs0 with hr0 | hs0
    · simp [hr0]
    · simp [hs0]
  have hr0 : r ≠ 0 := fun hr0 ↦ hrs0 (by simp [hr0])
  have hs0 : s ≠ 0 := fun hs0 ↦ hrs0 (by simp [hs0])
  have hKpos : 0 < r ^ 2 + s ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hr0, sq_pos_of_ne_zero hs0]
  have hcpos : r ^ 2 + s ^ 2 = c ^ 2 := by
    rcases hc with hc | hc
    · exact hc
    · nlinarith [sq_nonneg c]
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    rcases ha with ha | ha <;> norm_num at ha <;> exact hr0 ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    rcases hb with hb | hb <;> norm_num at hb <;> exact hs0 hb
  apply not_fermat_42 ha0 hb0
  calc
    a ^ 4 + b ^ 4 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2 := by ring
    _ = r ^ 2 + s ^ 2 := by
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [← ha, ← hb]
      · rw [← ha, hb]
        ring
      · rw [ha, ← hb]
        ring
      · rw [ha, hb]
        ring
    _ = c ^ 2 := hcpos

/-- Clearing denominators on the `X₁(16)` sextic gives the integral
three-factor certificate used by both parity branches. -/
lemma integral_certificate_of_sextic_solution
    {u v : ℚ}
    (hcurve :
      v ^ 2 = (u ^ 2 - 1) * (u ^ 2 + 1) *
        (u ^ 2 + 2 * u - 1)) :
    IsSquare
      ((u.num ^ 2 - (u.den : ℤ) ^ 2) *
        (u.num ^ 2 + (u.den : ℤ) ^ 2) *
        (u.num ^ 2 + 2 * u.num * (u.den : ℤ) -
          (u.den : ℤ) ^ 2)) := by
  let m : ℤ := u.num
  let n : ℤ := u.den
  let A : ℤ := m ^ 2 - n ^ 2
  let B : ℤ := m ^ 2 + n ^ 2
  let C : ℤ := m ^ 2 + 2 * m * n - n ^ 2
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast u.den_ne_zero
  have hu : u = (m : ℚ) / n := u.num_div_den.symm
  have hscaled :
      (v * (n : ℚ) ^ 3) ^ 2 = (((A * B * C : ℤ) : ℚ)) := by
    calc
      (v * (n : ℚ) ^ 3) ^ 2 = v ^ 2 * (n : ℚ) ^ 6 := by ring
      _ = (((m : ℚ) ^ 2 - (n : ℚ) ^ 2) *
          ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) *
          ((m : ℚ) ^ 2 + 2 * (m : ℚ) * n - (n : ℚ) ^ 2)) := by
        rw [hcurve, hu]
        field_simp [hn0]
      _ = (((A * B * C : ℤ) : ℚ)) := by
        dsimp [A, B, C]
        push_cast
        ring
  have hsquareRat : IsSquare (((A * B * C : ℤ) : ℚ)) :=
    ⟨v * (n : ℚ) ^ 3, by simpa [pow_two] using hscaled.symm⟩
  rw [← Rat.isSquare_intCast_iff]
  simpa [A, B, C, m, n] using hsquareRat

/-- The noncuspidal part of the rational `X₁(16)` sextic has no points.

The excluded equality `u² = 1` is exactly the degenerate numerator factor.
It is the nondegeneracy condition supplied by the order-eight and order-four
members of the duplication chain. -/
theorem no_nondegenerate_sextic_solution
    {u v : ℚ} (hu : u ≠ 0) (huOne : u ^ 2 ≠ 1) :
    v ^ 2 ≠
      (u ^ 2 - 1) * (u ^ 2 + 1) *
        (u ^ 2 + 2 * u - 1) := by
  intro hcurve
  let m : ℤ := u.num
  let n : ℤ := u.den
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den u
  have hm : m ≠ 0 := by
    dsimp [m]
    exact Rat.num_ne_zero.mpr hu
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast u.den_ne_zero
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have huFrac : u = (m : ℚ) / n := u.num_div_den.symm
  have hA : m ^ 2 - n ^ 2 ≠ 0 := by
    intro hA0
    apply huOne
    rw [huFrac]
    field_simp [hnq]
    exact_mod_cast (sub_eq_zero.mp hA0)
  obtain ⟨z, hz⟩ :=
    integral_certificate_of_sextic_solution hcurve
  have hprod :
      (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) *
        (m ^ 2 + 2 * m * n - n ^ 2) = z ^ 2 := by
    simpa [m, n, pow_two] using hz
  rcases Int.emod_two_eq_zero_or_one m with hmEven | hmOdd
  · rcases Int.emod_two_eq_zero_or_one n with hnEven | hnOdd
    · have htwoM : (2 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero hmEven
      have htwoN : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hnEven
      have hunit : IsUnit (2 : ℤ) :=
        hmn.isUnit_of_dvd' htwoM htwoN
      exact (by norm_num [Int.isUnit_iff] at hunit)
    · exact no_opposite_parity_certificate hmn hm hn hA
        (Or.inl ⟨hmEven, hnOdd⟩) hprod
  · rcases Int.emod_two_eq_zero_or_one n with hnEven | hnOdd
    · exact no_opposite_parity_certificate hmn hm hn hA
        (Or.inr ⟨hmOdd, hnEven⟩) hprod
    · exact no_odd_odd_certificate hmn
        (Int.odd_iff.mpr hmOdd) (Int.odd_iff.mpr hnOdd) hA hprod

private lemma sextic_solution_of_square_relation
    {n ξ : ℚ} (hn : n ≠ 0) (hξ : ξ ≠ 0) (hnOne : n ^ 2 ≠ 1)
    (hsquare :
      (n * (ξ ^ 2 + 1) - 2 * n ^ 3 * ξ) ^ 2 =
        (ξ * (n ^ 4 - 1)) ^ 2) :
    ∃ N V : ℚ, N ≠ 0 ∧ N ^ 2 ≠ 1 ∧
      V ^ 2 =
        (N ^ 2 - 1) * (N ^ 2 + 1) *
          (N ^ 2 + 2 * N - 1) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hplus | hminus
  · have hnPlus : n + 1 ≠ 0 := by
      intro hnPlus
      apply hnOne
      have hnNeg : n = -1 := by linarith
      rw [hnNeg]
      norm_num
    have hlinear :
        n * (ξ ^ 2 + 1) =
          ξ * (2 * n ^ 3 + n ^ 4 - 1) := by
      linear_combination hplus
    refine ⟨n, n * (ξ ^ 2 - 1) / (ξ * (n + 1)),
      hn, hnOne, ?_⟩
    field_simp [hξ, hnPlus]
    linear_combination
      (n * (ξ ^ 2 + 1) +
        ξ * (2 * n ^ 3 + n ^ 4 - 1)) * hlinear
  · have hnMinus : 1 - n ≠ 0 := by
      intro hnMinus
      apply hnOne
      have hnPos : n = 1 := by linarith
      rw [hnPos]
      norm_num
    have hlinear :
        n * (ξ ^ 2 + 1) =
          ξ * (2 * n ^ 3 - n ^ 4 + 1) := by
      linear_combination hminus
    refine ⟨-n, (-n) * (ξ ^ 2 - 1) / (ξ * (1 - n)),
      neg_ne_zero.mpr hn, ?_, ?_⟩
    · simpa only [neg_sq] using hnOne
    · field_simp [hξ, hnMinus]
      linear_combination
        (n * (ξ ^ 2 + 1) +
          ξ * (2 * n ^ 3 - n ^ 4 + 1)) * hlinear

/-- The two scaled duplication equations imply the difference-of-squares
identity from which the `X₁(16)` sextic is read off. -/
lemma square_relation_of_scaled_duplication
    {n s ξ : ℚ}
    (hP : 4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4)
    (hR :
      4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
        (ξ ^ 2 - 1) ^ 2) :
    (n * (ξ ^ 2 + 1) - 2 * n ^ 3 * ξ) ^ 2 =
      (ξ * (n ^ 4 - 1)) ^ 2 := by
  linear_combination ξ ^ 2 * hP - n ^ 2 * hR

/-- Arithmetic endpoint for a normalized order-sixteen duplication chain.

These are precisely the two equations obtained after writing the successive
square `X`-coordinates as `X(4R)=g²`, `X(2R)=g²n²`, and scaling
`X(R)=g²ξ`. -/
theorem no_scaled_duplication_chain
    {n s ξ : ℚ} (hn : n ≠ 0) (hξ : ξ ≠ 0)
    (hnOne : n ^ 2 ≠ 1)
    (hP : 4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4)
    (hR :
      4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
        (ξ ^ 2 - 1) ^ 2) :
    False := by
  have hsquare :=
    square_relation_of_scaled_duplication hP hR
  obtain ⟨N, V, hN, hNOne, hV⟩ :=
    sextic_solution_of_square_relation hn hξ hnOne hsquare
  exact no_nondegenerate_sextic_solution hN hNOne hV

private lemma first_scaled_identity
    {n s t : ℚ}
    (hcurve : t ^ 2 = n ^ 6 + (s ^ 2 - 2) * n ^ 4 + n ^ 2)
    (hdup : 4 * t ^ 2 = (n ^ 4 - 1) ^ 2) :
    4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4 := by
  nlinarith [hcurve, hdup]

private lemma second_scaled_identity
    {n s ξ η : ℚ}
    (hcurve : η ^ 2 = ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ)
    (hdup : 4 * n ^ 2 * η ^ 2 = (ξ ^ 2 - 1) ^ 2) :
    4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
      (ξ ^ 2 - 1) ^ 2 := by
  linear_combination -4 * n ^ 2 * hcurve + hdup

private lemma quotient_square_of_duplication
    {b x y x₂ : ℚ} (hy : y ≠ 0)
    (hdup : x₂ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2) :
    ((x ^ 2 - b) / (2 * y)) ^ 2 = x₂ := by
  field_simp [hy]
  nlinarith [hdup]

private theorem no_normalized_coordinate_duplication_chain_aux
    {a b xR yR xP yP xQ yQ f g : ℚ}
    (hRcurve : yR ^ 2 = xR ^ 3 + a * xR ^ 2 + b * xR)
    (hPcurve : yP ^ 2 = xP ^ 3 + a * xP ^ 2 + b * xP)
    (hQcurve : yQ ^ 2 = xQ ^ 3 + a * xQ ^ 2 + b * xQ)
    (hRP : xP * (2 * yR) ^ 2 = (xR ^ 2 - b) ^ 2)
    (hPQ : xQ * (2 * yP) ^ 2 = (xP ^ 2 - b) ^ 2)
    (hb : b = xQ ^ 2)
    (hf : f ^ 2 = xP) (hg : g ^ 2 = xQ)
    (hxR : xR ≠ 0) (hxP : xP ≠ 0) (hxQ : xQ ≠ 0)
    (hxPQ : xP ≠ xQ) :
    False := by
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hxP
    rw [← hf, hf0]
    norm_num
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hxQ
    rw [← hg, hg0]
    norm_num
  have hbg : b = g ^ 4 := by
    rw [hb, ← hg]
    ring
  let n : ℚ := f / g
  let s : ℚ := yQ / g ^ 3
  let ξ : ℚ := xR / g ^ 2
  let t : ℚ := yP / g ^ 3
  let η : ℚ := yR / g ^ 3
  have hn : n ≠ 0 := div_ne_zero hf0 hg0
  have hξ : ξ ≠ 0 := div_ne_zero hxR (pow_ne_zero 2 hg0)
  have hnOne : n ^ 2 ≠ 1 := by
    intro hnOne
    apply hxPQ
    rw [← hf, ← hg]
    dsimp [n] at hnOne
    field_simp [hg0] at hnOne
    exact hnOne
  have haScaled : a = g ^ 2 * (s ^ 2 - 2) := by
    dsimp [s]
    field_simp [hg0]
    rw [← hg, hbg] at hQcurve
    nlinarith [hQcurve]
  have hsCoeff : s ^ 2 - 2 = a / g ^ 2 := by
    rw [haScaled]
    field_simp [hg0]
  have hPscaled :
      t ^ 2 = n ^ 6 + (s ^ 2 - 2) * n ^ 4 + n ^ 2 := by
    rw [hsCoeff]
    dsimp [t, n]
    field_simp [hg0]
    rw [← hf, hbg] at hPcurve
    nlinarith [hPcurve]
  have hPQscaled :
      4 * t ^ 2 = (n ^ 4 - 1) ^ 2 := by
    dsimp [t, n]
    field_simp [hg0]
    rw [← hg, ← hf, hbg] at hPQ
    nlinarith [hPQ]
  have hPidentity : 4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4 :=
    first_scaled_identity hPscaled hPQscaled
  have hRscaled :
      η ^ 2 = ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ := by
    rw [hsCoeff]
    dsimp [η, ξ]
    field_simp [hg0]
    rw [hbg] at hRcurve
    nlinarith [hRcurve]
  have hRPscaled :
      4 * n ^ 2 * η ^ 2 = (ξ ^ 2 - 1) ^ 2 := by
    dsimp [n, η, ξ]
    field_simp [hg0]
    rw [← hf, hbg] at hRP
    ring_nf at hRP ⊢
    exact hRP
  have hRidentity :
      4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
        (ξ ^ 2 - 1) ^ 2 :=
    second_scaled_identity hRscaled hRPscaled
  exact no_scaled_duplication_chain hn hξ hnOne hPidentity hRidentity

/-- A coordinate-level normalized duplication chain cannot exist.

The three displayed square identities are the `X`-coordinate duplication
formula

`X(2S) (2Y(S))² = (X(S)² - b)²`

for `S = R, 2R, 4R`; in the last identity `X(8R)=0`.  Keeping this theorem
purely algebraic makes the substantial descent independent of the details of
mathlib's affine-point addition API. -/
theorem no_normalized_coordinate_duplication_chain
    {a b xR yR xP yP xQ yQ : ℚ}
    (hRcurve : yR ^ 2 = xR ^ 3 + a * xR ^ 2 + b * xR)
    (hPcurve : yP ^ 2 = xP ^ 3 + a * xP ^ 2 + b * xP)
    (hQcurve : yQ ^ 2 = xQ ^ 3 + a * xQ ^ 2 + b * xQ)
    (hRP : xP * (2 * yR) ^ 2 = (xR ^ 2 - b) ^ 2)
    (hPQ : xQ * (2 * yP) ^ 2 = (xP ^ 2 - b) ^ 2)
    (hQT : (xQ ^ 2 - b) ^ 2 = 0)
    (hxR : xR ≠ 0) (hxP : xP ≠ 0) (hxQ : xQ ≠ 0)
    (hyR : yR ≠ 0) (hyP : yP ≠ 0)
    (hxPQ : xP ≠ xQ) :
    False := by
  have hb : b = xQ ^ 2 := by
    nlinarith [sq_nonneg (xQ ^ 2 - b)]
  have hf :
      ((xR ^ 2 - b) / (2 * yR)) ^ 2 = xP :=
    quotient_square_of_duplication hyR hRP
  have hg :
      ((xP ^ 2 - b) / (2 * yP)) ^ 2 = xQ :=
    quotient_square_of_duplication hyP hPQ
  exact no_normalized_coordinate_duplication_chain_aux
    hRcurve hPcurve hQcurve hRP hPQ hb hf hg
    hxR hxP hxQ hxPQ

private lemma normalized_point_eq_origin_of_x_eq_zero
    {a b x y : ℚ}
    (h : (normalizedCurve a b).toAffine.Nonsingular x y)
    (h00 : (normalizedCurve a b).toAffine.Nonsingular 0 0)
    (hx : x = 0) :
    WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some 0 0 h00 := by
  have hcurve := normalized_curve_equation h
  have hy : y = 0 := by
    rw [hx] at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg y]
  exact WeierstrassCurve.Affine.Point.some_eq_some
    (normalizedCurve a b) hx hy

private lemma normalized_origin_double_eq_zero
    {a b : ℚ} [_hEll : (normalizedCurve a b).IsElliptic]
    (h00 : (normalizedCurve a b).toAffine.Nonsingular 0 0) :
    (2 : ℕ) •
        WeierstrassCurve.Affine.Point.some 0 0 h00 = 0 := by
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_eq]
  simp [normalizedCurve, WeierstrassCurve.Affine.negY]

/-- There is no point of order sixteen on a normalized curve whose eighth
multiple is the distinguished two-torsion point `(0,0)`. -/
theorem normalizedCurve_no_order_sixteen
    (a b : ℚ) [hEll : (normalizedCurve a b).IsElliptic]
    (h00 : (normalizedCurve a b).toAffine.Nonsingular 0 0)
    (R : (normalizedCurve a b).toAffine.Point)
    (hRorder : addOrderOf R = 16)
    (hlast :
      (8 : ℕ) • R =
        WeierstrassCurve.Affine.Point.some 0 0 h00) :
    False := by
  let W := normalizedCurve a b
  let T : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  let P : W.toAffine.Point := (2 : ℕ) • R
  let Q : W.toAffine.Point := (2 : ℕ) • P
  have hPorder : addOrderOf P = 8 := by
    dsimp [P]
    rw [addOrderOf_nsmul' R (by norm_num), hRorder]
    norm_num
  have hQorder : addOrderOf Q = 4 := by
    dsimp [Q]
    rw [addOrderOf_nsmul' P (by norm_num), hPorder]
    norm_num
  have hR0 : R ≠ 0 := by
    intro hR0
    rw [hR0, addOrderOf_zero] at hRorder
    norm_num at hRorder
  have hP0 : P ≠ 0 := by
    intro hP0
    rw [hP0, addOrderOf_zero] at hPorder
    norm_num at hPorder
  have hQ0 : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, addOrderOf_zero] at hQorder
    norm_num at hQorder
  have hPQne : P ≠ Q := by
    intro hPQ
    rw [hPQ, hQorder] at hPorder
    norm_num at hPorder
  have hQTpoint : (2 : ℕ) • Q = T := by
    dsimp [Q, P, T]
    calc
      (2 : ℕ) • ((2 : ℕ) • ((2 : ℕ) • R)) =
          (8 : ℕ) • R := by abel
      _ = WeierstrassCurve.Affine.Point.some 0 0 h00 := hlast
  have hTdouble : (2 : ℕ) • T = 0 := by
    dsimp [T, W]
    exact normalized_origin_double_eq_zero h00
  obtain ⟨xR, yR, hRns, hRxy⟩ :
      ∃ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        R = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : R with
    | zero => exact (hR0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨xP, yP, hPns, hPxy⟩ :
      ∃ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        P = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : P with
    | zero => exact (hP0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨xQ, yQ, hQns, hQxy⟩ :
      ∃ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        Q = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : Q with
    | zero => exact (hQ0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hRPpoint :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some xR yR hRns =
        WeierstrassCurve.Affine.Point.some xP yP hPns := by
    have hdef : (2 : ℕ) • R = P := rfl
    simpa only [hRxy, hPxy] using hdef
  have hPQpoint :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some xP yP hPns =
        WeierstrassCurve.Affine.Point.some xQ yQ hQns := by
    have hdef : (2 : ℕ) • P = Q := rfl
    simpa only [hPxy, hQxy] using hdef
  have hQTcoord :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some xQ yQ hQns =
        WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    simpa only [hQxy, T] using hQTpoint
  have hxR : xR ≠ 0 := by
    intro hxR
    have hsome :=
      normalized_point_eq_origin_of_x_eq_zero hRns h00 hxR
    have hRT : R = T := by
      dsimp [T]
      rw [hRxy]
      exact hsome
    apply hP0
    dsimp [P]
    rw [hRT, hTdouble]
  have hxP : xP ≠ 0 := by
    intro hxP
    have hsome :=
      normalized_point_eq_origin_of_x_eq_zero hPns h00 hxP
    have hPT : P = T := by
      dsimp [T]
      rw [hPxy]
      exact hsome
    apply hQ0
    dsimp [Q]
    rw [hPT, hTdouble]
  have hxQ : xQ ≠ 0 := by
    intro hxQ
    have hsome :=
      normalized_point_eq_origin_of_x_eq_zero hQns h00 hxQ
    have hQT : Q = T := by
      dsimp [T]
      rw [hQxy]
      exact hsome
    have hbad := hQTpoint
    rw [hQT, hTdouble] at hbad
    exact WeierstrassCurve.Affine.Point.some_ne_zero h00 hbad.symm
  have hyR : yR ≠ 0 := by
    intro hyR
    have hvertical : yR = W.toAffine.negY xR yR := by
      simp [W, normalizedCurve, WeierstrassCurve.Affine.negY, hyR]
    have hzero :
        (2 : ℕ) •
            WeierstrassCurve.Affine.Point.some xR yR hRns = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hvertical]
    rw [hRPpoint] at hzero
    exact WeierstrassCurve.Affine.Point.some_ne_zero hPns hzero
  have hyP : yP ≠ 0 := by
    intro hyP
    have hvertical : yP = W.toAffine.negY xP yP := by
      simp [W, normalizedCurve, WeierstrassCurve.Affine.negY, hyP]
    have hzero :
        (2 : ℕ) •
            WeierstrassCurve.Affine.Point.some xP yP hPns = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hvertical]
    rw [hPQpoint] at hzero
    exact WeierstrassCurve.Affine.Point.some_ne_zero hQns hzero
  have hxPQ : xP ≠ xQ := by
    intro hxPQ
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq
        hPns.1 hQns.1 hxPQ with hy | hy
    · apply hPQne
      rw [hPxy, hQxy]
      exact WeierstrassCurve.Affine.Point.some_eq_some W hxPQ hy
    · have hPnegQ : P = -Q := by
        rw [hPxy, hQxy,
          WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some_eq_some W hxPQ hy
      rw [hPnegQ, addOrderOf_neg, hQorder] at hPorder
      norm_num at hPorder
  have hRcurve := normalized_curve_equation hRns
  have hPcurve := normalized_curve_equation hPns
  have hQcurve := normalized_curve_equation hQns
  have hRP :=
    normalized_duplication_identity_of_double hRns hPns hRPpoint
  have hPQ :=
    normalized_duplication_identity_of_double hPns hQns hPQpoint
  have hQT :
      (xQ ^ 2 - b) ^ 2 = 0 := by
    have h :=
      normalized_duplication_identity_of_double hQns h00 hQTcoord
    simpa only [zero_mul] using h.symm
  exact no_normalized_coordinate_duplication_chain
    hRcurve hPcurve hQcurve hRP hPQ hQT
    hxR hxP hxQ hyR hyP hxPQ

/-- A rational elliptic curve has no rational point of exact order sixteen.

Starting with `T = 8R`, the admissible change

`x_old = x_new + x(T)`,
`y_old = y_new - a₁ x_new / 2 + y(T)`

sends `T` to `(0,0)` and turns the equation into
`Y² = X³ + aX² + bX`.  The induced point-group equivalence then reduces
the assertion to `normalizedCurve_no_order_sixteen`. -/
theorem no_rational_point_of_order_sixteen
    (E : WeierstrassCurve ℚ) [hEll : E.IsElliptic]
    (R : E.toAffine.Point) (hRorder : addOrderOf R = 16) :
    False := by
  let T : E.toAffine.Point := (8 : ℕ) • R
  have hTorder : addOrderOf T = 2 := by
    dsimp [T]
    rw [addOrderOf_nsmul' R (by norm_num), hRorder]
    norm_num
  have hT0 : T ≠ 0 := by
    intro hT0
    rw [hT0, addOrderOf_zero] at hTorder
    norm_num at hTorder
  have hTdouble : (2 : ℕ) • T = 0 := by
    rw [← hTorder]
    exact addOrderOf_nsmul_eq_zero T
  obtain ⟨θ, yT, hTns, hTxy⟩ :
      ∃ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
        T = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : T with
    | zero => exact (hT0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hvertical : yT = E.toAffine.negY θ yT := by
    by_contra hne
    have hnonzero :
        WeierstrassCurve.Affine.Point.some θ yT hTns +
            WeierstrassCurve.Affine.Point.some θ yT hTns ≠ 0 := by
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    apply hnonzero
    rw [← two_nsmul, ← hTxy]
    exact hTdouble
  have hvertical' : E.a₃ + θ * E.a₁ + 2 * yT = 0 := by
    rw [WeierstrassCurve.Affine.negY] at hvertical
    linear_combination hvertical
  set C : WeierstrassCurve.VariableChange ℚ :=
    ⟨1, θ, -E.a₁ / 2, yT⟩ with hC
  let W : WeierstrassCurve ℚ := C • E
  have hWa₁ : W.a₁ = 0 := by
    dsimp [W]
    rw [WeierstrassCurve.variableChange_a₁, hC]
    simp
    ring
  have hWa₃ : W.a₃ = 0 := by
    dsimp [W]
    rw [WeierstrassCurve.variableChange_a₃, hC]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hvertical'
  have hWa₆ : W.a₆ = 0 := by
    have heq := hTns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    dsimp [W]
    rw [WeierstrassCurve.variableChange_a₆, hC]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00 : W.toAffine.Nonsingular 0 0 := by
    apply W.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_zero]
    exact hWa₆
  let e : W.toAffine.Point ≃+ E.toAffine.Point :=
    WeierstrassCurve.Affine.Point.equivVariableChange E C
  have hmapOrigin :
      e (WeierstrassCurve.Affine.Point.some 0 0 h00) = T := by
    dsimp [e]
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some, hTxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some E
      (by simp [hC]) (by simp [hC])
  let R₀ : W.toAffine.Point := e.symm R
  have hR₀order : addOrderOf R₀ = 16 := by
    dsimp [R₀]
    rw [AddEquiv.addOrderOf_eq]
    exact hRorder
  have hlast₀ :
      (8 : ℕ) • R₀ =
        WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    apply e.injective
    calc
      e ((8 : ℕ) • R₀) = (8 : ℕ) • R := by simp [R₀]
      _ = T := rfl
      _ = e (WeierstrassCurve.Affine.Point.some 0 0 h00) :=
        hmapOrigin.symm
  let a : ℚ := W.a₂
  let b : ℚ := W.a₄
  have hWnorm : W = normalizedCurve a b := by
    ext <;> simp [normalizedCurve, a, b, hWa₁, hWa₃, hWa₆]
  let eNorm :
      W.toAffine.Point ≃+
        (normalizedCurve a b).toAffine.Point :=
    WeierstrassCurve.Affine.Point.equivOfEq hWnorm
  let S : (normalizedCurve a b).toAffine.Point := eNorm R₀
  let h00Norm :
      (normalizedCurve a b).toAffine.Nonsingular 0 0 :=
    hWnorm ▸ h00
  letI : (normalizedCurve a b).IsElliptic :=
    hWnorm ▸ (inferInstance : W.IsElliptic)
  have hSorder : addOrderOf S = 16 := by
    dsimp [S]
    rw [AddEquiv.addOrderOf_eq]
    exact hR₀order
  have hlastS :
      (8 : ℕ) • S =
        WeierstrassCurve.Affine.Point.some 0 0 h00Norm := by
    calc
      (8 : ℕ) • S = eNorm ((8 : ℕ) • R₀) := by
        rw [map_nsmul]
      _ = eNorm (WeierstrassCurve.Affine.Point.some 0 0 h00) := by
        rw [hlast₀]
      _ = WeierstrassCurve.Affine.Point.some 0 0 h00Norm := by
        dsimp [eNorm, h00Norm]
        rw [WeierstrassCurve.Affine.Point.equivOfEq_some]
  exact normalizedCurve_no_order_sixteen
    a b h00Norm S hSorder hlastS

/-- Obstruction-form restatement of `no_rational_point_of_order_sixteen`. -/
theorem point_addOrderOf_ne_sixteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : E.toAffine.Point) :
    addOrderOf R ≠ 16 :=
  no_rational_point_of_order_sixteen E R

/-- The order-sixteen obstruction on the canonical rational base change
used by `RationalTorsion`. -/
theorem rationalPoint_addOrderOf_ne_sixteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : (E⁄ℚ).Point) :
    addOrderOf R ≠ 16 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  exact point_addOrderOf_ne_sixteen (E⁄ℚ) R

end MazurTorsion.Kubert
