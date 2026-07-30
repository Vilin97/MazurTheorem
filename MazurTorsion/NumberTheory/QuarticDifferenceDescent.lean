/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib.NumberTheory.FLT.Four

/-!
# Fermat's quartic-difference descent

This file proves that a nonzero square cannot be the difference of two nonzero
fourth powers:

`x ^ 4 - y ^ 4 ≠ z ^ 2` when `x`, `y`, and `z` are all nonzero integers.

The hypothesis on `z` is essential: when `z = 0`, the choices `x = y ≠ 0`
give a degenerate family of solutions.

The proof is the classical infinite descent.  A least solution is primitive.
The equation makes `(y², z, x²)` a primitive Pythagorean triple.  When `y` is
odd, its parametrization immediately produces a smaller quartic-difference
solution.  When `y` is even, parametrizing twice and extracting squares from
coprime products produces the smaller solution.
-/


namespace MazurTorsion.QuarticDifference

/-- A nondegenerate integral solution of `x⁴ - y⁴ = z²`. -/
private def IsSolution (x y z : ℤ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ 4 - y ^ 4 = z ^ 2

private theorem IsSolution.mul {x y z k : ℤ} (hk : k ≠ 0) :
    IsSolution x y z ↔ IsSolution (k * x) (k * y) (k ^ 2 * z) := by
  unfold IsSolution
  constructor
  · rintro ⟨hx, hy, hz, h⟩
    refine ⟨mul_ne_zero hk hx, mul_ne_zero hk hy, mul_ne_zero (pow_ne_zero 2 hk) hz, ?_⟩
    linear_combination k ^ 4 * h
  · rintro ⟨hx, hy, hz, h⟩
    refine ⟨right_ne_zero_of_mul hx, right_ne_zero_of_mul hy,
      right_ne_zero_of_mul hz, ?_⟩
    apply (mul_left_inj' (pow_ne_zero 4 hk)).mp
    linear_combination h

/-- A solution is minimal when the square of the absolute value of its first
coordinate is least among all nondegenerate solutions. -/
private def IsMinimal (x y z : ℤ) : Prop :=
  IsSolution x y z ∧
    ∀ x' y' z' : ℤ, IsSolution x' y' z' →
      Int.natAbs (x ^ 2) ≤ Int.natAbs (x' ^ 2)

private theorem exists_minimal {x y z : ℤ} (h : IsSolution x y z) :
    ∃ x₀ y₀ z₀ : ℤ, IsMinimal x₀ y₀ z₀ := by
  classical
  let S : Set ℕ :=
    {n | ∃ s : ℤ × ℤ × ℤ, IsSolution s.1 s.2.1 s.2.2 ∧
      n = Int.natAbs (s.1 ^ 2)}
  have hS : S.Nonempty := by
    refine ⟨Int.natAbs (x ^ 2), ?_⟩
    exact ⟨(x, y, z), h, rfl⟩
  let m := Nat.find hS
  obtain ⟨s, hs, hm⟩ := Nat.find_spec hS
  refine ⟨s.1, s.2.1, s.2.2, hs, ?_⟩
  intro x' y' z' h'
  rw [← hm]
  apply Nat.find_min'
  exact ⟨(x', y', z'), h', rfl⟩

private theorem coprime_of_minimal {x y z : ℤ} (h : IsMinimal x y z) :
    IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hxy
  obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hxy
  obtain ⟨x₁, hx₁⟩ := Int.natCast_dvd.mpr hpx
  obtain ⟨y₁, hy₁⟩ := Int.natCast_dvd.mpr hpy
  have hpz : (p : ℤ) ^ 2 ∣ z := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2.2]
    refine ⟨x₁ ^ 4 - y₁ ^ 4, ?_⟩
    rw [hx₁, hy₁]
    ring
  obtain ⟨z₁, hz₁⟩ := hpz
  have h₁ : IsSolution x₁ y₁ z₁ := by
    apply (IsSolution.mul (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    simpa only [hx₁, hy₁, hz₁]
      using h.1
  have hle := h.2 x₁ y₁ z₁ h₁
  have hlt : Int.natAbs (x₁ ^ 2) < Int.natAbs (x ^ 2) := by
    rw [hx₁, show ((p : ℤ) * x₁) ^ 2 = (p : ℤ) ^ 2 * x₁ ^ 2 by ring,
      Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_pow,
      Int.natAbs_natCast]
    · exact Nat.one_lt_pow two_ne_zero hp.one_lt
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (pow_ne_zero 2 h₁.1))
  omega

private theorem square_and_third_coprime
    {x y z : ℤ} (hcop : IsCoprime x y)
    (hcurve : x ^ 4 - y ^ 4 = z ^ 2) :
    IsCoprime (y ^ 2) z := by
  rw [Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
  by_contra hnot
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  rw [← Int.natCast_dvd] at hpy hpz
  have hpxpow : (p : ℤ) ∣ x ^ 4 := by
    have hrewrite : x ^ 4 = y ^ 4 + z ^ 2 := by
      linear_combination hcurve
    rw [hrewrite]
    exact dvd_add (by
      rw [show y ^ 4 = y ^ 2 * y ^ 2 by ring]
      exact hpy.mul_right _) (by
      rw [show z ^ 2 = z * z by ring]
      exact hpz.mul_right _)
  have hpx : p ∣ Int.natAbs x :=
    Int.Prime.dvd_pow hp hpxpow
  have hpy' : p ∣ Int.natAbs y :=
    Int.Prime.dvd_pow hp hpy
  apply hp.not_dvd_one
  rw [← hcop]
  exact Nat.dvd_gcd hpx hpy'

private theorem square_measure_lt_of_sq_add_sq
    {a b x : ℤ} (hb : b ≠ 0) (h : x ^ 2 = a ^ 2 + b ^ 2) :
    Int.natAbs (a ^ 2) < Int.natAbs (x ^ 2) := by
  apply Int.ofNat_lt.mp
  rw [Int.natAbs_of_nonneg (sq_nonneg a),
    Int.natAbs_of_nonneg (sq_nonneg x), h]
  exact lt_add_of_pos_right _ (sq_pos_of_ne_zero hb)

private theorem positive_coprime_factors_of_square
    {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hcop : IsCoprime a b)
    (hmul : a * b = c ^ 2) :
    ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2 ∧ r ≠ 0 ∧ s ≠ 0 := by
  obtain ⟨r, hr⟩ := Int.sq_of_isCoprime hcop hmul
  have hr' : a = r ^ 2 := Or.resolve_right hr (by
    intro hneg
    have := sq_nonneg r
    nlinarith)
  have hmul' : b * a = c ^ 2 := by simpa only [mul_comm] using hmul
  obtain ⟨s, hs⟩ := Int.sq_of_isCoprime hcop.symm hmul'
  have hs' : b = s ^ 2 := Or.resolve_right hs (by
    intro hneg
    have := sq_nonneg s
    nlinarith)
  exact ⟨r, s, hr', hs',
    fun hr0 ↦ by rw [hr0, zero_pow two_ne_zero] at hr'; omega,
    fun hs0 ↦ by rw [hs0, zero_pow two_ne_zero] at hs'; omega⟩

private theorem even_factor_of_twice_product_square
    {a b q : ℤ} (ha : 0 < a) (hb : 0 < b) (hcop : IsCoprime a b)
    (haeven : a % 2 = 0) (hsq : q ^ 2 = 2 * a * b) :
    ∃ r s : ℤ, a = 2 * r ^ 2 ∧ b = s ^ 2 ∧ r ≠ 0 ∧ s ≠ 0 := by
  have htwoa : (2 : ℤ) ∣ a := Int.dvd_of_emod_eq_zero haeven
  obtain ⟨a', ha'⟩ := htwoa
  have htwoq : (2 : ℤ) ∣ q := by
    apply Int.Prime.dvd_pow' Nat.prime_two
    rw [hsq]
    exact ⟨a * b, by ring⟩
  obtain ⟨q', hq'⟩ := htwoq
  have hcop' : IsCoprime a' b := by
    rw [ha'] at hcop
    exact hcop.of_mul_left_right
  have ha'pos : 0 < a' := by nlinarith
  have hsq' : a' * b = q' ^ 2 := by
    rw [hq', ha'] at hsq
    nlinarith
  obtain ⟨r, s, hr, hs, hr0, hs0⟩ :=
    positive_coprime_factors_of_square ha'pos hb hcop' hsq'
  exact ⟨r, s, by rw [ha', hr], hs, hr0, hs0⟩

private theorem descend_from_even_parameter
    {x evenParam oddParam r s : ℤ}
    (hx : x ≠ 0) (hcop : IsCoprime oddParam evenParam)
    (hoddParity : oddParam % 2 = 1)
    (heven : evenParam = 2 * r ^ 2) (hodd : oddParam = s ^ 2)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hxsum : x ^ 2 = evenParam ^ 2 + oddParam ^ 2) :
    ∃ x' y' z' : ℤ, IsSolution x' y' z' ∧
      Int.natAbs (x' ^ 2) < Int.natAbs (x ^ 2) := by
  have ht : PythagoreanTriple oddParam evenParam |x| := by
    unfold PythagoreanTriple
    rw [show oddParam * oddParam = oddParam ^ 2 by ring,
      show evenParam * evenParam = evenParam ^ 2 by ring,
      show |x| * |x| = x ^ 2 by rw [← sq, sq_abs]]
    rw [add_comm, ← hxsum]
  have hcopGcd : Int.gcd oddParam evenParam = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcop
  obtain ⟨u, v, hodduv, hevenuv, hxuv, huvcop, _, hunonneg⟩ :=
    ht.coprime_classification' hcopGcd hoddParity (abs_pos.mpr hx)
  have huv : u * v = r ^ 2 := by
    rw [heven] at hevenuv
    nlinarith
  have huvpos : 0 < u * v := by
    rw [huv]
    exact sq_pos_of_ne_zero hr0
  have hvpos : 0 < v :=
    pos_of_mul_pos_right huvpos hunonneg
  have hupos : 0 < u :=
    pos_of_mul_pos_left huvpos (le_of_lt hvpos)
  obtain ⟨a, b, hua, hvb, ha0, hb0⟩ :=
    positive_coprime_factors_of_square hupos hvpos
      (Int.isCoprime_iff_gcd_eq_one.mpr huvcop) huv
  have hnew : IsSolution a b s := by
    refine ⟨ha0, hb0, hs0, ?_⟩
    calc
      a ^ 4 - b ^ 4 = u ^ 2 - v ^ 2 := by rw [hua, hvb]; ring
      _ = oddParam := hodduv.symm
      _ = s ^ 2 := hodd
  have hux : u < x ^ 2 := by
    have huabs : u < |x| := by
      rw [hxuv]
      exact lt_of_le_of_lt (Int.le_self_sq u)
        (lt_add_of_pos_right _ (sq_pos_of_ne_zero (ne_of_gt hvpos)))
    have habsx : |x| ≤ x ^ 2 := by
      simpa only [Int.natCast_natAbs] using Int.natAbs_le_self_sq x
    exact huabs.trans_le habsx
  have hmeasure : Int.natAbs (a ^ 2) < Int.natAbs (x ^ 2) := by
    apply Int.ofNat_lt.mp
    rw [Int.natAbs_of_nonneg (sq_nonneg a),
      Int.natAbs_of_nonneg (sq_nonneg x), ← hua]
    exact hux
  exact ⟨a, b, s, hnew, hmeasure⟩

private theorem descend_of_odd
    {x y z : ℤ} (h : IsSolution x y z) (hcop : IsCoprime x y)
    (hyodd : y % 2 = 1) :
    ∃ x' y' z' : ℤ, IsSolution x' y' z' ∧
      Int.natAbs (x' ^ 2) < Int.natAbs (x ^ 2) := by
  have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
    unfold PythagoreanTriple
    rw [show y ^ 2 * y ^ 2 = y ^ 4 by ring,
      show z * z = z ^ 2 by ring, show x ^ 2 * x ^ 2 = x ^ 4 by ring]
    linear_combination -h.2.2.2
  have hlegs : Int.gcd (y ^ 2) z = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp
      (square_and_third_coprime hcop h.2.2.2)
  have hypar : y ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, hyodd]
    decide
  obtain ⟨m, n, hymn, hzmn, hxmn, hmncop, _, hmnonneg⟩ :=
    ht.coprime_classification' hlegs hypar (sq_pos_of_ne_zero h.1)
  have hm0 : m ≠ 0 := by
    intro hm
    apply h.2.2.1
    rw [hzmn, hm]
    ring
  have hn0 : n ≠ 0 := by
    intro hn
    apply h.2.2.1
    rw [hzmn, hn]
    ring
  have hnew : IsSolution m n (x * y) := by
    refine ⟨hm0, hn0, mul_ne_zero h.1 h.2.1, ?_⟩
    calc
      m ^ 4 - n ^ 4 = (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) := by ring
      _ = y ^ 2 * x ^ 2 := by rw [← hymn, ← hxmn]
      _ = (x * y) ^ 2 := by ring
  exact ⟨m, n, x * y, hnew,
    square_measure_lt_of_sq_add_sq hn0 hxmn⟩

private theorem descend_of_even
    {x y z : ℤ} (h : IsSolution x y z) (hcop : IsCoprime x y)
    (hyeven : y % 2 = 0) :
    ∃ x' y' z' : ℤ, IsSolution x' y' z' ∧
      Int.natAbs (x' ^ 2) < Int.natAbs (x ^ 2) := by
  have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
    unfold PythagoreanTriple
    rw [show y ^ 2 * y ^ 2 = y ^ 4 by ring,
      show z * z = z ^ 2 by ring, show x ^ 2 * x ^ 2 = x ^ 4 by ring]
    linear_combination -h.2.2.2
  have hlegs : Int.gcd (y ^ 2) z = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp
      (square_and_third_coprime hcop h.2.2.2)
  have hypar : y ^ 2 % 2 = 0 := by
    rw [sq, Int.mul_emod, hyeven]
    decide
  have hzodd : z % 2 = 1 := by
    rcases ht.even_odd_of_coprime hlegs with hpar | hpar
    · exact hpar.2
    · rw [hypar] at hpar
      exact (zero_ne_one hpar.1).elim
  have hlegs' : Int.gcd z (y ^ 2) = 1 := by
    rw [Int.gcd_comm]
    exact hlegs
  obtain ⟨m, n, hzmn, hymn, hxmn, hmncop, hmnpar, hmnonneg⟩ :=
    ht.symm.coprime_classification' hlegs' hzodd (sq_pos_of_ne_zero h.1)
  have hm0 : m ≠ 0 := by
    intro hm
    apply h.2.1
    apply sq_eq_zero_iff.mp
    rw [hymn, hm]
    ring
  have hmpos : 0 < m :=
    lt_of_le_of_ne hmnonneg (Ne.symm hm0)
  have hmnpos : 0 < m * n := by
    have hypos : 0 < y ^ 2 := sq_pos_of_ne_zero h.2.1
    nlinarith [hymn]
  have hnpos : 0 < n :=
    pos_of_mul_pos_right hmnpos hmnonneg
  have hmncop' : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmncop
  rcases hmnpar with hpar | hpar
  · obtain ⟨r, s, hm, hn, hr0, hs0⟩ :=
      even_factor_of_twice_product_square hmpos hnpos hmncop'
        hpar.1 hymn
    exact descend_from_even_parameter h.1 hmncop'.symm hpar.2
      hm hn hr0 hs0 hxmn
  · have hymn' : y ^ 2 = 2 * n * m := by
      simpa only [mul_comm, mul_left_comm] using hymn
    obtain ⟨r, s, hn, hm, hr0, hs0⟩ :=
      even_factor_of_twice_product_square hnpos hmpos hmncop'.symm
        hpar.2 hymn'
    have hxmn' : x ^ 2 = n ^ 2 + m ^ 2 := by
      simpa only [add_comm] using hxmn
    exact descend_from_even_parameter h.1 hmncop' hpar.1
      hn hm hr0 hs0 hxmn'

/--
Fermat's quartic-difference theorem: a nonzero square is not the difference
of two nonzero fourth powers.

The assumption `hz` is necessary.  Without it, `x = y ≠ 0` gives the
degenerate identity `x⁴ - y⁴ = 0²`.
-/
theorem sq_ne_quartic_sub_quartic
    {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro hcurve
  obtain ⟨x₀, y₀, z₀, hmin⟩ :=
    exists_minimal (show IsSolution x y z from ⟨hx, hy, hz, hcurve⟩)
  have hcop : IsCoprime x₀ y₀ :=
    coprime_of_minimal hmin
  obtain hyeven | hyodd := Int.emod_two_eq_zero_or_one y₀
  · obtain ⟨x', y', z', hnew, hlt⟩ :=
      descend_of_even hmin.1 hcop hyeven
    exact (not_lt_of_ge (hmin.2 x' y' z' hnew)) hlt
  · obtain ⟨x', y', z', hnew, hlt⟩ :=
      descend_of_odd hmin.1 hcop hyodd
    exact (not_lt_of_ge (hmin.2 x' y' z' hnew)) hlt

end MazurTorsion.QuarticDifference
