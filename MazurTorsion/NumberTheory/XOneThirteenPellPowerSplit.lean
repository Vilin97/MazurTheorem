/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPositivePell

/-!
# Global power splitting of the positive `X₁(13)` Pell factors

The integral Pell identity leaves two positive factors with product
`4 b³⁸`.  This file removes the scalar `2` from both factors and proves
that the resulting integers are coprime.  Unique factorization in `ℤ` then
forces both halves to be genuine thirty-eighth powers:

`H + cK = 2 r³⁸`, `cK - H = 2 s³⁸`, and `b = rs`.

The proof treats the prime two rather than hiding it in the earlier odd-prime
allocation.  The resulting fixed power-split Diophantine cover is a strictly
narrower global boundary for the remaining Mazur--Tate descent.  It is not a
rational-point classification or a Jacobian rank computation.
-/

namespace MazurTorsion.XOneThirteenDescent

open scoped WeierstrassCurve.Affine

private lemma odd_of_isCoprime_of_even_right
    {a b : ℤ} (hab : IsCoprime a b) (hb : Even b) : Odd a := by
  have htwoB : (2 : ℤ) ∣ b := even_iff_two_dvd.mp hb
  exact Int.isCoprime_two_right.mp
    (IsCoprime.of_isCoprime_of_dvd_right hab htwoB)

private lemma integerSexticHomogeneous_odd
    (a b : ℤ) (hab : IsCoprime a b) :
    Odd (integerSexticHomogeneous a b) := by
  rcases Int.even_or_odd b with hb | hb
  · have ha : Odd a := odd_of_isCoprime_of_even_right hab hb
    simp +decide [integerSexticHomogeneous, ha, hb, parity_simps]
  · rcases Int.even_or_odd a with ha | ha
    · have haNotOdd : ¬Odd a := Int.not_odd_iff_even.mpr ha
      have hbNotEven : ¬Even b := Int.not_even_iff_odd.mpr hb
      simp +decide [integerSexticHomogeneous, ha, haNotOdd, hbNotEven,
        parity_simps]
    · simp +decide [integerSexticHomogeneous, ha, parity_simps]

private lemma ordinate_odd
    (a b c : ℤ) (hab : IsCoprime a b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) : Odd c := by
  have hcSq : Odd (c ^ 2) := by
    rw [hcurve]
    exact integerSexticHomogeneous_odd a b hab
  exact (Int.odd_pow' (by norm_num : (2 : ℕ) ≠ 0)).mp hcSq

private lemma pell_forms_same_parity
    (a b : ℤ) (hab : IsCoprime a b) :
    (Odd (pellHHomogeneous a b) ∧ Odd (pellKHomogeneous a b)) ∨
      (Even (pellHHomogeneous a b) ∧ Even (pellKHomogeneous a b)) := by
  rcases Int.even_or_odd b with hb | hb
  · have ha : Odd a := odd_of_isCoprime_of_even_right hab hb
    left
    constructor <;>
      simp +decide [pellHHomogeneous, pellKHomogeneous, ha, hb,
        parity_simps]
  · right
    constructor <;>
      simp +decide [pellHHomogeneous, pellKHomogeneous, hb, parity_simps]

/-- Both positive Pell-factor magnitudes contain the forced scalar two. -/
theorem positive_pell_factors_even
    (a b c : ℤ) (hab : IsCoprime a b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    Even (positivePellFactor a b c) ∧
      Even (negativePellFactorMagnitude a b c) := by
  have hc : Odd c := ordinate_odd a b c hab hcurve
  rcases pell_forms_same_parity a b hab with hodd | heven
  · have hcK : Odd (c * pellKHomogeneous a b) := hc.mul hodd.2
    exact ⟨hodd.1.add_odd hcK, hcK.sub_odd hodd.1⟩
  · have hcK : Even (c * pellKHomogeneous a b) := heven.2.mul_left c
    exact ⟨heven.1.add hcK, hcK.sub heven.1⟩

/-- The two halves of the positive Pell factors are coprime.  The odd primes
are separated by `odd_prime_not_common_pell_factor`; at two, primitivity and
the explicit parities of `H` and `K` rule out simultaneous divisibility. -/
theorem positive_pell_half_factors_isCoprime
    (a b c : ℤ) (hab : IsCoprime a b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    IsCoprime (positivePellFactor a b c / 2)
      (negativePellFactorMagnitude a b c / 2) := by
  let u : ℤ := positivePellFactor a b c / 2
  let v : ℤ := negativePellFactorMagnitude a b c / 2
  have heven := positive_pell_factors_even a b c hab hcurve
  have huScale : 2 * u = positivePellFactor a b c := by
    exact Int.two_mul_ediv_two_of_even heven.1
  have hvScale : 2 * v = negativePellFactorMagnitude a b c := by
    exact Int.two_mul_ediv_two_of_even heven.2
  have huv : u * v = b ^ 38 := by
    apply Int.eq_of_mul_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
    calc
      4 * (u * v) = (2 * u) * (2 * v) := by ring
      _ = positivePellFactor a b c *
          negativePellFactorMagnitude a b c := by rw [huScale, hvScale]
      _ = 4 * b ^ 38 := positive_pell_factorization a b c hcurve
  have htwoNotCommon : ¬((2 : ℤ) ∣ u ∧ (2 : ℤ) ∣ v) := by
    rintro ⟨htwoU, htwoV⟩
    have htwoBpow : (2 : ℤ) ∣ b ^ 38 := by
      rw [← huv]
      exact dvd_mul_of_dvd_left htwoU v
    have htwoB : (2 : ℤ) ∣ b :=
      Int.prime_two.dvd_of_dvd_pow htwoBpow
    have hbEven : Even b := even_iff_two_dvd.mpr htwoB
    have haOdd : Odd a := odd_of_isCoprime_of_even_right hab hbEven
    have hcOdd : Odd c := ordinate_odd a b c hab hcurve
    have hHOdd : Odd (pellHHomogeneous a b) := by
      simp +decide [pellHHomogeneous, haOdd, hbEven, parity_simps]
    have hKOdd : Odd (pellKHomogeneous a b) := by
      simp +decide [pellKHomogeneous, haOdd, hbEven, parity_simps]
    have hcKOdd : Odd (c * pellKHomogeneous a b) := hcOdd.mul hKOdd
    have huvAdd : u + v = c * pellKHomogeneous a b := by
      apply Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
      calc
        2 * (u + v) = 2 * u + 2 * v := by ring
        _ = positivePellFactor a b c +
            negativePellFactorMagnitude a b c := by rw [huScale, hvScale]
        _ = 2 * (c * pellKHomogeneous a b) := by
          simp only [positivePellFactor, negativePellFactorMagnitude]
          ring
    have huvEven : Even (u + v) :=
      (even_iff_two_dvd.mpr htwoU).add (even_iff_two_dvd.mpr htwoV)
    rw [huvAdd] at huvEven
    exact Int.not_even_iff_odd.mpr hcKOdd huvEven
  have hcopNat : u.natAbs.Coprime v.natAbs := by
    apply Nat.coprime_of_dvd
    intro p hp hpU hpV
    have hpU' : (p : ℤ) ∣ u := Int.natCast_dvd.mpr hpU
    have hpV' : (p : ℤ) ∣ v := Int.natCast_dvd.mpr hpV
    rcases hp.eq_two_or_odd' with rfl | hpOdd
    · exact htwoNotCommon ⟨hpU', hpV'⟩
    · have hpPlus : (p : ℤ) ∣ positivePellFactor a b c := by
        rw [← huScale]
        exact hpU'.mul_left 2
      have hpMinus : (p : ℤ) ∣ negativePellFactorMagnitude a b c := by
        rw [← hvScale]
        exact hpV'.mul_left 2
      exact odd_prime_not_common_pell_factor
        a b c p hab (Nat.prime_iff_prime_int.mp hp)
        (by
          intro hpTwo
          have : p ∣ (2 : ℕ) := by exact_mod_cast hpTwo
          rcases (Nat.dvd_prime Nat.prime_two).mp this with hpOne | hpTwo
          · exact hp.ne_one hpOne
          · subst p
            exact Nat.not_even_iff_odd.mpr hpOdd (by decide))
        hcurve ⟨hpPlus, hpMinus⟩
  exact Int.isCoprime_iff_nat_coprime.mpr hcopNat

/-- Global unique-factorization split of the two positive Pell factors.
Unlike prime-by-prime allocation, this produces actual integral power
coordinates on a fixed Diophantine cover. -/
theorem positive_pell_factor_power_split
    (a b c : ℤ) (hab : IsCoprime a b) (hb : 0 < b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b)
    (hplus : 0 < positivePellFactor a b c)
    (hminus : 0 < negativePellFactorMagnitude a b c) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧ IsCoprime r s ∧
      positivePellFactor a b c = 2 * r ^ 38 ∧
      negativePellFactorMagnitude a b c = 2 * s ^ 38 ∧
      b = r * s := by
  let u : ℤ := positivePellFactor a b c / 2
  let v : ℤ := negativePellFactorMagnitude a b c / 2
  have heven := positive_pell_factors_even a b c hab hcurve
  have huScale : 2 * u = positivePellFactor a b c := by
    exact Int.two_mul_ediv_two_of_even heven.1
  have hvScale : 2 * v = negativePellFactorMagnitude a b c := by
    exact Int.two_mul_ediv_two_of_even heven.2
  have huPos : 0 < u :=
    Int.ediv_pos_of_pos_of_dvd hplus (by norm_num)
      (even_iff_two_dvd.mp heven.1)
  have hvPos : 0 < v :=
    Int.ediv_pos_of_pos_of_dvd hminus (by norm_num)
      (even_iff_two_dvd.mp heven.2)
  have huv : u * v = b ^ 38 := by
    apply Int.eq_of_mul_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
    calc
      4 * (u * v) = (2 * u) * (2 * v) := by ring
      _ = positivePellFactor a b c *
          negativePellFactorMagnitude a b c := by rw [huScale, hvScale]
      _ = 4 * b ^ 38 := positive_pell_factorization a b c hcurve
  have hcopInt : IsCoprime u v := by
    exact positive_pell_half_factors_isCoprime a b c hab hcurve
  have hcopNat : u.natAbs.Coprime v.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hcopInt
  have huvNat : u.natAbs * v.natAbs = b.natAbs ^ 38 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs huv
  have hunitGcd : IsUnit (GCDMonoid.gcd u.natAbs v.natAbs) := by
    rw [show GCDMonoid.gcd u.natAbs v.natAbs = 1 from hcopNat.gcd_eq_one]
    exact isUnit_one
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow hunitGcd huvNat
  have hunitGcd' : IsUnit (GCDMonoid.gcd v.natAbs u.natAbs) := by
    rw [gcd_comm, show GCDMonoid.gcd u.natAbs v.natAbs = 1 from hcopNat.gcd_eq_one]
    exact isUnit_one
  obtain ⟨s, hs⟩ :=
    exists_eq_pow_of_mul_eq_pow hunitGcd' (mul_comm v.natAbs u.natAbs ▸ huvNat)
  have hrPos : 0 < r := by
    by_contra hrZero
    have : r = 0 := Nat.eq_zero_of_not_pos hrZero
    rw [this, zero_pow (by norm_num : (38 : ℕ) ≠ 0)] at hr
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt huPos)) hr
  have hsPos : 0 < s := by
    by_contra hsZero
    have : s = 0 := Nat.eq_zero_of_not_pos hsZero
    rw [this, zero_pow (by norm_num : (38 : ℕ) ≠ 0)] at hs
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hvPos)) hs
  have hrsNat : r.Coprime s := by
    have hpowers : (r ^ 38).Coprime (s ^ 38) := by
      simpa only [← hr, ← hs] using hcopNat
    have hleft : r.Coprime (s ^ 38) :=
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 38) r (s ^ 38)).mp
        hpowers
    exact (Nat.coprime_pow_right_iff (by norm_num : 0 < 38) r s).mp hleft
  have hrs : IsCoprime (r : ℤ) (s : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hrsNat
  have hrsEq : r * s = b.natAbs := by
    apply Nat.pow_left_injective (by norm_num : (38 : ℕ) ≠ 0)
    change (r * s) ^ 38 = b.natAbs ^ 38
    rw [mul_pow, ← hr, ← hs, huvNat]
  refine ⟨r, s, by exact_mod_cast hrPos, by exact_mod_cast hsPos, hrs, ?_, ?_, ?_⟩
  · rw [← huScale]
    have huCast : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg huPos.le
    rw [← huCast, hr]
    norm_num
  · rw [← hvScale]
    have hvCast : (v.natAbs : ℤ) = v := Int.natAbs_of_nonneg hvPos.le
    rw [← hvCast, hs]
    norm_num
  · have hbCast : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb.le
    rw [← hbCast, ← hrsEq]
    norm_num

/-- The remaining arithmetic after global Pell factor splitting.  It is the
fixed two-equation thirty-eighth-power cover, not the earlier collection of
prime-by-prime allocation conditions. -/
def PositivePellPowerSplitObstruction : Prop :=
  ∀ m n a b c r s : ℤ,
    0 < n →
    0 < a →
    0 < b →
    0 < c →
    0 < r →
    0 < s →
    IsCoprime m n →
    IsCoprime a b →
    IsCoprime c b →
    IsCoprime r s →
    Odd m →
    Odd n →
    -n < m ∧ m < n →
    n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)) →
    m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3) →
    2 * m ^ 2 - 4 * m * n - 2 * n ^ 2 =
      4 * (-a ^ 3 - 3 * a ^ 2 * b + b ^ 3) →
    ¬SixthRootPiConjDivides (a, b) →
    2 * c = m ^ 2 + n ^ 2 →
    c ^ 2 = integerSexticHomogeneous a b →
    positivePellFactor a b c = 2 * r ^ 38 →
    negativePellFactorMagnitude a b c = 2 * s ^ 38 →
    b = r * s →
    False

/-- The global power-split cover implies the normalized positive split-cubic
obstruction. -/
theorem positiveSplitCyclicCubicObstruction_of_positivePellPowerSplit
    (hpower : PositivePellPowerSplitObstruction) :
    PositiveSplitCyclicCubicObstruction := by
  intro m n a b hn ha hb hmn hab hmOdd hnOdd hbetween hlead htrace
    hpair hpi _hnorm
  obtain ⟨c, hc, htwice, hcurve⟩ :=
    positive_split_homogeneous_curve
      m n a b hn hmOdd hnOdd hlead htrace
  have hcb : IsCoprime c b :=
    positive_split_ordinate_coprime a b c hab hcurve
  obtain ⟨hplus, hminus⟩ :=
    homogeneous_pell_factor_signs a b c ha hb hc hcurve
  have hminusMagnitude :
      0 < negativePellFactorMagnitude a b c := by
    simp only [negativePellFactorMagnitude]
    linarith
  obtain ⟨r, s, hr, hs, hrs, hfactorPlus, hfactorMinus, hrsB⟩ :=
    positive_pell_factor_power_split
      a b c hab hb hcurve hplus hminusMagnitude
  exact hpower m n a b c r s hn ha hb hc hr hs hmn hab hcb hrs
    hmOdd hnOdd hbetween hlead htrace hpair hpi htwice hcurve
    hfactorPlus hfactorMinus hrsB

/-- The global power-split boundary is a checked input to the actual
exact-order-thirteen exclusion. -/
theorem rationalPoint_addOrderOf_ne_thirteen_of_positivePellPowerSplit
    (hpower : PositivePellPowerSplitObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 13 :=
  rationalPoint_addOrderOf_ne_thirteen_of_positiveSplitCyclicCubicObstruction
    (positiveSplitCyclicCubicObstruction_of_positivePellPowerSplit hpower)
    E Q

end MazurTorsion.XOneThirteenDescent
