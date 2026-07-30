/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import MazurTorsion.Arithmetic.ExceptionalTwoTen
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Infinite descent for the exceptional two-by-ten quartic

This file proves that the primitive nonzero integral equation

`q² = x⁴ - 11x²y² - y⁴`

has no solutions.  Reduction modulo eight first makes `x` and `q` odd and makes `y`
divisible by four.  Writing `y = 2z`, two positive coprime factors have product
`125 z⁴`.  Their fourth-power decomposition produces a primitive Pythagorean triple.
The standard parametrization of that triple gives another solution whose
`Int.natAbs` of the second coordinate is strictly smaller.  A least-counterexample
argument completes the descent.
-/


private lemma quartic_mod_eight :
    ∀ x y q : ZMod 8,
      q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4 →
        (((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) x ≠ 0) ∧
          ((ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)) y = 0) ∧
          ((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) q ≠ 0)) ∨
        (((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) x = 0) ∧
          ((ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) y = 0)) := by
  decide

private lemma two_nonsquare_mod_five :
    ∀ x z : ZMod 5, x ^ 2 = 2 * z ^ 2 → z = 0 := by
  decide

private lemma square_zero_mod_two :
    ∀ x : ZMod 2, x ^ 2 = 0 → x = 0 := by
  decide


namespace MazurTorsion.ExceptionalTwoTen

private lemma quartic_parity
    {X Y q : ℤ} (hcop : IsCoprime X Y)
    (h : q ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4) :
    (X : ZMod 2) ≠ 0 ∧ (Y : ZMod 4) = 0 ∧ (q : ZMod 2) ≠ 0 := by
  have h8 :
      (q : ZMod 8) ^ 2 =
        (X : ZMod 8) ^ 4 - 11 * (X : ZMod 8) ^ 2 * (Y : ZMod 8) ^ 2 -
          (Y : ZMod 8) ^ 4 := by
    simpa using congrArg (fun z : ℤ => (z : ZMod 8)) h
  rcases quartic_mod_eight (X : ZMod 8) (Y : ZMod 8) (q : ZMod 8) h8 with hgood | hbad
  · simpa [ZMod.castHom_apply] using hgood
  · exfalso
    have hX : (2 : ℤ) ∣ X := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd X 2).mp
      simpa [ZMod.castHom_apply] using hbad.1
    have hY : (2 : ℤ) ∣ Y := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd Y 2).mp
      simpa [ZMod.castHom_apply] using hbad.2
    have hu : IsUnit (2 : ℤ) := hcop.isRelPrime hX hY
    exact (Nat.prime_iff_prime_int.mp Nat.prime_two).not_unit hu

private lemma exceptional_factors_coprime
    {x z D₁ D₂ : ℤ} (hcop : IsCoprime x z)
    (hprod : D₁ * D₂ = 125 * z ^ 4)
    (hsum : D₁ + D₂ = x ^ 2 - 22 * z ^ 2) :
    IsCoprime D₁ D₂ := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpgZ : (p : ℤ) ∣ (Int.gcd D₁ D₂ : ℤ) := by
    exact_mod_cast hpg
  have hpD₁ : (p : ℤ) ∣ D₁ := hpgZ.trans (Int.gcd_dvd_left D₁ D₂)
  have hpD₂ : (p : ℤ) ∣ D₂ := hpgZ.trans (Int.gcd_dvd_right D₁ D₂)
  have hpSum : (p : ℤ) ∣ x ^ 2 - 22 * z ^ 2 := by
    rw [← hsum]
    exact dvd_add hpD₁ hpD₂
  have hpz_not : ¬(p : ℤ) ∣ z := by
    intro hpz
    have hpzSq : (p : ℤ) ∣ z ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hpz z
    have hpTerm : (p : ℤ) ∣ 22 * z ^ 2 :=
      dvd_mul_of_dvd_right hpzSq 22
    have hpxSq : (p : ℤ) ∣ x ^ 2 := by
      simpa only [sub_add_cancel] using dvd_add hpSum hpTerm
    have hpx : (p : ℤ) ∣ x := hpZ.dvd_of_dvd_pow hpxSq
    exact hpZ.not_unit (hcop.isRelPrime hpx hpz)
  have hpRight : (p : ℤ) ∣ 125 * z ^ 4 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpD₁ D₂
  have hp125 : (p : ℤ) ∣ 125 := by
    rcases hpZ.dvd_mul.mp hpRight with hp125 | hpz
    · exact hp125
    · exact (hpz_not (hpZ.dvd_of_dvd_pow hpz)).elim
  have hpFivePow : (p : ℤ) ∣ (5 : ℤ) ^ 3 := by
    norm_num at hp125 ⊢
    exact hp125
  have hpFive : (p : ℤ) ∣ 5 := hpZ.dvd_of_dvd_pow hpFivePow
  have hpFiveNat : p ∣ 5 := by
    exact_mod_cast hpFive
  have hp_eq_five : p = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hpFiveNat with hp1 | hp5
    · exact (hp.ne_one hp1).elim
    · exact hp5
  subst p
  have hD₁5 : (D₁ : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd D₁ 5).mpr hpD₁
  have hD₂5 : (D₂ : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd D₂ 5).mpr hpD₂
  have hsum5 := congrArg (fun t : ℤ => (t : ZMod 5)) hsum
  have hmod : (x : ZMod 5) ^ 2 = 2 * (z : ZMod 5) ^ 2 := by
    push_cast at hsum5
    rw [hD₁5, hD₂5] at hsum5
    have hz := hsum5.symm
    norm_num at hz
    exact sub_eq_zero.mp hz
  have hz5 : (z : ZMod 5) = 0 :=
    two_nonsquare_mod_five (x : ZMod 5) (z : ZMod 5) hmod
  apply hpz_not
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mp hz5

private lemma exceptional_factorization_of_five_dvd_left
    {D₁ D₂ z : ℤ} (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hz : 0 < z)
    (hcop : IsCoprime D₁ D₂) (hprod : D₁ * D₂ = 125 * z ^ 4)
    (hfive : (5 : ℤ) ∣ D₁) :
    ∃ a b : ℤ, IsCoprime a b ∧ a ≠ 0 ∧ b ≠ 0 ∧
      D₁ = 125 * a ^ 4 ∧ D₂ = b ^ 4 ∧ z ^ 2 = (a * b) ^ 2 := by
  have hpFive : Prime (5 : ℤ) :=
    Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 5)
  have hfive_not_D₂ : ¬(5 : ℤ) ∣ D₂ := by
    intro hfive₂
    exact hpFive.not_unit (hcop.isRelPrime hfive hfive₂)
  have hcopFive : IsCoprime (5 : ℤ) D₂ :=
    hpFive.coprime_iff_not_dvd.mpr hfive_not_D₂
  have hcopScaled : IsCoprime ((5 : ℤ) * D₁) D₂ :=
    IsCoprime.mul_left hcopFive hcop
  have hscaled : ((5 : ℤ) * D₁) * D₂ = (5 * z) ^ 4 := by
    rw [mul_assoc, hprod]
    ring
  have hgcdScaled : IsUnit (gcd ((5 : ℤ) * D₁) D₂) :=
    gcd_isUnit_iff_isRelPrime.mpr hcopScaled.isRelPrime
  obtain ⟨A, hAassoc⟩ :=
    exists_associated_pow_of_mul_eq_pow hgcdScaled hscaled
  have hscaled' : D₂ * ((5 : ℤ) * D₁) = (5 * z) ^ 4 := by
    simpa [mul_comm] using hscaled
  have hgcdScaled' : IsUnit (gcd D₂ ((5 : ℤ) * D₁)) :=
    gcd_isUnit_iff_isRelPrime.mpr hcopScaled.symm.isRelPrime
  obtain ⟨B, hBassoc⟩ :=
    exists_associated_pow_of_mul_eq_pow hgcdScaled' hscaled'
  have hA : A ^ 4 = 5 * D₁ := by
    rcases Int.associated_iff.mp hAassoc with hA | hA
    · exact hA
    · have hpow : 0 ≤ A ^ 4 := by positivity
      nlinarith
  have hB : B ^ 4 = D₂ := by
    rcases Int.associated_iff.mp hBassoc with hB | hB
    · exact hB
    · have hpow : 0 ≤ B ^ 4 := by positivity
      nlinarith
  have hfiveA4 : (5 : ℤ) ∣ A ^ 4 := by
    rw [hA]
    exact dvd_mul_right 5 D₁
  have hfiveA : (5 : ℤ) ∣ A := hpFive.dvd_of_dvd_pow hfiveA4
  obtain ⟨a, ha⟩ := hfiveA
  have hD₁eq : D₁ = 125 * a ^ 4 := by
    rw [ha] at hA
    nlinarith
  let b := B
  have hD₂eq : D₂ = b ^ 4 := hB.symm
  have habcop : IsCoprime a b := by
    have hpows : IsCoprime (a ^ 4) (b ^ 4) := by
      rw [hD₁eq, hD₂eq] at hcop
      exact hcop.of_mul_left_right
    exact (IsCoprime.pow_iff (by decide) (by decide)).mp hpows
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0] at hD₁eq
    norm_num at hD₁eq
    linarith
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0] at hD₂eq
    norm_num at hD₂eq
    linarith
  have hfour : (a * b) ^ 4 = z ^ 4 := by
    rw [hD₁eq, hD₂eq] at hprod
    nlinarith
  have hsquares : ((a * b) ^ 2) ^ 2 = (z ^ 2) ^ 2 := by
    calc
      ((a * b) ^ 2) ^ 2 = (a * b) ^ 4 := by ring
      _ = z ^ 4 := hfour
      _ = (z ^ 2) ^ 2 := by ring
  have habsq : (a * b) ^ 2 = z ^ 2 := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with hs | hs
    · exact hs
    · have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
      have habnonneg : 0 ≤ (a * b) ^ 2 := sq_nonneg _
      nlinarith
  exact ⟨a, b, habcop, ha0, hb0, hD₁eq, hD₂eq, habsq.symm⟩

private lemma exceptional_factorization
    {D₁ D₂ z : ℤ} (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hz : 0 < z)
    (hcop : IsCoprime D₁ D₂) (hprod : D₁ * D₂ = 125 * z ^ 4) :
    ∃ a b : ℤ, IsCoprime a b ∧ a ≠ 0 ∧ b ≠ 0 ∧
      D₁ + D₂ = a ^ 4 + 125 * b ^ 4 ∧ z ^ 2 = (a * b) ^ 2 := by
  have hpFive : Prime (5 : ℤ) :=
    Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 5)
  have hfiveProd : (5 : ℤ) ∣ D₁ * D₂ := by
    rw [hprod]
    exact dvd_mul_of_dvd_left (by norm_num : (5 : ℤ) ∣ 125) (z ^ 4)
  rcases hpFive.dvd_mul.mp hfiveProd with hfive₁ | hfive₂
  · obtain ⟨b, a, hba, hb0, ha0, hD₁eq, hD₂eq, hzsq⟩ :=
      exceptional_factorization_of_five_dvd_left hD₁ hD₂ hz hcop hprod hfive₁
    refine ⟨a, b, hba.symm, ha0, hb0, ?_, ?_⟩
    · rw [hD₁eq, hD₂eq]
      ring
    · simpa [mul_comm] using hzsq
  · have hprod' : D₂ * D₁ = 125 * z ^ 4 := by
      simpa [mul_comm] using hprod
    obtain ⟨b, a, hba, hb0, ha0, hD₂eq, hD₁eq, hzsq⟩ :=
      exceptional_factorization_of_five_dvd_left hD₂ hD₁ hz hcop.symm hprod' hfive₂
    refine ⟨a, b, hba.symm, ha0, hb0, ?_, ?_⟩
    · rw [hD₁eq, hD₂eq]
    · simpa [mul_comm] using hzsq

theorem exceptional_quartic_descent_step
    {x y q : ℤ} (hcop : IsCoprime x y) (hx : 0 < x) (hy : 0 < y) (hq : 0 ≤ q)
    (h : q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4) :
    ∃ x' y' q' : ℤ, IsCoprime x' y' ∧ x' ≠ 0 ∧ y' ≠ 0 ∧
      q' ^ 2 = x' ^ 4 - 11 * x' ^ 2 * y' ^ 2 - y' ^ 4 ∧
      y'.natAbs < y.natAbs := by
  have hpar := quartic_parity hcop h
  have hxNotEven : ¬Even x := by
    intro heven
    exact hpar.1 heven.intCast_zmod_two
  have hqNotEven : ¬Even q := by
    intro heven
    exact hpar.2.2 heven.intCast_zmod_two
  have hxOdd : Odd x := Int.not_even_iff_odd.mp hxNotEven
  have hqOdd : Odd q := Int.not_even_iff_odd.mp hqNotEven
  have hfourY : (4 : ℤ) ∣ y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y 4).mp hpar.2.1
  obtain ⟨r, hr⟩ := hxOdd
  obtain ⟨s, hs⟩ := hqOdd
  obtain ⟨t, ht⟩ := hfourY
  let z : ℤ := 2 * t
  let D₁ : ℤ := 2 * r ^ 2 + 2 * r + 1 + s - 44 * t ^ 2
  let D₂ : ℤ := 2 * r ^ 2 + 2 * r - s - 44 * t ^ 2
  have hyz : y = 2 * z := by
    dsimp [z]
    rw [ht]
    ring
  have hscale₁ : 4 * D₁ = 2 * x ^ 2 - 11 * y ^ 2 + 2 * q := by
    dsimp [D₁]
    rw [hr, hs, ht]
    ring
  have hscale₂ : 4 * D₂ = 2 * x ^ 2 - 11 * y ^ 2 - 2 * q := by
    dsimp [D₂]
    rw [hr, hs, ht]
    ring
  have hxSq : 0 < x ^ 2 := sq_pos_of_pos hx
  have hyFourth : 0 < y ^ 4 := pow_pos hy 4
  have hcurveProduct :
      q ^ 2 + y ^ 4 = x ^ 2 * (x ^ 2 - 11 * y ^ 2) := by
    linear_combination h
  have hfactor : 0 < x ^ 2 - 11 * y ^ 2 := by
    by_contra hnonpos
    have hmul : x ^ 2 * (x ^ 2 - 11 * y ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (le_of_not_gt hnonpos)
    nlinarith [sq_nonneg q]
  have hcenter : 0 < 2 * x ^ 2 - 11 * y ^ 2 := by
    nlinarith
  have hcenterSq :
      (2 * x ^ 2 - 11 * y ^ 2) ^ 2 = (2 * q) ^ 2 + 125 * y ^ 4 := by
    linear_combination -4 * h
  have hcenter_gt : 2 * q < 2 * x ^ 2 - 11 * y ^ 2 := by
    nlinarith [sq_nonneg (2 * x ^ 2 - 11 * y ^ 2 - 2 * q)]
  have hD₁pos : 0 < D₁ := by
    nlinarith [hscale₁]
  have hD₂pos : 0 < D₂ := by
    nlinarith [hscale₂]
  have hzpos : 0 < z := by
    nlinarith [hy]
  have hprod : D₁ * D₂ = 125 * z ^ 4 := by
    have hscaled :
        16 * (D₁ * D₂) = 16 * (125 * z ^ 4) := by
      calc
        16 * (D₁ * D₂) = (4 * D₁) * (4 * D₂) := by ring
        _ = (2 * x ^ 2 - 11 * y ^ 2 + 2 * q) *
              (2 * x ^ 2 - 11 * y ^ 2 - 2 * q) := by rw [hscale₁, hscale₂]
        _ = (2 * x ^ 2 - 11 * y ^ 2) ^ 2 - (2 * q) ^ 2 := by ring
        _ = 125 * y ^ 4 := by nlinarith [hcenterSq]
        _ = 16 * (125 * z ^ 4) := by rw [hyz]; ring
    nlinarith
  have hsum : D₁ + D₂ = x ^ 2 - 22 * z ^ 2 := by
    have hscaled : 4 * (D₁ + D₂) = 4 * (x ^ 2 - 22 * z ^ 2) := by
      rw [mul_add, hscale₁, hscale₂, hyz]
      ring
    nlinarith
  have hcopxz : IsCoprime x z := by
    have hcop' : IsCoprime x (2 * z) := by
      simpa [hyz] using hcop
    exact hcop'.of_mul_right_right
  have hcopD : IsCoprime D₁ D₂ :=
    exceptional_factors_coprime hcopxz hprod hsum
  obtain ⟨a, b, hab, ha0, hb0, hfactorSum, hzsq⟩ :=
    exceptional_factorization hD₁pos hD₂pos hzpos hcopD hprod
  have hpyth :
      x ^ 2 = (a ^ 2 + 11 * b ^ 2) ^ 2 + (2 * b ^ 2) ^ 2 := by
    rw [hfactorSum] at hsum
    nlinarith [hzsq]
  let L : ℤ := a ^ 2 + 11 * b ^ 2
  let K : ℤ := 2 * b ^ 2
  have hLpos : 0 < L := by
    dsimp [L]
    nlinarith [sq_pos_of_ne_zero ha0, sq_nonneg b]
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (by norm_num) (sq_pos_of_ne_zero hb0)
  have htrip : PythagoreanTriple L K x := by
    delta PythagoreanTriple
    dsimp only [L, K]
    simpa only [pow_two] using hpyth.symm
  have hLoddCast : (L : ZMod 2) ≠ 0 := by
    intro hLzero
    have hKzero : (K : ZMod 2) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd K 2).2 ⟨b ^ 2, rfl⟩
    have hpythLK : x ^ 2 = L ^ 2 + K ^ 2 := by
      simpa [L, K] using hpyth
    have htrip2 := congrArg (fun w : ℤ => (w : ZMod 2)) hpythLK
    push_cast at htrip2
    rw [hLzero, hKzero] at htrip2
    norm_num at htrip2
    apply hpar.1
    exact square_zero_mod_two (x : ZMod 2) htrip2
  have hLNotEven : ¬Even L := by
    intro heven
    exact hLoddCast heven.intCast_zmod_two
  have hLmod : L % 2 = 1 := Int.not_even_iff.mp hLNotEven
  have hcopLb : IsCoprime L b := by
    have haSqCop : IsCoprime (a ^ 2) b := hab.pow_left
    dsimp [L]
    obtain ⟨c, d, hbez⟩ := haSqCop
    refine ⟨c, d - 11 * c * b, ?_⟩
    linear_combination hbez
  have hcopLtwo : IsCoprime L (2 : ℤ) := by
    have htwoNot : ¬(2 : ℤ) ∣ L := by
      intro htwo
      exact hLoddCast (even_iff_two_dvd.mpr htwo).intCast_zmod_two
    exact ((Nat.prime_iff_prime_int.mp Nat.prime_two).coprime_iff_not_dvd.mpr htwoNot).symm
  have hcopLK : IsCoprime L K := by
    dsimp [K]
    exact IsCoprime.mul_right hcopLtwo hcopLb.pow_right
  have hLKgcd : Int.gcd L K = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcopLK
  obtain ⟨m, n, hL, hK, hxmn, hmngcd, _hmnParity, hmnonneg⟩ :=
    htrip.coprime_classification' hLKgcd hLmod hx
  have hmn : b ^ 2 = m * n := by
    dsimp [K] at hK
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    simpa [mul_assoc] using hK
  have hbSqPos : 0 < b ^ 2 := sq_pos_of_ne_zero hb0
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0] at hmn
    norm_num at hmn
    exact hb0 hmn
  have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hm0)
  have hmnpos : 0 < m * n := by
    rw [← hmn]
    exact hbSqPos
  have hnpos : 0 < n := pos_of_mul_pos_right hmnpos (le_of_lt hmpos)
  have hmnCop : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmngcd
  obtain ⟨u, huSign⟩ := Int.sq_of_gcd_eq_one hmngcd hmn.symm
  have hnm : n * m = b ^ 2 := by
    simpa [mul_comm] using hmn.symm
  have hnmgcd : Int.gcd n m = 1 := by
    simpa [Int.gcd_comm] using hmngcd
  obtain ⟨v, hvSign⟩ := Int.sq_of_gcd_eq_one hnmgcd hnm
  have hu : m = u ^ 2 := by
    rcases huSign with hu | hu
    · exact hu
    · have hmle : m ≤ 0 := by
        rw [hu]
        exact neg_nonpos.mpr (sq_nonneg u)
      exact (not_lt_of_ge hmle hmpos).elim
  have hv : n = v ^ 2 := by
    rcases hvSign with hv | hv
    · exact hv
    · have hnle : n ≤ 0 := by
        rw [hv]
        exact neg_nonpos.mpr (sq_nonneg v)
      exact (not_lt_of_ge hnle hnpos).elim
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu
    norm_num at hu
    exact hm0 hu
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0] at hv
    norm_num at hv
    exact hn0 hv
  have huvCop : IsCoprime u v := by
    rw [hu, hv] at hmnCop
    exact (IsCoprime.pow_iff (by decide) (by decide)).mp hmnCop
  have hbuv : b ^ 2 = (u * v) ^ 2 := by
    rw [hmn, hu, hv]
    ring
  have hnew : a ^ 2 = u ^ 4 - 11 * u ^ 2 * v ^ 2 - v ^ 4 := by
    dsimp [L] at hL
    rw [hu, hv] at hL
    calc
      a ^ 2 = (u ^ 2) ^ 2 - (v ^ 2) ^ 2 - 11 * b ^ 2 := by
        linarith only [hL]
      _ = u ^ 4 - 11 * u ^ 2 * v ^ 2 - v ^ 4 := by
        rw [hbuv]
        ring
  have hzAbs : z.natAbs = (a * b).natAbs := by
    rcases eq_or_eq_neg_of_sq_eq_sq z (a * b) hzsq with hzab | hzab
    · rw [hzab]
    · rw [hzab, Int.natAbs_neg]
  have hbAbs : b.natAbs = (u * v).natAbs := by
    rcases eq_or_eq_neg_of_sq_eq_sq b (u * v) hbuv with hbuv' | hbuv'
    · rw [hbuv']
    · rw [hbuv', Int.natAbs_neg]
  have haAbsPos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  have huAbsPos : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  have hzAbsEq : z.natAbs = a.natAbs * b.natAbs := by
    rw [hzAbs, Int.natAbs_mul]
  have hbAbsEq : b.natAbs = u.natAbs * v.natAbs := by
    rw [hbAbs, Int.natAbs_mul]
  have hv_le_b : v.natAbs ≤ b.natAbs := by
    rw [hbAbsEq]
    exact le_mul_of_one_le_left (Nat.zero_le _) huAbsPos
  have hb_le_z : b.natAbs ≤ z.natAbs := by
    rw [hzAbsEq]
    exact le_mul_of_one_le_left (Nat.zero_le _) haAbsPos
  have hyAbs : y.natAbs = 2 * z.natAbs := by
    rw [hyz, Int.natAbs_mul]
    norm_num
  have hzAbsPos : 0 < z.natAbs := Int.natAbs_pos.mpr (ne_of_gt hzpos)
  have hmeasure : v.natAbs < y.natAbs := by
    rw [hyAbs]
    omega
  exact ⟨u, v, a, huvCop, hu0, hv0, hnew, hmeasure⟩

private lemma normalize_exceptional_solution
    {X Y e : ℤ} (hcop : IsCoprime X Y) (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4) :
    ∃ x y q : ℤ, IsCoprime x y ∧ 0 < x ∧ 0 < y ∧ 0 ≤ q ∧
      q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4 ∧
      y.natAbs = Y.natAbs := by
  let x : ℤ := X.natAbs
  let y : ℤ := Y.natAbs
  let q : ℤ := e.natAbs
  have hxpos : 0 < x := by
    dsimp only [x]
    exact_mod_cast Int.natAbs_pos.mpr hX
  have hypos : 0 < y := by
    dsimp only [y]
    exact_mod_cast Int.natAbs_pos.mpr hY
  have hqnonneg : 0 ≤ q := by
    dsimp only [q]
    exact Int.natCast_nonneg _
  have hcop' : IsCoprime x y := by
    simpa only [x, y, Int.natCast_natAbs] using hcop.abs_abs
  have hcurve :
      q ^ 2 = x ^ 4 - 11 * x ^ 2 * y ^ 2 - y ^ 4 := by
    have hpow4 (z : ℤ) : |z| ^ 4 = z ^ 4 :=
      (show Even 4 from by decide).pow_abs z
    simpa only [x, y, q, Int.natCast_natAbs, sq_abs, hpow4] using h
  have hyabs : y.natAbs = Y.natAbs := by
    dsimp only [y]
    rw [Int.natCast_natAbs]
    exact Int.natAbs_abs Y
  exact ⟨x, y, q, hcop', hxpos, hypos, hqnonneg, hcurve, hyabs⟩

/--
The exceptional quartic has no primitive nonzero integral solution.  The proof
uses infinite descent with the strict measure `Int.natAbs Y`.
-/
theorem noExceptionalQuartic : NoExceptionalQuartic := by
  classical
  intro X Y e hcop hX hY h
  let P : ℕ → Prop := fun n =>
    ∃ X Y e : ℤ, IsCoprime X Y ∧ X ≠ 0 ∧ Y ≠ 0 ∧
      e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4 ∧ Y.natAbs = n
  have hP : ∃ n : ℕ, P n :=
    ⟨Y.natAbs, X, Y, e, hcop, hX, hY, h, rfl⟩
  obtain ⟨X₀, Y₀, e₀, hcop₀, hX₀, hY₀, hcurve₀, hYmeasure⟩ :=
    Nat.find_spec hP
  obtain ⟨x, y, q, hcopxy, hx, hy, hq, hcurve, hynorm⟩ :=
    normalize_exceptional_solution hcop₀ hX₀ hY₀ hcurve₀
  obtain ⟨x', y', q', hcop', hx', hy', hcurve', hdesc⟩ :=
    exceptional_quartic_descent_step hcopxy hx hy hq hcurve
  have hP' : P y'.natAbs :=
    ⟨x', y', q', hcop', hx', hy', hcurve', rfl⟩
  have hminimal : Nat.find hP ≤ y'.natAbs :=
    Nat.find_min' hP hP'
  omega

end MazurTorsion.ExceptionalTwoTen
