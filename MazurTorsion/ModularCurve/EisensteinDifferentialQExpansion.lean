/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.HeckeDifferentialQExpansion

/-!
# Eisenstein eigenseries for the weight-two q-expansion operator

This file constructs the positive-degree formal series whose coefficient in degree `m` is the
sum of the divisors of `m` that are coprime to the level.  The coefficient in degree zero is zero.
It verifies directly, via the Busche--Ramanujan divisor identity, that this formal series is a
nonzero simultaneous eigenvector for the explicit weight-two Hecke q-expansion operators.

This is a formal q-expansion calculation.  It does not assert that the series is the expansion of
a global holomorphic differential; that geometric realization is a separate modular-form input.

## Provenance

The divisor identity is the weight-one specialization of the classical Busche--Ramanujan
identity.  See S. Ramanujan, "Some formulae in the analytic theory of numbers", *Messenger of
Mathematics* 45 (1916), 81--84.  The proof retained here is an elementary finite-divisor proof;
no source text, code, or data is copied.  This Lean implementation is released under Apache-2.0.
-/

namespace MazurTorsion.ModularCurve

open Finset

namespace EisensteinDifferentialQExpansion

private def buscheTarget (m n : ℕ) : Finset (Σ _d : ℕ, ℕ × ℕ) :=
  (Nat.gcd m n).divisors.sigma fun d ↦
    Nat.divisorsAntidiagonal (m * n / d ^ 2)

private def buscheForward (z : (ℕ × ℕ) × (ℕ × ℕ)) : Σ _d : ℕ, ℕ × ℕ :=
  ⟨Nat.gcd z.1.2 z.2.1,
    (z.1.1 * (z.2.1 / Nat.gcd z.1.2 z.2.1),
      (z.1.2 / Nat.gcd z.1.2 z.2.1) * z.2.2)⟩

private theorem buscheForward_mem {m n : ℕ}
    (z : (ℕ × ℕ) × (ℕ × ℕ))
    (hz : z ∈ m.divisorsAntidiagonal ×ˢ n.divisorsAntidiagonal) :
    buscheForward z ∈ buscheTarget m n := by
  rcases z with ⟨⟨a, b⟩, ⟨c, e⟩⟩
  simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal] at hz
  rcases hz with ⟨⟨hab, hm⟩, ⟨hce, hn⟩⟩
  have ha : a ≠ 0 := left_ne_zero_of_mul (hab.trans_ne hm)
  have hb : b ≠ 0 := right_ne_zero_of_mul (hab.trans_ne hm)
  have hc : c ≠ 0 := left_ne_zero_of_mul (hce.trans_ne hn)
  have he : e ≠ 0 := right_ne_zero_of_mul (hce.trans_ne hn)
  let d := Nat.gcd b c
  have hd : d ≠ 0 := (Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero hb)).ne'
  have hdb : d ∣ b := Nat.gcd_dvd_left b c
  have hdc : d ∣ c := Nat.gcd_dvd_right b c
  have hdgcd : d ∣ Nat.gcd m n := by
    apply Nat.dvd_gcd
    · rw [← hab]
      exact dvd_mul_of_dvd_right hdb a
    · rw [← hce]
      exact dvd_mul_of_dvd_left hdc e
  have hgcd : Nat.gcd m n ≠ 0 := Nat.gcd_ne_zero_left hm
  have hdsq : d ^ 2 ∣ m * n := by
    refine ⟨a * (b / d) * (c / d) * e, ?_⟩
    calc
      m * n = (a * b) * (c * e) := by rw [hab, hce]
      _ = (a * ((b / d) * d)) * (((c / d) * d) * e) := by
        rw [Nat.div_mul_cancel hdb, Nat.div_mul_cancel hdc]
      _ = d ^ 2 * (a * (b / d) * (c / d) * e) := by ring
  have hproduct :
      (a * (c / d)) * ((b / d) * e) = m * n / d ^ 2 := by
    apply (Nat.eq_div_iff_mul_eq_left (pow_ne_zero 2 hd) hdsq).2
    calc
      m * n = (a * b) * (c * e) := by rw [hab, hce]
      _ = (a * ((b / d) * d)) * (((c / d) * d) * e) := by
        rw [Nat.div_mul_cancel hdb, Nat.div_mul_cancel hdc]
      _ = (a * (c / d) * ((b / d) * e)) * d ^ 2 := by ring
  rw [buscheTarget, Finset.mem_sigma]
  constructor
  · exact Nat.mem_divisors.mpr ⟨hdgcd, hgcd⟩
  · rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨hproduct, (Nat.div_pos ?_ (pow_pos (Nat.pos_of_ne_zero hd) 2)).ne'⟩
    exact Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)) hdsq

private def buscheBackward (m : ℕ) (z : Σ _d : ℕ, ℕ × ℕ) :
    (ℕ × ℕ) × (ℕ × ℕ) :=
  let d := z.1
  let x := z.2.1
  let y := z.2.2
  let M := m / d
  let a := Nat.gcd x M
  let b₀ := M / a
  let c₀ := x / a
  let e := y / b₀
  ((a, d * b₀), (d * c₀, e))

private theorem buscheBackward_mem {m n : ℕ} (z : Σ _d : ℕ, ℕ × ℕ)
    (hz : z ∈ buscheTarget m n) :
    buscheBackward m z ∈ m.divisorsAntidiagonal ×ˢ n.divisorsAntidiagonal := by
  rcases z with ⟨d, ⟨x, y⟩⟩
  rw [buscheTarget, Finset.mem_sigma] at hz
  rcases hz with ⟨hdmem, hxymem⟩
  rw [Nat.mem_divisors] at hdmem
  rw [Nat.mem_divisorsAntidiagonal] at hxymem
  rcases hdmem with ⟨hdgcd, hgcd⟩
  rcases hxymem with ⟨hxy, hquot⟩
  change d ∣ Nat.gcd m n at hdgcd
  change x * y = m * n / d ^ 2 at hxy
  change m * n / d ^ 2 ≠ 0 at hquot
  have hmn : m * n ≠ 0 := by
    intro hzero
    apply hquot
    simp [hzero]
  have hm : m ≠ 0 := left_ne_zero_of_mul hmn
  have hn : n ≠ 0 := right_ne_zero_of_mul hmn
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero hgcd hdgcd
  have hdm : d ∣ m := hdgcd.trans (Nat.gcd_dvd_left m n)
  have hdn : d ∣ n := hdgcd.trans (Nat.gcd_dvd_right m n)
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let M := m / d
  let N := n / d
  have hMpos : 0 < M := Nat.div_pos (Nat.le_of_dvd hmpos hdm) hdpos
  have hNpos : 0 < N := Nat.div_pos (Nat.le_of_dvd hnpos hdn) hdpos
  have hdsq : d ^ 2 ∣ m * n := by
    refine ⟨M * N, ?_⟩
    calc
      m * n = (d * M) * (d * N) := by
        rw [Nat.mul_div_cancel' hdm, Nat.mul_div_cancel' hdn]
      _ = d ^ 2 * (M * N) := by ring
  have hquotient : m * n / d ^ 2 = M * N := by
    apply (Nat.div_eq_iff_eq_mul_left (pow_pos hdpos 2) hdsq).2
    calc
      m * n = (d * M) * (d * N) := by
        rw [Nat.mul_div_cancel' hdm, Nat.mul_div_cancel' hdn]
      _ = (M * N) * d ^ 2 := by ring
  have hxyMN : x * y = M * N := hxy.trans hquotient
  have hx : x ≠ 0 := left_ne_zero_of_mul (hxyMN.trans_ne (mul_ne_zero hMpos.ne' hNpos.ne'))
  have hy : y ≠ 0 := right_ne_zero_of_mul (hxyMN.trans_ne (mul_ne_zero hMpos.ne' hNpos.ne'))
  let a := Nat.gcd x M
  let b₀ := M / a
  let c₀ := x / a
  have hapos : 0 < a := Nat.gcd_pos_of_pos_left M (Nat.pos_of_ne_zero hx)
  have hax : a ∣ x := Nat.gcd_dvd_left x M
  have haM : a ∣ M := Nat.gcd_dvd_right x M
  have hac₀ : a * c₀ = x := Nat.mul_div_cancel' hax
  have hab₀ : a * b₀ = M := Nat.mul_div_cancel' haM
  have hb₀pos : 0 < b₀ := Nat.div_pos (Nat.le_of_dvd hMpos haM) hapos
  have hc₀b₀ : Nat.Coprime c₀ b₀ :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left M (Nat.pos_of_ne_zero hx))
  have hc₀y : c₀ * y = b₀ * N := by
    apply Nat.eq_of_mul_eq_mul_left hapos
    calc
      a * (c₀ * y) = (a * c₀) * y := by ring
      _ = x * y := by rw [hac₀]
      _ = M * N := hxyMN
      _ = (a * b₀) * N := by rw [hab₀]
      _ = a * (b₀ * N) := by ring
  have hb₀dvdY : b₀ ∣ y := by
    apply hc₀b₀.symm.dvd_of_dvd_mul_right
    exact ⟨N, by simpa [mul_comm] using hc₀y⟩
  let e := y / b₀
  have hb₀e : b₀ * e = y := Nat.mul_div_cancel' hb₀dvdY
  have hc₀e : c₀ * e = N := by
    apply Nat.eq_of_mul_eq_mul_left hb₀pos
    calc
      b₀ * (c₀ * e) = c₀ * (b₀ * e) := by ring
      _ = c₀ * y := by rw [hb₀e]
      _ = b₀ * N := hc₀y
  rw [Finset.mem_product]
  constructor
  · rw [Nat.mem_divisorsAntidiagonal]
    constructor
    · change a * (d * b₀) = m
      calc
        a * (d * b₀) = d * (a * b₀) := by ring
        _ = d * M := by rw [hab₀]
        _ = m := Nat.mul_div_cancel' hdm
    · exact hm
  · rw [Nat.mem_divisorsAntidiagonal]
    constructor
    · change (d * c₀) * e = n
      calc
        (d * c₀) * e = d * (c₀ * e) := by ring
        _ = d * N := by rw [hc₀e]
        _ = n := Nat.mul_div_cancel' hdn
    · exact hn

private theorem buscheBackward_forward {m n : ℕ}
    (z : (ℕ × ℕ) × (ℕ × ℕ))
    (hz : z ∈ m.divisorsAntidiagonal ×ˢ n.divisorsAntidiagonal) :
    buscheBackward m (buscheForward z) = z := by
  rcases z with ⟨⟨a, b⟩, ⟨c, e⟩⟩
  simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal] at hz
  rcases hz with ⟨⟨hab, hm⟩, ⟨hce, hn⟩⟩
  have ha : a ≠ 0 := left_ne_zero_of_mul (hab.trans_ne hm)
  have hb : b ≠ 0 := right_ne_zero_of_mul (hab.trans_ne hm)
  have hc : c ≠ 0 := left_ne_zero_of_mul (hce.trans_ne hn)
  let d := Nat.gcd b c
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero hb)
  have hdb : d ∣ b := Nat.gcd_dvd_left b c
  have hdc : d ∣ c := Nat.gcd_dvd_right b c
  have hbdivpos : 0 < b / d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hdb) hdpos
  have hM : m / d = a * (b / d) := by
    rw [← hab, Nat.mul_div_assoc a hdb]
  have hcop : Nat.Coprime (c / d) (b / d) := by
    exact (Nat.coprime_div_gcd_div_gcd hdpos).symm
  have hgcd : Nat.gcd (a * (c / d)) (m / d) = a := by
    rw [hM, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  simp only [buscheBackward, buscheForward]
  change
    ((Nat.gcd (a * (c / d)) (m / d),
        d * ((m / d) / Nat.gcd (a * (c / d)) (m / d))),
      (d * ((a * (c / d)) / Nat.gcd (a * (c / d)) (m / d)),
        ((b / d) * e) / ((m / d) / Nat.gcd (a * (c / d)) (m / d)))) =
      ((a, b), (c, e))
  rw [hgcd, hM]
  rw [Nat.mul_div_cancel_left (b / d) (Nat.pos_of_ne_zero ha)]
  rw [Nat.mul_div_cancel_left (c / d) (Nat.pos_of_ne_zero ha)]
  rw [Nat.mul_div_cancel_left e hbdivpos]
  rw [Nat.mul_div_cancel' hdb, Nat.mul_div_cancel' hdc]

private theorem buscheForward_backward {m n : ℕ} (z : Σ _d : ℕ, ℕ × ℕ)
    (hz : z ∈ buscheTarget m n) :
    buscheForward (buscheBackward m z) = z := by
  rcases z with ⟨d, ⟨x, y⟩⟩
  rw [buscheTarget, Finset.mem_sigma] at hz
  rcases hz with ⟨hdmem, hxymem⟩
  rw [Nat.mem_divisors] at hdmem
  rw [Nat.mem_divisorsAntidiagonal] at hxymem
  rcases hdmem with ⟨hdgcd, hgcd⟩
  rcases hxymem with ⟨hxy, hquot⟩
  change d ∣ Nat.gcd m n at hdgcd
  change x * y = m * n / d ^ 2 at hxy
  change m * n / d ^ 2 ≠ 0 at hquot
  have hmn : m * n ≠ 0 := by
    intro hzero
    apply hquot
    simp [hzero]
  have hm : m ≠ 0 := left_ne_zero_of_mul hmn
  have hn : n ≠ 0 := right_ne_zero_of_mul hmn
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero hgcd hdgcd
  have hdm : d ∣ m := hdgcd.trans (Nat.gcd_dvd_left m n)
  have hdn : d ∣ n := hdgcd.trans (Nat.gcd_dvd_right m n)
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let M := m / d
  let N := n / d
  have hMpos : 0 < M := Nat.div_pos (Nat.le_of_dvd hmpos hdm) hdpos
  have hNpos : 0 < N := Nat.div_pos (Nat.le_of_dvd hnpos hdn) hdpos
  have hdsq : d ^ 2 ∣ m * n := by
    refine ⟨M * N, ?_⟩
    calc
      m * n = (d * M) * (d * N) := by
        rw [Nat.mul_div_cancel' hdm, Nat.mul_div_cancel' hdn]
      _ = d ^ 2 * (M * N) := by ring
  have hquotient : m * n / d ^ 2 = M * N := by
    apply (Nat.div_eq_iff_eq_mul_left (pow_pos hdpos 2) hdsq).2
    calc
      m * n = (d * M) * (d * N) := by
        rw [Nat.mul_div_cancel' hdm, Nat.mul_div_cancel' hdn]
      _ = (M * N) * d ^ 2 := by ring
  have hxyMN : x * y = M * N := hxy.trans hquotient
  have hx : x ≠ 0 := left_ne_zero_of_mul (hxyMN.trans_ne (mul_ne_zero hMpos.ne' hNpos.ne'))
  let a := Nat.gcd x M
  let b₀ := M / a
  let c₀ := x / a
  have hapos : 0 < a := Nat.gcd_pos_of_pos_left M (Nat.pos_of_ne_zero hx)
  have hax : a ∣ x := Nat.gcd_dvd_left x M
  have haM : a ∣ M := Nat.gcd_dvd_right x M
  have hac₀ : a * c₀ = x := Nat.mul_div_cancel' hax
  have hab₀ : a * b₀ = M := Nat.mul_div_cancel' haM
  have hb₀pos : 0 < b₀ := Nat.div_pos (Nat.le_of_dvd hMpos haM) hapos
  have hc₀b₀ : Nat.Coprime c₀ b₀ :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left M (Nat.pos_of_ne_zero hx))
  have hc₀y : c₀ * y = b₀ * N := by
    apply Nat.eq_of_mul_eq_mul_left hapos
    calc
      a * (c₀ * y) = (a * c₀) * y := by ring
      _ = x * y := by rw [hac₀]
      _ = M * N := hxyMN
      _ = (a * b₀) * N := by rw [hab₀]
      _ = a * (b₀ * N) := by ring
  have hb₀dvdY : b₀ ∣ y := by
    apply hc₀b₀.symm.dvd_of_dvd_mul_right
    exact ⟨N, by simpa [mul_comm] using hc₀y⟩
  let e := y / b₀
  have hb₀e : b₀ * e = y := Nat.mul_div_cancel' hb₀dvdY
  have hgcdBack : Nat.gcd (d * b₀) (d * c₀) = d := by
    rw [Nat.gcd_mul_left, hc₀b₀.symm.gcd_eq_one, mul_one]
  simp only [buscheForward, buscheBackward]
  change
    (Sigma.mk (Nat.gcd (d * b₀) (d * c₀))
      (a * ((d * c₀) / Nat.gcd (d * b₀) (d * c₀)),
        ((d * b₀) / Nat.gcd (d * b₀) (d * c₀)) * e) :
        Σ _d : ℕ, ℕ × ℕ) =
      (Sigma.mk d (x, y) : Σ _d : ℕ, ℕ × ℕ)
  rw [hgcdBack]
  rw [Nat.mul_div_cancel_left c₀ hdpos, Nat.mul_div_cancel_left b₀ hdpos]
  rw [hac₀, hb₀e]

variable {K : Type*} [Field K]

/-- A divisor cast into the coefficient field when it is coprime to the level, and zero
otherwise.  Writing filtered divisor sums in this form makes complete multiplicativity visible. -/
noncomputable def restrictedDivisorCast (level d : ℕ) : K :=
  if Nat.Coprime d level then (d : K) else 0

@[simp]
theorem restrictedDivisorCast_mul (level a b : ℕ) :
    restrictedDivisorCast (K := K) level (a * b) =
      restrictedDivisorCast level a * restrictedDivisorCast level b := by
  simp only [restrictedDivisorCast, Nat.coprime_mul_iff_left, Nat.cast_mul]
  by_cases ha : Nat.Coprime a level
  · by_cases hb : Nat.Coprime b level
    · rw [if_pos ⟨ha, hb⟩, if_pos ha, if_pos hb]
    · rw [if_neg (fun h ↦ hb h.2), if_pos ha, if_neg hb, mul_zero]
  · rw [if_neg (fun h ↦ ha h.1), if_neg ha, zero_mul]

/-- The level-`N` Eisenstein coefficient in positive degree.  Since `Nat.divisors 0` is empty,
this definition also gives coefficient zero in degree zero. -/
noncomputable def levelEisensteinCoefficient (level m : ℕ) : K :=
  ∑ d ∈ m.divisors.filter (fun d ↦ Nat.Coprime d level), (d : K)

@[simp]
theorem levelEisensteinCoefficient_zero (level : ℕ) :
    levelEisensteinCoefficient (K := K) level 0 = 0 := by
  simp [levelEisensteinCoefficient]

@[simp]
theorem levelEisensteinCoefficient_one (level : ℕ) :
    levelEisensteinCoefficient (K := K) level 1 = 1 := by
  have hfilter :
      ({1} : Finset ℕ).filter (fun d ↦ Nat.Coprime d level) = {1} := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    simp only [Finset.mem_singleton] at hd
    subst d
    exact Nat.coprime_one_left level
  rw [levelEisensteinCoefficient, Nat.divisors_one, hfilter]
  simp

theorem levelEisensteinCoefficient_eq_sum_restrictedDivisorCast (level m : ℕ) :
    levelEisensteinCoefficient (K := K) level m =
      ∑ d ∈ m.divisors, restrictedDivisorCast level d := by
  rw [levelEisensteinCoefficient, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcop : Nat.Coprime d level <;> simp [restrictedDivisorCast, hcop]

private theorem levelEisensteinCoefficient_eq_sum_antidiagonal (level m : ℕ) :
    levelEisensteinCoefficient (K := K) level m =
      ∑ z ∈ m.divisorsAntidiagonal, restrictedDivisorCast level z.2 := by
  rw [levelEisensteinCoefficient_eq_sum_restrictedDivisorCast,
    ← Nat.map_div_left_divisors, Finset.sum_map]
  change (∑ d ∈ m.divisors, restrictedDivisorCast level d) =
    ∑ d ∈ m.divisors, restrictedDivisorCast level d
  rfl

/-- The restricted divisor sum satisfies the weight-one Busche--Ramanujan identity. -/
theorem levelEisensteinCoefficient_mul (level m n : ℕ) :
    levelEisensteinCoefficient (K := K) level m * levelEisensteinCoefficient level n =
      ∑ d ∈ (Nat.gcd m n).divisors,
        restrictedDivisorCast level d *
          levelEisensteinCoefficient level (m * n / d ^ 2) := by
  rw [levelEisensteinCoefficient_eq_sum_antidiagonal,
    levelEisensteinCoefficient_eq_sum_antidiagonal]
  calc
    (∑ z ∈ m.divisorsAntidiagonal, restrictedDivisorCast level z.2) *
        ∑ z ∈ n.divisorsAntidiagonal, restrictedDivisorCast level z.2 =
      ∑ z ∈ m.divisorsAntidiagonal ×ˢ n.divisorsAntidiagonal,
        restrictedDivisorCast level z.1.2 * restrictedDivisorCast level z.2.2 := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
    _ = ∑ z ∈ buscheTarget m n,
        restrictedDivisorCast level z.1 * restrictedDivisorCast level z.2.2 := by
      apply Finset.sum_bij' (fun z _hz ↦ buscheForward z)
        (fun z _hz ↦ buscheBackward m z)
      · exact fun z hz ↦ buscheForward_mem z hz
      · exact fun z hz ↦ buscheBackward_mem z hz
      · exact fun z hz ↦ buscheBackward_forward z hz
      · exact fun z hz ↦ buscheForward_backward z hz
      · rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩ hz
        simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal] at hz
        let d := Nat.gcd b c
        have hdb : d ∣ b := Nat.gcd_dvd_left b c
        change restrictedDivisorCast level b * restrictedDivisorCast level e =
          restrictedDivisorCast level d *
            restrictedDivisorCast level ((b / d) * e)
        have hbdecomp : b = d * (b / d) := (Nat.mul_div_cancel' hdb).symm
        have hweightB : restrictedDivisorCast (K := K) level b =
            restrictedDivisorCast level d * restrictedDivisorCast level (b / d) := by
          calc
            restrictedDivisorCast level b =
                restrictedDivisorCast level (d * (b / d)) :=
              congrArg (restrictedDivisorCast (K := K) level) hbdecomp
            _ = _ := restrictedDivisorCast_mul level d (b / d)
        have hweightY : restrictedDivisorCast (K := K) level ((b / d) * e) =
            restrictedDivisorCast level (b / d) * restrictedDivisorCast level e :=
          restrictedDivisorCast_mul level (b / d) e
        rw [hweightB, hweightY]
        ring
    _ = ∑ d ∈ (Nat.gcd m n).divisors,
        restrictedDivisorCast level d *
          levelEisensteinCoefficient level (m * n / d ^ 2) := by
      rw [buscheTarget, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro d hd
      rw [levelEisensteinCoefficient_eq_sum_antidiagonal, Finset.mul_sum]

/-- Filtered form of the Busche--Ramanujan identity, matching the coefficient formula in
`weightTwoHeckeQExpansion`. -/
theorem weightTwoHeckeCoefficient_levelEisensteinCoefficient
    (level m n : ℕ) :
    (∑ d ∈ (Nat.gcd m n).divisors.filter (fun d ↦ Nat.Coprime d level),
        (d : K) * levelEisensteinCoefficient level (m * n / d ^ 2)) =
      levelEisensteinCoefficient level n * levelEisensteinCoefficient level m := by
  calc
    (∑ d ∈ (Nat.gcd m n).divisors.filter (fun d ↦ Nat.Coprime d level),
        (d : K) * levelEisensteinCoefficient level (m * n / d ^ 2)) =
      ∑ d ∈ (Nat.gcd m n).divisors,
        restrictedDivisorCast level d *
          levelEisensteinCoefficient level (m * n / d ^ 2) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcop : Nat.Coprime d level <;>
        simp [restrictedDivisorCast, hcop]
    _ = levelEisensteinCoefficient level m * levelEisensteinCoefficient level n :=
      (levelEisensteinCoefficient_mul level m n).symm
    _ = levelEisensteinCoefficient level n * levelEisensteinCoefficient level m := mul_comm _ _

/-- The canonical formal weight-two Eisenstein differential series at positive level `N`.

Its constant coefficient is zero, and its coefficient in positive degree `m` is
`sum_{d | m, gcd(d,N)=1} d`.  This definition makes no geometric realization claim. -/
noncomputable def eisensteinDifferentialExpansion
    (level : {N : ℕ // 0 < N}) : PowerSeries K :=
  PowerSeries.mk fun m ↦ levelEisensteinCoefficient level.1 m

@[simp]
theorem coeff_eisensteinDifferentialExpansion
    (level : {N : ℕ // 0 < N}) (m : ℕ) :
    PowerSeries.coeff m (eisensteinDifferentialExpansion (K := K) level) =
      levelEisensteinCoefficient level.1 m := by
  rw [eisensteinDifferentialExpansion, PowerSeries.coeff_mk]

@[simp]
theorem coeff_zero_eisensteinDifferentialExpansion
    (level : {N : ℕ // 0 < N}) :
    PowerSeries.coeff 0 (eisensteinDifferentialExpansion (K := K) level) = 0 := by
  simp

@[simp]
theorem coeff_one_eisensteinDifferentialExpansion
    (level : {N : ℕ // 0 < N}) :
    PowerSeries.coeff 1 (eisensteinDifferentialExpansion (K := K) level) = 1 := by
  simp

/-- The Eisenstein differential series is nonzero over every coefficient field, in every
characteristic, because its coefficient in degree one is one. -/
theorem eisensteinDifferentialExpansion_ne_zero
    (level : {N : ℕ // 0 < N}) :
    eisensteinDifferentialExpansion (K := K) level ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (PowerSeries.coeff 1) hzero
  simp at hcoeff

/-- The explicit eigenvalue of `T_n` on the canonical Eisenstein differential series. -/
noncomputable def eisensteinHeckeEigenvalue
    (level n : {N : ℕ // 0 < N}) : K :=
  levelEisensteinCoefficient level.1 n.1

/-- The canonical Eisenstein differential series is an eigenvector for every positive-index
standard weight-two Hecke q-expansion operator. -/
theorem weightTwoHeckeQExpansion_eisensteinDifferentialExpansion
    (level n : {N : ℕ // 0 < N}) :
    HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n
        (eisensteinDifferentialExpansion (K := K) level) =
      eisensteinHeckeEigenvalue (K := K) level n •
        eisensteinDifferentialExpansion (K := K) level := by
  ext m
  rw [HeckeDifferentialQExpansion.coeff_weightTwoHeckeQExpansion]
  simp only [coeff_eisensteinDifferentialExpansion, PowerSeries.coeff_smul,
    smul_eq_mul, eisensteinHeckeEigenvalue]
  exact weightTwoHeckeCoefficient_levelEisensteinCoefficient level.1 m n.1

/-- Simultaneous-eigenvector packaging for direct use by the formal-immersion q-expansion
consumer. -/
theorem eisensteinDifferentialExpansion_simultaneousEigen
    (level : {N : ℕ // 0 < N}) :
    ∀ n : {n : ℕ // 0 < n},
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n
          (eisensteinDifferentialExpansion (K := K) level) =
        eisensteinHeckeEigenvalue (K := K) level n •
          eisensteinDifferentialExpansion (K := K) level :=
  weightTwoHeckeQExpansion_eisensteinDifferentialExpansion (K := K) level

end EisensteinDifferentialQExpansion

end MazurTorsion.ModularCurve
