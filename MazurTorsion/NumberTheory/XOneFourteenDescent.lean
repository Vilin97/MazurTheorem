/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.ExceptionalCubicDescent

/-!
# Two-isogeny descent for `X₁(14)`

The genus-one model

`s² + s t + s = t³ - t`

is transformed by

`U = 4(t+1)`, `V = 4(2s+t+1)`

to

`V² = U(U² - 11U + 32)`.

Its two-isogenous curve is

`W² = Z(Z² + 22Z - 7)`.

The explicit two-isogeny descent first proves that the
abscissa of every rational point on the dual curve has squareclass `1` or
`-7`.  The only other possible squareclasses are `-1` and `7`.  After
clearing denominators, either class is impossible modulo sixteen: opposite
parities give the nonsquare residue `7` modulo eight, while two odd
parameters give `12` modulo sixteen.

On the original curve, positivity and a gcd-divides-`32` calculation leave
only squareclasses `1` and `2`.  A checked reverse-doubling calculation
then gives two cosets modulo doubling.  Naïve-height descent and the exact
rational two-torsion cardinality imply finite generation and
Mordell--Weil rank zero.

The file records visible torsion points but does not depend on the
order-fourteen Tate-normal-form reduction and does not classify every
rational point.
-/

namespace MazurTorsion.XOneFourteen

/-- A Weierstrass model of `X₁(14)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨0, -11, 0, 32, 0⟩

/-- The curve two-isogenous to `curve`. -/
def dualCurve : WeierstrassCurve ℚ :=
  ⟨0, 22, 0, -7, 0⟩

private instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private instance dualCurve_isElliptic : dualCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [dualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private abbrev redTwo : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

private lemma neg_one_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠ -m ^ 4 + 22 * m ^ 2 * n ^ 2 + 7 * n ^ 4 := by
  decide

private lemma seven_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠ 7 * m ^ 4 + 22 * m ^ 2 * n ^ 2 - n ^ 4 := by
  decide

private lemma primitive_not_both_even
    {m n : ℤ} (hcoprime : IsCoprime m n) :
    redTwo (m : ZMod 16) ≠ 0 ∨ redTwo (n : ZMod 16) ≠ 0 := by
  by_contra hboth
  simp only [not_or, not_not] at hboth
  have hmeven : Even m := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [redTwo] using hboth.1
  have hneven : Even n := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [redTwo] using hboth.2
  have hunit : IsUnit (2 : ℤ) :=
    hcoprime.isUnit_of_dvd'
      (even_iff_two_dvd.mp hmeven) (even_iff_two_dvd.mp hneven)
  norm_num [Int.isUnit_iff] at hunit

/-- The primitive quartic attached to the dual squareclass `-1` has no
integer point. -/
theorem no_dual_neg_one_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ -m ^ 4 + 22 * m ^ 2 * n ^ 2 + 7 * n ^ 4 := by
  intro h
  apply neg_one_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to the dual squareclass `7` has no
integer point. -/
theorem no_dual_seven_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ 7 * m ^ 4 + 22 * m ^ 2 * n ^ 2 - n ^ 4 := by
  intro h
  apply seven_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- Rational denominator-cleared form of `no_dual_neg_one_class`. -/
theorem no_dual_neg_one_class_rat (z q : ℚ) :
    q ^ 2 ≠ -z ^ 4 + 22 * z ^ 2 + 7 := by
  intro h
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / n :=
    z.num_div_den.symm
  have hscaled :
      (q * n ^ 2) ^ 2 =
        (((-m ^ 4 + 22 * m ^ 2 * n ^ 2 + 7 * n ^ 4 : ℤ) : ℚ)) := by
    rw [hz] at h
    field_simp [hn] at h
    calc
      (q * n ^ 2) ^ 2 = q ^ 2 * n ^ 4 := by ring
      _ = -(m : ℚ) ^ 4 + 22 * (m : ℚ) ^ 2 * n ^ 2 +
          7 * n ^ 4 := by nlinarith [h]
      _ = (((-m ^ 4 + 22 * m ^ 2 * n ^ 2 + 7 * n ^ 4 : ℤ) : ℚ)) := by
        push_cast
        ring
  have hsquare :
      IsSquare
        (((-m ^ 4 + 22 * m ^ 2 * n ^ 2 + 7 * n ^ 4 : ℤ) : ℚ)) :=
    ⟨q * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨w, hw⟩ := Rat.isSquare_intCast_iff.mp hsquare
  exact no_dual_neg_one_class m n w
    (by simpa [m, n] using Rat.isCoprime_num_den z)
    (by simpa [pow_two] using hw.symm)

/-- Rational denominator-cleared form of `no_dual_seven_class`. -/
theorem no_dual_seven_class_rat (z q : ℚ) :
    q ^ 2 ≠ 7 * z ^ 4 + 22 * z ^ 2 - 1 := by
  intro h
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / n :=
    z.num_div_den.symm
  have hscaled :
      (q * n ^ 2) ^ 2 =
        (((7 * m ^ 4 + 22 * m ^ 2 * n ^ 2 - n ^ 4 : ℤ) : ℚ)) := by
    rw [hz] at h
    field_simp [hn] at h
    calc
      (q * n ^ 2) ^ 2 = q ^ 2 * n ^ 4 := by ring
      _ = 7 * (m : ℚ) ^ 4 + 22 * (m : ℚ) ^ 2 * n ^ 2 -
          n ^ 4 := by nlinarith [h]
      _ = (((7 * m ^ 4 + 22 * m ^ 2 * n ^ 2 - n ^ 4 : ℤ) : ℚ)) := by
        push_cast
        ring
  have hsquare :
      IsSquare
        (((7 * m ^ 4 + 22 * m ^ 2 * n ^ 2 - n ^ 4 : ℤ) : ℚ)) :=
    ⟨q * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨w, hw⟩ := Rat.isSquare_intCast_iff.mp hsquare
  exact no_dual_seven_class m n w
    (by simpa [m, n] using Rat.isCoprime_num_den z)
    (by simpa [pow_two] using hw.symm)

private lemma common_divisor_dual_dvd_seven
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 + 22 * m * n - 7 * n ^ 2) :
    d ∣ 7 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (22 * m - 7 * n) * a, ?_⟩
    linear_combination m * hb - (22 * m - 7 * n) * ha
  have h7n3 : d ∣ 7 * n ^ 3 := by
    refine ⟨(m + 22 * n) * a - n * b, ?_⟩
    linear_combination (m + 22 * n) * ha - n * hb
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h7n3)

private lemma squareclass_of_gcd_dvd_seven
    {A B C : ℤ} (hA0 : A ≠ 0) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (7 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨
        A = 7 * z ^ 2 ∨ A = -7 * z ^ 2 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg] at hgA
    exact hA0 (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hprod] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hprod
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcoprime : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcoprime hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    have hgabs : g.natAbs ∣ 7 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 7 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 7 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 7 := by
        exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals : g = 1 ∨ g = 7 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inl (by simpa using hAz)))⟩
  · have hAz : A = -(g * z ^ 2) := by rw [← hga, hz]; ring
    have hgabs : g.natAbs ∣ 7 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 7 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 7 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 7 := by
        exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals : g = 1 ∨ g = 7 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inl (by nlinarith [hAz]))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (by nlinarith [hAz])))⟩

/-- On the dual `X₁(14)` curve, every nonzero abscissa initially has one
of the four squareclasses `1`, `-1`, `7`, and `-7`. -/
theorem dual_abscissa_squareclass
    {X Y : ℚ} (hX0 : X ≠ 0)
    (hcurve : Y ^ 2 = X * (X ^ 2 + 22 * X - 7)) :
    (∃ z : ℚ, X = z ^ 2) ∨
      (∃ z : ℚ, X = -z ^ 2) ∨
      (∃ z : ℚ, X = 7 * z ^ 2) ∨
      (∃ z : ℚ, X = -7 * z ^ 2) := by
  let m : ℤ := X.num
  let n : ℤ := X.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 + 22 * m * n - 7 * n ^ 2
  have hn : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hX : X = (m : ℚ) / n :=
    X.num_div_den.symm
  have hscaled :
      (Y * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hX] at hcurve
    field_simp [hn] at hcurve
    calc
      (Y * n ^ 2) ^ 2 = Y ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 + 22 * m * n - 7 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsquare : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨Y * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsquare
  have hprod : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : A ≠ 0 := by
    apply mul_ne_zero
    · dsimp [m]
      exact Rat.num_ne_zero.mpr hX0
    · dsimp [n]
      exact_mod_cast X.den_ne_zero
  have hmnCoprime : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den X
  have hgcd : GCDMonoid.gcd A B ∣ (7 : ℤ) :=
    common_divisor_dual_dvd_seven hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  obtain ⟨z, hA | hA | hA | hA⟩ :=
    squareclass_of_gcd_dvd_seven hA0 hprod hgcd
  · left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hX]
    simp only [A] at hA
    field_simp [hn]
    exact_mod_cast hA
  · right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hX]
    simp only [A] at hA
    field_simp [hn]
    exact_mod_cast hA
  · right; right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hX]
    simp only [A] at hA
    field_simp [hn]
    exact_mod_cast hA
  · right; right; right
    have hA' : A = -(7 * z ^ 2) := by nlinarith [hA]
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hX]
    simp only [A] at hA'
    field_simp [hn]
    exact_mod_cast hA'

/-- The two impossible squareclasses are removed: a rational point on the
dual curve has abscissa a square or `-7` times a square. -/
theorem dual_abscissa_isSquare_or_negSeven
    {X Y : ℚ}
    (hcurve : Y ^ 2 = X * (X ^ 2 + 22 * X - 7)) :
    IsSquare X ∨ ∃ z : ℚ, X = -7 * z ^ 2 := by
  rcases eq_or_ne X 0 with rfl | hX0
  · exact Or.inl IsSquare.zero
  rcases dual_abscissa_squareclass hX0 hcurve with
      ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    exact ⟨z, by simpa [pow_two] using hz⟩
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hX0 hz
    exfalso
    apply no_dual_neg_one_class_rat z (Y / z)
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hX0 hz
    exfalso
    apply no_dual_seven_class_rat z (Y / (7 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · exact Or.inr ⟨z, hz⟩

private lemma common_divisor_curve_dvd_thirty_two
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 - 11 * m * n + 32 * n ^ 2) :
    d ∣ 32 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (-11 * m + 32 * n) * a, ?_⟩
    linear_combination m * hb - (-11 * m + 32 * n) * ha
  have h32n3 : d ∣ 32 * n ^ 3 := by
    refine ⟨n * b - (m - 11 * n) * a, ?_⟩
    linear_combination n * hb - (m - 11 * n) * ha
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h32n3)

private lemma positive_squareclass_of_gcd_dvd_thirty_two
    {A B C : ℤ} (hApos : 0 < A) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (32 : ℤ)) :
    ∃ z : ℤ, A = z ^ 2 ∨ A = 2 * z ^ 2 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg] at hgA
    exact hApos.ne' (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hprod] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hprod
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcoprime : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcoprime hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    have hgabs : g.natAbs ∣ 32 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 32 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 32 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 32 := by
        exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals :
        g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 8 ∨ g = 16 ∨ g = 32 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg | hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨2 * z, Or.inl (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨2 * z, Or.inr (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨4 * z, Or.inl (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨4 * z, Or.inr (by nlinarith [hAz])⟩
  · have haNonpos : a ≤ 0 := by nlinarith [sq_nonneg z]
    have hAnonpos : A ≤ 0 := by
      rw [← hga]
      exact mul_nonpos_of_nonneg_of_nonpos hgpos.le haNonpos
    exact (not_lt_of_ge hAnonpos hApos).elim

/-- Every nonzero abscissa on the original curve has squareclass `1` or
`2`. -/
theorem curve_abscissa_isSquare_or_two
    {U V : ℚ} (hU0 : U ≠ 0)
    (hcurve : V ^ 2 = U * (U ^ 2 - 11 * U + 32)) :
    IsSquare U ∨ ∃ z : ℚ, U = 2 * z ^ 2 := by
  have hquadratic : 0 < U ^ 2 - 11 * U + 32 := by
    nlinarith [sq_nonneg (2 * U - 11)]
  have hUpos : 0 < U := by
    by_contra! hUnonpos
    have hUneg : U < 0 := lt_of_le_of_ne hUnonpos hU0
    have hnegative : U * (U ^ 2 - 11 * U + 32) < 0 :=
      mul_neg_of_neg_of_pos hUneg hquadratic
    rw [← hcurve] at hnegative
    exact (not_lt_of_ge (sq_nonneg V)) hnegative
  let m : ℤ := U.num
  let n : ℤ := U.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 - 11 * m * n + 32 * n ^ 2
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast U.den_pos
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hU : U = (m : ℚ) / n := U.num_div_den.symm
  have hscaled :
      (V * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hU] at hcurve
    field_simp [hn0] at hcurve
    calc
      (V * n ^ 2) ^ 2 = V ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 - 11 * m * n + 32 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsquareRat : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨V * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsquareRat
  have hprod : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hApos : 0 < A := by
    have hmpos : 0 < m := by
      dsimp [m]
      exact Rat.num_pos.mpr hUpos
    exact mul_pos hmpos hnpos
  have hmnCoprime : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den U
  have hgcd : GCDMonoid.gcd A B ∣ (32 : ℤ) :=
    common_divisor_curve_dvd_thirty_two hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  obtain ⟨z, hA | hA⟩ :=
    positive_squareclass_of_gcd_dvd_thirty_two hApos hprod hgcd
  · left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0]
    exact_mod_cast hA
  · right
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0]
    exact_mod_cast hA

private lemma y_linear_of_reverse_definition
    {X Y q v : ℚ} (hq0 : q ≠ 0)
    (hv : v = 11 / 2 + X / 2 - Y / (2 * q)) :
    Y = q * (X + 11 - 2 * v) := by
  field_simp [hq0] at hv
  linear_combination hv

private lemma y_formula_of_reverse_linear
    {X Y q v : ℚ} (hv0 : v ≠ 0)
    (hlinear : Y = q * (X + 11 - 2 * v))
    (hXv : X * v = v ^ 2 - 11 * v + 32) :
    Y = -q * (v ^ 2 - 32) / v := by
  rw [hlinear]
  field_simp [hv0]
  linear_combination q * hXv

private lemma y_formula_squared
    {Y q v : ℚ} (hv0 : v ≠ 0)
    (hY : Y = -q * (v ^ 2 - 32) / v) :
    Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 - 32) ^ 2 := by
  rw [hY]
  field_simp [hv0]

/-- A nonzero rational point whose abscissa is a square is divisible by
two.  The proof is an explicit reverse-doubling calculation.  If the first
auxiliary dual abscissa has squareclass `-7`, its conjugate (their product
is `-7`) is a square and gives the same doubling abscissa. -/
theorem double_of_square_abscissa
    {U V : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hUSquare : IsSquare U) :
    ∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  obtain ⟨s, hs⟩ := hUSquare
  have hU : U = s ^ 2 := by
    simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve : V ^ 2 = U * (U ^ 2 - 11 * U + 32) := by
    have heq := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    norm_num [curve] at heq
    nlinarith
  let t : ℚ := V / s
  have ht : t ^ 2 = U ^ 2 - 11 * U + 32 := by
    dsimp [t]
    rw [div_pow]
    field_simp [hs0]
    nlinarith [hcurve, hU]
  let X₀ : ℚ := 2 * U - 11 - 2 * t
  let X₁ : ℚ := 2 * U - 11 + 2 * t
  have hXprod : X₀ * X₁ = -7 := by
    dsimp [X₀, X₁]
    nlinarith [ht]
  have hX₀0 : X₀ ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  let Y₀ : ℚ := 2 * s * X₀
  have hdualFactor :
      X₀ ^ 2 + 22 * X₀ - 7 = 4 * U * X₀ := by
    dsimp [X₀]
    nlinarith [ht]
  have hdual :
      Y₀ ^ 2 = X₀ * (X₀ ^ 2 + 22 * X₀ - 7) := by
    rw [hdualFactor]
    dsimp [Y₀]
    rw [hU]
    ring
  obtain ⟨τ, X, q, hτ, hXdef, hX0, hXq⟩ :
      ∃ τ X q : ℚ,
        τ ^ 2 = U ^ 2 - 11 * U + 32 ∧
        X = 2 * U - 11 - 2 * τ ∧
        X ≠ 0 ∧ X = q ^ 2 := by
    rcases dual_abscissa_isSquare_or_negSeven hdual with
        hXsquare | ⟨z, hz⟩
    · obtain ⟨q, hq⟩ := hXsquare
      exact
        ⟨t, X₀, q, ht, rfl, hX₀0,
          by simpa [pow_two] using hq⟩
    · have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0] at hz
        norm_num at hz
        exact hX₀0 hz
      have hX₁square : X₁ = (1 / z) ^ 2 := by
        rw [hz] at hXprod
        dsimp [X₁]
        field_simp [hz0]
        nlinarith [hXprod]
      have hX₁0 : X₁ ≠ 0 := by
        rw [hX₁square]
        exact pow_ne_zero 2 (div_ne_zero (by norm_num) hz0)
      refine ⟨-t, X₁, 1 / z, ?_, ?_, hX₁0, hX₁square⟩
      · nlinarith [ht]
      · dsimp [X₁]
        ring
  let Y : ℚ := 2 * s * X
  have hfactor :
      X ^ 2 + 22 * X - 7 = 4 * U * X := by
    rw [hXdef]
    nlinarith [hτ]
  have hdualChosen :
      Y ^ 2 = X * (X ^ 2 + 22 * X - 7) := by
    rw [hfactor]
    dsimp [Y]
    rw [hU]
    ring
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq] at hXq
    norm_num at hXq
    exact hX0 hXq
  have hYq :
      (Y / q) ^ 2 = X ^ 2 + 22 * X - 7 := by
    rw [div_pow]
    field_simp [hq0]
    nlinarith [hdualChosen, hXq]
  let v : ℚ := 11 / 2 + X / 2 - Y / (2 * q)
  let w : ℚ := q * v
  have hvdef : v = 11 / 2 + X / 2 - Y / (2 * q) := rfl
  have hwdef : w = q * v := rfl
  have hXv : X * v = v ^ 2 - 11 * v + 32 := by
    dsimp [v]
    field_simp [hq0] at hYq ⊢
    nlinarith [hYq, hXq]
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv] at hXv
    norm_num at hXv
  have hw0 : w ≠ 0 :=
    mul_ne_zero hq0 hv0
  have hcurveQ : w ^ 2 = v * (v ^ 2 - 11 * v + 32) := by
    rw [hwdef, ← hXv, hXq]
    ring
  have hQ : curve.toAffine.Nonsingular v w := by
    apply curve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve]
    linear_combination hcurveQ
  have hwneneg : w ≠ -w := by
    intro h
    apply hw0
    linarith
  have hneg : w ≠ curve.toAffine.negY v w := by
    simp only [WeierstrassCurve.Affine.negY]
    norm_num [curve]
    exact hwneneg
  let Q : curve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some v w hQ
  have hdouble :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (h₁ := hQ) hneg
  have hslope :
      curve.toAffine.slope v v w w =
        (3 * v ^ 2 - 22 * v + 32) / (2 * w) := by
    simp [WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve, hwneneg]
    ring
  have haddX :
      curve.toAffine.addX v v
          (curve.toAffine.slope v v w w) =
        (v ^ 2 - 32) ^ 2 / (4 * w ^ 2) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hw0]
    rw [hcurveQ]
    ring
  have hYformula :
      Y = -q * (v ^ 2 - 32) / v :=
    y_formula_of_reverse_linear hv0
      (y_linear_of_reverse_definition hq0 hvdef) hXv
  have haddXeq :
      curve.toAffine.addX v v
          (curve.toAffine.slope v v w w) = U := by
    rw [haddX]
    have hYsq : Y ^ 2 = 4 * U * X ^ 2 := by
      dsimp [Y]
      rw [hU]
      ring
    have hYformulaCleared :
        Y ^ 2 * v ^ 2 =
          q ^ 2 * (v ^ 2 - 32) ^ 2 :=
      y_formula_squared hv0 hYformula
    have hcancel :
        q ^ 2 * (v ^ 2 - 32) ^ 2 =
          q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
      calc
        q ^ 2 * (v ^ 2 - 32) ^ 2 =
            Y ^ 2 * v ^ 2 := hYformulaCleared.symm
        _ = q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
          rw [hYsq, hXq]
          ring
    have htarget :
        (v ^ 2 - 32) ^ 2 = 4 * w ^ 2 * U := by
      have hcancelled :=
        mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      calc
        (v ^ 2 - 32) ^ 2 =
            4 * U * q ^ 2 * v ^ 2 := hcancelled
        _ = 4 * w ^ 2 * U := by rw [hwdef]; ring
    rw [htarget]
    field_simp [hw0]
  have hXcoord :
      Q + Q =
          WeierstrassCurve.Affine.Point.some U V hP ∨
        Q + Q =
          -WeierstrassCurve.Affine.Point.some U V hP := by
    rw [hdouble]
    apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
    exact haddXeq
  rcases hXcoord with hQQ | hQQ
  · exact ⟨Q, by simpa [two_nsmul] using hQQ⟩
  · refine ⟨-Q, ?_⟩
    simp only [two_nsmul]
    calc
      -Q + -Q = -(Q + Q) := by rw [neg_add]
      _ = -(-WeierstrassCurve.Affine.Point.some U V hP) := by
        rw [hQQ]
      _ = WeierstrassCurve.Affine.Point.some U V hP := neg_neg _

private lemma nonsingular_zero_zero :
    curve.toAffine.Nonsingular 0 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

/-- The unique nonzero rational point killed by two. -/
def T : curve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

private lemma curve_equation_of_nonsingular
    {U V : ℚ} (hP : curve.toAffine.Nonsingular U V) :
    V ^ 2 = U * (U ^ 2 - 11 * U + 32) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [curve] at heq
  nlinarith

private lemma decompose_of_sub_eq_some
    {P R : curve.toAffine.Point} {x y : ℚ}
    {hxy : curve.toAffine.Nonsingular x y}
    (hsub : P - R = .some x y hxy)
    (hx0 : x ≠ 0) (hxSquare : IsSquare x) :
    ∃ Q : curve.toAffine.Point, P = R + (2 : ℕ) • Q := by
  obtain ⟨Q, hQ⟩ :=
    double_of_square_abscissa hx0 hxy hxSquare
  refine ⟨Q, ?_⟩
  calc
    P = R + (P - R) := by abel
    _ = R + (2 : ℕ) • Q := by rw [hsub, hQ]

private lemma decompose_two_class
    {U V z : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = 2 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      .some U V hP = T + (2 : ℕ) • Q := by
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve := curve_equation_of_nonsingular hP
  have hslope :
      curve.toAffine.slope U 0 V 0 = V / U := by
    simp [WeierstrassCurve.Affine.slope, hU0]
  have haddX :
      curve.toAffine.addX U 0
          (curve.toAffine.slope U 0 V 0) = 32 / U := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hU0]
    nlinarith [hcurve]
  let hsum : curve.toAffine.Nonsingular
      (curve.toAffine.addX U 0
        (curve.toAffine.slope U 0 V 0))
      (curve.toAffine.addY U 0 V
        (curve.toAffine.slope U 0 V 0)) :=
    WeierstrassCurve.Affine.nonsingular_add
      hP nonsingular_zero_zero (fun h ↦ hU0 h.1)
  have hnegT : -T = T := by
    rw [T, WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    norm_num [WeierstrassCurve.Affine.negY, curve]
  have hsub :
      (.some U V hP : curve.toAffine.Point) - T =
        .some
          (curve.toAffine.addX U 0
            (curve.toAffine.slope U 0 V 0))
          (curve.toAffine.addY U 0 V
            (curve.toAffine.slope U 0 V 0)) hsum := by
    rw [sub_eq_add_neg, hnegT]
    change (.some U V hP : curve.toAffine.Point) +
        .some 0 0 nonsingular_zero_zero = _
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hU0
  apply decompose_of_sub_eq_some hsub
  · rw [haddX, hU]
    exact div_ne_zero (by norm_num)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0))
  · refine ⟨4 / z, ?_⟩
    rw [haddX, hU]
    field_simp [hz0]
    norm_num

/-- Every rational point lies in one of two explicit cosets of twice the
rational point group. -/
theorem two_doubling_cosets (P : curve.toAffine.Point) :
    (∃ Q : curve.toAffine.Point, P = (2 : ℕ) • Q) ∨
      (∃ Q : curve.toAffine.Point, P = T + (2 : ℕ) • Q) := by
  cases P with
  | zero =>
      left
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hcurve := curve_equation_of_nonsingular hP
      rcases eq_or_ne U 0 with rfl | hU0
      · have hV : V = 0 := by
          norm_num at hcurve
          nlinarith [sq_nonneg V]
        subst V
        right
        refine ⟨0, ?_⟩
        simp [T]
      · rcases curve_abscissa_isSquare_or_two hU0 hcurve with
          hUsquare | ⟨z, hU⟩
        · left
          obtain ⟨Q, hQ⟩ :=
            double_of_square_abscissa hU0 hP hUsquare
          exact ⟨Q, hQ.symm⟩
        · right
          exact decompose_two_class hU0 hP hU

/-- The image of multiplication by two on the rational point group. -/
abbrev doublingRange : AddSubgroup curve.toAffine.Point :=
  (nsmulAddMonoidHom (α := curve.toAffine.Point) 2).range

private def doublingRepresentative : Fin 2 → curve.toAffine.Point
  | 0 => 0
  | 1 => T

private lemma doubling_quotient_surjective :
    Function.Surjective
      (fun i : Fin 2 ↦
        QuotientAddGroup.mk' doublingRange
          (doublingRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective doublingRange c
  rcases two_doubling_cosets P with ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · refine
      ⟨0, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨1, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm

/-- The image of multiplication by two has finite index. -/
theorem doubling_finiteIndex : doublingRange.FiniteIndex := by
  letI : Finite (curve.toAffine.Point ⧸ doublingRange) :=
    Finite.of_surjective _ doubling_quotient_surjective
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The rational point group is finitely generated. -/
theorem point_fg : AddGroup.FG curve.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_two curve
    doubling_finiteIndex

/-- The multiplication-by-two index is at most two. -/
theorem doubling_index_le_two : doublingRange.index ≤ 2 := by
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      doubling_quotient_surjective).trans_eq (by simp)

private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private def twoToTwoTorsion :
    Fin 2 → {P : curve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T⟩

private lemma twoToTwoTorsion_injective :
    Function.Injective twoToTwoTorsion := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [twoToTwoTorsion, T] at hij ⊢

private lemma twoToTwoTorsion_surjective :
    Function.Surjective twoToTwoTorsion := by
  rintro ⟨P, htwo⟩
  cases P with
  | zero =>
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hself :
          WeierstrassCurve.Affine.Point.some U V hP =
            -WeierstrassCurve.Affine.Point.some U V hP := by
        rw [← add_eq_zero_iff_eq_neg]
        simpa [two_nsmul] using htwo
      have hV : V = 0 := by
        rw [WeierstrassCurve.Affine.Point.neg_some] at hself
        simp only [WeierstrassCurve.Affine.Point.some.injEq,
          true_and] at hself
        norm_num [WeierstrassCurve.Affine.negY, curve] at hself
        linarith
      have hcurve := curve_equation_of_nonsingular hP
      have hquadratic : 0 < U ^ 2 - 11 * U + 32 := by
        nlinarith [sq_nonneg (2 * U - 11)]
      have hU : U = 0 := by
        rw [hV] at hcurve
        norm_num at hcurve
        rcases hcurve with hU | hquad
        · exact hU
        · exact (ne_of_gt hquadratic hquad).elim
      subst U
      subst V
      refine ⟨1, ?_⟩
      apply Subtype.ext
      rfl

/-- The curve has exactly two rational points killed by two. -/
theorem two_torsion_card_eq_two :
    Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2 := by
  letI : Finite
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion curve
  simpa using
    (Nat.card_congr
      (Equiv.ofBijective twoToTwoTorsion
        ⟨twoToTwoTorsion_injective,
          twoToTwoTorsion_surjective⟩)).symm

/-- The rational point group has Mordell--Weil rank zero. -/
theorem point_rank_zero :
    Module.finrank ℤ curve.toAffine.Point = 0 := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  have hker :
      Nat.card
          (nsmulAddMonoidHom
            (α := curve.toAffine.Point) 2).ker = 2 := by
    change Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2
    exact two_torsion_card_eq_two
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg curve.toAffine.Point
      (by norm_num : (2 : ℕ) ≠ 0)
  rw [hker] at hformula
  have hpow :
      2 ^ Module.finrank ℤ curve.toAffine.Point ≤ 1 := by
    have hindex := doubling_index_le_two
    change
      (nsmulAddMonoidHom
        (α := curve.toAffine.Point) 2).range.index ≤ 2
      at hindex
    omega
  have hpowequal :
      2 ^ Module.finrank ℤ curve.toAffine.Point = 1 :=
    le_antisymm hpow
      (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- All rational points are torsion; in particular, the rational point
group is finite. -/
theorem point_finite : Finite curve.toAffine.Point := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  letI : Module.Finite ℤ curve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr point_fg
  have hmoduleTorsion :
      Module.IsTorsion ℤ curve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      point_rank_zero
  exact AddCommGroup.finite_of_fg_torsion curve.toAffine.Point
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

private lemma nonsingular_eight_eight :
    curve.toAffine.Nonsingular 8 8 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_eight_neg_eight :
    curve.toAffine.Nonsingular 8 (-8) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_four_four :
    curve.toAffine.Nonsingular 4 4 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_four_neg_four :
    curve.toAffine.Nonsingular 4 (-4) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

/-- The visible point `(8, 8)`, which has exact order six. -/
def G : curve.toAffine.Point :=
  .some 8 8 nonsingular_eight_eight

/-- The negative visible point `(8, -8)`. -/
def Gneg : curve.toAffine.Point :=
  .some 8 (-8) nonsingular_eight_neg_eight

/-- The visible point `(4, 4) = 2G`. -/
def H : curve.toAffine.Point :=
  .some 4 4 nonsingular_four_four

/-- The negative visible point `(4, -4)`. -/
def Hneg : curve.toAffine.Point :=
  .some 4 (-4) nonsingular_four_neg_four

/-- Doubling `(8,8)` gives `(4,4)`. -/
theorem double_G : (2 : ℕ) • G = H := by
  simp only [two_nsmul, G]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (by norm_num [WeierstrassCurve.Affine.negY, curve])]
  rw [H]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve]

private theorem add_G_H : G + H = T := by
  rw [G, H, T]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne
    (by norm_num : (8 : ℚ) ≠ 4)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, curve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, curve]

/-- Tripling `(8,8)` gives the nonzero rational two-torsion point. -/
theorem triple_G : (3 : ℕ) • G = T := by
  calc
    (3 : ℕ) • G = G + (2 : ℕ) • G := by abel
    _ = G + H := by rw [double_G]
    _ = T := add_G_H

private lemma six_G : (6 : ℕ) • G = 0 := by
  calc
    (6 : ℕ) • G = (2 : ℕ) • ((3 : ℕ) • G) := by
      norm_num [← mul_nsmul]
    _ = (2 : ℕ) • T := by rw [triple_G]
    _ = 0 := double_T

/-- The visible point `(8,8)` has exact additive order six. -/
theorem addOrderOf_G : addOrderOf G = 6 := by
  apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul
    (by norm_num) six_G
  intro p hp hpdiv
  have hp23 : p ∣ 2 * 3 := by
    simpa using hpdiv
  have hpvals : p = 2 ∨ p = 3 := by
    rcases hp.dvd_mul.mp hp23 with hp2 | hp3
    · rcases (Nat.dvd_prime
        (by decide : Nat.Prime 2)).mp hp2 with hp1 | hp2
      · exact (hp.ne_one hp1).elim
      · exact Or.inl hp2
    · rcases (Nat.dvd_prime
        (by decide : Nat.Prime 3)).mp hp3 with hp1 | hp3
      · exact (hp.ne_one hp1).elim
      · exact Or.inr hp3
  rcases hpvals with rfl | rfl
  · rw [show 6 / 2 = 3 by norm_num, triple_G]
    simp [T]
  · rw [show 6 / 3 = 2 by norm_num, double_G]
    simp [H]

/-- The six visibly distinct torsion points.  No exhaustiveness claim is
made here. -/
def sixVisiblePoints : Fin 6 → curve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => G
  | 3 => Gneg
  | 4 => H
  | 5 => Hneg

theorem sixVisiblePoints_injective :
    Function.Injective sixVisiblePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [sixVisiblePoints, T, G, Gneg, H, Hneg] at hij ⊢
  all_goals norm_num at hij

end MazurTorsion.XOneFourteen
