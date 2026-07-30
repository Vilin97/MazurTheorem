/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.ExceptionalCubicDescent

/-!
# Two-isogeny descent for `X₁(15)`

The genus-one equation

`s² + s t + s = t³ + t²`

is carried by

`U = 4(t+1)`, `V = 4(2s+t+1)`

to the Weierstrass equation

`V² = U(U² - 7U + 16)`.

The associated two-isogenous curve is

`W² = Z(Z² + 14Z - 15)`.

On the original curve, positivity and a gcd-divides-`16` calculation leave
the squareclasses `1` and `2`; the latter is excluded by a primitive
quartic modulo sixteen.  On the dual curve, the eight initial squareclasses
are `±1`, `±3`, `±5`, and `±15`.  Four primitive quartic obstructions leave
the visible classes `1`, `-15`, `5`, and `-3`.

An explicit reverse-doubling calculation handles the first two dual
classes.  Translation by the visible point `(4,4)` exchanges the remaining
two with the first two.  Consequently the rational point group has at most
two cosets modulo doubling.  Naïve-height descent supplies finite
generation, and the exact rational two-torsion cardinality then gives
Mordell--Weil rank zero and finiteness.
-/

namespace MazurTorsion.XOneFifteen

/-- The short Weierstrass model obtained from the standard affine model of
`X₁(15)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨0, -7, 0, 16, 0⟩

/-- The curve two-isogenous to `curve`. -/
def dualCurve : WeierstrassCurve ℚ :=
  ⟨0, 14, 0, -15, 0⟩

private instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private instance dualCurve_isElliptic : dualCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [dualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The affine modular equation is exactly the displayed Weierstrass
equation after the denominator-safe integral change of variables. -/
theorem modular_equation_iff_curve_equation (s t : ℚ) :
    s ^ 2 + s * t + s = t ^ 3 + t ^ 2 ↔
      (4 * (2 * s + t + 1)) ^ 2 =
        (4 * (t + 1)) *
          ((4 * (t + 1)) ^ 2 - 7 * (4 * (t + 1)) + 16) := by
  constructor
  · intro h
    linear_combination 64 * h
  · intro h
    linear_combination (1 / 64 : ℚ) * h

/-- Forward form of the integral change of variables from the affine
`X₁(15)` equation to `curve`. -/
theorem to_curve_equation
    {s t : ℚ} (h : s ^ 2 + s * t + s = t ^ 3 + t ^ 2) :
    (4 * (2 * s + t + 1)) ^ 2 =
      (4 * (t + 1)) *
        ((4 * (t + 1)) ^ 2 - 7 * (4 * (t + 1)) + 16) :=
  (modular_equation_iff_curve_equation s t).mp h

private abbrev redTwo : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

private lemma curve_two_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          2 * m ^ 4 - 7 * m ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  decide

private lemma dual_neg_one_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          -m ^ 4 + 14 * m ^ 2 * n ^ 2 + 15 * n ^ 4 := by
  decide

private lemma dual_three_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          3 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - 5 * n ^ 4 := by
  decide

private lemma dual_neg_five_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          -5 * m ^ 4 + 14 * m ^ 2 * n ^ 2 + 3 * n ^ 4 := by
  decide

private lemma dual_fifteen_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          15 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - n ^ 4 := by
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

/-- The primitive quartic attached to squareclass `2` on `curve` has no
integer point. -/
theorem no_curve_two_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ 2 * m ^ 4 - 7 * m ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  intro h
  apply curve_two_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `-1` on `dualCurve` has
no integer point. -/
theorem no_dual_neg_one_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ -m ^ 4 + 14 * m ^ 2 * n ^ 2 + 15 * n ^ 4 := by
  intro h
  apply dual_neg_one_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `3` on `dualCurve` has
no integer point. -/
theorem no_dual_three_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ 3 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - 5 * n ^ 4 := by
  intro h
  apply dual_three_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `-5` on `dualCurve` has
no integer point. -/
theorem no_dual_neg_five_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ -5 * m ^ 4 + 14 * m ^ 2 * n ^ 2 + 3 * n ^ 4 := by
  intro h
  apply dual_neg_five_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `15` on `dualCurve` has
no integer point. -/
theorem no_dual_fifteen_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ 15 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - n ^ 4 := by
  intro h
  apply dual_fifteen_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

private lemma no_quartic_rat_of_no_int
    (a b c : ℤ)
    (hno :
      ∀ m n w : ℤ, IsCoprime m n →
        w ^ 2 ≠ a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4)
    (z q : ℚ) :
    q ^ 2 ≠ (a : ℚ) * z ^ 4 + (b : ℚ) * z ^ 2 + c := by
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
        (((a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4 : ℤ) : ℚ)) := by
    rw [hz] at h
    field_simp [hn] at h
    calc
      (q * n ^ 2) ^ 2 = q ^ 2 * n ^ 4 := by ring
      _ = (a : ℚ) * (m : ℚ) ^ 4 +
          (b : ℚ) * (m : ℚ) ^ 2 * n ^ 2 +
          (c : ℚ) * n ^ 4 := by nlinarith [h]
      _ =
          (((a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4 : ℤ) : ℚ)) := by
        push_cast
        ring
  have hsquare :
      IsSquare
        (((a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4 : ℤ) : ℚ)) :=
    ⟨q * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨w, hw⟩ := Rat.isSquare_intCast_iff.mp hsquare
  exact hno m n w
    (by simpa [m, n] using Rat.isCoprime_num_den z)
    (by simpa [pow_two] using hw.symm)

/-- Rational denominator-cleared form of `no_curve_two_class`. -/
theorem no_curve_two_class_rat (z q : ℚ) :
    q ^ 2 ≠ 2 * z ^ 4 - 7 * z ^ 2 + 8 := by
  convert
    no_quartic_rat_of_no_int 2 (-7) 8
      (fun m n w h ↦ by
        convert no_curve_two_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

/-- Rational denominator-cleared form of `no_dual_neg_one_class`. -/
theorem no_dual_neg_one_class_rat (z q : ℚ) :
    q ^ 2 ≠ -z ^ 4 + 14 * z ^ 2 + 15 := by
  convert
    no_quartic_rat_of_no_int (-1) 14 15
      (fun m n w h ↦ by
        convert no_dual_neg_one_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

/-- Rational denominator-cleared form of `no_dual_three_class`. -/
theorem no_dual_three_class_rat (z q : ℚ) :
    q ^ 2 ≠ 3 * z ^ 4 + 14 * z ^ 2 - 5 := by
  convert
    no_quartic_rat_of_no_int 3 14 (-5)
      (fun m n w h ↦ by
        convert no_dual_three_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

/-- Rational denominator-cleared form of `no_dual_neg_five_class`. -/
theorem no_dual_neg_five_class_rat (z q : ℚ) :
    q ^ 2 ≠ -5 * z ^ 4 + 14 * z ^ 2 + 3 := by
  simpa using
    no_quartic_rat_of_no_int (-5) 14 3 no_dual_neg_five_class z q

/-- Rational denominator-cleared form of `no_dual_fifteen_class`. -/
theorem no_dual_fifteen_class_rat (z q : ℚ) :
    q ^ 2 ≠ 15 * z ^ 4 + 14 * z ^ 2 - 1 := by
  convert
    no_quartic_rat_of_no_int 15 14 (-1)
      (fun m n w h ↦ by
        convert no_dual_fifteen_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

private lemma common_divisor_dual_dvd_fifteen
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 + 14 * m * n - 15 * n ^ 2) :
    d ∣ 15 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (14 * m - 15 * n) * a, ?_⟩
    linear_combination m * hb - (14 * m - 15 * n) * ha
  have h15n3 : d ∣ 15 * n ^ 3 := by
    refine ⟨(m + 14 * n) * a - n * b, ?_⟩
    linear_combination (m + 14 * n) * ha - n * hb
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h15n3)

private lemma squareclass_of_gcd_dvd_fifteen
    {A B C : ℤ} (hA0 : A ≠ 0) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (15 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨
        A = 3 * z ^ 2 ∨ A = -3 * z ^ 2 ∨
          A = 5 * z ^ 2 ∨ A = -5 * z ^ 2 ∨
            A = 15 * z ^ 2 ∨ A = -15 * z ^ 2 := by
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
  have hgabs : g.natAbs ∣ 15 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hgleNat : g.natAbs ≤ 15 :=
    Nat.le_of_dvd (by norm_num) hgabs
  have hgle : g ≤ 15 := by
    have hgleCast : (g.natAbs : ℤ) ≤ 15 := by
      exact_mod_cast hgleNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
  have hgvals : g = 1 ∨ g = 3 ∨ g = 5 ∨ g = 15 := by
    interval_cases g <;> norm_num at hgabs
    all_goals simp
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcoprime hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    rcases hgvals with hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inl (by simpa using hAz)))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (by simpa using hAz)))))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl (by simpa using hAz)))))))⟩
  · have hAz : A = -(g * z ^ 2) := by rw [← hga, hz]; ring
    rcases hgvals with hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inl (by nlinarith [hAz]))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr
          (Or.inl (by nlinarith [hAz]))))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl (by nlinarith [hAz]))))))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (by nlinarith [hAz])))))))⟩

/-- On the dual curve, every nonzero rational abscissa initially has one
of the eight squareclasses `±1`, `±3`, `±5`, and `±15`. -/
theorem dual_abscissa_squareclass
    {X Y : ℚ} (hX0 : X ≠ 0)
    (hcurve : Y ^ 2 = X * (X ^ 2 + 14 * X - 15)) :
    (∃ z : ℚ, X = z ^ 2) ∨
      (∃ z : ℚ, X = -z ^ 2) ∨
      (∃ z : ℚ, X = 3 * z ^ 2) ∨
      (∃ z : ℚ, X = -3 * z ^ 2) ∨
      (∃ z : ℚ, X = 5 * z ^ 2) ∨
      (∃ z : ℚ, X = -5 * z ^ 2) ∨
      (∃ z : ℚ, X = 15 * z ^ 2) ∨
      (∃ z : ℚ, X = -15 * z ^ 2) := by
  let m : ℤ := X.num
  let n : ℤ := X.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 + 14 * m * n - 15 * n ^ 2
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
          ((m : ℚ) ^ 2 + 14 * m * n - 15 * n ^ 2) := by
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
  have hgcd : GCDMonoid.gcd A B ∣ (15 : ℤ) :=
    common_divisor_dual_dvd_fifteen hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  have lift_squareclass :
      ∀ {d z : ℤ}, A = d * z ^ 2 →
        X = (d : ℚ) * (((z : ℚ) / n) ^ 2) := by
    intro d z hd
    rw [hX]
    simp only [A] at hd
    field_simp [hn]
    exact_mod_cast hd
  obtain ⟨z, hA | hA | hA | hA | hA | hA | hA | hA⟩ :=
    squareclass_of_gcd_dvd_fifteen hA0 hprod hgcd
  · left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := 1) (by simpa using hA)
  · right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -1) (by nlinarith [hA])
  · right; right; left
    exact ⟨(z : ℚ) / n, lift_squareclass hA⟩
  · right; right; right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -3) (by nlinarith [hA])
  · right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift_squareclass hA⟩
  · right; right; right; right; right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -5) (by nlinarith [hA])
  · right; right; right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift_squareclass hA⟩
  · right; right; right; right; right; right; right
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -15) (by nlinarith [hA])

/-- The four locally impossible dual squareclasses are removed.  Thus a
rational point on `dualCurve` has one of the four visible squareclasses
`1`, `-15`, `5`, and `-3`. -/
theorem dual_abscissa_visible_squareclasses
    {X Y : ℚ}
    (hcurve : Y ^ 2 = X * (X ^ 2 + 14 * X - 15)) :
    IsSquare X ∨
      (∃ z : ℚ, X = -15 * z ^ 2) ∨
      (∃ z : ℚ, X = 5 * z ^ 2) ∨
      (∃ z : ℚ, X = -3 * z ^ 2) := by
  rcases eq_or_ne X 0 with rfl | hX0
  · exact Or.inl IsSquare.zero
  rcases dual_abscissa_squareclass hX0 hcurve with
      ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ |
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
    apply no_dual_three_class_rat z (Y / (3 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · right; right; right
    exact ⟨z, hz⟩
  · right; right; left
    exact ⟨z, hz⟩
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hX0 hz
    exfalso
    apply no_dual_neg_five_class_rat z (Y / (5 * z))
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
    apply no_dual_fifteen_class_rat z (Y / (15 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · right; left
    exact ⟨z, hz⟩

private lemma common_divisor_curve_dvd_sixteen
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 - 7 * m * n + 16 * n ^ 2) :
    d ∣ 16 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (-7 * m + 16 * n) * a, ?_⟩
    linear_combination m * hb - (-7 * m + 16 * n) * ha
  have h16n3 : d ∣ 16 * n ^ 3 := by
    refine ⟨n * b - (m - 7 * n) * a, ?_⟩
    linear_combination n * hb - (m - 7 * n) * ha
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h16n3)

private lemma positive_squareclass_of_gcd_dvd_sixteen
    {A B C : ℤ} (hApos : 0 < A) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (16 : ℤ)) :
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
    have hgabs : g.natAbs ∣ 16 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 16 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 16 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 16 := by
        exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals :
        g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 8 ∨ g = 16 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg | hg | hg | hg
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
  · have haNonpos : a ≤ 0 := by nlinarith [sq_nonneg z]
    have hAnonpos : A ≤ 0 := by
      rw [← hga]
      exact mul_nonpos_of_nonneg_of_nonpos hgpos.le haNonpos
    exact (not_lt_of_ge hAnonpos hApos).elim

/-- Before the local obstruction is applied, every nonzero abscissa on
`curve` has squareclass `1` or `2`. -/
theorem curve_abscissa_isSquare_or_two
    {U V : ℚ} (hU0 : U ≠ 0)
    (hcurve : V ^ 2 = U * (U ^ 2 - 7 * U + 16)) :
    IsSquare U ∨ ∃ z : ℚ, U = 2 * z ^ 2 := by
  have hquadratic : 0 < U ^ 2 - 7 * U + 16 := by
    nlinarith [sq_nonneg (2 * U - 7)]
  have hUpos : 0 < U := by
    by_contra! hUnonpos
    have hUneg : U < 0 := lt_of_le_of_ne hUnonpos hU0
    have hnegative : U * (U ^ 2 - 7 * U + 16) < 0 :=
      mul_neg_of_neg_of_pos hUneg hquadratic
    rw [← hcurve] at hnegative
    exact (not_lt_of_ge (sq_nonneg V)) hnegative
  let m : ℤ := U.num
  let n : ℤ := U.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 - 7 * m * n + 16 * n ^ 2
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
          ((m : ℚ) ^ 2 - 7 * m * n + 16 * n ^ 2) := by
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
  have hgcd : GCDMonoid.gcd A B ∣ (16 : ℤ) :=
    common_divisor_curve_dvd_sixteen hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  obtain ⟨z, hA | hA⟩ :=
    positive_squareclass_of_gcd_dvd_sixteen hApos hprod hgcd
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

/-- The nontrivial possible squareclass on the original curve is locally
impossible.  Consequently every rational abscissa on `curve` is a square. -/
theorem curve_abscissa_isSquare
    {U V : ℚ}
    (hcurve : V ^ 2 = U * (U ^ 2 - 7 * U + 16)) :
    IsSquare U := by
  rcases eq_or_ne U 0 with rfl | hU0
  · exact IsSquare.zero
  rcases curve_abscissa_isSquare_or_two hU0 hcurve with
      hUsquare | ⟨z, hU⟩
  · exact hUsquare
  · have hz0 : z ≠ 0 := by
      intro hz
      rw [hz] at hU
      norm_num at hU
      exact hU0 hU
    exfalso
    apply no_curve_two_class_rat z (V / (2 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hU] at hcurve
    nlinarith [hcurve]

private lemma y_linear_of_reverse_definition
    {X Y q v : ℚ} (hq0 : q ≠ 0)
    (hv : v = 7 / 2 + X / 2 - Y / (2 * q)) :
    Y = q * (X + 7 - 2 * v) := by
  field_simp [hq0] at hv
  linear_combination hv

private lemma y_formula_of_reverse_linear
    {X Y q v : ℚ} (hv0 : v ≠ 0)
    (hlinear : Y = q * (X + 7 - 2 * v))
    (hXv : X * v = v ^ 2 - 7 * v + 16) :
    Y = -q * (v ^ 2 - 16) / v := by
  rw [hlinear]
  field_simp [hv0]
  linear_combination q * hXv

private lemma y_formula_squared
    {Y q v : ℚ} (hv0 : v ≠ 0)
    (hY : Y = -q * (v ^ 2 - 16) / v) :
    Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 - 16) ^ 2 := by
  rw [hY]
  field_simp [hv0]

private theorem double_of_chosen_square_dual_abscissa
    {U V s τ X q : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = s ^ 2)
    (hτ : τ ^ 2 = U ^ 2 - 7 * U + 16)
    (hXdef : X = 2 * U - 7 - 2 * τ)
    (hX0 : X ≠ 0) (hXq : X = q ^ 2) :
    ∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hU
    norm_num at hU
    exact hU0 hU
  let Y : ℚ := 2 * s * X
  have hfactor :
      X ^ 2 + 14 * X - 15 = 4 * U * X := by
    rw [hXdef]
    nlinarith [hτ]
  have hdual :
      Y ^ 2 = X * (X ^ 2 + 14 * X - 15) := by
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
      (Y / q) ^ 2 = X ^ 2 + 14 * X - 15 := by
    rw [div_pow]
    field_simp [hq0]
    nlinarith [hdual, hXq]
  let v : ℚ := 7 / 2 + X / 2 - Y / (2 * q)
  let w : ℚ := q * v
  have hvdef : v = 7 / 2 + X / 2 - Y / (2 * q) := rfl
  have hwdef : w = q * v := rfl
  have hXv : X * v = v ^ 2 - 7 * v + 16 := by
    dsimp [v]
    field_simp [hq0] at hYq ⊢
    nlinarith [hYq, hXq]
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv] at hXv
    norm_num at hXv
  have hw0 : w ≠ 0 :=
    mul_ne_zero hq0 hv0
  have hcurveQ : w ^ 2 = v * (v ^ 2 - 7 * v + 16) := by
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
        (3 * v ^ 2 - 14 * v + 16) / (2 * w) := by
    simp [WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve, hwneneg]
    ring
  have haddX :
      curve.toAffine.addX v v
          (curve.toAffine.slope v v w w) =
        (v ^ 2 - 16) ^ 2 / (4 * w ^ 2) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hw0]
    rw [hcurveQ]
    ring
  have hYformula :
      Y = -q * (v ^ 2 - 16) / v :=
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
          q ^ 2 * (v ^ 2 - 16) ^ 2 :=
      y_formula_squared hv0 hYformula
    have hcancel :
        q ^ 2 * (v ^ 2 - 16) ^ 2 =
          q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
      calc
        q ^ 2 * (v ^ 2 - 16) ^ 2 =
            Y ^ 2 * v ^ 2 := hYformulaCleared.symm
        _ = q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
          rw [hYsq, hXq]
          ring
    have htarget :
        (v ^ 2 - 16) ^ 2 = 4 * w ^ 2 * U := by
      have hcancelled :=
        mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      calc
        (v ^ 2 - 16) ^ 2 =
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

private theorem double_of_direct_auxiliary_class
    {U V s τ X : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = s ^ 2)
    (hτ : τ ^ 2 = U ^ 2 - 7 * U + 16)
    (hXdef : X = 2 * U - 7 - 2 * τ)
    (hX0 : X ≠ 0)
    (hclass : IsSquare X ∨ ∃ z : ℚ, X = -15 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  rcases hclass with hXsquare | ⟨z, hz⟩
  · obtain ⟨q, hq⟩ := hXsquare
    exact
      double_of_chosen_square_dual_abscissa hU0 hP hU hτ hXdef hX0
        (by simpa [pow_two] using hq)
  · have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0] at hz
      norm_num at hz
      exact hX0 hz
    let X₁ : ℚ := 2 * U - 7 + 2 * τ
    have hprod : X * X₁ = -15 := by
      rw [hXdef]
      dsimp [X₁]
      nlinarith [hτ]
    have hX₁square : X₁ = (1 / z) ^ 2 := by
      rw [hz] at hprod
      field_simp [hz0]
      nlinarith [hprod]
    have hX₁0 : X₁ ≠ 0 := by
      rw [hX₁square]
      exact pow_ne_zero 2 (div_ne_zero (by norm_num) hz0)
    apply
      double_of_chosen_square_dual_abscissa hU0 hP hU
        (τ := -τ) (X := X₁) (q := 1 / z)
    · nlinarith [hτ]
    · dsimp [X₁]
      ring
    · exact hX₁0
    · exact hX₁square

/-- For a nonzero affine point, the explicit reverse-doubling construction
either succeeds, or produces one of the two exceptional auxiliary dual
squareclasses `5` and `-3`.  These are precisely the two cases exchanged
by translation by the visible order-four point `(4,4)`. -/
theorem doubling_or_exceptional_auxiliary_squareclass
    {U V : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V) :
    (∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP) ∨
      ∃ s t X z : ℚ,
        U = s ^ 2 ∧ t = V / s ∧
          X = 2 * U - 7 - 2 * t ∧
            (X = 5 * z ^ 2 ∨ X = -3 * z ^ 2) := by
  have hcurve : V ^ 2 = U * (U ^ 2 - 7 * U + 16) := by
    have heq := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    norm_num [curve] at heq
    nlinarith
  obtain ⟨s, hs⟩ := curve_abscissa_isSquare hcurve
  have hU : U = s ^ 2 := by
    simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hU
    norm_num at hU
    exact hU0 hU
  let t : ℚ := V / s
  have ht : t ^ 2 = U ^ 2 - 7 * U + 16 := by
    dsimp [t]
    rw [div_pow]
    field_simp [hs0]
    nlinarith [hcurve, hU]
  let X₀ : ℚ := 2 * U - 7 - 2 * t
  let X₁ : ℚ := 2 * U - 7 + 2 * t
  have hXprod : X₀ * X₁ = -15 := by
    dsimp [X₀, X₁]
    nlinarith [ht]
  have hX₀0 : X₀ ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  let Y₀ : ℚ := 2 * s * X₀
  have hdualFactor :
      X₀ ^ 2 + 14 * X₀ - 15 = 4 * U * X₀ := by
    dsimp [X₀]
    nlinarith [ht]
  have hdual :
      Y₀ ^ 2 = X₀ * (X₀ ^ 2 + 14 * X₀ - 15) := by
    rw [hdualFactor]
    dsimp [Y₀]
    rw [hU]
    ring
  rcases dual_abscissa_visible_squareclasses hdual with
      hXsquare | ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨q, hq⟩ := hXsquare
    left
    exact
      double_of_chosen_square_dual_abscissa hU0 hP hU ht rfl hX₀0
        (by simpa [pow_two] using hq)
  · have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0] at hz
      norm_num at hz
      exact hX₀0 hz
    have hX₁square : X₁ = (1 / z) ^ 2 := by
      rw [hz] at hXprod
      field_simp [hz0]
      nlinarith [hXprod]
    have hX₁0 : X₁ ≠ 0 := by
      rw [hX₁square]
      exact pow_ne_zero 2 (div_ne_zero (by norm_num) hz0)
    left
    apply
      double_of_chosen_square_dual_abscissa hU0 hP hU
        (τ := -t) (X := X₁) (q := 1 / z)
    · nlinarith [ht]
    · dsimp [X₁]
      ring
    · exact hX₁0
    · exact hX₁square
  · right
    exact ⟨s, t, X₀, z, hU, rfl, rfl, Or.inl hz⟩
  · right
    exact ⟨s, t, X₀, z, hU, rfl, rfl, Or.inr hz⟩

private lemma nonsingular_zero_zero :
    curve.toAffine.Nonsingular 0 0 := by
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

/-- The rational two-torsion point `(0,0)`. -/
def T : curve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

/-- The visible order-four point `(4,4)`. -/
def G : curve.toAffine.Point :=
  .some 4 4 nonsingular_four_four

private lemma double_G : (2 : ℕ) • G = T := by
  simp only [two_nsmul, G]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (by norm_num [WeierstrassCurve.Affine.negY, curve])]
  rw [T]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve]

private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private lemma four_G : (4 : ℕ) • G = 0 := by
  calc
    (4 : ℕ) • G = (2 : ℕ) • ((2 : ℕ) • G) := by
      norm_num [← mul_nsmul]
    _ = (2 : ℕ) • T := by rw [double_G]
    _ = 0 := double_T

private lemma translated_x_identity
    {U V s t : ℚ} (hU : U = s ^ 2) (hV : V = s * t)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4) :
    ((V + 4) / (U - 4)) ^ 2 + 7 - U - 4 =
      (2 * (t + s) / (U - 4)) ^ 2 := by
  rw [hU] at ht hUfour ⊢
  rw [hV]
  field_simp [hUfour]
  linear_combination (s ^ 2 - 4) * ht

private lemma translated_y_identity
    {U V s t : ℚ} (hU : U = s ^ 2) (hV : V = s * t)
    (hUfour : U ≠ 4) :
    -((V + 4) / (U - 4) *
          ((2 * (t + s) / (U - 4)) ^ 2 - U) + V) =
      (2 * (t + s) / (U - 4)) *
        (2 *
          (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
            (U - 4) ^ 2) := by
  rw [hU] at hUfour ⊢
  rw [hV]
  field_simp [hUfour]
  ring

private lemma translated_t_square
    {U s t : ℚ} (hU : U = s ^ 2)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4) :
    (2 *
        (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
          (U - 4) ^ 2) ^ 2 =
      (2 * (t + s) / (U - 4)) ^ 4 -
        7 * (2 * (t + s) / (U - 4)) ^ 2 + 16 := by
  rw [hU] at ht hUfour ⊢
  field_simp [hUfour]
  linear_combination
    -4 * (s ^ 2 - s - t - 4) * (s ^ 2 + s + t - 4) *
      (s ^ 2 - 4) * ht

private lemma translated_auxiliary_identity
    {U s t : ℚ} (hU : U = s ^ 2)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4) :
    2 * (2 * (t + s) / (U - 4)) ^ 2 - 7 -
        2 *
          (2 *
            (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
              (U - 4) ^ 2) =
      (s ^ 2 + 4 * t + 4) / (s - 2) ^ 2 := by
  have hsminus : s - 2 ≠ 0 := by
    intro hs
    apply hUfour
    rw [hU]
    nlinarith
  rw [hU] at ht hUfour ⊢
  field_simp [hUfour, hsminus]
  linear_combination 4 * (s + 2) * (s - 2) ^ 2 * ht

private lemma translated_auxiliary_product
    {U s t X₁ : ℚ} (hU : U = s ^ 2)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hX₁ : X₁ = 2 * U - 7 + 2 * t) :
    (s ^ 2 + 4 * t + 4) * X₁ =
      5 * (t + s ^ 2 - 2) ^ 2 := by
  rw [hU] at ht hX₁
  rw [hX₁]
  nlinarith [ht]

private theorem exceptional_auxiliary_translate_double
    {U V s t z : ℚ}
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = s ^ 2) (hV : V = s * t)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4)
    (hcase :
      2 * U - 7 - 2 * t = 5 * z ^ 2 ∨
        2 * U - 7 - 2 * t = -3 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      WeierstrassCurve.Affine.Point.some U V hP =
        G + (2 : ℕ) • Q := by
  let sr : ℚ := 2 * (t + s) / (U - 4)
  let tr : ℚ :=
    2 * (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
      (U - 4) ^ 2
  let ur : ℚ := sr ^ 2
  let vr : ℚ := sr * tr
  have htr : tr ^ 2 = ur ^ 2 - 7 * ur + 16 := by
    dsimp [tr, ur, sr]
    convert translated_t_square hU ht hUfour using 1
    all_goals ring
  have hcurveR : vr ^ 2 = ur * (ur ^ 2 - 7 * ur + 16) := by
    calc
      vr ^ 2 = ur * tr ^ 2 := by dsimp [vr, ur]; ring
      _ = ur * (ur ^ 2 - 7 * ur + 16) := by rw [htr]
  have hR : curve.toAffine.Nonsingular ur vr := by
    apply curve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve]
    linear_combination hcurveR
  let R : curve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some ur vr hR
  have hslope :
      curve.toAffine.slope U 4 V (-4) = (V + 4) / (U - 4) := by
    simp [WeierstrassCurve.Affine.slope, hUfour]
  have haddX :
      curve.toAffine.addX U 4
          (curve.toAffine.slope U 4 V (-4)) = ur := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    dsimp [ur, sr]
    exact translated_x_identity hU hV ht hUfour
  have haddY :
      curve.toAffine.addY U 4 V
          (curve.toAffine.slope U 4 V (-4)) = vr := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY]
    norm_num [curve]
    rw [translated_x_identity hU hV ht hUfour]
    dsimp [vr, sr, tr]
    convert translated_y_identity hU hV hUfour using 1
    all_goals ring
  have hnegG :
      -G =
        WeierstrassCurve.Affine.Point.some
          4 (-4) nonsingular_four_neg_four := by
    rw [G, WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    norm_num [WeierstrassCurve.Affine.negY, curve]
  have hsub :
      WeierstrassCurve.Affine.Point.some U V hP - G = R := by
    rw [sub_eq_add_neg, hnegG]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hUfour]
    dsimp [R]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨haddX, haddY⟩
  have hsum0 : t + s ≠ 0 := by
    intro hsum
    have htneg : t = -s := by linarith
    have hsquare : (s ^ 2 - 4) ^ 2 = 0 := by
      rw [htneg, hU] at ht
      nlinarith [ht]
    have hsvalue : s ^ 2 - 4 = 0 :=
      sq_eq_zero_iff.mp hsquare
    apply hUfour
    rw [hU]
    linarith
  have hsr0 : sr ≠ 0 := by
    dsimp [sr]
    exact div_ne_zero
      (mul_ne_zero (by norm_num) hsum0)
      (sub_ne_zero.mpr hUfour)
  have hur0 : ur ≠ 0 := by
    dsimp [ur]
    exact pow_ne_zero 2 hsr0
  let X₀ : ℚ := 2 * U - 7 - 2 * t
  let X₁ : ℚ := 2 * U - 7 + 2 * t
  have hXprod : X₀ * X₁ = -15 := by
    dsimp [X₀, X₁]
    nlinarith [ht]
  have hX₀0 : X₀ ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  have hsminus : s - 2 ≠ 0 := by
    intro hs
    apply hUfour
    rw [hU]
    nlinarith
  let Xr : ℚ := 2 * ur - 7 - 2 * tr
  let Xr₁ : ℚ := 2 * ur - 7 + 2 * tr
  have hXrprod : Xr * Xr₁ = -15 := by
    dsimp [Xr, Xr₁]
    nlinarith [htr]
  have hXr0 : Xr ≠ 0 := by
    intro h
    rw [h] at hXrprod
    norm_num at hXrprod
  have hXrformula :
      Xr = (s ^ 2 + 4 * t + 4) / (s - 2) ^ 2 := by
    dsimp [Xr, ur, sr, tr]
    exact translated_auxiliary_identity hU ht hUfour
  have hauxprod :
      (s ^ 2 + 4 * t + 4) * X₁ =
        5 * (t + s ^ 2 - 2) ^ 2 :=
    translated_auxiliary_product hU ht rfl
  have hdirect :
      IsSquare Xr ∨ ∃ q : ℚ, Xr = -15 * q ^ 2 := by
    rcases hcase with hfive | hnegthree
    · have hz0 : z ≠ 0 := by
        intro hz
        rw [hz] at hfive
        norm_num at hfive
        exact hX₀0 (by simpa [X₀] using hfive)
      have hX₁eq : X₁ = -3 / z ^ 2 := by
        rw [show X₀ = 5 * z ^ 2 by simpa [X₀] using hfive] at hXprod
        field_simp [hz0]
        linear_combination (1 / 5 : ℚ) * hXprod
      have hnumerator :
          3 * (s ^ 2 + 4 * t + 4) =
            -5 * z ^ 2 * (t + s ^ 2 - 2) ^ 2 := by
        rw [hX₁eq] at hauxprod
        field_simp [hz0] at hauxprod
        linear_combination -hauxprod
      right
      refine
        ⟨z * (t + s ^ 2 - 2) / (3 * (s - 2)), ?_⟩
      rw [hXrformula]
      field_simp [hsminus]
      linear_combination 3 * hnumerator
    · have hz0 : z ≠ 0 := by
        intro hz
        rw [hz] at hnegthree
        norm_num at hnegthree
        exact hX₀0 (by simpa [X₀] using hnegthree)
      have hX₁eq : X₁ = 5 / z ^ 2 := by
        rw [show X₀ = -3 * z ^ 2 by simpa [X₀] using hnegthree] at hXprod
        field_simp [hz0]
        linear_combination (-1 / 3 : ℚ) * hXprod
      have hnumerator :
          s ^ 2 + 4 * t + 4 =
            z ^ 2 * (t + s ^ 2 - 2) ^ 2 := by
        rw [hX₁eq] at hauxprod
        field_simp [hz0] at hauxprod
        linear_combination hauxprod
      left
      refine
        ⟨z * (t + s ^ 2 - 2) / (s - 2), ?_⟩
      rw [hXrformula]
      field_simp [hsminus]
      linear_combination hnumerator
  obtain ⟨Q, hQ⟩ :=
    double_of_direct_auxiliary_class hur0 hR rfl htr rfl hXr0 hdirect
  refine ⟨Q, ?_⟩
  calc
    WeierstrassCurve.Affine.Point.some U V hP =
        G + (WeierstrassCurve.Affine.Point.some U V hP - G) := by
          abel
    _ = G + R := by rw [hsub]
    _ = G + (2 : ℕ) • Q := by rw [hQ]

private lemma curve_equation_of_nonsingular
    {U V : ℚ} (hP : curve.toAffine.Nonsingular U V) :
    V ^ 2 = U * (U ^ 2 - 7 * U + 16) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [curve] at heq
  nlinarith

/-- Every rational point lies in one of the two cosets represented by the
identity and the visible order-four point `(4,4)`, modulo doubling. -/
theorem two_doubling_cosets (P : curve.toAffine.Point) :
    (∃ Q : curve.toAffine.Point, P = (2 : ℕ) • Q) ∨
      (∃ Q : curve.toAffine.Point, P = G + (2 : ℕ) • Q) := by
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
        left
        refine ⟨G, ?_⟩
        simpa [T] using double_G.symm
      · rcases eq_or_ne U 4 with rfl | hUfour
        · have hVsquare : V ^ 2 = (4 : ℚ) ^ 2 := by
            norm_num at hcurve ⊢
            exact hcurve
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hVsquare with hV | hV
          · subst V
            right
            exact ⟨0, by simp [G]⟩
          · have hV' : V = -4 := by simpa using hV
            subst V
            have hpointneg :
                WeierstrassCurve.Affine.Point.some 4 (-4) hP = -G := by
              rw [G, WeierstrassCurve.Affine.Point.neg_some]
              simp only [WeierstrassCurve.Affine.Point.some.injEq]
              norm_num [WeierstrassCurve.Affine.negY, curve]
            have hthree : G + (2 : ℕ) • G = -G := by
              rw [eq_neg_iff_add_eq_zero]
              calc
                G + (2 : ℕ) • G + G = (4 : ℕ) • G := by abel
                _ = 0 := four_G
            right
            exact ⟨G, hpointneg.trans hthree.symm⟩
        · rcases doubling_or_exceptional_auxiliary_squareclass hU0 hP with
            ⟨Q, hQ⟩ | ⟨s, t, X, z, hU, htdef, hXdef, hcase⟩
          · left
            exact ⟨Q, hQ.symm⟩
          · have hs0 : s ≠ 0 := by
              intro hs
              rw [hs] at hU
              norm_num at hU
              exact hU0 hU
            have hV : V = s * t := by
              rw [htdef]
              field_simp [hs0]
            have ht : t ^ 2 = U ^ 2 - 7 * U + 16 := by
              rw [htdef, div_pow]
              field_simp [hs0]
              nlinarith [hcurve, hU]
            have hcase' :
                2 * U - 7 - 2 * t = 5 * z ^ 2 ∨
                  2 * U - 7 - 2 * t = -3 * z ^ 2 := by
              rw [← hXdef]
              exact hcase
            right
            exact
              exceptional_auxiliary_translate_double hP hU hV ht hUfour hcase'

/-- The image of multiplication by two on the rational point group. -/
abbrev doublingRange : AddSubgroup curve.toAffine.Point :=
  (nsmulAddMonoidHom (α := curve.toAffine.Point) 2).range

private def doublingRepresentative : Fin 2 → curve.toAffine.Point
  | 0 => 0
  | 1 => G

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

/-- Multiplication by two has finite index on the rational point group. -/
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
      have hquadratic : 0 < U ^ 2 - 7 * U + 16 := by
        nlinarith [sq_nonneg (2 * U - 7)]
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

end MazurTorsion.XOneFifteen
