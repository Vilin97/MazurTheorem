/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XZeroTwentyOneDescent
import MazurTorsion.NumberTheory.RatNorthcott
import MazurTorsion.Foundations.NaiveHeightDescent
import MazurTorsion.Foundations.TwoTorsion
import MazurTorsion.GroupTheory.IndexNSmulFG
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Rank zero for the split `X₀(21)` model

`XZeroTwentyOneDescent` reduces the abscissa classification on

`W² = V(V - 9)(V + 7)`

to two quartic leaves.  This file replaces those leaves by a complete
two-isogeny descent.  The two-isogenous curve is

`Y² = X(X² + 4X + 256)`,

and every nonzero rational abscissa on it is a rational square: the
negative squareclasses are impossible by positivity, and the squareclass
`2` dies by an explicit two-adic descent.  Consequently a rational point of
the split model whose abscissa is a square is divisible by two, by the same
explicit reverse-doubling calculation as on the `X₁(14)` model.

The four surviving squareclasses `1`, `-3`, `-7`, `21` then produce four
explicit doubling cosets with representatives

`0`, `(0,0)`, `(-3,12)`, `(21,84)`.

Since the model has full rational two-torsion, the finitely generated index
formula forces Mordell--Weil rank zero, and the rational point group is
finite.
-/

namespace MazurTorsion.XZeroTwentyOne

/-! ## The affine equation and its nonsingular points -/

lemma fullTwoCurve_equation_of_nonsingular
    {U V : ℚ} (hP : fullTwoCurve.toAffine.Nonsingular U V) :
    V ^ 2 = U * (U ^ 2 - 2 * U - 63) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [fullTwoCurve] at heq
  nlinarith [heq]

lemma onFullTwoCurve_of_nonsingular
    {U V : ℚ} (hP : fullTwoCurve.toAffine.Nonsingular U V) :
    OnFullTwoCurve U V := by
  have h := fullTwoCurve_equation_of_nonsingular hP
  unfold OnFullTwoCurve
  linear_combination h

lemma nonsingular_of_onFullTwoCurve
    {U V : ℚ} (h : OnFullTwoCurve U V) :
    fullTwoCurve.toAffine.Nonsingular U V := by
  apply fullTwoCurve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold OnFullTwoCurve at h
  norm_num [fullTwoCurve]
  linear_combination h

/-! ## The squareclass `2` on the dual curve is impossible

The dual curve is `Y² = X(X² + 4X + 256)`.  An abscissa `X = 2z²` leads,
after clearing denominators, to the primitive integral equation
`c² = 2(m⁴ + 2m²n² + 64n⁴)`, which dies by a short two-adic descent. -/

private abbrev reduceTwoOfFour : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

private lemma odd_leaf_obstruction :
    ∀ μ n c : ZMod 4,
      reduceTwoOfFour μ ≠ 0 → reduceTwoOfFour n ≠ 0 →
      c ^ 2 ≠ 2 * μ ^ 4 + μ ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  decide

private lemma even_leaf_obstruction :
    ∀ ν n c : ZMod 4,
      reduceTwoOfFour n ≠ 0 →
      c ^ 2 ≠ 8 * ν ^ 4 + ν ^ 2 * n ^ 2 + 2 * n ^ 4 := by
  decide

private lemma intCast_reduceTwoOfFour_ne_zero
    {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    reduceTwoOfFour (m : ZMod 4) ≠ 0 := by
  intro h
  apply hm
  have : ((m : ZMod 2) : ZMod 2) = 0 := by
    simpa [reduceTwoOfFour] using h
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this

private lemma two_dvd_of_two_dvd_sq {c : ℤ} (h : (2 : ℤ) ∣ c ^ 2) :
    (2 : ℤ) ∣ c :=
  (Int.Prime.dvd_pow' (by norm_num) h)

/-- The primitive integral quartic attached to the dual squareclass `2`
has no solution. -/
private lemma no_dual_two_class_int
    {m n c : ℤ} (hmn : IsCoprime m n) :
    c ^ 2 ≠ 2 * (m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4) := by
  intro hc
  have hc2 : (2 : ℤ) ∣ c := by
    apply two_dvd_of_two_dvd_sq
    exact ⟨m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4, hc⟩
  obtain ⟨c₁, rfl⟩ := hc2
  have hc₁ : 2 * c₁ ^ 2 = m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4 := by
    nlinarith [hc]
  have hm2 : (2 : ℤ) ∣ m := by
    by_contra hodd
    have h1 : (m : ZMod 4) ^ 4 + 2 * (m : ZMod 4) ^ 2 * (n : ZMod 4) ^ 2 +
        64 * (n : ZMod 4) ^ 4 = 2 * (c₁ : ZMod 4) ^ 2 := by
      have := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hc₁
      push_cast at this
      linear_combination -this
    have hmu : reduceTwoOfFour (m : ZMod 4) ≠ 0 :=
      intCast_reduceTwoOfFour_ne_zero hodd
    -- modulo four the equation forces `2c₁² = m⁴ + 2m²n²`, odd `m` gives
    -- `2 ∈ {c² - stuff}`, impossible; we discharge by a small decision.
    revert h1
    have : ∀ M N C : ZMod 4, reduceTwoOfFour M ≠ 0 →
        M ^ 4 + 2 * M ^ 2 * N ^ 2 + 64 * N ^ 4 ≠ 2 * C ^ 2 := by
      decide
    exact this _ _ _ hmu
  obtain ⟨μ, rfl⟩ := hm2
  have hn_odd : ¬ (2 : ℤ) ∣ n := by
    intro hn
    have : IsUnit (2 : ℤ) := hmn.isUnit_of_dvd' ⟨μ, rfl⟩ hn
    norm_num [Int.isUnit_iff] at this
  have hc₂eq : c₁ ^ 2 = 8 * μ ^ 4 + 4 * μ ^ 2 * n ^ 2 + 32 * n ^ 4 := by
    nlinarith [hc₁]
  have hc₁2 : (2 : ℤ) ∣ c₁ := by
    apply two_dvd_of_two_dvd_sq
    exact ⟨4 * μ ^ 4 + 2 * μ ^ 2 * n ^ 2 + 16 * n ^ 4, by linarith [hc₂eq]⟩
  obtain ⟨c₂, rfl⟩ := hc₁2
  have hc₂ : c₂ ^ 2 = 2 * μ ^ 4 + μ ^ 2 * n ^ 2 + 8 * n ^ 4 := by
    nlinarith [hc₂eq]
  by_cases hμ : (2 : ℤ) ∣ μ
  · obtain ⟨ν, rfl⟩ := hμ
    have hc₃eq : c₂ ^ 2 = 32 * ν ^ 4 + 4 * ν ^ 2 * n ^ 2 + 8 * n ^ 4 := by
      nlinarith [hc₂]
    have hc₂2 : (2 : ℤ) ∣ c₂ := by
      apply two_dvd_of_two_dvd_sq
      exact ⟨16 * ν ^ 4 + 2 * ν ^ 2 * n ^ 2 + 4 * n ^ 4, by linarith [hc₃eq]⟩
    obtain ⟨c₃, rfl⟩ := hc₂2
    have hc₃ : c₃ ^ 2 = 8 * ν ^ 4 + ν ^ 2 * n ^ 2 + 2 * n ^ 4 := by
      nlinarith [hc₃eq]
    apply even_leaf_obstruction (ν : ZMod 4) (n : ZMod 4) (c₃ : ZMod 4)
      (intCast_reduceTwoOfFour_ne_zero hn_odd)
    have := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hc₃
    push_cast at this
    linear_combination this
  · apply odd_leaf_obstruction (μ : ZMod 4) (n : ZMod 4) (c₂ : ZMod 4)
      (intCast_reduceTwoOfFour_ne_zero hμ)
      (intCast_reduceTwoOfFour_ne_zero hn_odd)
    have := congrArg (fun z : ℤ ↦ (z : ZMod 4)) hc₂
    push_cast at this
    linear_combination this

/-- The rational quartic attached to the dual squareclass `2` has no
solution. -/
private lemma no_dual_two_class_rat (z q : ℚ) :
    q ^ 2 ≠ 2 * (z ^ 4 + 2 * z ^ 2 + 64) := by
  intro hq
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / (n : ℚ) := z.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den z
  have hscaled :
      (q * (n : ℚ) ^ 2) ^ 2 =
        ((2 * (m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4) : ℤ) : ℚ) := by
    rw [hz] at hq
    push_cast
    field_simp at hq
    nlinarith [hq]
  have hsq :
      IsSquare ((2 * (m ^ 4 + 2 * m ^ 2 * n ^ 2 + 64 * n ^ 4) : ℤ) : ℚ) :=
    ⟨q * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hc⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact no_dual_two_class_int hmn (by simpa [pow_two] using hc.symm)

/-! ## Every nonzero dual abscissa is a square -/

private lemma common_divisor_dual_dvd_256
    {m n d : ℤ} (hmn : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 + 4 * m * n + 256 * n ^ 2) :
    d ∣ 256 := by
  have hm3 : d ∣ m ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨m * b - (4 * m + 256 * n) * a, ?_⟩
    linear_combination m * hb - (4 * m + 256 * n) * ha
  have h256n3 : d ∣ 256 * n ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨n * b - (m + 4 * n) * a, ?_⟩
    linear_combination n * hb - (m + 4 * n) * ha
  have hd_coprime_n3 : IsCoprime d (n ^ 3) :=
    hmn.pow.of_isCoprime_of_dvd_left hm3
  exact hd_coprime_n3.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h256n3)

/-- A nonzero factor of a square whose gcd with the cofactor divides `256`
has squareclass `±1` or `±2`. -/
private lemma squareclass_of_gcd_dvd_256
    {A B C : ℤ} (hA : A ≠ 0) (hAB : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (256 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨
      A = 2 * z ^ 2 ∨ A = -(2 * z ^ 2) := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz] at hgA
    exact hA (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hAB] using mul_dvd_mul hgA hgB
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
      _ = C ^ 2 := hAB
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcop : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hdivNat : g.natAbs ∣ 256 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hdivNat' : g.natAbs ∣ 2 ^ 8 := by
    have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
    rwa [h256] at hdivNat
  obtain ⟨k, hk_le, hk⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdivNat'
  have hgk : g = 2 ^ k := by
    have : (g.natAbs : ℤ) = ((2 : ℕ) ^ k : ℕ) := by exact_mod_cast hk
    rw [Int.natCast_natAbs, abs_of_pos hgpos] at this
    simpa using this
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcop hab
  · -- `A = g z²` with `g = 2^k`
    have hAz : A = 2 ^ k * z ^ 2 := by rw [← hga, hz, hgk]
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨2 ^ j * z, Or.inl ?_⟩
      rw [hAz, hj]
      ring
    · refine ⟨2 ^ j * z, Or.inr (Or.inr (Or.inl ?_))⟩
      rw [hAz, hj]
      ring
  · have hAz : A = -(2 ^ k * z ^ 2) := by rw [← hga, hz, hgk]; ring
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨2 ^ j * z, Or.inr (Or.inl ?_)⟩
      rw [hAz, hj]
      ring
    · refine ⟨2 ^ j * z, Or.inr (Or.inr (Or.inr ?_))⟩
      rw [hAz, hj]
      ring

/-- On the two-isogenous curve `Y² = X(X² + 4X + 256)`, every nonzero
rational abscissa is a square. -/
theorem dual_abscissa_isSquare
    {X Y : ℚ} (hX0 : X ≠ 0)
    (hdual : Y ^ 2 = X * (X ^ 2 + 4 * X + 256)) :
    IsSquare X := by
  -- positivity: a negative abscissa is impossible
  have hXpos : 0 < X := by
    rcases lt_or_gt_of_ne hX0 with hneg | hpos
    · exfalso
      nlinarith [sq_nonneg Y, sq_nonneg (X + 2), hdual]
    · exact hpos
  -- clear denominators
  let m : ℤ := X.num
  let n : ℤ := X.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hX : X = (m : ℚ) / (n : ℚ) := X.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den X
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact Rat.num_ne_zero.mpr hX0
  have hscaled :
      (Y * (n : ℚ) ^ 2) ^ 2 =
        (((m * n) * (m ^ 2 + 4 * m * n + 256 * n ^ 2) : ℤ) : ℚ) := by
    rw [hX] at hdual
    push_cast
    field_simp at hdual
    linear_combination (n : ℚ) * hdual
  have hsq :
      IsSquare
        (((m * n) * (m ^ 2 + 4 * m * n + 256 * n ^ 2) : ℤ) : ℚ) :=
    ⟨Y * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hAB : (m * n) * (m ^ 2 + 4 * m * n + 256 * n ^ 2) = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : m * n ≠ 0 := by
    apply mul_ne_zero hm0
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hgcd : GCDMonoid.gcd (m * n) (m ^ 2 + 4 * m * n + 256 * n ^ 2) ∣
      (256 : ℤ) :=
    common_divisor_dual_dvd_256 hmn
      (GCDMonoid.gcd_dvd_left _ _)
      (GCDMonoid.gcd_dvd_right _ _)
  obtain ⟨z, hz | hz | hz | hz⟩ :=
    squareclass_of_gcd_dvd_256 hA0 hAB hgcd
  · -- squareclass 1: `X = (z/n)²`
    refine ⟨(z : ℚ) / (n : ℚ), ?_⟩
    rw [hX]
    have hzQ : ((m : ℚ) * n) = (z : ℚ) ^ 2 := by exact_mod_cast hz
    field_simp
    nlinarith [hzQ]
  · -- squareclass -1 contradicts positivity
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hz2 : 0 < z ^ 2 :=
      lt_of_le_of_ne (sq_nonneg z) (Ne.symm (pow_ne_zero 2 hz0))
    have hmnneg : m * n < 0 := by
      rw [hz]
      linarith
    have hnposZ : (0 : ℤ) < n := by
      dsimp [n]
      exact_mod_cast X.den_pos
    have hmneg : m < 0 := by nlinarith [hmnneg, hnposZ]
    have hXneg : X < 0 := by
      rw [hX]
      apply div_neg_of_neg_of_pos
      · exact_mod_cast hmneg
      · exact_mod_cast hnposZ
    linarith
  · -- squareclass 2 dies by the two-adic quartic
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hXval : X = 2 * ((z : ℚ) / n) ^ 2 := by
      rw [hX]
      have hzQ : ((m : ℚ) * n) = 2 * (z : ℚ) ^ 2 := by exact_mod_cast hz
      field_simp
      nlinarith [hzQ]
    have hr0 : ((z : ℚ) / n) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hz0) hn0
    set r : ℚ := (z : ℚ) / n with hrdef
    have hq : (Y / (2 * r)) ^ 2 = 2 * (r ^ 4 + 2 * r ^ 2 + 64) := by
      rw [div_pow]
      rw [hXval] at hdual
      field_simp [hr0]
      nlinarith [hdual]
    exact no_dual_two_class_rat r (Y / (2 * r)) hq
  · -- squareclass -2 contradicts positivity
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hz2 : 0 < z ^ 2 :=
      lt_of_le_of_ne (sq_nonneg z) (Ne.symm (pow_ne_zero 2 hz0))
    have hmnneg : m * n < 0 := by
      rw [hz]
      linarith
    have hnposZ : (0 : ℤ) < n := by
      dsimp [n]
      exact_mod_cast X.den_pos
    have hmneg : m < 0 := by nlinarith [hmnneg, hnposZ]
    have hXneg : X < 0 := by
      rw [hX]
      apply div_neg_of_neg_of_pos
      · exact_mod_cast hmneg
      · exact_mod_cast hnposZ
    linarith

/-! ## Reverse doubling from a square abscissa -/

private lemma y_linear_of_reverse_definition
    {X Y q v : ℚ} (hq0 : q ≠ 0)
    (hv : v = 1 + X / 2 - Y / (2 * q)) :
    Y = q * (X + 2 - 2 * v) := by
  field_simp [hq0] at hv
  linear_combination hv

private lemma y_formula_of_reverse_linear
    {X Y q v : ℚ} (hv0 : v ≠ 0)
    (hlinear : Y = q * (X + 2 - 2 * v))
    (hXv : X * v = v ^ 2 - 2 * v - 63) :
    Y = -q * (v ^ 2 + 63) / v := by
  rw [hlinear]
  field_simp [hv0]
  linear_combination q * hXv

private lemma y_formula_squared
    {Y q v : ℚ} (hv0 : v ≠ 0)
    (hY : Y = -q * (v ^ 2 + 63) / v) :
    Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 + 63) ^ 2 := by
  rw [hY]
  field_simp [hv0]

/-- A nonzero rational point of the split model whose abscissa is a square
is divisible by two.  The proof is an explicit reverse-doubling
calculation through the two-isogenous curve. -/
theorem double_of_square_abscissa
    {U V : ℚ} (hU0 : U ≠ 0)
    (hP : fullTwoCurve.toAffine.Nonsingular U V)
    (hUSquare : IsSquare U) :
    ∃ Q : fullTwoCurve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  obtain ⟨s, hs⟩ := hUSquare
  have hU : U = s ^ 2 := by
    simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve : V ^ 2 = U * (U ^ 2 - 2 * U - 63) :=
    fullTwoCurve_equation_of_nonsingular hP
  let t : ℚ := V / s
  have ht : t ^ 2 = U ^ 2 - 2 * U - 63 := by
    dsimp [t]
    rw [div_pow]
    field_simp [hs0]
    nlinarith [hcurve, hU]
  let X : ℚ := 2 * U - 2 - 2 * t
  let X' : ℚ := 2 * U - 2 + 2 * t
  have hXprod : X * X' = 256 := by
    dsimp [X, X']
    nlinarith [ht]
  have hX0 : X ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  have hdualFactor :
      X ^ 2 + 4 * X + 256 = 4 * U * X := by
    dsimp [X]
    nlinarith [ht]
  let Y : ℚ := 2 * s * X
  have hdual :
      Y ^ 2 = X * (X ^ 2 + 4 * X + 256) := by
    rw [hdualFactor]
    dsimp [Y]
    rw [hU]
    ring
  obtain ⟨q, hq⟩ := dual_abscissa_isSquare hX0 hdual
  have hXq : X = q ^ 2 := by
    simpa [pow_two] using hq
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hXq
    norm_num at hXq
    exact hX0 hXq
  have hYq :
      (Y / q) ^ 2 = X ^ 2 + 4 * X + 256 := by
    rw [div_pow]
    field_simp [hq0]
    nlinarith [hdual, hXq]
  let v : ℚ := 1 + X / 2 - Y / (2 * q)
  let w : ℚ := q * v
  have hvdef : v = 1 + X / 2 - Y / (2 * q) := rfl
  have hwdef : w = q * v := rfl
  have hXv : X * v = v ^ 2 - 2 * v - 63 := by
    dsimp [v]
    field_simp [hq0] at hYq ⊢
    nlinarith [hYq, hXq]
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv] at hXv
    norm_num at hXv
  have hw0 : w ≠ 0 :=
    mul_ne_zero hq0 hv0
  have hcurveQ : w ^ 2 = v * (v ^ 2 - 2 * v - 63) := by
    rw [hwdef, ← hXv, hXq]
    ring
  have hQ : fullTwoCurve.toAffine.Nonsingular v w := by
    apply fullTwoCurve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [fullTwoCurve]
    linear_combination hcurveQ
  have hwneneg : w ≠ -w := by
    intro h
    apply hw0
    linarith
  have hneg : w ≠ fullTwoCurve.toAffine.negY v w := by
    simp only [WeierstrassCurve.Affine.negY]
    norm_num [fullTwoCurve]
    exact hwneneg
  let Q : fullTwoCurve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some v w hQ
  have hdouble :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (h₁ := hQ) hneg
  have hslope :
      fullTwoCurve.toAffine.slope v v w w =
        (3 * v ^ 2 - 4 * v - 63) / (2 * w) := by
    simp [WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, fullTwoCurve, hwneneg]
    ring
  have haddX :
      fullTwoCurve.toAffine.addX v v
          (fullTwoCurve.toAffine.slope v v w w) =
        (v ^ 2 + 63) ^ 2 / (4 * w ^ 2) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [fullTwoCurve]
    field_simp [hw0]
    rw [hcurveQ]
    ring
  have hYformula :
      Y = -q * (v ^ 2 + 63) / v :=
    y_formula_of_reverse_linear hv0
      (y_linear_of_reverse_definition hq0 hvdef) hXv
  have haddXeq :
      fullTwoCurve.toAffine.addX v v
          (fullTwoCurve.toAffine.slope v v w w) = U := by
    rw [haddX]
    have hYsq : Y ^ 2 = 4 * U * X ^ 2 := by
      dsimp [Y]
      rw [hU]
      ring
    have hYformulaCleared :
        Y ^ 2 * v ^ 2 =
          q ^ 2 * (v ^ 2 + 63) ^ 2 :=
      y_formula_squared hv0 hYformula
    have hcancel :
        q ^ 2 * (v ^ 2 + 63) ^ 2 =
          q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
      calc
        q ^ 2 * (v ^ 2 + 63) ^ 2 =
            Y ^ 2 * v ^ 2 := hYformulaCleared.symm
        _ = q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
          rw [hYsq, hXq]
          ring
    have htarget :
        (v ^ 2 + 63) ^ 2 = 4 * w ^ 2 * U := by
      have hcancelled :=
        mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      calc
        (v ^ 2 + 63) ^ 2 =
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

/-! ## The four residual squareclasses -/

/-- Every nonzero abscissa on the split model has squareclass `1`, `-3`,
`-7`, or `21`. -/
theorem abscissa_class_of_ne_zero
    {V W : ℚ} (hV0 : V ≠ 0) (hcurve : OnFullTwoCurve V W) :
    (∃ r : ℚ, r ≠ 0 ∧ V = r ^ 2) ∨
    (∃ r : ℚ, r ≠ 0 ∧ V = -(3 * r ^ 2)) ∨
    (∃ r : ℚ, r ≠ 0 ∧ V = -(7 * r ^ 2)) ∨
    (∃ r : ℚ, r ≠ 0 ∧ V = 21 * r ^ 2) := by
  have hinv := translate_by_zero_twoTorsion hV0 hcurve
  rcases abscissa_squareClass hV0 hcurve with
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ |
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩
  all_goals
    have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
  · exact Or.inl ⟨r, hr, hc⟩
  · exact (no_negativeOne_squareClass hr hc hcurve).elim
  · exact (no_three_squareClass hr hc hcurve).elim
  · exact Or.inr (Or.inl ⟨r, hr, hc⟩)
  · -- squareclass `7` translates to the impossible class `-1`
    exfalso
    have hr' : (3 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = -(3 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact no_negativeOne_squareClass hr' hc' hinv
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr, hc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hc⟩))
  · -- squareclass `-21` translates to the impossible class `3`
    exfalso
    have hr' : (1 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = 3 * (1 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact no_three_squareClass hr' hc' hinv

/-! ## The visible torsion points -/

private lemma nonsingular_zero_zero :
    fullTwoCurve.toAffine.Nonsingular 0 0 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_nine_zero :
    fullTwoCurve.toAffine.Nonsingular 9 0 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_negSeven_zero :
    fullTwoCurve.toAffine.Nonsingular (-7) 0 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_negThree_twelve :
    fullTwoCurve.toAffine.Nonsingular (-3) 12 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_negThree_negTwelve :
    fullTwoCurve.toAffine.Nonsingular (-3) (-12) :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_twentyOne_eightyFour :
    fullTwoCurve.toAffine.Nonsingular 21 84 :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

private lemma nonsingular_twentyOne_negEightyFour :
    fullTwoCurve.toAffine.Nonsingular 21 (-84) :=
  nonsingular_of_onFullTwoCurve (by norm_num [OnFullTwoCurve])

/-- The rational two-torsion point `(0,0)`. -/
def T : fullTwoCurve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

/-- The rational two-torsion point `(9,0)`. -/
def T₉ : fullTwoCurve.toAffine.Point :=
  .some 9 0 nonsingular_nine_zero

/-- The rational two-torsion point `(-7,0)`. -/
def T₇ : fullTwoCurve.toAffine.Point :=
  .some (-7) 0 nonsingular_negSeven_zero

/-- The visible order-four point `(-3,12)`. -/
def P₃ : fullTwoCurve.toAffine.Point :=
  .some (-3) 12 nonsingular_negThree_twelve

/-- The negative of `P₃`. -/
def P₃neg : fullTwoCurve.toAffine.Point :=
  .some (-3) (-12) nonsingular_negThree_negTwelve

/-- The visible order-four point `(21,84)`. -/
def P₂₁ : fullTwoCurve.toAffine.Point :=
  .some 21 84 nonsingular_twentyOne_eightyFour

/-- The negative of `P₂₁`. -/
def P₂₁neg : fullTwoCurve.toAffine.Point :=
  .some 21 (-84) nonsingular_twentyOne_negEightyFour

private lemma negY_eq {x y : ℚ} :
    fullTwoCurve.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma neg_T : -T = T := by
  rw [T, WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma neg_P₃ : -P₃ = P₃neg := by
  rw [P₃, P₃neg, WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma neg_P₂₁ : -P₂₁ = P₂₁neg := by
  rw [P₂₁, P₂₁neg, WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

/-- Adding `(0,0)` to `(-3,12)` gives `(21,84)`. -/
theorem P₃_add_T : P₃ + T = P₂₁ := by
  rw [P₃, T, P₂₁]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne
    (by norm_num : (-3 : ℚ) ≠ 0)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, fullTwoCurve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope, fullTwoCurve]

/-- Adding `(0,0)` to `(21,84)` gives `(-3,12)`. -/
theorem P₂₁_add_T : P₂₁ + T = P₃ := by
  rw [P₃, T, P₂₁]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne
    (by norm_num : (21 : ℚ) ≠ 0)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, fullTwoCurve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope, fullTwoCurve]

/-! ## Coset decompositions for the residual squareclasses -/

private lemma decompose_of_sub_eq_some
    {P R : fullTwoCurve.toAffine.Point} {x y : ℚ}
    {hxy : fullTwoCurve.toAffine.Nonsingular x y}
    (hsub : P - R = .some x y hxy)
    (hx0 : x ≠ 0) (hxSquare : IsSquare x) :
    ∃ Q : fullTwoCurve.toAffine.Point, P = R + (2 : ℕ) • Q := by
  obtain ⟨Q, hQ⟩ :=
    double_of_square_abscissa hx0 hxy hxSquare
  refine ⟨Q, ?_⟩
  calc
    P = R + (P - R) := by abel
    _ = R + (2 : ℕ) • Q := by rw [hsub, hQ]

/-- A point with squareclass `-7` lies in the coset of `T`. -/
private lemma decompose_negSeven_class
    {U V z : ℚ} (hU0 : U ≠ 0)
    (hP : fullTwoCurve.toAffine.Nonsingular U V)
    (hU : U = -(7 * z ^ 2)) :
    ∃ Q : fullTwoCurve.toAffine.Point,
      .some U V hP = T + (2 : ℕ) • Q := by
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve := fullTwoCurve_equation_of_nonsingular hP
  have hslope :
      fullTwoCurve.toAffine.slope U 0 V 0 = V / U := by
    simp [WeierstrassCurve.Affine.slope, hU0]
  have haddX :
      fullTwoCurve.toAffine.addX U 0
          (fullTwoCurve.toAffine.slope U 0 V 0) = -63 / U := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [fullTwoCurve]
    field_simp [hU0]
    nlinarith [hcurve]
  let hsum : fullTwoCurve.toAffine.Nonsingular
      (fullTwoCurve.toAffine.addX U 0
        (fullTwoCurve.toAffine.slope U 0 V 0))
      (fullTwoCurve.toAffine.addY U 0 V
        (fullTwoCurve.toAffine.slope U 0 V 0)) :=
    WeierstrassCurve.Affine.nonsingular_add
      hP nonsingular_zero_zero (fun h ↦ hU0 h.1)
  have hsub :
      (.some U V hP : fullTwoCurve.toAffine.Point) - T =
        .some
          (fullTwoCurve.toAffine.addX U 0
            (fullTwoCurve.toAffine.slope U 0 V 0))
          (fullTwoCurve.toAffine.addY U 0 V
            (fullTwoCurve.toAffine.slope U 0 V 0)) hsum := by
    rw [sub_eq_add_neg, neg_T]
    change (.some U V hP : fullTwoCurve.toAffine.Point) +
        .some 0 0 nonsingular_zero_zero = _
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hU0
  apply decompose_of_sub_eq_some hsub
  · rw [haddX, hU]
    apply div_ne_zero (by norm_num)
    intro h
    rw [h] at hU
    exact hU0 hU
  · refine ⟨3 / z, ?_⟩
    rw [haddX, hU]
    field_simp [hz0]
    ring

/-- The chord identity: subtracting an affine representative multiplies
abscissas into the intercept square.  Stated for the two concrete
order-four representatives via their common shape. -/
private lemma decompose_affine_rep
    {U V xR yR : ℚ}
    (hP : fullTwoCurve.toAffine.Nonsingular U V)
    (hR : fullTwoCurve.toAffine.Nonsingular xR yR)
    (hRneg : fullTwoCurve.toAffine.Nonsingular xR (-yR))
    (hU0 : U ≠ 0) (hxR0 : xR ≠ 0) (hne : U ≠ xR)
    {ρ : ℚ} (hρ0 : ρ ≠ 0) (hprod : U * xR = ρ ^ 2) :
    (∃ Q : fullTwoCurve.toAffine.Point,
      .some U V hP = .some xR yR hR + (2 : ℕ) • Q) ∨
    .some U V hP = .some xR yR hR + T := by
  have hcurveP := fullTwoCurve_equation_of_nonsingular hP
  have hcurveR := fullTwoCurve_equation_of_nonsingular hR
  have hnesub : U - xR ≠ 0 := sub_ne_zero.mpr hne
  have hnegR :
      -(.some xR yR hR : fullTwoCurve.toAffine.Point) =
        .some xR (-yR) hRneg := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨trivial, negY_eq⟩
  set L : ℚ := fullTwoCurve.toAffine.slope U xR V (-yR) with hLdef
  have hL : L * (U - xR) = V + yR := by
    rw [hLdef, WeierstrassCurve.Affine.slope_of_X_ne hne]
    field_simp [hnesub]
    ring
  have haddX :
      fullTwoCurve.toAffine.addX U xR L = L ^ 2 + 2 - U - xR := by
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [fullTwoCurve]
  have hkey :
      fullTwoCurve.toAffine.addX U xR L * (U * xR) =
        (V - L * U) ^ 2 := by
    have hA2 : L ^ 2 * (U - xR) ^ 2 = (V + yR) ^ 2 := by
      linear_combination (L * (U - xR) + (V + yR)) * hL
    have hVL2 :
        (V - L * U) ^ 2 * (U - xR) ^ 2 =
          (V * (U - xR) - (V + yR) * U) ^ 2 := by
      linear_combination
        (((V - L * U) * (U - xR) +
            (V * (U - xR) - (V + yR) * U)) * (-U)) * hL
    have hcleared :
        (fullTwoCurve.toAffine.addX U xR L * (U * xR) -
            (V - L * U) ^ 2) * (U - xR) ^ 2 = 0 := by
      rw [haddX]
      linear_combination
        (U * xR) * hA2 - hVL2 + (xR * (U - xR)) * hcurveP -
          (U * (U - xR)) * hcurveR
    have hne2 : (U - xR) ^ 2 ≠ 0 := pow_ne_zero 2 hnesub
    rcases mul_eq_zero.mp hcleared with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne2
  let hsum : fullTwoCurve.toAffine.Nonsingular
      (fullTwoCurve.toAffine.addX U xR L)
      (fullTwoCurve.toAffine.addY U xR V L) :=
    WeierstrassCurve.Affine.nonsingular_add
      hP hRneg (fun h ↦ (hne h.1).elim)
  have hsub :
      (.some U V hP : fullTwoCurve.toAffine.Point) -
          .some xR yR hR =
        .some
          (fullTwoCurve.toAffine.addX U xR L)
          (fullTwoCurve.toAffine.addY U xR V L) hsum := by
    rw [sub_eq_add_neg, hnegR]
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hne
  have hUxR : U * xR ≠ 0 := mul_ne_zero hU0 hxR0
  by_cases hc0 : V - L * U = 0
  · -- the difference is the two-torsion point `(0,0)`
    right
    have haddX0 : fullTwoCurve.toAffine.addX U xR L = 0 := by
      have h0 : fullTwoCurve.toAffine.addX U xR L * (U * xR) = 0 := by
        rw [hkey, hc0]
        norm_num
      exact (mul_eq_zero.mp h0).resolve_right hUxR
    have haddY0 :
        fullTwoCurve.toAffine.addY U xR V L = 0 := by
      have hOn := onFullTwoCurve_of_nonsingular hsum
      rw [haddX0] at hOn
      unfold OnFullTwoCurve at hOn
      norm_num at hOn
      exact hOn
    have hsubT :
        (.some U V hP : fullTwoCurve.toAffine.Point) -
            .some xR yR hR = T := by
      rw [hsub, T]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨haddX0, haddY0⟩
    calc
      (.some U V hP : fullTwoCurve.toAffine.Point) =
          .some xR yR hR +
            ((.some U V hP : fullTwoCurve.toAffine.Point) -
              .some xR yR hR) := by abel
      _ = .some xR yR hR + T := by rw [hsubT]
  · left
    apply decompose_of_sub_eq_some hsub
    · intro h
      rw [h] at hkey
      norm_num at hkey
      exact hc0 ((pow_eq_zero_iff (two_ne_zero)).mp hkey.symm)
    · refine ⟨(V - L * U) / ρ, ?_⟩
      have haddXval : fullTwoCurve.toAffine.addX U xR L =
          (V - L * U) ^ 2 / (U * xR) := by
        rw [eq_div_iff hUxR]
        exact hkey
      rw [haddXval, hprod]
      field_simp [hρ0]

/-! ## The four doubling cosets -/

/-- Every rational point lies in one of four explicit cosets of twice the
rational point group. -/
theorem four_doubling_cosets (P : fullTwoCurve.toAffine.Point) :
    (∃ Q : fullTwoCurve.toAffine.Point, P = (2 : ℕ) • Q) ∨
    (∃ Q : fullTwoCurve.toAffine.Point, P = T + (2 : ℕ) • Q) ∨
    (∃ Q : fullTwoCurve.toAffine.Point, P = P₃ + (2 : ℕ) • Q) ∨
    (∃ Q : fullTwoCurve.toAffine.Point, P = P₂₁ + (2 : ℕ) • Q) := by
  cases P with
  | zero =>
      left
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hcurve := fullTwoCurve_equation_of_nonsingular hP
      rcases eq_or_ne U 0 with rfl | hU0
      · have hV : V = 0 := by
          norm_num at hcurve
          nlinarith [sq_nonneg V]
        subst V
        right; left
        refine ⟨0, ?_⟩
        simp [T]
      · have hOn : OnFullTwoCurve U V :=
          onFullTwoCurve_of_nonsingular hP
        rcases abscissa_class_of_ne_zero hU0 hOn with
            ⟨r, hr, hU⟩ | ⟨r, hr, hU⟩ | ⟨r, hr, hU⟩ | ⟨r, hr, hU⟩
        · -- squareclass 1: the point is divisible by two
          left
          obtain ⟨Q, hQ⟩ :=
            double_of_square_abscissa hU0 hP ⟨r, by rw [hU]; ring⟩
          exact ⟨Q, hQ.symm⟩
        · -- squareclass -3: coset of `(-3,12)`
          rcases eq_or_ne U (-3) with rfl | hne
          · have hV : V = 12 ∨ V = -12 := by
              norm_num at hcurve
              have : (V - 12) * (V + 12) = 0 := by nlinarith [hcurve]
              rcases mul_eq_zero.mp this with h | h
              · exact Or.inl (by linarith)
              · exact Or.inr (by linarith)
            rcases hV with rfl | rfl
            · right; right; left
              exact ⟨0, by simp [P₃]⟩
            · right; right; left
              refine ⟨P₃neg, ?_⟩
              rw [← neg_P₃]
              have : (.some (-3) (-12)
                  nonsingular_negThree_negTwelve :
                    fullTwoCurve.toAffine.Point) = -P₃ := by
                rw [neg_P₃]
                rfl
              rw [this]
              simp only [two_nsmul]
              abel
          · have hρ : U * (-3) = (3 * r) ^ 2 := by
              rw [hU]
              ring
            rcases decompose_affine_rep hP
                nonsingular_negThree_twelve
                nonsingular_negThree_negTwelve
                hU0 (by norm_num) hne
                (by positivity : (3 : ℚ) * r ≠ 0) hρ with
                ⟨Q, hQ⟩ | hQ
            · right; right; left
              exact ⟨Q, by rw [hQ]; rfl⟩
            · right; right; right
              refine ⟨0, ?_⟩
              have hPT : (.some (-3) 12
                  nonsingular_negThree_twelve :
                    fullTwoCurve.toAffine.Point) + T = P₂₁ := P₃_add_T
              rw [hQ, hPT]
              simp
        · -- squareclass -7: coset of `T`
          right; left
          exact decompose_negSeven_class hU0 hP hU
        · -- squareclass 21: coset of `(21,84)`
          rcases eq_or_ne U 21 with rfl | hne
          · have hV : V = 84 ∨ V = -84 := by
              norm_num at hcurve
              have : (V - 84) * (V + 84) = 0 := by nlinarith [hcurve]
              rcases mul_eq_zero.mp this with h | h
              · exact Or.inl (by linarith)
              · exact Or.inr (by linarith)
            rcases hV with rfl | rfl
            · right; right; right
              exact ⟨0, by simp [P₂₁]⟩
            · right; right; right
              refine ⟨P₂₁neg, ?_⟩
              rw [← neg_P₂₁]
              have : (.some 21 (-84)
                  nonsingular_twentyOne_negEightyFour :
                    fullTwoCurve.toAffine.Point) = -P₂₁ := by
                rw [neg_P₂₁]
                rfl
              rw [this]
              simp only [two_nsmul]
              abel
          · have hρ : U * 21 = (21 * r) ^ 2 := by
              rw [hU]
              ring
            rcases decompose_affine_rep hP
                nonsingular_twentyOne_eightyFour
                nonsingular_twentyOne_negEightyFour
                hU0 (by norm_num) hne
                (by positivity : (21 : ℚ) * r ≠ 0) hρ with
                ⟨Q, hQ⟩ | hQ
            · right; right; right
              exact ⟨Q, by rw [hQ]; rfl⟩
            · right; right; left
              refine ⟨0, ?_⟩
              have hPT : (.some 21 84
                  nonsingular_twentyOne_eightyFour :
                    fullTwoCurve.toAffine.Point) + T = P₃ := P₂₁_add_T
              rw [hQ, hPT]
              simp

/-! ## Finite index, finite generation, and rank zero -/

/-- The image of multiplication by two on the rational point group. -/
abbrev doublingRange : AddSubgroup fullTwoCurve.toAffine.Point :=
  (nsmulAddMonoidHom (α := fullTwoCurve.toAffine.Point) 2).range

private def doublingRepresentative :
    Fin 4 → fullTwoCurve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => P₃
  | 3 => P₂₁

private lemma doubling_quotient_surjective :
    Function.Surjective
      (fun i : Fin 4 ↦
        QuotientAddGroup.mk' doublingRange
          (doublingRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective doublingRange c
  rcases four_doubling_cosets P with
      ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · refine
      ⟨0, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨1, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨2, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨3, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm

/-- The image of multiplication by two has finite index. -/
theorem doubling_finiteIndex : doublingRange.FiniteIndex := by
  letI : Finite (fullTwoCurve.toAffine.Point ⧸ doublingRange) :=
    Finite.of_surjective _ doubling_quotient_surjective
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The rational point group is finitely generated. -/
theorem point_fg : AddGroup.FG fullTwoCurve.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_two fullTwoCurve
    doubling_finiteIndex

/-- The multiplication-by-two index is at most four. -/
theorem doubling_index_le_four : doublingRange.index ≤ 4 := by
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      doubling_quotient_surjective).trans_eq (by simp)

/-! ## The rational two-torsion has cardinality four -/

private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma double_T₉ : (2 : ℕ) • T₉ = 0 := by
  simp only [two_nsmul]
  rw [T₉]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private lemma double_T₇ : (2 : ℕ) • T₇ = 0 := by
  simp only [two_nsmul]
  rw [T₇]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve]

private def fourToTwoTorsion :
    Fin 4 → {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T⟩
  | 2 => ⟨T₉, double_T₉⟩
  | 3 => ⟨T₇, double_T₇⟩

private lemma fourToTwoTorsion_injective :
    Function.Injective fourToTwoTorsion := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [fourToTwoTorsion, T, T₉, T₇] at hij ⊢
  all_goals norm_num at hij

private lemma fourToTwoTorsion_surjective :
    Function.Surjective fourToTwoTorsion := by
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
        norm_num [WeierstrassCurve.Affine.negY, fullTwoCurve] at hself
        linarith
      have hcurve := fullTwoCurve_equation_of_nonsingular hP
      rw [hV] at hcurve
      norm_num at hcurve
      have hU : U = 0 ∨ U = 9 ∨ U = -7 := by
        rcases hcurve with h | h
        · exact Or.inl h
        · have hfac : (U - 9) * (U + 7) = 0 := by
            linear_combination h
          rcases mul_eq_zero.mp hfac with h' | h'
          · exact Or.inr (Or.inl (by linarith))
          · exact Or.inr (Or.inr (by linarith))
      subst hV
      rcases hU with rfl | rfl | rfl
      · exact ⟨1, by apply Subtype.ext; rfl⟩
      · exact ⟨2, by apply Subtype.ext; rfl⟩
      · exact ⟨3, by apply Subtype.ext; rfl⟩

/-- The split model has exactly four rational points killed by two. -/
theorem two_torsion_card_eq_four :
    Nat.card
      {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0} = 4 := by
  letI : Finite
      {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion fullTwoCurve
  simpa using
    (Nat.card_congr
      (Equiv.ofBijective fourToTwoTorsion
        ⟨fourToTwoTorsion_injective,
          fourToTwoTorsion_surjective⟩)).symm

/-- The rational point group has Mordell--Weil rank zero. -/
theorem point_rank_zero :
    Module.finrank ℤ fullTwoCurve.toAffine.Point = 0 := by
  letI : AddGroup.FG fullTwoCurve.toAffine.Point := point_fg
  have hker :
      Nat.card
          (nsmulAddMonoidHom
            (α := fullTwoCurve.toAffine.Point) 2).ker = 4 := by
    change Nat.card
      {P : fullTwoCurve.toAffine.Point // (2 : ℕ) • P = 0} = 4
    exact two_torsion_card_eq_four
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg fullTwoCurve.toAffine.Point
      (by norm_num : (2 : ℕ) ≠ 0)
  rw [hker] at hformula
  have hpow :
      2 ^ Module.finrank ℤ fullTwoCurve.toAffine.Point ≤ 1 := by
    have hindex := doubling_index_le_four
    change
      (nsmulAddMonoidHom
        (α := fullTwoCurve.toAffine.Point) 2).range.index ≤ 4
      at hindex
    omega
  have hpowequal :
      2 ^ Module.finrank ℤ fullTwoCurve.toAffine.Point = 1 :=
    le_antisymm hpow
      (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- All rational points are torsion; in particular, the rational point
group of the split model is finite. -/
theorem point_finite : Finite fullTwoCurve.toAffine.Point := by
  letI : AddGroup.FG fullTwoCurve.toAffine.Point := point_fg
  letI : Module.Finite ℤ fullTwoCurve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr point_fg
  have hmoduleTorsion :
      Module.IsTorsion ℤ fullTwoCurve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      point_rank_zero
  exact AddCommGroup.finite_of_fg_torsion fullTwoCurve.toAffine.Point
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

/-! ## The eight visible points -/

/-- The eight visibly distinct rational points.  No exhaustiveness claim
is made here. -/
def eightVisiblePoints : Fin 8 → fullTwoCurve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => T₉
  | 3 => T₇
  | 4 => P₃
  | 5 => P₃neg
  | 6 => P₂₁
  | 7 => P₂₁neg

theorem eightVisiblePoints_injective :
    Function.Injective eightVisiblePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [eightVisiblePoints, T, T₉, T₇, P₃, P₃neg,
      P₂₁, P₂₁neg] at hij ⊢
  all_goals norm_num at hij

end MazurTorsion.XZeroTwentyOne
