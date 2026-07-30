/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# The elementary two-descent boundary for `X₀(21)`

The conductor-`21` elliptic curve

`y² + xy = x³ - 4x - 1`

is a standard model of `X₀(21)`.  Completing the square and making the
integral change of coordinates

`V = 4x + 1`, `W = 8y + 4x`

gives the full rational two-torsion model

`W² = V(V - 9)(V + 7)`.

This file carries out the denominator and local parts of the complete
two-descent on this model.  Every nonzero rational abscissa has one of the
eight squareclasses `±1`, `±3`, `±7`, `±21`.  Two classes are impossible
modulo sixteen, and translation by `(0,0)`, expressed by

`(V,W) ↦ (-63/V, 63W/V²)`,

pairs the other four local branches with them.  The two remaining
homogeneous spaces are

`c² = m⁴ - 2m²n² - 63n⁴`

and

`c² = -3m⁴ - 2m²n² + 21n⁴`.

They are everywhere locally soluble and require genuine infinite descent.
Rather than conceal those global steps, the final rational-point
classification takes their precise primitive classifications as explicit
hypotheses.

The plane equation obtained by eliminating `j` between the classical
`X₀(3)` and `X₀(7)` hauptmoduls is also recorded, together with its four
visible noncuspidal points.  No modular interpretation or birational map
from that plane model is asserted here.
-/

namespace MazurTorsion.XZeroTwentyOne

/-- The minimal conductor-`21` Weierstrass model used for `X₀(21)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨1, 0, 0, -4, -1⟩

/-- The full rational two-torsion model obtained by completing the square. -/
def fullTwoCurve : WeierstrassCurve ℚ :=
  ⟨0, -2, 0, -63, 0⟩

instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance fullTwoCurve_isElliptic : fullTwoCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [fullTwoCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The affine equation of the minimal model, without a nonsingularity
wrapper. -/
def OnCurve (x y : ℚ) : Prop :=
  y ^ 2 + x * y = x ^ 3 - 4 * x - 1

/-- The affine equation of the full-two-torsion model. -/
def OnFullTwoCurve (V W : ℚ) : Prop :=
  W ^ 2 = V * (V - 9) * (V + 7)

/-- Completing the square sends the minimal model to the split cubic. -/
theorem onCurve_iff_onFullTwoCurve (x y : ℚ) :
    OnCurve x y ↔ OnFullTwoCurve (4 * x + 1) (8 * y + 4 * x) := by
  unfold OnCurve OnFullTwoCurve
  constructor
  · intro h
    linear_combination 64 * h
  · intro h
    linear_combination (1 / 64 : ℚ) * h

/-- The inverse coordinate change, in equation form. -/
theorem onFullTwoCurve_iff_onCurve (V W : ℚ) :
    OnFullTwoCurve V W ↔ OnCurve ((V - 1) / 4) ((W - V + 1) / 8) := by
  constructor
  · intro h
    apply (onCurve_iff_onFullTwoCurve _ _).mpr
    convert h using 1 <;> ring
  · intro h
    have h' := (onCurve_iff_onFullTwoCurve _ _).mp h
    convert h' using 1 <;> ring

/-- Affine rational solutions of the minimal equation. -/
def AffineSolution :=
  {p : ℚ × ℚ // OnCurve p.1 p.2}

/-- Affine rational solutions of the split cubic. -/
def FullTwoAffineSolution :=
  {p : ℚ × ℚ // OnFullTwoCurve p.1 p.2}

/-- The explicit affine equivalence between the two models. -/
def affineSolutionEquiv : AffineSolution ≃ FullTwoAffineSolution where
  toFun p :=
    ⟨(4 * p.1.1 + 1, 8 * p.1.2 + 4 * p.1.1),
      (onCurve_iff_onFullTwoCurve p.1.1 p.1.2).mp p.2⟩
  invFun p :=
    ⟨((p.1.1 - 1) / 4, (p.1.2 - p.1.1 + 1) / 8),
      (onFullTwoCurve_iff_onCurve p.1.1 p.1.2).mp p.2⟩
  left_inv p := by
    apply Subtype.ext
    ext <;> dsimp <;> ring
  right_inv p := by
    apply Subtype.ext
    ext <;> dsimp <;> ring

/-- The denominator-free fibre-product equation for the classical
hauptmoduls on `X₀(3)` and `X₀(7)`. -/
def HauptmodulPair (t₃ t₇ : ℚ) : Prop :=
  (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 =
    t₃ * (t₇ ^ 2 + 13 * t₇ + 49) *
      (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3

/-- The four visible noncuspidal rational pairs on the hauptmodul model. -/
theorem visible_hauptmodul_pairs :
    HauptmodulPair (-18) (-49 / 2) ∧
      HauptmodulPair (-81 / 2) (-49 / 8) ∧
      HauptmodulPair (-1152) (-2) ∧
      HauptmodulPair (-81 / 128) (-8) := by
  norm_num [HauptmodulPair]

/-- The `X₀(3)` formula for `j`, written away from its zero cusp. -/
def jOfThreeHauptmodul (t : ℚ) : ℚ :=
  (t + 27) * (t + 3) ^ 3 / t

/-- The four visible pairs give the expected four `j`-values. -/
theorem visible_j_values :
    jOfThreeHauptmodul (-18) = 3375 / 2 ∧
      jOfThreeHauptmodul (-81 / 2) = -140625 / 8 ∧
      jOfThreeHauptmodul (-1152) = -189613868625 / 128 ∧
      jOfThreeHauptmodul (-81 / 128) = -1159088625 / 2097152 := by
  norm_num [jOfThreeHauptmodul]

private lemma commonDivisor_dvd_sixtyThree
    {m n d : ℤ} (hmn : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 - 2 * m * n - 63 * n ^ 2) :
    d ∣ 63 := by
  have hm3 : d ∣ m ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨m * b - (-2 * m - 63 * n) * a, ?_⟩
    linear_combination m * hb - (-2 * m - 63 * n) * ha
  have h63n3 : d ∣ 63 * n ^ 3 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨(m - 2 * n) * a - n * b, ?_⟩
    linear_combination (m - 2 * n) * ha - n * hb
  have hd_coprime_n3 : IsCoprime d (n ^ 3) :=
    hmn.pow.of_isCoprime_of_dvd_left hm3
  exact hd_coprime_n3.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h63n3)

/-- If a nonzero factor of a square has gcd dividing `63` with its cofactor,
its squareclass is represented by a signed squarefree divisor of `63`. -/
theorem squareClass_of_gcd_dvd_sixtyThree
    {A B C : ℤ} (hA : A ≠ 0) (hAB : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (63 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨
      A = 3 * z ^ 2 ∨ A = -(3 * z ^ 2) ∨
      A = 7 * z ^ 2 ∨ A = -(7 * z ^ 2) ∨
      A = 21 * z ^ 2 ∨ A = -(21 * z ^ 2) := by
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
  have hdiv : g.natAbs ∣ 63 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hboundNat : g.natAbs ≤ 63 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have hbound : g ≤ 63 := by
    have : (g.natAbs : ℤ) ≤ 63 := by exact_mod_cast hboundNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using this
  have hg :
      g = 1 ∨ g = 3 ∨ g = 7 ∨ g = 9 ∨ g = 21 ∨ g = 63 := by
    interval_cases g <;> norm_num at hdiv
    all_goals simp
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcop hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    rcases hg with hg | hg | hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inl (by simpa using hAz)))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by simpa using hAz)))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inl (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl (by simpa using hAz)))))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by nlinarith [hAz])))))⟩
  · have hAz : A = -(g * z ^ 2) := by rw [← hga, hz]; ring
    rcases hg with hg | hg | hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inl (by nlinarith [hAz]))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr
        (Or.inl (by nlinarith [hAz]))))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (by nlinarith [hAz]))))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inr (Or.inl (by nlinarith [hAz]))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (by nlinarith [hAz])))))))⟩
    · rw [hg] at hAz
      exact ⟨3 * z, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (by nlinarith [hAz]))))))⟩

/-- Every nonzero rational abscissa of the split cubic belongs to one of the
eight squareclasses supported at `3` and `7`. -/
theorem abscissa_squareClass
    {V W : ℚ} (hV : V ≠ 0) (hcurve : OnFullTwoCurve V W) :
    (∃ r : ℚ, V = r ^ 2) ∨
    (∃ r : ℚ, V = -r ^ 2) ∨
    (∃ r : ℚ, V = 3 * r ^ 2) ∨
    (∃ r : ℚ, V = -(3 * r ^ 2)) ∨
    (∃ r : ℚ, V = 7 * r ^ 2) ∨
    (∃ r : ℚ, V = -(7 * r ^ 2)) ∨
    (∃ r : ℚ, V = 21 * r ^ 2) ∨
    (∃ r : ℚ, V = -(21 * r ^ 2)) := by
  let m : ℤ := V.num
  let n : ℤ := V.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 - 2 * m * n - 63 * n ^ 2
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast V.den_ne_zero
  have hVmn : V = (m : ℚ) / n :=
    V.num_div_den.symm
  have hscaled : (W * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hVmn] at hcurve
    unfold OnFullTwoCurve at hcurve
    field_simp [hn0] at hcurve
    calc
      (W * n ^ 2) ^ 2 = W ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 - 2 * m * n - 63 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsq : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨W * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hAB : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : A ≠ 0 := by
    apply mul_ne_zero
    · dsimp [m]
      exact Rat.num_ne_zero.mpr hV
    · dsimp [n]
      exact_mod_cast V.den_ne_zero
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den V
  have hgcd : GCDMonoid.gcd A B ∣ (63 : ℤ) :=
    commonDivisor_dvd_sixtyThree hmn
      (GCDMonoid.gcd_dvd_left A B)
      (GCDMonoid.gcd_dvd_right A B)
  have lift :
      ∀ {d z : ℤ}, A = d * z ^ 2 →
        V = (d : ℚ) * ((z : ℚ) / n) ^ 2 := by
    intro d z hd
    rw [hVmn]
    simp only [A] at hd
    field_simp [hn0]
    exact_mod_cast hd
  obtain ⟨z, hz | hz | hz | hz | hz | hz | hz | hz⟩ :=
    squareClass_of_gcd_dvd_sixtyThree hA0 hAB hgcd
  · left
    exact ⟨(z : ℚ) / n, by simpa using lift (d := 1) (by simpa using hz)⟩
  · right; left
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -1) (by nlinarith [hz])⟩
  · right; right; left
    exact ⟨(z : ℚ) / n, lift hz⟩
  · right; right; right; left
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -3) (by nlinarith [hz])⟩
  · right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift hz⟩
  · right; right; right; right; right; left
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -7) (by nlinarith [hz])⟩
  · right; right; right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift hz⟩
  · right; right; right; right; right; right; right
    exact ⟨(z : ℚ) / n, by
      simpa using lift (d := -21) (by nlinarith [hz])⟩

/-- Clearing the denominator of a chosen squareclass produces its primitive
integral homogeneous space. -/
theorem homogeneousSpace_of_squareClass
    (d : ℤ) {V W r : ℚ} (hr : r ≠ 0)
    (hV : V = (d : ℚ) * r ^ 2) (hcurve : OnFullTwoCurve V W) :
    ∃ m n c : ℤ,
      IsCoprime m n ∧ m ≠ 0 ∧ 0 < n ∧
      r = (m : ℚ) / (n : ℚ) ∧
      c ^ 2 =
        d * (d * m ^ 2 - 9 * n ^ 2) *
          (d * m ^ 2 + 7 * n ^ 2) := by
  let m : ℤ := r.num
  let n : ℤ := r.den
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact Rat.num_ne_zero.mpr hr
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast r.den_pos
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den r
  have hrmn : r = (m : ℚ) / (n : ℚ) :=
    r.num_div_den.symm
  have hscaled :
      (W * (n : ℚ) ^ 3 / (m : ℚ)) ^ 2 =
        ((d * (d * m ^ 2 - 9 * n ^ 2) *
          (d * m ^ 2 + 7 * n ^ 2) : ℤ) : ℚ) := by
    unfold OnFullTwoCurve at hcurve
    rw [div_pow, mul_pow, hcurve, hV, hrmn]
    push_cast
    field_simp [hmQ, hnQ]
  have hsquare :
      IsSquare
        (((d * (d * m ^ 2 - 9 * n ^ 2) *
          (d * m ^ 2 + 7 * n ^ 2) : ℤ) : ℚ)) :=
    ⟨W * (n : ℚ) ^ 3 / (m : ℚ),
      by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hc⟩ := Rat.isSquare_intCast_iff.mp hsquare
  refine ⟨m, n, c, hmn, hm0, hnpos, hrmn, ?_⟩
  simpa [pow_two] using hc.symm

private abbrev reduceTwo : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

private lemma primitive_has_odd_coordinate
    {m n : ℤ} (hmn : IsCoprime m n) :
    reduceTwo (m : ZMod 16) ≠ 0 ∨ reduceTwo (n : ZMod 16) ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  have hmEven : Even m := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [reduceTwo] using h.1
  have hnEven : Even n := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [reduceTwo] using h.2
  have hunit : IsUnit (2 : ℤ) :=
    hmn.isUnit_of_dvd'
      (even_iff_two_dvd.mp hmEven) (even_iff_two_dvd.mp hnEven)
  norm_num [Int.isUnit_iff] at hunit

private lemma negativeOne_obstruction_mod_sixteen :
    ∀ m n c : ZMod 16,
      (reduceTwo m ≠ 0 ∨ reduceTwo n ≠ 0) →
      c ^ 2 ≠
        (-1) * ((-1) * m ^ 2 - 9 * n ^ 2) *
          ((-1) * m ^ 2 + 7 * n ^ 2) := by
  decide

private lemma three_obstruction_mod_sixteen :
    ∀ m n c : ZMod 16,
      (reduceTwo m ≠ 0 ∨ reduceTwo n ≠ 0) →
      c ^ 2 ≠
        3 * (3 * m ^ 2 - 9 * n ^ 2) *
          (3 * m ^ 2 + 7 * n ^ 2) := by
  decide

/-- The squareclass `-1` is locally impossible. -/
theorem no_negativeOne_squareClass
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = -r ^ 2)
    (hcurve : OnFullTwoCurve V W) : False := by
  obtain ⟨m, n, c, hmn, -, -, -, hc⟩ :=
    homogeneousSpace_of_squareClass (-1) hr
      (by simpa using hV) hcurve
  apply negativeOne_obstruction_mod_sixteen
    (m : ZMod 16) (n : ZMod 16) (c : ZMod 16)
    (primitive_has_odd_coordinate hmn)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) hc

/-- The squareclass `3` is locally impossible. -/
theorem no_three_squareClass
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = 3 * r ^ 2)
    (hcurve : OnFullTwoCurve V W) : False := by
  obtain ⟨m, n, c, hmn, -, -, -, hc⟩ :=
    homogeneousSpace_of_squareClass 3 hr hV hcurve
  apply three_obstruction_mod_sixteen
    (m : ZMod 16) (n : ZMod 16) (c : ZMod 16)
    (primitive_has_odd_coordinate hmn)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) hc

/-- The exact global leaf for squareclass `1`. -/
def PrincipalQuarticClassified : Prop :=
  ∀ m n c : ℤ, IsCoprime m n →
    c ^ 2 = m ^ 4 - 2 * m ^ 2 * n ^ 2 - 63 * n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = 9 * n ^ 2

/-- The exact global leaf for squareclass `-3`, after removing the forced
square factor `9`. -/
def NegativeThreeQuarticClassified : Prop :=
  ∀ m n c : ℤ, IsCoprime m n →
    c ^ 2 = -3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

/-- The principal homogeneous space is locally soluble: this visible
primitive point rules out any direct congruence obstruction. -/
theorem principal_quartic_visible_point :
    IsCoprime (3 : ℤ) 1 ∧
      (0 : ℤ) ^ 2 = 3 ^ 4 - 2 * 3 ^ 2 * 1 ^ 2 - 63 * 1 ^ 4 := by
  norm_num

/-- The `-3` homogeneous space is also locally soluble. -/
theorem negativeThree_quartic_visible_point :
    IsCoprime (1 : ℤ) 1 ∧
      (4 : ℤ) ^ 2 = -3 * 1 ^ 4 - 2 * 1 ^ 2 * 1 ^ 2 + 21 * 1 ^ 4 := by
  norm_num

private lemma normalize_negativeThree_space
    {m n c : ℤ}
    (h : c ^ 2 =
      (-3) * ((-3) * m ^ 2 - 9 * n ^ 2) *
        ((-3) * m ^ 2 + 7 * n ^ 2)) :
    ∃ q : ℤ,
      c = 3 * q ∧
      q ^ 2 = -3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4 := by
  have hthree : (3 : ℤ) ∣ c ^ 2 := by
    rw [h]
    refine ⟨3 * (-3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4), ?_⟩
    ring
  have hprime : Prime (3 : ℤ) :=
    Nat.prime_iff_prime_int.mp (by norm_num)
  have hc : (3 : ℤ) ∣ c :=
    hprime.dvd_of_dvd_pow hthree
  obtain ⟨q, hq⟩ := hc
  refine ⟨q, hq, ?_⟩
  have hfactor :
      (-3) * ((-3) * m ^ 2 - 9 * n ^ 2) *
          ((-3) * m ^ 2 + 7 * n ^ 2) =
        9 * (-3 * m ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4) := by
    ring
  rw [hfactor] at h
  rw [hq] at h
  nlinarith [h]

/-- Assuming the principal quartic descent, squareclass `1` contains only
the visible two-torsion abscissa `9`. -/
theorem one_squareClass_eq_nine
    (hprincipal : PrincipalQuarticClassified)
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = r ^ 2)
    (hcurve : OnFullTwoCurve V W) :
    V = 9 := by
  obtain ⟨m, n, c, hmn, hm0, hnpos, hrmn, hc⟩ :=
    homogeneousSpace_of_squareClass 1 hr
      (by simpa using hV) hcurve
  have hc' :
      c ^ 2 = m ^ 4 - 2 * m ^ 2 * n ^ 2 - 63 * n ^ 4 := by
    linear_combination hc
  rcases hprincipal m n c hmn hc' with hm | hn | hmnSq
  · exact absurd hm hm0
  · omega
  · have hmnSqQ : (m : ℚ) ^ 2 = 9 * (n : ℚ) ^ 2 := by
      exact_mod_cast hmnSq
    rw [hV, hrmn]
    field_simp
    nlinarith [hmnSqQ]

/-- Assuming the second quartic descent, squareclass `-3` contains only the
visible order-four abscissa `-3`. -/
theorem negativeThree_squareClass_eq
    (hnegative : NegativeThreeQuarticClassified)
    {V W r : ℚ} (hr : r ≠ 0) (hV : V = -(3 * r ^ 2))
    (hcurve : OnFullTwoCurve V W) :
    V = -3 := by
  obtain ⟨m, n, c, hmn, hm0, hnpos, hrmn, hc⟩ :=
    homogeneousSpace_of_squareClass (-3) hr
      (by simpa using hV) hcurve
  obtain ⟨q, -, hq⟩ := normalize_negativeThree_space hc
  rcases hnegative m n q hmn hq with hm | hn | hmnSq
  · exact absurd hm hm0
  · omega
  · have hmnSqQ : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 := by
      exact_mod_cast hmnSq
    rw [hV, hrmn]
    field_simp
    nlinarith [hmnSqQ]

/-- Translation by the rational two-torsion point `(0,0)`, on coordinates. -/
theorem translate_by_zero_twoTorsion
    {V W : ℚ} (hV : V ≠ 0) (hcurve : OnFullTwoCurve V W) :
    OnFullTwoCurve (-63 / V) (63 * W / V ^ 2) := by
  unfold OnFullTwoCurve at hcurve ⊢
  field_simp
  linear_combination (63 : ℚ) * hcurve

/-- Conditional rank-zero statement for the split model.  Its hypotheses are
exactly the two everywhere-locally-soluble quartic descents isolated above. -/
theorem abscissa_classification
    (hprincipal : PrincipalQuarticClassified)
    (hnegative : NegativeThreeQuarticClassified)
    {V W : ℚ} (hcurve : OnFullTwoCurve V W) :
    V = 0 ∨ V = 9 ∨ V = -7 ∨ V = -3 ∨ V = 21 := by
  by_cases hV0 : V = 0
  · exact Or.inl hV0
  have hinv := translate_by_zero_twoTorsion hV0 hcurve
  rcases abscissa_squareClass hV0 hcurve with
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ |
      ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩ | ⟨r, hc⟩
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact Or.inr (Or.inl
      (one_squareClass_eq_nine hprincipal hr hc hcurve))
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact (no_negativeOne_squareClass hr hc hcurve).elim
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact (no_three_squareClass hr hc hcurve).elim
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (negativeThree_squareClass_eq hnegative hr hc hcurve))))
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (3 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = -(3 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact (no_negativeOne_squareClass hr' hc' hinv).elim
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (3 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = (3 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    have h9 :=
      one_squareClass_eq_nine hprincipal hr' hc' hinv
    right; right; left
    field_simp at h9
    linarith
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (1 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = -(3 * (1 / r) ^ 2) := by
      rw [hc]
      field_simp
      ring
    have hneg :=
      negativeThree_squareClass_eq hnegative hr' hc' hinv
    right; right; right; right
    field_simp at hneg
    linarith
  · have hr : r ≠ 0 := by
      intro hz
      rw [hz] at hc
      norm_num at hc
      exact hV0 hc
    have hr' : (1 / r : ℚ) ≠ 0 := div_ne_zero (by norm_num) hr
    have hc' : -63 / V = 3 * (1 / r) ^ 2 := by
      rw [hc]
      field_simp
      ring
    exact (no_three_squareClass hr' hc' hinv).elim

/-- The corresponding conditional list of abscissas on the minimal
conductor-`21` model. -/
theorem curve_abscissa_classification
    (hprincipal : PrincipalQuarticClassified)
    (hnegative : NegativeThreeQuarticClassified)
    {x y : ℚ} (hcurve : OnCurve x y) :
    x = -1 / 4 ∨ x = 2 ∨ x = -2 ∨ x = -1 ∨ x = 5 := by
  have hsplit :=
    (onCurve_iff_onFullTwoCurve x y).mp hcurve
  rcases abscissa_classification hprincipal hnegative hsplit with
      h | h | h | h | h
  · left; linarith
  · right; left; linarith
  · right; right; left; linarith
  · right; right; right; left; linarith
  · right; right; right; right; linarith

/-- Conditional classification of all affine solutions on the split model.
Together with the point at infinity, these are the eight expected rational
points. -/
theorem fullTwo_affine_classification
    (hprincipal : PrincipalQuarticClassified)
    (hnegative : NegativeThreeQuarticClassified)
    {V W : ℚ} (hcurve : OnFullTwoCurve V W) :
    (V = 0 ∧ W = 0) ∨
    (V = 9 ∧ W = 0) ∨
    (V = -7 ∧ W = 0) ∨
    (V = -3 ∧ W = 12) ∨
    (V = -3 ∧ W = -12) ∨
    (V = 21 ∧ W = 84) ∨
    (V = 21 ∧ W = -84) := by
  rcases abscissa_classification hprincipal hnegative hcurve with
      hV | hV | hV | hV | hV
  · left
    refine ⟨hV, ?_⟩
    rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg W]
  · right; left
    refine ⟨hV, ?_⟩
    rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg W]
  · right; right; left
    refine ⟨hV, ?_⟩
    rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg W]
  · rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    have hfac : (W - 12) * (W + 12) = 0 := by
      nlinarith [hcurve]
    rcases mul_eq_zero.mp hfac with hW | hW
    · right; right; right; left
      exact ⟨hV, by linarith⟩
    · right; right; right; right; left
      exact ⟨hV, by linarith⟩
  · rw [hV] at hcurve
    unfold OnFullTwoCurve at hcurve
    norm_num at hcurve
    have hfac : (W - 84) * (W + 84) = 0 := by
      nlinarith [hcurve]
    rcases mul_eq_zero.mp hfac with hW | hW
    · right; right; right; right; right; left
      exact ⟨hV, by linarith⟩
    · right; right; right; right; right; right
      exact ⟨hV, by linarith⟩

/-- Conditional classification of all affine solutions on the minimal
conductor-`21` model. -/
theorem curve_affine_classification
    (hprincipal : PrincipalQuarticClassified)
    (hnegative : NegativeThreeQuarticClassified)
    {x y : ℚ} (hcurve : OnCurve x y) :
    (x = -1 / 4 ∧ y = 1 / 8) ∨
    (x = 2 ∧ y = -1) ∨
    (x = -2 ∧ y = 1) ∨
    (x = -1 ∧ y = 2) ∨
    (x = -1 ∧ y = -1) ∨
    (x = 5 ∧ y = 8) ∨
    (x = 5 ∧ y = -13) := by
  have hsplit :=
    (onCurve_iff_onFullTwoCurve x y).mp hcurve
  rcases fullTwo_affine_classification hprincipal hnegative hsplit with
      ⟨hV, hW⟩ | ⟨hV, hW⟩ | ⟨hV, hW⟩ |
      ⟨hV, hW⟩ | ⟨hV, hW⟩ | ⟨hV, hW⟩ | ⟨hV, hW⟩
  · left
    constructor <;> linarith
  · right; left
    constructor <;> linarith
  · right; right; left
    constructor <;> linarith
  · right; right; right; left
    constructor <;> linarith
  · right; right; right; right; left
    constructor <;> linarith
  · right; right; right; right; right; left
    constructor <;> linarith
  · right; right; right; right; right; right
    constructor <;> linarith

end MazurTorsion.XZeroTwentyOne
