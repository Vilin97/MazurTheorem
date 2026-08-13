/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.TateNormalForm

/-!
# Further multiples on Tate normal form

This file extends the kernel-checked low-multiple calculations for the marked point
`P = (0, 0)` on

`y² + (1-c)xy - by = x³ - bx²`.

The central lemma is a small recurrence: if `Q = (x, y)` and `x ≠ 0`, it computes `Q + P`.
The formulas for `5P` and `6P` are then consequences of the already checked formula for `4P`.
Every denominator used below has a corresponding explicit nonvanishing hypothesis.
-/
@[expose] public section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The `X`-coordinate obtained by adding the marked Tate point `(0, 0)` to `(x, y)`. -/
def tateNextX (b c x y : ℚ) : ℚ :=
  (y / x) ^ 2 + (1 - c) * (y / x) + b - x

/-- The `Y`-coordinate obtained by adding the marked Tate point `(0, 0)` to `(x, y)`. -/
def tateNextY (b c x y : ℚ) : ℚ :=
  -((y / x) * (tateNextX b c x y - x) + y) -
      (1 - c) * tateNextX b c x y + b

/-- Kernel-checked recurrence for adding the marked point to an affine Tate-normal-form point.
The sole denominator introduced by the secant formula is recorded as `hx`. -/
theorem add_origin_coordinates
    (b c x y : ℚ) (hx : x ≠ 0)
    (hxy : (tateNormalCurve b c).toAffine.Nonsingular x y)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ hnext : (tateNormalCurve b c).toAffine.Nonsingular
        (tateNextX b c x y) (tateNextY b c x y),
      WeierstrassCurve.Affine.Point.some x y hxy +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (tateNextX b c x y) (tateNextY b c x y) hnext := by
  let W := tateNormalCurve b c
  have hslope : W.toAffine.slope x 0 y 0 = y / x := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    ring
  have hxnext :
      W.toAffine.addX x 0 (W.toAffine.slope x 0 y 0) =
        tateNextX b c x y := by
    rw [hslope]
    simp [W, tateNormalCurve, tateNextX]
  have hynext :
      W.toAffine.addY x 0 y (W.toAffine.slope x 0 y 0) =
        tateNextY b c x y := by
    rw [hslope]
    simp [W, tateNormalCurve, tateNextX, tateNextY,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY]
  have hnext :
      W.toAffine.Nonsingular (tateNextX b c x y) (tateNextY b c x y) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add hxy h00
        (fun hpair => hx hpair.left)
    rwa [hxnext, hynext] at h
  refine ⟨hnext, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hxnext hynext

/-- Successive affine coordinates obtained by starting at `2P = (b, bc)` and
repeatedly adding the marked Tate point `P = (0, 0)`.  Index `n` is intended
to represent `(n + 2)P`; the accompanying theorem records exactly the
nonzero abscissas needed for this rational recurrence to agree with the group
law. -/
def tateSuccessiveCoordinates (b c : ℚ) : ℕ → ℚ × ℚ
  | 0 => (b, b * c)
  | n + 1 =>
      let Q := tateSuccessiveCoordinates b c n
      (tateNextX b c Q.1 Q.2, tateNextY b c Q.1 Q.2)

/-- The recurrence-defined abscissa of `(n + 2)P`. -/
def tateSuccessiveX (b c : ℚ) (n : ℕ) : ℚ :=
  (tateSuccessiveCoordinates b c n).1

/-- The recurrence-defined ordinate of `(n + 2)P`. -/
def tateSuccessiveY (b c : ℚ) (n : ℕ) : ℚ :=
  (tateSuccessiveCoordinates b c n).2

@[simp] lemma tateSuccessiveX_zero (b c : ℚ) :
    tateSuccessiveX b c 0 = b := rfl

@[simp] lemma tateSuccessiveY_zero (b c : ℚ) :
    tateSuccessiveY b c 0 = b * c := rfl

@[simp] lemma tateSuccessiveX_succ (b c : ℚ) (n : ℕ) :
    tateSuccessiveX b c (n + 1) =
      tateNextX b c (tateSuccessiveX b c n) (tateSuccessiveY b c n) := by
  rfl

@[simp] lemma tateSuccessiveY_succ (b c : ℚ) (n : ℕ) :
    tateSuccessiveY b c (n + 1) =
      tateNextY b c (tateSuccessiveX b c n) (tateSuccessiveY b c n) := by
  rfl

/-- The rational recurrence computes `(n + 2)P` whenever every earlier
abscissa used as a secant denominator is nonzero. -/
theorem nsmul_origin_eq_successiveCoordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (n : ℕ) (hx : ∀ k < n, tateSuccessiveX b c k ≠ 0) :
    ∃ h : (tateNormalCurve b c).toAffine.Nonsingular
        (tateSuccessiveX b c n) (tateSuccessiveY b c n),
      (n + 2) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (tateSuccessiveX b c n) (tateSuccessiveY b c n) h := by
  induction n with
  | zero =>
      simpa using two_nsmul_origin_coordinates b c hb h00
  | succ n ih =>
      have hx' : ∀ k < n, tateSuccessiveX b c k ≠ 0 := by
        intro k hk
        exact hx k (Nat.lt_succ_of_lt hk)
      obtain ⟨hn, hncoord⟩ := ih hx'
      obtain ⟨hsucc, hsucccoord⟩ :=
        add_origin_coordinates b c
          (tateSuccessiveX b c n) (tateSuccessiveY b c n)
          (hx n (Nat.lt_succ_self n)) hn h00
      refine ⟨?_, ?_⟩
      · simpa using hsucc
      · rw [show n + 1 + 2 = (n + 2) + 1 by omega, add_nsmul,
          one_nsmul, hncoord, hsucccoord]
        rfl

/-- Fraction-free numerator and denominator data for one pair of Tate
recurrence coordinates. -/
structure TateClearedCoordinateDatum where
  xNum : ℚ
  xDen : ℚ
  yNum : ℚ
  yDen : ℚ

/-- One fraction-free step of the Tate recurrence.  No division occurs in
this definition; its specification theorem records the nonzero inputs needed
to recover `tateNextX` and `tateNextY`. -/
def tateClearedNext (b c : ℚ)
    (Q : TateClearedCoordinateDatum) : TateClearedCoordinateDatum :=
  let rNum := Q.yNum * Q.xDen
  let rDen := Q.yDen * Q.xNum
  let nextXNum :=
    rNum ^ 2 * Q.xDen +
      (1 - c) * rNum * rDen * Q.xDen +
      b * rDen ^ 2 * Q.xDen - Q.xNum * rDen ^ 2
  let nextXDen := rDen ^ 2 * Q.xDen
  let nextYNum :=
    -rNum * (nextXNum * Q.xDen - Q.xNum * nextXDen) * Q.yDen -
      Q.yNum * rDen * nextXDen * Q.xDen -
      (1 - c) * nextXNum * rDen * Q.xDen * Q.yDen +
      b * rDen * nextXDen * Q.xDen * Q.yDen
  let nextYDen := rDen * nextXDen * Q.xDen * Q.yDen
  ⟨nextXNum, nextXDen, nextYNum, nextYDen⟩

/-- Fraction-free coordinates corresponding to `tateSuccessiveCoordinates`.
Index zero is the cleared presentation `(b/1, bc/1)` of `2P`. -/
def tateClearedCoordinates (b c : ℚ) : ℕ → TateClearedCoordinateDatum
  | 0 => ⟨b, 1, b * c, 1⟩
  | n + 1 => tateClearedNext b c (tateClearedCoordinates b c n)

private lemma tateClearedNext_spec
    (b c : ℚ) (Q : TateClearedCoordinateDatum)
    (hxNum : Q.xNum ≠ 0) (hxDen : Q.xDen ≠ 0)
    (hyDen : Q.yDen ≠ 0) :
    let next := tateClearedNext b c Q
    next.xDen ≠ 0 ∧ next.yDen ≠ 0 ∧
      tateNextX b c (Q.xNum / Q.xDen) (Q.yNum / Q.yDen) =
        next.xNum / next.xDen ∧
      tateNextY b c (Q.xNum / Q.xDen) (Q.yNum / Q.yDen) =
        next.yNum / next.yDen := by
  dsimp only [tateClearedNext]
  have hrDen : Q.yDen * Q.xNum ≠ 0 := mul_ne_zero hyDen hxNum
  constructor
  · exact mul_ne_zero (pow_ne_zero 2 hrDen) hxDen
  constructor
  · exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hrDen
          (mul_ne_zero (pow_ne_zero 2 hrDen) hxDen))
        hxDen)
      hyDen
  constructor
  · simp only [tateNextX]
    field_simp [hxNum, hxDen, hyDen]
  · simp only [tateNextY, tateNextX]
    field_simp [hxNum, hxDen, hyDen]
    ring

/-- The fraction-free recurrence represents the rational Tate recurrence,
and all its denominators are nonzero whenever the abscissas used as secants
are nonzero. -/
theorem tateClearedCoordinates_spec
    (b c : ℚ) (n : ℕ)
    (hx : ∀ k < n, tateSuccessiveX b c k ≠ 0) :
    let Q := tateClearedCoordinates b c n
    Q.xDen ≠ 0 ∧ Q.yDen ≠ 0 ∧
      tateSuccessiveX b c n = Q.xNum / Q.xDen ∧
      tateSuccessiveY b c n = Q.yNum / Q.yDen := by
  induction n with
  | zero =>
      simp [tateClearedCoordinates]
  | succ n ih =>
      have hx' : ∀ k < n, tateSuccessiveX b c k ≠ 0 := by
        intro k hk
        exact hx k (Nat.lt_succ_of_lt hk)
      obtain ⟨hxDen, hyDen, hxEq, hyEq⟩ := ih hx'
      let Q := tateClearedCoordinates b c n
      have hxNum : Q.xNum ≠ 0 := by
        intro hxNum
        apply hx n (Nat.lt_succ_self n)
        rw [hxEq, hxNum]
        simp
      obtain ⟨hnextXDen, hnextYDen, hnextX, hnextY⟩ :=
        tateClearedNext_spec b c Q hxNum hxDen hyDen
      refine ⟨hnextXDen, hnextYDen, ?_, ?_⟩
      · rw [tateSuccessiveX_succ, hxEq, hyEq]
        exact hnextX
      · rw [tateSuccessiveY_succ, hxEq, hyEq]
        exact hnextY

/-- The `X`-coordinate of `5P` in Tate normal form. -/
def tateFiveX (b c : ℚ) : ℚ :=
  b * c * (c ^ 2 + c - b) / (b - c) ^ 2

/-- The `Y`-coordinate of `5P` in Tate normal form. -/
def tateFiveY (b c : ℚ) : ℚ :=
  b * c ^ 2 * (b ^ 2 - b * c - c ^ 3) / (b - c) ^ 3

/-- Provided `b`, `c`, and `b-c` are nonzero, the marked point has the displayed fifth
multiple. These are exactly the denominators used in the calculation. -/
theorem five_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₅ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateFiveX b c) (tateFiveY b c),
      (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some (tateFiveX b c) (tateFiveY b c) h₅ := by
  let x₄ : ℚ := b * (b - c) / c ^ 2
  let y₄ : ℚ := b ^ 2 * (c ^ 2 + c - b) / c ^ 3
  obtain ⟨h₄, hfour⟩ := four_mul_origin_coordinates b c hb hc h00
  have hx₄ : x₄ ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hb (sub_ne_zero.mpr hbc))
      (pow_ne_zero 2 hc)
  obtain ⟨h₅, hfive⟩ := add_origin_coordinates b c x₄ y₄ hx₄ h₄ h00
  have hx :
      tateNextX b c x₄ y₄ = tateFiveX b c := by
    simp only [x₄, y₄, tateNextX, tateFiveX]
    field_simp [hc, sub_ne_zero.mpr hbc]
    ring
  have hy :
      tateNextY b c x₄ y₄ = tateFiveY b c := by
    simp only [x₄, y₄, tateNextY, tateNextX, tateFiveY]
    field_simp [hc, sub_ne_zero.mpr hbc]
    ring
  refine ⟨hx ▸ hy ▸ h₅, ?_⟩
  rw [show (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (WeierstrassCurve.Affine.Point.some 0 0 h00 +
              WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00) +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hfour, hfive]
  exact WeierstrassCurve.Affine.Point.some_eq_some _ hx hy

/-- The recurrence-defined `X`-coordinate of `6P`. Keeping the sixth multiple in recurrence
form avoids expanding a much larger rational expression and makes subsequent calculations
share the same checked addition interface. -/
def tateSixX (b c : ℚ) : ℚ :=
  tateNextX b c (tateFiveX b c) (tateFiveY b c)

/-- The recurrence-defined `Y`-coordinate of `6P`. -/
def tateSixY (b c : ℚ) : ℚ :=
  tateNextY b c (tateFiveX b c) (tateFiveY b c)

/-- If the additional fifth-multiple numerator `c²+c-b` is nonzero, the recurrence computes
`6P`. Together with `b ≠ 0`, `c ≠ 0`, and `b ≠ c`, this is precisely what proves that the
`X`-coordinate of `5P` is nonzero. -/
theorem six_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₆ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateSixX b c) (tateSixY b c),
      (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some (tateSixX b c) (tateSixY b c) h₆ := by
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hx₅ : tateFiveX b c ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hb hc) hfiveNumerator)
      (pow_ne_zero 2 (sub_ne_zero.mpr hbc))
  obtain ⟨h₆, hsix⟩ :=
    add_origin_coordinates b c (tateFiveX b c) (tateFiveY b c) hx₅ h₅ h00
  refine ⟨h₆, ?_⟩
  rw [show (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hfive, hsix]
  rfl

end MazurTorsion.Kubert
