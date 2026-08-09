/-
VENDORED from mathlib4 PR #25218 — "feat(AlgebraicGeometry): Tate normal form of
elliptic curves" — branch `kckennylau/tatenf`, commit
`8b7741e0d12ae7a6e8eb998bfbcff29a4f2470c8`, file
`Mathlib/AlgebraicGeometry/EllipticCurve/Modular/TateNormalForm.lean`.

Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

AINTLIB VENDOR REGISTER: **DELETE WHEN UPSTREAM LANDS** and switch imports to
mathlib (see `.mathlib-quality/ecosystem-survey-2026-07-05.md`, Tier 1).
Local changes relative to the PR (kept minimal, adapt-don't-fork):
* dropped the `IsTateNF` class (the project's predicate is
  `WeierstrassCurve.IsTateNormal` in `Moduli/Representability.lean`; the final
  `instance : IsTateNF …` is replaced there by consuming the three component
  lemmas `toTateNF_a₆/a₄/a₂₃` directly);
* dropped the `DecidablePred NeZero` instance (unused here);
* §`Project additions` at the bottom (uniqueness of the variable change and the
  division-polynomial bridge `Ψ₃.eval P.X = …`) is OURS, not in the PR —
  upstream candidates to offer on the PR thread.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Tate normal form of elliptic curves (vendored)

This file defines the Tate normal form of Weierstrass equations of elliptic curves. It
parametrises elliptic curves with a given point `P` with `P, 2P, 3P ≠ 0`.

The equation is $$y^2 + (1-c)xy - by = x^3 - bx^2$$, and the point `P` is moved to
`(0, 0)`. Everything works over an arbitrary commutative ring `R`: the conditions
`2P ≠ 0` / `3P ≠ 0` "on all fibres" are the unit conditions `IsUnit P.pY` /
`IsUnit ((W.a₂ + 3P.X)·pY² + pX·a₁·pY − pX²)` (the latter equals `Ψ₃.eval P.X` on the
curve — see `Ψ₃_eval_X` below).
-/

noncomputable section

namespace WeierstrassCurve

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} (P : W.toAffine.Point)

/-- Typeclass for a given point not being zero (the point at infinity). -/
@[mk_iff]
class NeZero : Prop where
  neZero : P ≠ 0

/-- The `X` coordinate of a given point. For the point at infinity, this returns `0`
(junk value). -/
def X : W.toAffine.Point → R
  | 0 => 0
  | @some _ _ _ x _ _ => x

/-- The `Y` coordinate of a given point. For the point at infinity, this returns `0`
(junk value). -/
def Y : W.toAffine.Point → R
  | 0 => 0
  | @some _ _ _ _ y _ => y

variable (W) in
@[simp] lemma not_neZero_zero : ¬(NeZero (0 : W.toAffine.Point)) :=
  fun ⟨h⟩ ↦ h rfl

lemma equation_X_Y [NeZero P] : W.toAffine.Equation P.X P.Y := by
  cases P with
  | zero => exact (not_neZero_zero W).elim (by assumption)
  | some _ _ h => exact h.1

lemma equation_X_Y' [NeZero P] : P.Y^2 + W.a₁ * P.X * P.Y + W.a₃ * P.Y
    = P.X^3 + W.a₂ * P.X^2 + W.a₄ * P.X + W.a₆ :=
  (Affine.equation_iff ..).1 P.equation_X_Y

/-- The partial derivative `∂W/∂X` of the Weierstrass cubic at a given point `P`. -/
def pX : R :=
  W.a₁ * P.Y - (3 * P.X ^ 2 + 2 * W.a₂ * P.X + W.a₄)

/-- The partial derivative `∂W/∂Y` of the Weierstrass cubic at a given point `P`. -/
def pY : R :=
  2 * P.Y + W.a₁ * P.X + W.a₃

/-- The condition `2 • P ≠ 0` on all fibres. -/
@[mk_iff]
class TwiceNeZero : Prop extends P.NeZero where
  twiceNeZero : IsUnit P.pY

lemma isUnit_pY [P.TwiceNeZero] : IsUnit P.pY :=
  TwiceNeZero.twiceNeZero

lemma pY_ne_zero [P.TwiceNeZero] [Nontrivial R] : P.pY ≠ 0 :=
  P.isUnit_pY.ne_zero

/-- The inverse of `pY` as a unit, whenever `2 • P ≠ 0` (i.e. `P.TwiceNeZero`). -/
def pY_inv [P.TwiceNeZero] : Rˣ :=
  P.isUnit_pY.unit⁻¹

@[simp] lemma pY_mul_inv [P.TwiceNeZero] : P.pY * P.pY_inv = 1 := by
  have : P.isUnit_pY.unit * P.isUnit_pY.unit⁻¹ = 1 := mul_inv_cancel _
  rwa [Units.ext_iff, Units.val_mul, IsUnit.unit_spec] at this

@[simp] lemma pY_inv_mul [P.TwiceNeZero] : (P.pY_inv : R) * P.pY = 1 :=
  (mul_comm ..).trans P.pY_mul_inv

@[simp] lemma pY_inv_inv [P.TwiceNeZero] : P.pY_inv⁻¹ = P.pY := by
  rw [pY_inv, inv_inv]; rfl

/-- A quantity that determines whether `3 • P = 0`. -/
def μ [P.TwiceNeZero] : R :=
  W.a₂ + 3 * P.X + P.pX * P.pY_inv * W.a₁ - (P.pX * P.pY_inv) ^ 2

/-- The condition `3 • P ≠ 0` on all fibres. -/
@[mk_iff]
class ThriceNeZero : Prop extends P.NeZero where
  thriceNeZero : IsUnit ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2)

lemma thriceNeZero_isUnit [P.ThriceNeZero] :
    IsUnit ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2) :=
  ThriceNeZero.thriceNeZero

lemma isUnit_μ [P.TwiceNeZero] [P.ThriceNeZero] : IsUnit P.μ := by
  have h1 : P.pY * (P.pY_inv : R) = 1 := P.pY_mul_inv
  have h : P.μ = ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2)
      * (P.pY_inv : R) ^ 2 := by
    rw [μ]
    linear_combination (-(W.a₂ + 3 * P.X) * (1 + P.pY * (P.pY_inv : R))
      - P.pX * W.a₁ * (P.pY_inv : R)) * h1
  rw [h]
  exact P.thriceNeZero_isUnit.mul (P.pY_inv.isUnit.pow 2)

/-- The inverse of `μ` as a unit, whenever `3 • P ≠ 0` (i.e. `P.ThriceNeZero`). -/
def μ_inv [P.TwiceNeZero] [P.ThriceNeZero] : Rˣ :=
  P.isUnit_μ.unit⁻¹

@[simp] lemma μ_mul_inv [P.TwiceNeZero] [P.ThriceNeZero] : P.μ * P.μ_inv = 1 := by
  have : P.isUnit_μ.unit * P.isUnit_μ.unit⁻¹ = 1 := mul_inv_cancel _
  rwa [Units.ext_iff, Units.val_mul, IsUnit.unit_spec] at this

@[simp] lemma μ_inv_mul [P.TwiceNeZero] [P.ThriceNeZero] : (P.μ_inv : R) * P.μ = 1 :=
  (mul_comm ..).trans P.μ_mul_inv

@[simp] lemma μ_inv_inv [P.TwiceNeZero] [P.ThriceNeZero] : P.μ_inv⁻¹ = P.μ := by
  rw [μ_inv, inv_inv]; rfl

end Affine.Point

namespace Affine

variable {R : Type*} [CommRing R] (W : Affine R) (P : W.toAffine.Point)

/-- Whenever a point is not zero, we can transform the Weierstrass cubic to move the point to
the origin `(0, 0)`, which eliminates the `a₆` coefficient. -/
def ofNeZero : VariableChange R where
  u := 1
  r := P.X
  s := 0
  t := P.Y

@[simp] lemma ofNeZero_a₆ [P.NeZero] : (W.ofNeZero P • W).a₆ = 0 :=
  equation_zero.1 <| (equation_iff_variableChange ..).1 <| P.equation_X_Y

@[simp] lemma ofNeZero_a₄ : (W.ofNeZero P • W).a₄ = -P.pX := by
  simp [variableChange_a₄, ofNeZero, Point.pX]; ring_nf

@[simp] lemma ofNeZero_a₃ : (W.ofNeZero P • W).a₃ = P.pY := by
  simp [variableChange_a₃, ofNeZero, Point.pY]; ring_nf

@[simp] lemma ofNeZero_a₂ : (W.ofNeZero P • W).a₂ = W.a₂ + 3 * P.X := by
  simp [variableChange_a₂, ofNeZero]

@[simp] lemma ofNeZero_a₁ : (W.ofNeZero P • W).a₁ = W.a₁ := by
  simp [variableChange_a₁, ofNeZero]

/-- The intermediate step used in `ofTwiceNeZero`. See `ofTwiceNeZero_eq`. -/
def ofTwiceNeZero_aux [P.TwiceNeZero] : VariableChange R where
  u := 1
  r := 0
  s := -P.pX * P.pY_inv
  t := 0

/-- Whenever a point `P` satisfies `2 • P ≠ 0`, we can transform the Weierstrass cubic to move the
point to the origin `(0, 0)`, and also transform the tangent line at `(0, 0)` to be horizontal.
This eliminates the `a₄` and `a₆` coefficient. -/
def ofTwiceNeZero [P.TwiceNeZero] : VariableChange R where
  u := 1
  r := P.X
  s := -P.pX * P.pY_inv
  t := P.Y

lemma ofTwiceNeZero_eq [P.TwiceNeZero] : W.ofTwiceNeZero P =
    W.ofTwiceNeZero_aux P * W.ofNeZero P := by
  simp [ofTwiceNeZero, ofTwiceNeZero_aux, ofNeZero, VariableChange.mul_def]

@[simp] lemma ofTwiceNeZero_a₆ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₆ = 0 := by
  rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₆, ofTwiceNeZero_aux]
  simp

@[simp] lemma ofTwiceNeZero_a₄ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₄ = 0 := calc
  _ = -P.pX + P.pX * P.pY_inv * P.pY := by
    rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₄, ofTwiceNeZero_aux]
    simp
  _ = 0 := by rw [mul_assoc, P.pY_inv_mul, mul_one, neg_add_cancel]

@[simp] lemma ofTwiceNeZero_a₃ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₃ = P.pY := by
    rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₃, ofTwiceNeZero_aux]
    simp

@[simp] lemma ofTwiceNeZero_a₂ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₂ = P.μ := by
    rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₂, ofTwiceNeZero_aux, Point.μ]
    simp

/-- The intermediate step used in `toTateNF`. See `toTateNF_eq`. -/
def toTateNF_aux [P.TwiceNeZero] [P.ThriceNeZero] : VariableChange R where
  u := P.isUnit_pY.unit * P.μ_inv
  r := 0
  s := 0
  t := 0

/-- Whenever a point `P` satisfies `3 • P ≠ 0`, we can transform the Weierstrass cubic to move the
point to the origin `(0, 0)`, and also transform the tangent line at `(0, 0)` to be horizontal,
and also make the x-intercept and y-intercept the same. This brings the curve to the Tate normal
form, by eliminating the `a₄` and `a₆` coefficient, and also making `a₂ = a₃`. -/
def toTateNF [P.TwiceNeZero] [P.ThriceNeZero] : VariableChange R where
  u := P.isUnit_pY.unit * P.μ_inv
  r := P.X
  s := -P.pX * P.pY_inv
  t := P.Y

lemma toTateNF_eq [P.TwiceNeZero] [P.ThriceNeZero] : W.toTateNF P =
    W.toTateNF_aux P * W.ofTwiceNeZero P := by
  simp [toTateNF, toTateNF_aux, ofTwiceNeZero, VariableChange.mul_def]

lemma toTateNF_a₆ [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P • W).a₆ = 0 := by
  rw [toTateNF_eq, mul_smul, variableChange_a₆, ofTwiceNeZero_a₆, ofTwiceNeZero_a₄]
  simp [toTateNF_aux]

lemma toTateNF_a₄ [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P • W).a₄ = 0 := by
  rw [toTateNF_eq, mul_smul, variableChange_a₄, ofTwiceNeZero_a₄]
  simp [toTateNF_aux]

lemma toTateNF_a₂₃ [P.TwiceNeZero] [P.ThriceNeZero] :
    (W.toTateNF P • W).a₂ = (W.toTateNF P • W).a₃ := by
  rw [toTateNF_eq, mul_smul, variableChange_a₂, variableChange_a₃]
  simp [toTateNF_aux, -Units.val_inv_eq_inv_val]
  calc (P.μ * P.pY_inv) ^ 2 * P.μ
    = (P.μ * P.pY_inv) ^ 2 * P.μ * (P.pY * P.pY_inv) := by rw [P.pY_mul_inv, mul_one]
  _ = (P.μ * P.pY_inv) ^ 3 * P.pY := by ring_nf

end Affine

/-! ## Project additions (NOT in PR #25218 — AINTLIB, upstream candidates)

The uniqueness half of Loeffler Prop 3.3.4 (the PR only constructs the variable
change), and the bridge from the division-polynomial hypotheses `IsUnit (ψ₂-eval)`,
`IsUnit (Ψ₃-eval)` to the PR's `TwiceNeZero` / `ThriceNeZero` classes. The bridge
identity is
`(a₂ + 3x)·pY² + pX·a₁·pY − pX² = Ψ₃(x) + (b₂ + 12x)·(equation defect)`,
so on the curve the `ThriceNeZero` quantity IS `Ψ₃.eval x`. -/

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} (P : W.toAffine.Point)

@[simp] lemma X_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    (Affine.Point.some x y h).X = x := rfl

@[simp] lemma Y_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    (Affine.Point.some x y h).Y = y := rfl

/-- On the curve, the `ThriceNeZero` quantity is the value of the `3`-division
polynomial: `(a₂ + 3X)·pY² + pX·a₁·pY − pX² = Ψ₃.eval X`. -/
lemma Ψ₃_eval_X [P.NeZero] :
    W.Ψ₃.eval P.X
      = (W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2 := by
  have h := P.equation_X_Y'
  simp only [Ψ₃, b₂, b₄, b₆, b₈, pX, pY, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  linear_combination (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * P.X)) * h

/-- Bridge: a point on the curve with `IsUnit (ψ₂-value)` satisfies `TwiceNeZero`. -/
lemma twiceNeZero_of_isUnit [P.NeZero] (h : IsUnit (W.ψ₂.evalEval P.X P.Y)) :
    P.TwiceNeZero where
  toNeZero := ‹P.NeZero›
  twiceNeZero := by
    rwa [ψ₂, Affine.evalEval_polynomialY] at h

/-- Bridge: a point on the curve with `IsUnit (Ψ₃-value)` satisfies `ThriceNeZero`. -/
lemma thriceNeZero_of_isUnit [P.NeZero] (h : IsUnit (W.Ψ₃.eval P.X)) :
    P.ThriceNeZero where
  toNeZero := ‹P.NeZero›
  thriceNeZero := by rwa [P.Ψ₃_eval_X] at h

end Affine.Point

namespace Affine

variable {R : Type*} [CommRing R] (W : Affine R) (P : W.toAffine.Point)

@[simp] lemma toTateNF_r [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P).r = P.X := rfl

@[simp] lemma toTateNF_t [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P).t = P.Y := rfl

/-- **Uniqueness of the Tate-normalising variable change** (the uniqueness half of
Loeffler Prop 3.3.4; not in PR #25218): a variable change carrying `P` to `(0,0)`
(`r = P.X`, `t = P.Y`) whose result has `a₄ = 0` and `a₂ = a₃` is `toTateNF`.
Note the `a₆`-condition is not even needed. -/
theorem toTateNF_unique [P.TwiceNeZero] [P.ThriceNeZero] (vc : VariableChange R)
    (hr : vc.r = P.X) (ht : vc.t = P.Y)
    (h₄ : (vc • W).a₄ = 0) (h₂₃ : (vc • W).a₂ = (vc • W).a₃) :
    vc = W.toTateNF P := by
  have hs : vc.s = -P.pX * P.pY_inv := by
    rw [variableChange_a₄, hr, ht] at h₄
    have h' : W.a₄ - vc.s * W.a₃ + 2 * P.X * W.a₂ - (P.Y + P.X * vc.s) * W.a₁
        + 3 * P.X ^ 2 - 2 * vc.s * P.Y = 0 :=
      ((vc.u⁻¹ : Rˣ).isUnit.pow 4).mul_right_eq_zero.mp h₄
    have h1 : vc.s * P.pY = -P.pX * P.pY_inv * P.pY := by
      rw [mul_assoc, P.pY_inv_mul, mul_one]
      simp only [Point.pX, Point.pY]
      linear_combination -h'
    exact P.isUnit_pY.mul_right_cancel h1
  have hu : (vc.u : R) = P.pY * (P.μ_inv : R) := by
    rw [variableChange_a₂, variableChange_a₃, hr, ht, hs] at h₂₃
    have hμ : W.a₂ - -P.pX * P.pY_inv * W.a₁ + 3 * P.X - (-P.pX * P.pY_inv) ^ 2 = P.μ := by
      rw [Point.μ]; ring
    have hpY : W.a₃ + P.X * W.a₁ + 2 * P.Y = P.pY := by
      rw [Point.pY]; ring
    rw [hμ, hpY] at h₂₃
    have hinv : ((vc.u⁻¹ : Rˣ) : R) * (vc.u : R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have key : (vc.u : R) * P.μ = P.pY := by
      linear_combination ((vc.u : R)) ^ 3 * h₂₃ +
        (P.pY * (((vc.u⁻¹ : Rˣ) : R) ^ 2 * (vc.u : R) ^ 2
            + ((vc.u⁻¹ : Rˣ) : R) * (vc.u : R) + 1)
          - (vc.u : R) * P.μ * (1 + ((vc.u⁻¹ : Rˣ) : R) * (vc.u : R))) * hinv
    calc (vc.u : R) = (vc.u : R) * (P.μ * (P.μ_inv : R)) := by rw [P.μ_mul_inv, mul_one]
    _ = ((vc.u : R) * P.μ) * (P.μ_inv : R) := by ring
    _ = P.pY * (P.μ_inv : R) := by rw [key]
  ext
  · show (vc.u : R) = ((W.toTateNF P).u : R)
    rw [hu, toTateNF]
    simp [IsUnit.unit_spec]
  · exact hr
  · exact hs
  · exact ht

end Affine

end WeierstrassCurve
