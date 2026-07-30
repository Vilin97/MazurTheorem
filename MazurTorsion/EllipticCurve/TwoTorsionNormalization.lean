/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TwoIsogeny
import MazurTorsion.EllipticCurve.VariableChange

/-!
# Normalizing a rational point of order two

Let `T` be a rational point of exact order two on a Weierstrass curve
`E/ℚ`.  This file packages the elementary admissible change of variables
which translates `T` to `(0,0)` and completes the square.  The transformed
curve has the form

`y² = x(x² + ax + b)`,

namely `TwoIsogeny.sourceCurve a b`.

The result is recorded as `Data E T`.  Besides the change of variables and
the two coefficients, the structure retains the nonsingularity proof for
the new origin, the equality with the standard source model, and the
point-group equivalence carrying the new origin back to `T`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.TwoTorsionNormalization

open WeierstrassCurve

/-- A checked normalization of a rational two-torsion point. -/
structure Data (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (T : E.toAffine.Point) where
  change : WeierstrassCurve.VariableChange ℚ
  a : ℚ
  b : ℚ
  originNonsingular :
    (change • E).toAffine.Nonsingular 0 0
  curve_eq :
    change • E = MazurTorsion.TwoIsogeny.sourceCurve a b
  map_origin :
    WeierstrassCurve.Affine.Point.equivVariableChange E change
        (.some 0 0 originNonsingular) = T

namespace Data

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]
  {T : E.toAffine.Point}

/-- The point-group equivalence supplied by the normalization. -/
noncomputable def equiv (D : Data E T) :
    (D.change • E).toAffine.Point ≃+ E.toAffine.Point :=
  WeierstrassCurve.Affine.Point.equivVariableChange E D.change

/-- The normalized origin `(0,0)`. -/
def origin (D : Data E T) :
    (D.change • E).toAffine.Point :=
  .some 0 0 D.originNonsingular

@[simp] theorem equiv_origin (D : Data E T) :
    D.equiv D.origin = T :=
  D.map_origin

/-- Pull a point of the original curve back to the normalized model. -/
noncomputable def pullback (D : Data E T)
    (P : E.toAffine.Point) :
    (D.change • E).toAffine.Point :=
  D.equiv.symm P

@[simp] theorem equiv_pullback (D : Data E T)
    (P : E.toAffine.Point) :
    D.equiv (D.pullback P) = P :=
  D.equiv.apply_symm_apply P

theorem addOrderOf_pullback (D : Data E T)
    (P : E.toAffine.Point) :
    addOrderOf (D.pullback P) = addOrderOf P := by
  rw [← AddEquiv.addOrderOf_eq D.equiv]
  exact congrArg addOrderOf (D.equiv_pullback P)

/-- A multiple relation ending at `T` pulls back to the normalized
origin. -/
theorem nsmul_pullback_eq_origin (D : Data E T)
    (P : E.toAffine.Point) (n : ℕ)
    (h : n • P = T) :
    n • D.pullback P = D.origin := by
  apply D.equiv.injective
  rw [map_nsmul, D.equiv_pullback, D.equiv_origin]
  exact h

/-- Ellipticity transported to the standard source curve. -/
theorem source_isElliptic (D : Data E T) :
    (MazurTorsion.TwoIsogeny.sourceCurve D.a D.b).IsElliptic := by
  rw [← D.curve_eq]
  infer_instance

/-- The normalization equivalence with its source written literally as
`TwoIsogeny.sourceCurve`. -/
noncomputable def sourceEquiv (D : Data E T) :
    letI := D.source_isElliptic
    (MazurTorsion.TwoIsogeny.sourceCurve D.a D.b).toAffine.Point ≃+
      E.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq D.curve_eq.symm).trans
    D.equiv

/-- Pull a point directly to the literal standard source curve. -/
noncomputable def sourcePullback (D : Data E T)
    (P : E.toAffine.Point) :
    letI := D.source_isElliptic
    (MazurTorsion.TwoIsogeny.sourceCurve D.a D.b).toAffine.Point :=
  D.sourceEquiv.symm P

@[simp] theorem sourceEquiv_sourcePullback (D : Data E T)
    (P : E.toAffine.Point) :
    letI := D.source_isElliptic
    D.sourceEquiv (D.sourcePullback P) = P :=
  D.sourceEquiv.apply_symm_apply P

theorem addOrderOf_sourcePullback (D : Data E T)
    (P : E.toAffine.Point) :
    letI := D.source_isElliptic
    addOrderOf (D.sourcePullback P) = addOrderOf P := by
  letI := D.source_isElliptic
  rw [← AddEquiv.addOrderOf_eq D.sourceEquiv]
  exact congrArg addOrderOf (D.sourceEquiv_sourcePullback P)

/-- A terminal relation `nP=T` becomes the literal source-origin relation
on `TwoIsogeny.sourceCurve`. -/
theorem nsmul_sourcePullback_eq_sourceOrigin
    (D : Data E T) (P : E.toAffine.Point) (n : ℕ)
    (h : n • P = T) :
    letI := D.source_isElliptic
    n • D.sourcePullback P =
      MazurTorsion.TwoIsogeny.sourceOrigin D.a D.b := by
  letI := D.source_isElliptic
  apply D.sourceEquiv.injective
  rw [map_nsmul, D.sourceEquiv_sourcePullback]
  calc
    n • P = T := h
    _ = D.equiv D.origin := D.equiv_origin.symm
    _ = D.equiv
        (WeierstrassCurve.Affine.Point.equivOfEq D.curve_eq.symm
          (MazurTorsion.TwoIsogeny.sourceOrigin D.a D.b)) := by
      apply congrArg D.equiv
      simp [Data.origin, MazurTorsion.TwoIsogeny.sourceOrigin,
        WeierstrassCurve.Affine.Point.equivOfEq_some]

end Data

/-- Every rational point of exact order two admits the standard
`y²=x(x²+ax+b)` normalization. -/
theorem exists_data_of_order_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (T : E.toAffine.Point) (hTorder : addOrderOf T = 2) :
    Nonempty (Data E T) := by
  have hT0 : T ≠ 0 := by
    intro hT0
    rw [hT0, addOrderOf_zero] at hTorder
    norm_num at hTorder
  have hTdouble : (2 : ℕ) • T = 0 := by
    rw [← hTorder]
    exact addOrderOf_nsmul_eq_zero T
  obtain ⟨theta, yT, hTns, hTxy⟩ :
      ∃ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
        T = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : T with
    | zero => exact (hT0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hvertical : yT = E.toAffine.negY theta yT := by
    by_contra hne
    have hnonzero :
        WeierstrassCurve.Affine.Point.some theta yT hTns +
            WeierstrassCurve.Affine.Point.some theta yT hTns ≠ 0 := by
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    apply hnonzero
    rw [← two_nsmul, ← hTxy]
    exact hTdouble
  have hvertical' :
      E.a₃ + theta * E.a₁ + 2 * yT = 0 := by
    rw [WeierstrassCurve.Affine.negY] at hvertical
    linear_combination hvertical
  let C : WeierstrassCurve.VariableChange ℚ :=
    ⟨1, theta, -E.a₁ / 2, yT⟩
  let W : WeierstrassCurve ℚ := C • E
  have hWa₁ : W.a₁ = 0 := by
    dsimp [W, C]
    rw [WeierstrassCurve.variableChange_a₁]
    simp
    ring
  have hWa₃ : W.a₃ = 0 := by
    dsimp [W, C]
    rw [WeierstrassCurve.variableChange_a₃]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hvertical'
  have hWa₆ : W.a₆ = 0 := by
    have heq := hTns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    dsimp [W, C]
    rw [WeierstrassCurve.variableChange_a₆]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00 : W.toAffine.Nonsingular 0 0 := by
    apply W.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_zero]
    exact hWa₆
  let a : ℚ := W.a₂
  let b : ℚ := W.a₄
  have hWsource :
      W = MazurTorsion.TwoIsogeny.sourceCurve a b := by
    ext <;>
      simp [MazurTorsion.TwoIsogeny.sourceCurve,
        a, b, hWa₁, hWa₃, hWa₆]
  have hmapOrigin :
      WeierstrassCurve.Affine.Point.equivVariableChange E C
          (WeierstrassCurve.Affine.Point.some 0 0 h00) = T := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some,
      hTxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some E
      (by simp [C]) (by simp [C])
  refine ⟨{
    change := C
    a := a
    b := b
    originNonsingular := ?_
    curve_eq := ?_
    map_origin := ?_ }⟩
  · simpa only [W] using h00
  · simpa only [W] using hWsource
  · simpa only [Data.origin] using hmapOrigin

end MazurTorsion.TwoTorsionNormalization
