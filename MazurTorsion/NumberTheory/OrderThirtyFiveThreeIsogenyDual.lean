/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveThreeIsogeny

/-!
# The equation-checked dual three-isogeny candidate at level 35

This file constructs the rational point function in the direction opposite to
`OrderThirtyFive.veluThreeCandidatePointFun`.  In completed-square
coordinates, the two fixed curves are

```
z² = 4x³ + 16x² + 56x + 49,
Z² = 4X³ + 16X² - 504X - 3115.
```

The dual kernel has linear abscissa factor `3X + 16`; it has no rational
affine point on the target curve.  Consequently the dual formulas define a
total rational point function.  We also check that its composite with the
first candidate is multiplication by three on the actual affine point group.

The declarations remain point-function candidates: the exact Mathlib pin has
no bundled elliptic-curve morphism API, and this file does not assert
additivity of either point function in isolation.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- The rational linear factor cutting out the geometric dual kernel. -/
def veluThreeDualCandidateKernel (X : ℚ) : ℚ :=
  3 * X + 16

/-- The candidate dual abscissa. -/
def veluThreeDualCandidateX (X : ℚ) : ℚ :=
  (X ^ 3 - 252 * X - 1771) /
    veluThreeDualCandidateKernel X ^ 2

/-- The completed-ordinate multiplier for the candidate dual map. -/
def veluThreeDualCandidateDifferential (X : ℚ) : ℚ :=
  (X ^ 3 + 16 * X ^ 2 + 252 * X + 2198) /
    veluThreeDualCandidateKernel X ^ 3

/-- The candidate dual ordinate. -/
def veluThreeDualCandidateY (X Y : ℚ) : ℚ :=
  ((2 * Y + 4 * X + 7) *
      veluThreeDualCandidateDifferential X -
    4 * veluThreeDualCandidateX X - 7) / 2

/-- The completed-square polynomial of the source curve. -/
private def sourceCompletedPolynomial (x : ℚ) : ℚ :=
  4 * x ^ 3 + 16 * x ^ 2 + 56 * x + 49

/-- The completed-square polynomial of the candidate target. -/
private def targetCompletedPolynomial (X : ℚ) : ℚ :=
  4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115

/-- The dual formulas carry the target completed-square equation to the
source completed-square equation. -/
private theorem veluThreeDualCandidate_completedSquare (X : ℚ)
    (hkernel : veluThreeDualCandidateKernel X ≠ 0) :
    veluThreeDualCandidateDifferential X ^ 2 *
        targetCompletedPolynomial X =
      sourceCompletedPolynomial (veluThreeDualCandidateX X) := by
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let B : ℚ := X ^ 3 + 16 * X ^ 2 + 252 * X + 2198
  let T : ℚ := 4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115
  have hK : K ≠ 0 := by
    simpa only [K, veluThreeDualCandidateKernel] using hkernel
  change (B / K ^ 3) ^ 2 * T =
    4 * (A / K ^ 2) ^ 3 + 16 * (A / K ^ 2) ^ 2 +
      56 * (A / K ^ 2) + 49
  field_simp [hK]
  dsimp only [A, B, K, T]
  ring

/-- No rational affine target point lies on the denominator of the dual
candidate. -/
theorem veluThreeDualCandidateKernel_ne_zero
    {X Y : ℚ}
    (hP : (veluThreeCandidateTarget.toAffine).Nonsingular X Y) :
    veluThreeDualCandidateKernel X ≠ 0 := by
  intro hkernel
  have hX : X = -16 / 3 := by
    dsimp only [veluThreeDualCandidateKernel] at hkernel
    linarith
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget, hX] at hcurve
  nlinarith [sq_nonneg (6 * Y - 43)]

/-- Direct substitution verifies that the dual formulas land on the source
curve. -/
theorem veluThreeDualCandidate_equation {X Y : ℚ}
    (hkernel : veluThreeDualCandidateKernel X ≠ 0)
    (hcurve : Y ^ 2 + 4 * X * Y + 7 * Y =
      X ^ 3 - 140 * X - 791) :
    threeTorsionCurve.toAffine.Equation
      (veluThreeDualCandidateX X)
      (veluThreeDualCandidateY X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [threeTorsionCurve]
  have hsource :
      (2 * Y + 4 * X + 7) ^ 2 =
        targetCompletedPolynomial X := by
    dsimp only [targetCompletedPolynomial]
    nlinarith
  have htarget :
      (2 * veluThreeDualCandidateY X Y +
          4 * veluThreeDualCandidateX X + 7) ^ 2 =
        sourceCompletedPolynomial (veluThreeDualCandidateX X) := by
    rw [← veluThreeDualCandidate_completedSquare X hkernel, ← hsource]
    simp only [veluThreeDualCandidateY]
    ring
  dsimp only [sourceCompletedPolynomial] at htarget
  nlinarith

/-- The affine value of the dual candidate. -/
noncomputable def veluThreeDualCandidatePoint
    {X Y : ℚ}
    (hP : (veluThreeCandidateTarget.toAffine).Nonsingular X Y) :
    threeTorsionCurve.toAffine.Point :=
  .some (veluThreeDualCandidateX X)
    (veluThreeDualCandidateY X Y)
    (threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
      (veluThreeDualCandidate_equation
        (veluThreeDualCandidateKernel_ne_zero hP) (by
        have heq := hP.1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        norm_num [veluThreeCandidateTarget] at heq ⊢
        simpa only [sub_eq_add_neg] using heq)))

/-- The total dual candidate on rational points.  The rational dual kernel is
trivial, so every nonzero rational point uses the affine formula. -/
noncomputable def veluThreeDualCandidatePointFun :
    (veluThreeCandidateTarget.toAffine).Point →
      threeTorsionCurve.toAffine.Point
  | .zero => .zero
  | .some _ _ hP => veluThreeDualCandidatePoint hP

@[simp] theorem veluThreeDualCandidatePointFun_zero :
    veluThreeDualCandidatePointFun 0 = 0 :=
  rfl

/-! ## The composite rational functions -/

/-- The completed-ordinate multiplier of the first candidate. -/
private def veluThreeCandidateDifferential (x : ℚ) : ℚ :=
  (x ^ 3 - 28 * x - 98) / x ^ 3

/-- The non-visible factor in the source third-division polynomial. -/
private def sourceThreeDivisionCofactor (x : ℚ) : ℚ :=
  (3 * x + 7) * (x ^ 2 + 3 * x + 21)

/-- The source third-division polynomial, in its fixed-model
factorization. -/
private def sourceThreeDivisionPolynomial (x : ℚ) : ℚ :=
  x * sourceThreeDivisionCofactor x

/-- The numerator of the multiplication-by-three abscissa. -/
private def tripleAbscissaNumerator (x : ℚ) : ℚ :=
  x ^ 9 - 168 * x ^ 7 - 1624 * x ^ 6 - 4704 * x ^ 5 -
    4116 * x ^ 4 + 29155 * x ^ 3 + 115248 * x ^ 2 +
    201684 * x + 117649

/-- The multiplication-by-three abscissa rational function. -/
private def tripleAbscissa (x : ℚ) : ℚ :=
  tripleAbscissaNumerator x / sourceThreeDivisionPolynomial x ^ 2

/-- The degree-six factor in the multiplication-by-three completed
ordinate. -/
private def tripleDifferentialCofactor (x : ℚ) : ℚ :=
  x ^ 6 + 9 * x ^ 5 + 280 * x ^ 4 + 1295 * x ^ 3 +
    3430 * x ^ 2 + 4459 * x + 2401

/-- The numerator of the multiplication-by-three completed-ordinate
multiplier. -/
private def tripleDifferentialNumerator (x : ℚ) : ℚ :=
  (x ^ 3 - 28 * x - 98) *
    (x ^ 3 + 7 * x ^ 2 - 7 * x + 49) *
      tripleDifferentialCofactor x

/-- The multiplication-by-three completed-ordinate multiplier. -/
private def tripleDifferential (x : ℚ) : ℚ :=
  tripleDifferentialNumerator x / sourceThreeDivisionPolynomial x ^ 3

/-- The first candidate acts diagonally on the completed ordinate. -/
private theorem veluThreeCandidate_completed {x y : ℚ}
    (hx : x ≠ 0) :
    2 * veluThreeCandidateY x y +
        4 * veluThreeCandidateX x + 7 =
      (2 * y + 4 * x + 7) * veluThreeCandidateDifferential x := by
  simp only [veluThreeCandidateY, veluThreeCandidateX,
    veluThreeCandidateDifferential]
  field_simp [hx]
  ring

/-- Pulling back the dual denominator gives the non-visible source
third-division factor. -/
private theorem veluThreeDualCandidateKernel_candidateX {x : ℚ}
    (hx : x ≠ 0) :
    veluThreeDualCandidateKernel (veluThreeCandidateX x) =
      sourceThreeDivisionCofactor x / x ^ 2 := by
  simp only [veluThreeDualCandidateKernel, veluThreeCandidateX,
    sourceThreeDivisionCofactor]
  field_simp [hx]
  ring

/-- Pulling back the dual abscissa gives the standard tripling rational
function. -/
private theorem veluThreeDualCandidateX_candidateX {x : ℚ}
    (hx : x ≠ 0)
    (hcofactor : sourceThreeDivisionCofactor x ≠ 0) :
    veluThreeDualCandidateX (veluThreeCandidateX x) =
      tripleAbscissa x := by
  simp only [veluThreeDualCandidateX, tripleAbscissa]
  rw [veluThreeDualCandidateKernel_candidateX hx]
  simp only [veluThreeCandidateX, sourceThreeDivisionPolynomial]
  field_simp [hx, hcofactor]
  simp only [tripleAbscissaNumerator]
  ring

/-- Pulling back the dual completed-ordinate multiplier gives the remaining
factor in the tripling multiplier. -/
private theorem veluThreeDualCandidateDifferential_candidateX {x : ℚ}
    (hx : x ≠ 0)
    (hcofactor : sourceThreeDivisionCofactor x ≠ 0) :
    veluThreeDualCandidateDifferential (veluThreeCandidateX x) =
      (x ^ 3 + 7 * x ^ 2 - 7 * x + 49) *
          tripleDifferentialCofactor x /
        sourceThreeDivisionCofactor x ^ 3 := by
  simp only [veluThreeDualCandidateDifferential]
  rw [veluThreeDualCandidateKernel_candidateX hx]
  simp only [veluThreeCandidateX]
  field_simp [hx, hcofactor]
  simp only [tripleDifferentialCofactor]
  ring

/-- The completed ordinate of the two candidate maps composes to the
tripling rational function. -/
private theorem veluThreeDualCandidateY_candidate_completed {x y : ℚ}
    (hx : x ≠ 0)
    (hcofactor : sourceThreeDivisionCofactor x ≠ 0) :
    2 * veluThreeDualCandidateY
          (veluThreeCandidateX x) (veluThreeCandidateY x y) +
        4 * veluThreeDualCandidateX (veluThreeCandidateX x) + 7 =
      (2 * y + 4 * x + 7) * tripleDifferential x := by
  calc
    2 * veluThreeDualCandidateY
          (veluThreeCandidateX x) (veluThreeCandidateY x y) +
        4 * veluThreeDualCandidateX (veluThreeCandidateX x) + 7 =
      (2 * veluThreeCandidateY x y +
          4 * veluThreeCandidateX x + 7) *
        veluThreeDualCandidateDifferential (veluThreeCandidateX x) := by
          simp only [veluThreeDualCandidateY]
          ring
    _ = (2 * y + 4 * x + 7) * tripleDifferential x := by
      rw [veluThreeCandidate_completed hx,
        veluThreeDualCandidateDifferential_candidateX hx hcofactor]
      simp only [veluThreeCandidateDifferential,
        tripleDifferential, tripleDifferentialNumerator,
        sourceThreeDivisionPolynomial]
      field_simp [hx, hcofactor]

/-! ## Identification with multiplication by three -/

/-- The abscissa of the double of a source point. -/
private def doubleAbscissa (x : ℚ) : ℚ :=
  x * (x ^ 3 - 28 * x - 98) / sourceCompletedPolynomial x

/-- The completed-ordinate multiplier of doubling on the source. -/
private def doubleDifferential (x : ℚ) : ℚ :=
  (2 * x ^ 6 + 16 * x ^ 5 + 140 * x ^ 4 + 490 * x ^ 3 -
      1372 * x - 2401) /
    sourceCompletedPolynomial x ^ 2

/-- The normalized completed slope of the secant from a point to its
double. -/
private def tripleSecantSlopeFactor (x : ℚ) : ℚ :=
  2 * (7 * x ^ 6 + 56 * x ^ 5 + 282 * x ^ 4 + 847 * x ^ 3 +
      2352 * x ^ 2 + 3430 * x + 2401) /
    (sourceThreeDivisionPolynomial x * sourceCompletedPolynomial x)

private theorem source_completed_equation {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y) :
    (2 * y + 4 * x + 7) ^ 2 = sourceCompletedPolynomial x := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve, sourceCompletedPolynomial] at hcurve ⊢
  nlinarith

private theorem source_eq_zero_of_two_nsmul_eq_zero
    (P : threeTorsionCurve.toAffine.Point)
    (hP : (2 : ℕ) • P = 0) :
    P = 0 := by
  apply threeTorsionEquiv.injective
  rw [map_zero]
  apply eq_zero_of_two_nsmul_eq_zero
  rw [← map_nsmul, hP, map_zero]

private theorem sourceThreeDivisionCofactor_ne_zero
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y) :
    sourceThreeDivisionCofactor x ≠ 0 := by
  apply mul_ne_zero
  · intro hlinear
    have hx : x = -7 / 3 := by linarith
    have hcompleted := source_completed_equation hP
    norm_num [sourceCompletedPolynomial, hx] at hcompleted
    nlinarith [sq_nonneg (2 * y + 4 * x + 7)]
  · have hpositive : 0 < x ^ 2 + 3 * x + 21 := by
      nlinarith [sq_nonneg (2 * x + 3)]
    exact ne_of_gt hpositive

private theorem sourceThreeDivisionPolynomial_ne_zero
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    sourceThreeDivisionPolynomial x ≠ 0 :=
  mul_ne_zero hx (sourceThreeDivisionCofactor_ne_zero hP)

private theorem eval_source_Psi_three (x : ℚ) :
    Polynomial.eval x threeTorsionCurve.Ψ₃ =
      sourceThreeDivisionPolynomial x := by
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, threeTorsionCurve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor]
  ring

private theorem source_three_nsmul_some_ne_zero
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP ≠ 0 := by
  intro hthree
  have hroot :=
    (MazurTorsion.ThreeTorsion.three_nsmul_some_eq_zero_iff
      threeTorsionCurve hP).mp hthree
  apply sourceThreeDivisionPolynomial_ne_zero hP hx
  rwa [eval_source_Psi_three] at hroot

private theorem addX_eq_completed
    (x₁ x₂ ℓ : ℚ) :
    threeTorsionCurve.toAffine.addX x₁ x₂ ℓ =
      (2 * ℓ + 4) ^ 2 / 4 - 4 - x₁ - x₂ := by
  simp only [WeierstrassCurve.Affine.addX, threeTorsionCurve]
  ring

private theorem addY_completed
    (x₁ x₂ y₁ ℓ : ℚ) :
    2 * threeTorsionCurve.toAffine.addY x₁ x₂ y₁ ℓ +
        4 * threeTorsionCurve.toAffine.addX x₁ x₂ ℓ + 7 =
      -(2 * y₁ + 4 * x₁ + 7) -
        (2 * ℓ + 4) *
          (threeTorsionCurve.toAffine.addX x₁ x₂ ℓ - x₁) := by
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX, threeTorsionCurve]
  ring

private theorem tangent_completed_slope {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hy : y ≠ threeTorsionCurve.toAffine.negY x y) :
    2 * threeTorsionCurve.toAffine.slope x x y y + 4 =
      (2 * y + 4 * x + 7) *
        (6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x := by
  let z : ℚ := 2 * y + 4 * x + 7
  let A : ℚ := 6 * x ^ 2 + 16 * x + 28
  have hz : z ≠ 0 := by
    intro hz
    apply hy
    simp only [threeTorsionCurve, WeierstrassCurve.Affine.negY]
    dsimp only [z] at hz
    linarith
  have hcompleted := source_completed_equation hP
  have hD : sourceCompletedPolynomial x ≠ 0 := by
    rw [← hcompleted]
    exact pow_ne_zero 2 hz
  have hden : y - threeTorsionCurve.toAffine.negY x y = z := by
    simp only [threeTorsionCurve, WeierstrassCurve.Affine.negY]
    dsimp only [z]
    ring
  rw [threeTorsionCurve.toAffine.slope_of_Y_ne rfl hy, hden]
  norm_num [threeTorsionCurve]
  change 2 * ((3 * x ^ 2 - 4 * y) / z) + 4 = z * A /
    sourceCompletedPolynomial x
  field_simp [hz, hD]
  dsimp only [z, A, sourceCompletedPolynomial] at hcompleted ⊢
  linear_combination
    -(6 * x ^ 2 + 16 * x + 28) * hcompleted

private theorem double_abscissa_identity {x z : ℚ}
    (hcompleted : z ^ 2 = sourceCompletedPolynomial x)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    (z * ((6 * x ^ 2 + 16 * x + 28) /
        sourceCompletedPolynomial x)) ^ 2 / 4 - 4 - x - x =
      doubleAbscissa x := by
  simp only [doubleAbscissa]
  field_simp [hD]
  dsimp only [sourceCompletedPolynomial] at hcompleted ⊢
  linear_combination
    (6 * x ^ 2 + 16 * x + 28) ^ 2 *
      hcompleted

private theorem double_completed_identity (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    -1 - (6 * x ^ 2 + 16 * x + 28) /
        sourceCompletedPolynomial x * (doubleAbscissa x - x) =
      doubleDifferential x := by
  simp only [doubleAbscissa, doubleDifferential]
  field_simp [hD]
  simp only [sourceCompletedPolynomial]
  ring

private theorem double_abscissa_difference (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    x - doubleAbscissa x =
      sourceThreeDivisionPolynomial x / sourceCompletedPolynomial x := by
  simp only [doubleAbscissa]
  field_simp [hD]
  simp only [sourceCompletedPolynomial,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor]
  ring

private theorem double_differential_difference (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    1 - doubleDifferential x =
      2 * (7 * x ^ 6 + 56 * x ^ 5 + 282 * x ^ 4 + 847 * x ^ 3 +
        2352 * x ^ 2 + 3430 * x + 2401) /
          sourceCompletedPolynomial x ^ 2 := by
  simp only [doubleDifferential]
  field_simp [hD]
  simp only [sourceCompletedPolynomial]
  ring

private theorem secant_completed_slope_identity (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0)
    (hψ : sourceThreeDivisionPolynomial x ≠ 0) :
    (1 - doubleDifferential x) /
        (x - doubleAbscissa x) =
      tripleSecantSlopeFactor x := by
  rw [double_differential_difference x hD,
    double_abscissa_difference x hD]
  simp only [tripleSecantSlopeFactor]
  field_simp [hD, hψ]

private theorem triple_abscissa_identity {x z : ℚ}
    (hcompleted : z ^ 2 = sourceCompletedPolynomial x)
    (hD : sourceCompletedPolynomial x ≠ 0)
    (hψ : sourceThreeDivisionPolynomial x ≠ 0) :
    (z * tripleSecantSlopeFactor x) ^ 2 / 4 - 4 - x -
        doubleAbscissa x = tripleAbscissa x := by
  simp only [tripleSecantSlopeFactor, doubleAbscissa, tripleAbscissa]
  field_simp [hD, hψ]
  dsimp only [sourceCompletedPolynomial,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor,
    tripleAbscissaNumerator] at hcompleted ⊢
  linear_combination
    4 * (7 * x ^ 6 + 56 * x ^ 5 + 282 * x ^ 4 + 847 * x ^ 3 +
      2352 * x ^ 2 + 3430 * x + 2401) ^ 2 *
        hcompleted

private theorem triple_completed_identity (x z : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0)
    (hψ : sourceThreeDivisionPolynomial x ≠ 0) :
    -z - z * tripleSecantSlopeFactor x * (tripleAbscissa x - x) =
      z * tripleDifferential x := by
  simp only [tripleSecantSlopeFactor, tripleAbscissa,
    tripleDifferential]
  field_simp [hD, hψ]
  simp only [sourceCompletedPolynomial,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor,
    tripleAbscissaNumerator, tripleDifferentialNumerator,
    tripleDifferentialCofactor]
  ring

/-- Away from the visible three-element fibre, the two equation-checked
candidate point functions compose to actual multiplication by three in
Mathlib's affine point group. -/
theorem veluThreeDualCandidatePointFun_candidate_some
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    veluThreeDualCandidatePointFun
        (veluThreeCandidatePointFun
          (WeierstrassCurve.Affine.Point.some x y hP)) =
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP := by
  let P : threeTorsionCurve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let z : ℚ := 2 * y + 4 * x + 7
  let ℓ₂ : ℚ := threeTorsionCurve.toAffine.slope x x y y
  let x₂ : ℚ := threeTorsionCurve.toAffine.addX x x ℓ₂
  let y₂ : ℚ := threeTorsionCurve.toAffine.addY x x y ℓ₂
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    exact hP_ne (source_eq_zero_of_two_nsmul_eq_zero P htwo)
  have hy : y ≠ threeTorsionCurve.toAffine.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  have hP₂ : threeTorsionCurve.toAffine.Nonsingular x₂ y₂ :=
    nonsingular_add hP hP (fun hxy => hy hxy.2)
  have hdouble :
      (2 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy
  have hcompleted : z ^ 2 = sourceCompletedPolynomial x := by
    simpa only [z] using source_completed_equation hP
  have hz : z ≠ 0 := by
    intro hz
    apply hy
    simp only [threeTorsionCurve, WeierstrassCurve.Affine.negY]
    dsimp only [z] at hz
    linarith
  have hD : sourceCompletedPolynomial x ≠ 0 := by
    rw [← hcompleted]
    exact pow_ne_zero 2 hz
  have htangent :
      2 * ℓ₂ + 4 =
        z * ((6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x) := by
    simpa only [ℓ₂, z, mul_div_assoc] using
      tangent_completed_slope hP hy
  have hx₂ : x₂ = doubleAbscissa x := by
    calc
      x₂ = (2 * ℓ₂ + 4) ^ 2 / 4 - 4 - x - x :=
        addX_eq_completed x x ℓ₂
      _ = (z * ((6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x)) ^ 2 / 4 - 4 - x - x := by
            rw [htangent]
      _ = doubleAbscissa x :=
        double_abscissa_identity hcompleted hD
  have hz₂ : 2 * y₂ + 4 * x₂ + 7 = z * doubleDifferential x := by
    calc
      2 * y₂ + 4 * x₂ + 7 =
          -z - (2 * ℓ₂ + 4) * (x₂ - x) := by
        simpa only [x₂, y₂, z, ℓ₂] using
          addY_completed x x y ℓ₂
      _ = -z -
          (z * ((6 * x ^ 2 + 16 * x + 28) /
            sourceCompletedPolynomial x)) * (doubleAbscissa x - x) := by
        rw [htangent, hx₂]
      _ = z * (-1 - (6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x * (doubleAbscissa x - x)) := by
        ring
      _ = z * doubleDifferential x := by
        rw [double_completed_identity x hD]
  have hψ : sourceThreeDivisionPolynomial x ≠ 0 :=
    sourceThreeDivisionPolynomial_ne_zero hP hx
  have hthree_ne : (3 : ℕ) • P ≠ 0 := by
    simpa only [P] using source_three_nsmul_some_ne_zero hP hx
  have hsec : x ≠ x₂ := by
    intro hxx₂
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxx₂ with
      heq | heq
    · have htwo_eq : (2 : ℕ) • P = P :=
        hdouble.trans heq.symm
      apply hP_ne
      calc
        P = (2 : ℕ) • P - P := by abel
        _ = P - P := by rw [htwo_eq]
        _ = 0 := sub_self P
    · apply hthree_ne
      calc
        (3 : ℕ) • P = P + (2 : ℕ) • P := by abel
        _ = P + WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
          rw [hdouble]
        _ = 0 := (add_eq_zero_iff_eq_neg).2 heq
  let ℓ₃ : ℚ := threeTorsionCurve.toAffine.slope x x₂ y y₂
  have hsecant :
      2 * ℓ₃ + 4 = z * tripleSecantSlopeFactor x := by
    have hcoordinateDifference :
        2 * (y - y₂) + 4 * (x - x₂) =
          z - (2 * y₂ + 4 * x₂ + 7) := by
      dsimp only [z]
      ring
    dsimp only [ℓ₃]
    rw [threeTorsionCurve.toAffine.slope_of_X_ne hsec]
    calc
      2 * ((y - y₂) / (x - x₂)) + 4 =
          (2 * (y - y₂) + 4 * (x - x₂)) / (x - x₂) := by
        field_simp [sub_ne_zero.mpr hsec]
      _ = (z - (2 * y₂ + 4 * x₂ + 7)) / (x - x₂) := by
        rw [hcoordinateDifference]
      _ = (z - z * doubleDifferential x) /
          (x - doubleAbscissa x) := by rw [hz₂, hx₂]
      _ = z * ((1 - doubleDifferential x) /
          (x - doubleAbscissa x)) := by ring
      _ = z * tripleSecantSlopeFactor x := by
        rw [secant_completed_slope_identity x hD hψ]
  have hx₃ :
      threeTorsionCurve.toAffine.addX x x₂ ℓ₃ =
        tripleAbscissa x := by
    calc
      threeTorsionCurve.toAffine.addX x x₂ ℓ₃ =
          (2 * ℓ₃ + 4) ^ 2 / 4 - 4 - x - x₂ :=
        addX_eq_completed x x₂ ℓ₃
      _ = (z * tripleSecantSlopeFactor x) ^ 2 / 4 - 4 - x -
          doubleAbscissa x := by rw [hsecant, hx₂]
      _ = tripleAbscissa x :=
        triple_abscissa_identity hcompleted hD hψ
  have hz₃ :
      2 * threeTorsionCurve.toAffine.addY x x₂ y ℓ₃ +
          4 * threeTorsionCurve.toAffine.addX x x₂ ℓ₃ + 7 =
        z * tripleDifferential x := by
    calc
      2 * threeTorsionCurve.toAffine.addY x x₂ y ℓ₃ +
          4 * threeTorsionCurve.toAffine.addX x x₂ ℓ₃ + 7 =
        -z - (2 * ℓ₃ + 4) *
          (threeTorsionCurve.toAffine.addX x x₂ ℓ₃ - x) := by
            simpa only [z] using addY_completed x x₂ y ℓ₃
      _ = -z - z * tripleSecantSlopeFactor x *
          (tripleAbscissa x - x) := by rw [hsecant, hx₃]
      _ = z * tripleDifferential x :=
        triple_completed_identity x z hD hψ
  have htriple :
      (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          (threeTorsionCurve.toAffine.addX x x₂ ℓ₃)
          (threeTorsionCurve.toAffine.addY x x₂ y ℓ₃)
          (nonsingular_add hP hP₂ (fun hxy => hsec hxy.1)) := by
    calc
      (3 : ℕ) • P = P + (2 : ℕ) • P := by abel
      _ = P + WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
        rw [hdouble]
      _ = WeierstrassCurve.Affine.Point.some _ _ _ :=
        WeierstrassCurve.Affine.Point.add_of_X_ne hsec
  rw [htriple]
  simp only [veluThreeCandidatePointFun]
  rw [dif_neg hx]
  simp only [veluThreeDualCandidatePointFun,
    veluThreeDualCandidatePoint,
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · exact (veluThreeDualCandidateX_candidateX hx
      (sourceThreeDivisionCofactor_ne_zero hP)).trans hx₃.symm
  · have hdual := veluThreeDualCandidateY_candidate_completed
      (y := y) hx (sourceThreeDivisionCofactor_ne_zero hP)
    rw [← hz₃] at hdual
    have hxdual := veluThreeDualCandidateX_candidateX hx
      (sourceThreeDivisionCofactor_ne_zero hP)
    linarith

private theorem three_nsmul_eq_zero_of_candidate_eq_zero
    (P : threeTorsionCurve.toAffine.Point)
    (hP : veluThreeCandidatePointFun P = 0) :
    (3 : ℕ) • P = 0 := by
  rcases (veluThreeCandidatePointFun_eq_zero_iff P).mp hP with
    rfl | rfl | rfl
  · simp
  · rw [← addOrderOf_threeTorsionOrigin]
    exact addOrderOf_nsmul_eq_zero threeTorsionOrigin
  · have hT : (3 : ℕ) • threeTorsionOrigin = 0 := by
      rw [← addOrderOf_threeTorsionOrigin]
      exact addOrderOf_nsmul_eq_zero threeTorsionOrigin
    simp [hT]

/-- The two equation-checked point functions compose to multiplication by
three on every rational source point.  This is a statement about the
composite only; it does not assert that either function is additive. -/
theorem veluThreeDualCandidatePointFun_candidate
    (P : threeTorsionCurve.toAffine.Point) :
    veluThreeDualCandidatePointFun (veluThreeCandidatePointFun P) =
      (3 : ℕ) • P := by
  cases P with
  | zero => rfl
  | some x y hP =>
      by_cases hx : x = 0
      · have hcandidate :
            veluThreeCandidatePointFun
              (WeierstrassCurve.Affine.Point.some x y hP) = 0 := by
          simp [veluThreeCandidatePointFun, hx]
          rfl
        rw [hcandidate, veluThreeDualCandidatePointFun_zero,
          three_nsmul_eq_zero_of_candidate_eq_zero _ hcandidate]
      · exact veluThreeDualCandidatePointFun_candidate_some hP hx

end MazurTorsion.OrderThirtyFive
