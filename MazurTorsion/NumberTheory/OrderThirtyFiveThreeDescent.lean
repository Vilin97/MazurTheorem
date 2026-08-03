/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveRankBoundary

/-!
# The rational three-cover attached to the order-35 dual candidate

For the normalized source curve

`y² + 4xy + 7y = x³`,

the fixed three-descent function is the source ordinate `y`.  Pulling this
function back along the checked dual candidate gives the literal cube

`((Y - 28) / (3X + 16))³`.

Conversely, if a nonzero source ordinate is a rational cube `t³`, writing
`x = tu` produces the plane cubic

`u³ = t³ + 4tu + 7`.

This cubic has an explicit map to the candidate target, and the dual
candidate sends the resulting point back to `(x,y)`.  Thus this file proves
the affine, nonexceptional part of the key descent equivalence

`y(P) is a cube ⇔ P lies in the image of the dual candidate`.

The exceptional points with `y = 0` encode the two nontrivial visible cosets
and are deliberately not folded into a multiplicative quotient by an ad hoc
zero convention.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- Pullback of the source ordinate along the dual candidate is a literal
rational cube. -/
theorem veluThreeDualCandidateY_eq_cube
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    veluThreeDualCandidateY X Y =
      ((Y - 28) / veluThreeDualCandidateKernel X) ^ 3 := by
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let B : ℚ := X ^ 3 + 16 * X ^ 2 + 252 * X + 2198
  let Z : ℚ := 2 * Y + 4 * X + 7
  have hkernel := veluThreeDualCandidateKernel_ne_zero hP
  have hK : K ≠ 0 := by
    simpa only [K, veluThreeDualCandidateKernel] using hkernel
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget] at hcurve
  change ((Z * (B / K ^ 3) - 4 * (A / K ^ 2) - 7) / 2) =
    ((Y - 28) / K) ^ 3
  field_simp [hK]
  dsimp only [A, B, K, Z]
  linear_combination 2 * (4 * X - Y + 91) * hcurve

/-- The abscissa on the rational three-cover. -/
def threeCoverTargetX (t u : ℚ) : ℚ :=
  3 * t ^ 2 + 3 * t * u - 4 * t + 3 * u ^ 2 + 4 * u

/-- The ordinate on the rational three-cover. -/
def threeCoverTargetY (t u : ℚ) : ℚ :=
  28 + t * (3 * threeCoverTargetX t u + 16)

/-- The covering cubic maps to the candidate target equation. -/
theorem threeCoverTarget_equation
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeCandidateTarget.toAffine.Equation
      (threeCoverTargetX t u) (threeCoverTargetY t u) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [veluThreeCandidateTarget]
  dsimp only [threeCoverTargetX, threeCoverTargetY]
  linear_combination
    -(54 * t ^ 3 + 81 * t ^ 2 * u + 81 * t * u ^ 2 +
      108 * t * u + 27 * u ^ 3 + 108 * u ^ 2 + 144 * u + 253) *
        hcover

/-- The rational point on the candidate target supplied by the covering
cubic. -/
noncomputable def threeCoverTargetPoint
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeCandidateTarget.toAffine.Point :=
  .some (threeCoverTargetX t u) (threeCoverTargetY t u)
    (veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover))

/-- The dual abscissa of a covering point is `tu`. -/
theorem veluThreeDualCandidateX_threeCoverTargetX
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeDualCandidateX (threeCoverTargetX t u) = t * u := by
  let X : ℚ := threeCoverTargetX t u
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let htarget : veluThreeCandidateTarget.toAffine.Nonsingular
      (threeCoverTargetX t u) (threeCoverTargetY t u) :=
    veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover)
  have hkernel := veluThreeDualCandidateKernel_ne_zero htarget
  have hK : K ≠ 0 := by
    simpa only [K, X, veluThreeDualCandidateKernel] using hkernel
  change A / K ^ 2 = t * u
  field_simp [hK]
  dsimp only [A, K, X, threeCoverTargetX] at hcover ⊢
  linear_combination
    -(27 * t ^ 3 - 108 * t ^ 2 + 144 * t - 27 * u ^ 3 -
      108 * u ^ 2 - 144 * u - 253) * hcover

/-- The dual ordinate of a covering point is `t³`. -/
theorem veluThreeDualCandidateY_threeCoverTarget
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeDualCandidateY
        (threeCoverTargetX t u) (threeCoverTargetY t u) = t ^ 3 := by
  let htarget : veluThreeCandidateTarget.toAffine.Nonsingular
      (threeCoverTargetX t u) (threeCoverTargetY t u) :=
    veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover)
  rw [veluThreeDualCandidateY_eq_cube htarget]
  have hkernel := veluThreeDualCandidateKernel_ne_zero htarget
  have hkernel' :
      3 * threeCoverTargetX t u + 16 ≠ 0 := by
    simpa only [veluThreeDualCandidateKernel] using hkernel
  have ht :
      (threeCoverTargetY t u - 28) /
          veluThreeDualCandidateKernel (threeCoverTargetX t u) = t := by
    simp only [threeCoverTargetY, veluThreeDualCandidateKernel]
    field_simp [hkernel']
    ring
  rw [ht]

/-- A nonzero cube source ordinate gives an explicit rational preimage under
the dual candidate. -/
theorem exists_dualCandidate_preimage_of_Y_eq_cube
    {x y t : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (ht : t ≠ 0)
    (hy : y = t ^ 3) :
    ∃ Q : veluThreeCandidateTarget.toAffine.Point,
      veluThreeDualCandidatePointFun Q =
        WeierstrassCurve.Affine.Point.some x y hP := by
  let u : ℚ := x / t
  have hxu : x = t * u := by
    dsimp only [u]
    field_simp [ht]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  have hfactor :
      t ^ 3 * (t ^ 3 + 4 * t * u + 7) = t ^ 3 * u ^ 3 := by
    calc
      t ^ 3 * (t ^ 3 + 4 * t * u + 7) =
          y ^ 2 + 4 * x * y + 7 * y := by rw [hy, hxu]; ring
      _ = x ^ 3 := hcurve
      _ = t ^ 3 * u ^ 3 := by rw [hxu]; ring
  have hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7 := by
    exact (mul_left_cancel₀ (pow_ne_zero 3 ht) hfactor).symm
  refine ⟨threeCoverTargetPoint hcover, ?_⟩
  simp only [threeCoverTargetPoint, veluThreeDualCandidatePointFun,
    veluThreeDualCandidatePoint,
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [veluThreeDualCandidateX_threeCoverTargetX hcover]
    exact hxu.symm
  · rw [veluThreeDualCandidateY_threeCoverTarget hcover]
    exact hy.symm

end MazurTorsion.OrderThirtyFive
