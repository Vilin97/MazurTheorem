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

/-! ## Translation by the visible kernel -/

/-- Translating by `(0,0)` multiplies the source descent class by `49`:
the new ordinate is `-49y/x³`. -/
theorem addY_threeTorsionOrigin
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y 0) =
      -49 * y / x ^ 3 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  rw [threeTorsionCurve.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, threeTorsionCurve]
  field_simp [hx]
  linear_combination -x ^ 3 * (4 * x + y - 7) * hcurve

/-- Translating by `(0,-7) = -(0,0)` gives the symmetric raw ordinate
formula. -/
theorem addY_neg_threeTorsionOrigin
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y (-7)) =
      -7 * (y + 4 * x + 7) ^ 2 / x ^ 3 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  rw [threeTorsionCurve.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, threeTorsionCurve]
  field_simp [hx]
  linear_combination -x ^ 3 * (4 * x + y + 7) * hcurve

/-- Away from the exceptional ordinate zero, translation by `(0,-7)`
multiplies the descent class by `7`, up to the displayed rational cube. -/
theorem addY_neg_threeTorsionOrigin_cubeClass
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y (-7)) =
      -7 * y * (x / y) ^ 3 := by
  rw [addY_neg_threeTorsionOrigin hP hx]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  field_simp [hx, hy]
  linear_combination
    -(x ^ 3 + 4 * x * y + y ^ 2 + 7 * y) * hcurve

/-! ## Exact arithmetic inputs and assembly of the three cosets -/

/-- The source local calculation needed from the fixed three-descent: every
nonexceptional ordinate has one of the three supported cube classes
`1`, `7`, or `49`. -/
def SourceThreeCubeClassBound : Prop :=
  ∀ {x y : ℚ},
    threeTorsionCurve.toAffine.Nonsingular x y → x ≠ 0 →
      ∃ t : ℚ, t ≠ 0 ∧
        (y = t ^ 3 ∨ y = 7 * t ^ 3 ∨ y = 49 * t ^ 3)

/-- The target local calculation needed from the fixed three-descent: every
rational target point is in the image of the first candidate point
function.  No additivity is included in this proposition. -/
def TargetThreeCandidateSurjective : Prop :=
  Function.Surjective veluThreeCandidatePointFun

/-- Under target surjectivity, a nonzero cube source ordinate makes the
source point an actual triple. -/
theorem exists_eq_three_nsmul_of_Y_eq_cube
    (htarget : TargetThreeCandidateSurjective)
    {x y t : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (ht : t ≠ 0) (hy : y = t ^ 3) :
    ∃ R : threeTorsionCurve.toAffine.Point,
      WeierstrassCurve.Affine.Point.some x y hP = (3 : ℕ) • R := by
  obtain ⟨Q, hQ⟩ := exists_dualCandidate_preimage_of_Y_eq_cube hP ht hy
  obtain ⟨R, hR⟩ := htarget Q
  refine ⟨R, ?_⟩
  calc
    WeierstrassCurve.Affine.Point.some x y hP =
        veluThreeDualCandidatePointFun Q := hQ.symm
    _ = veluThreeDualCandidatePointFun
          (veluThreeCandidatePointFun R) := by rw [hR]
    _ = (3 : ℕ) • R :=
      veluThreeDualCandidatePointFun_candidate R

private theorem two_nsmul_threeTorsionOrigin_eq_neg :
    (2 : ℕ) • threeTorsionOrigin = -threeTorsionOrigin := by
  have hthree : (3 : ℕ) • threeTorsionOrigin = 0 := by
    rw [← addOrderOf_threeTorsionOrigin]
    exact addOrderOf_nsmul_eq_zero threeTorsionOrigin
  calc
    (2 : ℕ) • threeTorsionOrigin =
        (3 : ℕ) • threeTorsionOrigin - threeTorsionOrigin := by abel
    _ = -threeTorsionOrigin := by rw [hthree]; simp

/-- The two fixed arithmetic outputs assemble to the exact three-coset
certificate consumed by the rank-zero boundary. -/
theorem threeCosetBound_of_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    ThreeCosetBound := by
  intro P
  cases P with
  | zero =>
      refine ⟨⟨0, by norm_num⟩, 0, ?_⟩
      simp [normalizedThreeRepresentative]
      rfl
  | some x y hP =>
      by_cases hx : x = 0
      · have hcandidate :
            veluThreeCandidatePointFun
              (WeierstrassCurve.Affine.Point.some x y hP) = 0 := by
          simp [veluThreeCandidatePointFun, hx]
          rfl
        rcases
            (veluThreeCandidatePointFun_eq_zero_iff
              (WeierstrassCurve.Affine.Point.some x y hP)).mp hcandidate with
          hzero | horigin | hnegOrigin
        · exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hzero).elim
        · refine ⟨⟨1, by norm_num⟩, 0, ?_⟩
          simpa [normalizedThreeRepresentative] using horigin
        · refine ⟨⟨2, by norm_num⟩, 0, ?_⟩
          rw [hnegOrigin, normalizedThreeRepresentative]
          norm_num
          exact two_nsmul_threeTorsionOrigin_eq_neg.symm
      · obtain ⟨t, ht, hy | hy | hy⟩ := hsource hP hx
        · obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP ht hy
          refine ⟨⟨0, by norm_num⟩, R, ?_⟩
          simpa [normalizedThreeRepresentative] using hR
        · have hT : threeTorsionCurve.toAffine.Nonsingular 0 0 := by
            apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff,
              threeTorsionCurve]
          let x' : ℚ := threeTorsionCurve.toAffine.addX x 0
            (threeTorsionCurve.toAffine.slope x 0 y 0)
          let y' : ℚ := threeTorsionCurve.toAffine.addY x 0 y
            (threeTorsionCurve.toAffine.slope x 0 y 0)
          have hP' : threeTorsionCurve.toAffine.Nonsingular x' y' :=
            nonsingular_add hP hT (fun hxy => hx hxy.1)
          let t' : ℚ := -7 * t / x
          have ht' : t' ≠ 0 := by
            dsimp only [t']
            exact div_ne_zero (mul_ne_zero (by norm_num) ht) hx
          have hy' : y' = t' ^ 3 := by
            dsimp only [y', t']
            rw [addY_threeTorsionOrigin hP hx, hy]
            field_simp [hx]
            ring
          obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP' ht' hy'
          have hsum :
              WeierstrassCurve.Affine.Point.some x y hP +
                  threeTorsionOrigin = (3 : ℕ) • R := by
            calc
              WeierstrassCurve.Affine.Point.some x y hP +
                    threeTorsionOrigin =
                  WeierstrassCurve.Affine.Point.some x' y' hP' := by
                rw [threeTorsionOrigin]
                exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
              _ = (3 : ℕ) • R := hR
          refine ⟨⟨2, by norm_num⟩, R, ?_⟩
          rw [normalizedThreeRepresentative]
          norm_num
          rw [two_nsmul_threeTorsionOrigin_eq_neg]
          calc
            WeierstrassCurve.Affine.Point.some x y hP =
                -threeTorsionOrigin +
                  (WeierstrassCurve.Affine.Point.some x y hP +
                    threeTorsionOrigin) := by abel
            _ = -threeTorsionOrigin + (3 : ℕ) • R := by rw [hsum]
        · have hnegT : threeTorsionCurve.toAffine.Nonsingular 0 (-7) := by
            apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff,
              threeTorsionCurve]
          let x' : ℚ := threeTorsionCurve.toAffine.addX x 0
            (threeTorsionCurve.toAffine.slope x 0 y (-7))
          let y' : ℚ := threeTorsionCurve.toAffine.addY x 0 y
            (threeTorsionCurve.toAffine.slope x 0 y (-7))
          have hP' : threeTorsionCurve.toAffine.Nonsingular x' y' :=
            nonsingular_add hP hnegT (fun hxy => hx hxy.1)
          have hy0 : y ≠ 0 := by rw [hy]; positivity
          let t' : ℚ := -7 * t * x / y
          have ht' : t' ≠ 0 := by
            dsimp only [t']
            exact div_ne_zero
              (mul_ne_zero (mul_ne_zero (by norm_num) ht) hx) hy0
          have hy' : y' = t' ^ 3 := by
            dsimp only [y', t']
            rw [addY_neg_threeTorsionOrigin_cubeClass hP hx hy0, hy]
            field_simp [hy0]
            ring
          obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP' ht' hy'
          have hsum :
              WeierstrassCurve.Affine.Point.some x y hP +
                  -threeTorsionOrigin = (3 : ℕ) • R := by
            calc
              WeierstrassCurve.Affine.Point.some x y hP +
                    -threeTorsionOrigin =
                  WeierstrassCurve.Affine.Point.some x' y' hP' := by
                rw [threeTorsionOrigin,
                  WeierstrassCurve.Affine.Point.neg_some]
                norm_num [WeierstrassCurve.Affine.negY,
                  threeTorsionCurve]
                exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
              _ = (3 : ℕ) • R := hR
          refine ⟨⟨1, by norm_num⟩, R, ?_⟩
          rw [normalizedThreeRepresentative]
          norm_num
          calc
            WeierstrassCurve.Affine.Point.some x y hP =
                threeTorsionOrigin +
                  (WeierstrassCurve.Affine.Point.some x y hP +
                    -threeTorsionOrigin) := by abel
            _ = threeTorsionOrigin + (3 : ℕ) • R := by rw [hsum]

/-- Finiteness of the candidate target is sufficient for the target
surjectivity input, because its checked rational torsion subgroup is
trivial. -/
theorem targetThreeCandidateSurjective_of_finite
    [Finite veluThreeCandidateTarget.toAffine.Point] :
    TargetThreeCandidateSurjective := by
  intro P
  have hPzero : P = 0 :=
    veluThreeCandidateTarget_torsion_eq_zero P
      (isOfFinAddOrder_of_finite P)
  refine ⟨0, ?_⟩
  rw [veluThreeCandidatePointFun_zero, hPzero]

/-- End-to-end rank-zero consumer of the two isolated fixed descent
calculations. -/
theorem optimalQuotientModel_rank_zero_of_three_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_point_rank_zero_of_cosetBound
    (threeCosetBound_of_descent_inputs hsource htarget)

/-- End-to-end finiteness consumer of the two isolated fixed descent
calculations. -/
theorem optimalQuotientModel_finite_of_three_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_point_finite_of_cosetBound
    (threeCosetBound_of_descent_inputs hsource htarget)

end MazurTorsion.OrderThirtyFive
