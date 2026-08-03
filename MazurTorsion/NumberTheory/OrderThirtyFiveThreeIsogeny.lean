/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.ThreeTorsion
import MazurTorsion.NumberTheory.OrderThirtyFiveQuotientReduction
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# An equation-checked Vélu three-isogeny candidate

On the normalized curve

`E : y² + 4xy + 7y = x³`,

the points `(0,0)` and `(0,-7)` form the nonidentity part of a rational
order-three subgroup.  Vélu's coordinate sums suggest the target model

`E' : Y² + 4XY + 7Y = X³ - 140X - 791`

and, away from that subgroup, the coordinate formulas

```
X = (x³ + 28x + 49) / x²,
Y = (x³y - 28xy - 98y - 112x² - 392x - 343) / x³.
```

This file checks that the denominator-safe point function lands on `E'`
and computes its zero fibre.  It does **not** yet prove that the function is
additive, construct a bundled isogeny, determine its degree, construct its
dual, or prove a multiplication-by-three composition.  Accordingly all
declarations below use candidate and zero-fibre language.

The file also proves that `E'` has
trivial rational torsion: reduction modulo three bounds torsion by three,
while an explicit factorization of the third division polynomial rules out
nonidentity rational three-torsion.  These are fixed-curve arithmetic inputs
for a prospective three-isogeny Selmer calculation, not such a calculation.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

/-- The candidate target obtained from the Vélu coordinate formulas for the
visible order-three subgroup. -/
def veluThreeCandidateTarget : WeierstrassCurve ℚ :=
  ⟨4, 0, 7, -140, -791⟩

/-- The integral model of the candidate target. -/
def veluThreeCandidateTargetIntegral : WeierstrassCurve ℤ :=
  ⟨4, 0, 7, -140, -791⟩

/-- The candidate target discriminant is `-5⁹7`. -/
theorem veluThreeCandidateTargetIntegral_discriminant :
    veluThreeCandidateTargetIntegral.Δ = -13671875 := by
  norm_num [veluThreeCandidateTargetIntegral,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

theorem map_veluThreeCandidateTargetIntegral :
    (veluThreeCandidateTargetIntegral.map
      (algebraMap ℤ ℚ)).toAffine =
        veluThreeCandidateTarget.toAffine := by
  ext <;> simp [veluThreeCandidateTargetIntegral,
    veluThreeCandidateTarget]

instance veluThreeCandidateTarget_isElliptic :
    veluThreeCandidateTarget.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [veluThreeCandidateTarget, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The candidate abscissa formula away from the visible subgroup. -/
def veluThreeCandidateX (x : ℚ) : ℚ :=
  (x ^ 3 + 28 * x + 49) / x ^ 2

/-- The candidate ordinate formula away from the visible subgroup. -/
def veluThreeCandidateY (x y : ℚ) : ℚ :=
  (x ^ 3 * y - 28 * x * y - 98 * y - 112 * x ^ 2 -
      392 * x - 343) / x ^ 3

private theorem threeTorsionCurve_equation
    {x y : ℚ}
    (h : threeTorsionCurve.toAffine.Nonsingular x y) :
    y ^ 2 + 4 * x * y + 7 * y = x ^ 3 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [threeTorsionCurve] at heq
  exact heq

/-- Direct substitution verifies the Vélu formulas. -/
theorem veluThreeCandidate_equation
    {x y : ℚ} (hx : x ≠ 0)
    (hcurve : y ^ 2 + 4 * x * y + 7 * y = x ^ 3) :
    veluThreeCandidateY x y ^ 2 +
        4 * veluThreeCandidateX x * veluThreeCandidateY x y +
        7 * veluThreeCandidateY x y =
      veluThreeCandidateX x ^ 3 - 140 * veluThreeCandidateX x - 791 := by
  simp only [veluThreeCandidateX, veluThreeCandidateY]
  field_simp [hx]
  linear_combination
    (x ^ 3 - 28 * x - 98) ^ 2 * hcurve

private theorem veluThreeCandidate_nonsingular
    {x y : ℚ}
    (h : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    veluThreeCandidateTarget.toAffine.Nonsingular
      (veluThreeCandidateX x) (veluThreeCandidateY x y) := by
  apply veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [veluThreeCandidateTarget]
  simpa only [sub_eq_add_neg] using
    veluThreeCandidate_equation hx (threeTorsionCurve_equation h)

/-- The denominator-safe point-function candidate.  No additivity theorem is
asserted here. -/
noncomputable def veluThreeCandidatePointFun :
    threeTorsionCurve.toAffine.Point →
      veluThreeCandidateTarget.toAffine.Point
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (veluThreeCandidateX x) (veluThreeCandidateY x y)
        (veluThreeCandidate_nonsingular h hx)

@[simp] theorem veluThreeCandidatePointFun_zero :
    veluThreeCandidatePointFun 0 = 0 :=
  rfl

@[simp] theorem veluThreeCandidatePointFun_threeTorsionOrigin :
    veluThreeCandidatePointFun threeTorsionOrigin = 0 := by
  simp [veluThreeCandidatePointFun, threeTorsionOrigin]
  rfl

@[simp] theorem veluThreeCandidatePointFun_neg_threeTorsionOrigin :
    veluThreeCandidatePointFun (-threeTorsionOrigin) = 0 := by
  rw [threeTorsionOrigin,
    WeierstrassCurve.Affine.Point.neg_some]
  simp [veluThreeCandidatePointFun]
  rfl

/-- The zero fibre of the explicit point function is exactly the visible
three-element set.  This is not a group-kernel theorem until additivity is
proved. -/
theorem veluThreeCandidatePointFun_eq_zero_iff
    (P : threeTorsionCurve.toAffine.Point) :
    veluThreeCandidatePointFun P = 0 ↔
      P = 0 ∨ P = threeTorsionOrigin ∨
        P = -threeTorsionOrigin := by
  cases P with
  | zero =>
      constructor
      · intro
        exact Or.inl rfl
      · intro
        exact veluThreeCandidatePointFun_zero
  | some x y h =>
      by_cases hx : x = 0
      · subst x
        have hcurve := threeTorsionCurve_equation h
        norm_num at hcurve
        have hfactor : y * (y + 7) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp hfactor with hy | hy
        · subst y
          have hP :
              (WeierstrassCurve.Affine.Point.some 0 0 h :
                threeTorsionCurve.toAffine.Point) =
                threeTorsionOrigin := by
            apply WeierstrassCurve.Affine.Point.some_eq_some
              threeTorsionCurve <;> rfl
          rw [hP]
          simp
        · have hy' : y = -7 := by linarith
          subst y
          have hP :
              (WeierstrassCurve.Affine.Point.some 0 (-7) h :
                threeTorsionCurve.toAffine.Point) =
                -threeTorsionOrigin := by
            rw [threeTorsionOrigin,
              WeierstrassCurve.Affine.Point.neg_some]
            apply WeierstrassCurve.Affine.Point.some_eq_some
              threeTorsionCurve
            · rfl
            · norm_num [WeierstrassCurve.Affine.negY,
                threeTorsionCurve]
          rw [hP]
          simp
      · simp [veluThreeCandidatePointFun, hx,
          threeTorsionOrigin,
          WeierstrassCurve.Affine.Point.neg_some]

/-! ## The candidate target has no rational three-torsion -/

/-- Evaluation of the third division polynomial on the candidate target. -/
theorem eval_veluThreeCandidateTarget_Psi_three (x : ℚ) :
    Polynomial.eval x veluThreeCandidateTarget.Ψ₃ =
      (3 * x + 16) * (x ^ 3 - 252 * x - 1771) := by
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat,
    veluThreeCandidateTarget, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private theorem cubic_threeKernel_ne_zero (x : ℚ) :
    x ^ 3 - 252 * x - 1771 ≠ 0 := by
  intro hx
  let p : Polynomial ℤ :=
    Polynomial.X ^ 3 - Polynomial.C 252 * Polynomial.X -
      Polynomial.C 1771
  have hroot : Polynomial.aeval x p = 0 := by
    simpa [p, map_ofNat] using hx
  have hdeg : p.natDegree = 3 := by
    dsimp only [p]
    compute_degree <;> norm_num
  have hlc : p.leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff, hdeg]
    norm_num [p, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_one]
  have hd : ((IsFractionRing.den ℤ x : ℤ)) ∣ 1 := by
    simpa only [hlc] using den_dvd_of_is_root hroot
  have hdAbs :
      ((IsFractionRing.den ℤ x : ℤ)).natAbs = 1 := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hd)
  have hdCases :
      (IsFractionRing.den ℤ x : ℤ) = 1 ∨
        (IsFractionRing.den ℤ x : ℤ) = -1 := by
    rcases Int.natAbs_eq
      (IsFractionRing.den ℤ x : ℤ) with h | h
    · left
      rw [hdAbs] at h
      norm_num at h ⊢
      exact h
    · right
      rw [hdAbs] at h
      norm_num at h ⊢
      exact h
  have hnoRoot :
      ∀ z : ZMod 13,
        z ^ 3 - 252 * z - 1771 ≠ 0 := by
    decide
  have noIntRoot (m : ℤ) :
      m ^ 3 - 252 * m - 1771 ≠ 0 := by
    intro hm
    have hmMod :=
      congrArg (fun z : ℤ ↦ (z : ZMod 13)) hm
    push_cast at hmMod
    exact hnoRoot _ hmMod
  have hrepr := IsFractionRing.mk'_num_den' ℤ x
  rcases hdCases with hdOne | hdNeg
  · rw [hdOne] at hrepr
    norm_num at hrepr
    apply noIntRoot (IsFractionRing.num ℤ x)
    rw [← hrepr] at hx
    exact_mod_cast hx
  · rw [hdNeg] at hrepr
    norm_num at hrepr
    apply noIntRoot (-IsFractionRing.num ℤ x)
    rw [← hrepr] at hx
    have hdiv :
        (IsFractionRing.num ℤ x : ℚ) / (-1 : ℚ) =
          -(IsFractionRing.num ℤ x : ℚ) := by
      ring
    rw [hdiv] at hx
    exact_mod_cast hx

private theorem linear_threeKernel_impossible
    {x y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular x y)
    (hx : 3 * x + 16 = 0) : False := by
  have hx' : x = -16 / 3 := by linarith
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget, hx'] at hcurve
  nlinarith [sq_nonneg (6 * y - 43)]

/-- The candidate target has no nonidentity rational point killed by three. -/
theorem veluThreeCandidateTarget_eq_zero_of_three_nsmul_eq_zero
    (P : veluThreeCandidateTarget.toAffine.Point)
    (hP : (3 : ℕ) • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      exfalso
      have hroot :=
        (MazurTorsion.ThreeTorsion.three_nsmul_some_eq_zero_iff
          veluThreeCandidateTarget hxy).mp hP
      rw [eval_veluThreeCandidateTarget_Psi_three] at hroot
      rcases mul_eq_zero.mp hroot with hlinear | hcubic
      · exact linear_threeKernel_impossible hxy hlinear
      · exact cubic_threeKernel_ne_zero x hcubic

/-! ## Reduction bounds all rational torsion on the candidate target -/

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

instance :
    (redCurve atThree
      veluThreeCandidateTargetIntegral).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (veluThreeCandidateTargetIntegral.map
      (algebraMap ℤ
        (ℤ ⧸ atThree.asIdeal))).Δ ≠ 0
  rw [Ne, WeierstrassCurve.map_Δ,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    atThree_asIdeal, Ideal.mem_span_singleton]
  norm_num [veluThreeCandidateTargetIntegral_discriminant]

/-- The concrete candidate-target reduction over `F₃`. -/
def veluThreeCandidateTargetModThree : WeierstrassCurve (ZMod 3) :=
  ⟨4, 0, 7, -140, -791⟩

instance : veluThreeCandidateTargetModThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

private theorem veluThreeCandidateTargetBaseChange_modThree :
    ((veluThreeCandidateTargetIntegral.toAffine ⁄ (ZMod 3)) :
      WeierstrassCurve _).toAffine =
        veluThreeCandidateTargetModThree.toAffine := by
  ext <;> decide +kernel

noncomputable def veluThreeCandidateTargetReducedPointEquiv :
    (redCurve atThree
        veluThreeCandidateTargetIntegral).Point ≃+
      veluThreeCandidateTargetModThree.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.mapEquiv
      (W' := veluThreeCandidateTargetIntegral.toAffine)
      residueThreeAlgEquiv).trans
    (WeierstrassCurve.Affine.Point.congr
      veluThreeCandidateTargetBaseChange_modThree)

noncomputable instance :
    Finite
      (redCurve atThree
        veluThreeCandidateTargetIntegral).Point :=
  .of_equiv veluThreeCandidateTargetModThree.toAffine.Point
    veluThreeCandidateTargetReducedPointEquiv.symm.toEquiv

theorem card_veluThreeCandidateTargetRedCurve_three :
    Nat.card
      (redCurve atThree
        veluThreeCandidateTargetIntegral).Point = 3 := by
  calc
    Nat.card
        (redCurve atThree
          veluThreeCandidateTargetIntegral).Point =
        Fintype.card
          veluThreeCandidateTargetModThree.toAffine.Point :=
      (Nat.card_congr
        veluThreeCandidateTargetReducedPointEquiv.toEquiv).trans
          Nat.card_eq_fintype_card
    _ = 3 := by decide

private theorem three_mem_targetIntPrime :
    (3 : ℤ) ∈ atThree.asIdeal :=
  three_mem_atThree

private theorem three_not_mem_targetIntPrime_sq :
    (3 : ℤ) ∉ atThree.asIdeal ^ (3 - 1) :=
  three_not_mem_atThree_pow_two

/-- Every rational torsion point on the candidate target is the identity. -/
theorem veluThreeCandidateTarget_torsion_eq_zero
    (P : veluThreeCandidateTarget.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    P = 0 := by
  have hdvd :
      addOrderOf P ∣ 3 := by
    rw [← card_veluThreeCandidateTargetRedCurve_three]
    exact addOrderOf_dvd_natCard_red
      atThree
      map_veluThreeCandidateTargetIntegral
      (by decide) three_mem_targetIntPrime
      three_not_mem_targetIntPrime_sq hP
  have hpos : 0 < addOrderOf P :=
    addOrderOf_pos_iff.mpr hP
  have hcases : addOrderOf P = 1 ∨ addOrderOf P = 3 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hneTwo : addOrderOf P ≠ 2 := by
      intro htwo
      rw [htwo] at hdvd
      norm_num at hdvd
    omega
  rcases hcases with horder | horder
  · exact AddMonoid.addOrderOf_eq_one_iff.mp horder
  · apply veluThreeCandidateTarget_eq_zero_of_three_nsmul_eq_zero P
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P

end MazurTorsion.OrderThirtyFive
