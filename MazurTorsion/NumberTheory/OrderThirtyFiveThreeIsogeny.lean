/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.ThreeTorsion
import MazurTorsion.NumberTheory.OrderThirtyFiveQuotientReduction
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The rational three-isogeny attached to the level-35 quotient

On the normalized curve

`E : y² + 4xy + 7y = x³`,

the points `(0,0)` and `(0,-7)` form the nonidentity part of a rational
order-three kernel.  Vélu's coordinate sums give the quotient

`E' : Y² + 4XY + 7Y = X³ - 140X - 791`

and, away from the kernel,

```
X = (x³ + 28x + 49) / x²,
Y = (x³y - 28xy - 98y - 112x² - 392x - 343) / x³.
```

This file checks that the denominator-safe point function lands on `E'`
and has exactly the expected rational kernel.  It also proves that `E'` has
trivial rational torsion: reduction modulo three bounds torsion by three,
while an explicit factorization of the third division polynomial rules out
nonidentity rational three-torsion.  These are the two fixed-curve group
inputs for the remaining three-isogeny Selmer calculation.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

/-- The quotient of `threeTorsionCurve` by its visible order-three
subgroup. -/
def threeIsogenousQuotient : WeierstrassCurve ℚ :=
  ⟨4, 0, 7, -140, -791⟩

/-- The integral model of the three-isogenous quotient. -/
def threeIsogenousQuotientIntegral : WeierstrassCurve ℤ :=
  ⟨4, 0, 7, -140, -791⟩

/-- The quotient discriminant is `-5⁹7`. -/
theorem threeIsogenousQuotientIntegral_discriminant :
    threeIsogenousQuotientIntegral.Δ = -13671875 := by
  norm_num [threeIsogenousQuotientIntegral,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

theorem map_threeIsogenousQuotientIntegral :
    (threeIsogenousQuotientIntegral.map
      (algebraMap ℤ ℚ)).toAffine =
        threeIsogenousQuotient.toAffine := by
  ext <;> simp [threeIsogenousQuotientIntegral,
    threeIsogenousQuotient]

instance threeIsogenousQuotient_isElliptic :
    threeIsogenousQuotient.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [threeIsogenousQuotient, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The abscissa of the three-isogeny away from its kernel. -/
def threeIsogenyX (x : ℚ) : ℚ :=
  (x ^ 3 + 28 * x + 49) / x ^ 2

/-- The ordinate of the three-isogeny away from its kernel. -/
def threeIsogenyY (x y : ℚ) : ℚ :=
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
theorem threeIsogeny_equation
    {x y : ℚ} (hx : x ≠ 0)
    (hcurve : y ^ 2 + 4 * x * y + 7 * y = x ^ 3) :
    threeIsogenyY x y ^ 2 +
        4 * threeIsogenyX x * threeIsogenyY x y +
        7 * threeIsogenyY x y =
      threeIsogenyX x ^ 3 - 140 * threeIsogenyX x - 791 := by
  simp only [threeIsogenyX, threeIsogenyY]
  field_simp [hx]
  linear_combination
    (x ^ 3 - 28 * x - 98) ^ 2 * hcurve

private theorem threeIsogeny_nonsingular
    {x y : ℚ}
    (h : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    threeIsogenousQuotient.toAffine.Nonsingular
      (threeIsogenyX x) (threeIsogenyY x y) := by
  apply threeIsogenousQuotient.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [threeIsogenousQuotient]
  simpa only [sub_eq_add_neg] using
    threeIsogeny_equation hx (threeTorsionCurve_equation h)

/-- The denominator-safe underlying point function of the rational
three-isogeny. -/
noncomputable def threeIsogenyPointFun :
    threeTorsionCurve.toAffine.Point →
      threeIsogenousQuotient.toAffine.Point
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (threeIsogenyX x) (threeIsogenyY x y)
        (threeIsogeny_nonsingular h hx)

@[simp] theorem threeIsogenyPointFun_zero :
    threeIsogenyPointFun 0 = 0 :=
  rfl

@[simp] theorem threeIsogenyPointFun_threeTorsionOrigin :
    threeIsogenyPointFun threeTorsionOrigin = 0 := by
  simp [threeIsogenyPointFun, threeTorsionOrigin]
  rfl

@[simp] theorem threeIsogenyPointFun_neg_threeTorsionOrigin :
    threeIsogenyPointFun (-threeTorsionOrigin) = 0 := by
  rw [threeTorsionOrigin,
    WeierstrassCurve.Affine.Point.neg_some]
  simp [threeIsogenyPointFun]
  rfl

/-- The rational kernel of the explicit point function is exactly the
visible order-three subgroup. -/
theorem threeIsogenyPointFun_eq_zero_iff
    (P : threeTorsionCurve.toAffine.Point) :
    threeIsogenyPointFun P = 0 ↔
      P = 0 ∨ P = threeTorsionOrigin ∨
        P = -threeTorsionOrigin := by
  cases P with
  | zero =>
      constructor
      · intro
        exact Or.inl rfl
      · intro
        exact threeIsogenyPointFun_zero
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
      · simp [threeIsogenyPointFun, hx,
          threeTorsionOrigin,
          WeierstrassCurve.Affine.Point.neg_some]

/-! ## The dual curve has no rational three-torsion -/

/-- Evaluation of the third division polynomial on the quotient. -/
theorem eval_threeIsogenousQuotient_Psi_three (x : ℚ) :
    Polynomial.eval x threeIsogenousQuotient.Ψ₃ =
      (3 * x + 16) * (x ^ 3 - 252 * x - 1771) := by
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat,
    threeIsogenousQuotient, WeierstrassCurve.b₂,
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
    (hP : threeIsogenousQuotient.toAffine.Nonsingular x y)
    (hx : 3 * x + 16 = 0) : False := by
  have hx' : x = -16 / 3 := by linarith
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeIsogenousQuotient, hx'] at hcurve
  nlinarith [sq_nonneg (6 * y - 43)]

/-- The quotient curve has no nonidentity rational point killed by three. -/
theorem threeIsogenous_eq_zero_of_three_nsmul_eq_zero
    (P : threeIsogenousQuotient.toAffine.Point)
    (hP : (3 : ℕ) • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      exfalso
      have hroot :=
        (MazurTorsion.ThreeTorsion.three_nsmul_some_eq_zero_iff
          threeIsogenousQuotient hxy).mp hP
      rw [eval_threeIsogenousQuotient_Psi_three] at hroot
      rcases mul_eq_zero.mp hroot with hlinear | hcubic
      · exact linear_threeKernel_impossible hxy hlinear
      · exact cubic_threeKernel_ne_zero x hcubic

/-! ## Reduction bounds all rational torsion on the dual curve -/

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

instance :
    (redCurve (quotientIntPrime 3)
      threeIsogenousQuotientIntegral).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (threeIsogenousQuotientIntegral.map
      (algebraMap ℤ
        (ℤ ⧸ (quotientIntPrime 3).asIdeal))).Δ ≠ 0
  rw [Ne, WeierstrassCurve.map_Δ,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    quotientIntPrime_asIdeal, Ideal.mem_span_singleton]
  norm_num [threeIsogenousQuotientIntegral_discriminant]

/-- The concrete dual reduction over `F₃`. -/
def threeIsogenousQuotientModThree : WeierstrassCurve (ZMod 3) :=
  ⟨4, 0, 7, -140, -791⟩

instance : threeIsogenousQuotientModThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

private theorem threeIsogenousBaseChange_modThree :
    ((threeIsogenousQuotientIntegral.toAffine ⁄ (ZMod 3)) :
      WeierstrassCurve _).toAffine =
        threeIsogenousQuotientModThree.toAffine := by
  ext <;> decide +kernel

noncomputable def threeIsogenousReducedPointEquiv :
    (redCurve (quotientIntPrime 3)
        threeIsogenousQuotientIntegral).Point ≃+
      threeIsogenousQuotientModThree.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.mapEquiv
      (W' := threeIsogenousQuotientIntegral.toAffine)
      quotientResidueThreeAlgEquiv).trans
    (WeierstrassCurve.Affine.Point.congr
      threeIsogenousBaseChange_modThree)

noncomputable instance :
    Finite
      (redCurve (quotientIntPrime 3)
        threeIsogenousQuotientIntegral).Point :=
  .of_equiv threeIsogenousQuotientModThree.toAffine.Point
    threeIsogenousReducedPointEquiv.symm.toEquiv

theorem card_threeIsogenousRedCurve_three :
    Nat.card
      (redCurve (quotientIntPrime 3)
        threeIsogenousQuotientIntegral).Point = 3 := by
  calc
    Nat.card
        (redCurve (quotientIntPrime 3)
          threeIsogenousQuotientIntegral).Point =
        Fintype.card
          threeIsogenousQuotientModThree.toAffine.Point :=
      (Nat.card_congr
        threeIsogenousReducedPointEquiv.toEquiv).trans
          Nat.card_eq_fintype_card
    _ = 3 := by decide

private theorem three_mem_dualIntPrime :
    (3 : ℤ) ∈ (quotientIntPrime 3).asIdeal :=
  Ideal.mem_span_singleton_self 3

private theorem three_not_mem_dualIntPrime_sq :
    (3 : ℤ) ∉ (quotientIntPrime 3).asIdeal ^ (3 - 1) := by
  rw [quotientIntPrime_asIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  norm_num

/-- Every rational torsion point on the three-isogenous quotient is the
identity. -/
theorem threeIsogenous_torsion_eq_zero
    (P : threeIsogenousQuotient.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    P = 0 := by
  have hdvd :
      addOrderOf P ∣ 3 := by
    rw [← card_threeIsogenousRedCurve_three]
    exact addOrderOf_dvd_natCard_red
      (quotientIntPrime 3)
      map_threeIsogenousQuotientIntegral
      (by decide) three_mem_dualIntPrime
      three_not_mem_dualIntPrime_sq hP
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
  · apply threeIsogenous_eq_zero_of_three_nsmul_eq_zero P
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P

end MazurTorsion.OrderThirtyFive
