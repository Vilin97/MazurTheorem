/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenQuotientRankZero
import MazurTorsion.NumberTheory.XOneEighteenQuotientReductionAtSeventeen
import MazurTorsion.NumberTheory.XOneEighteenMinimalTwoDescentModel

/-!
# Final rank-zero consumer for `X₁(18)`

This module is the downstream consumer of the concrete two-descent.  Once
the arithmetic calculation proves that the image of `x - T` is trivial,
the checked rank-zero bridge makes the real-cubic quotient finite.  Genuine
reduction at the degree-one prime above `17` then classifies its points and
excludes both noncuspidal points on the sextic and rational points of exact
order eighteen.

The unconditional arithmetic theorem is added here only after the global
and dyadic certificates close; the two theorems below record the exact
consumer contract without replacing that missing proof by an assumption.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenFinalRankZero

noncomputable section

open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenQuotientRankZero
open MazurTorsion.XOneEighteenQuotientReductionAtSeventeen
open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenMinimalTwoDescentModel

/-! ## Rank zero from the dyadic-support minimal model -/

/-- The image of multiplication by two on the minimal completed-square
model. -/
abbrev minimalDoublingRange :
    AddSubgroup minimalDescentCurve.toAffine.Point :=
  (nsmulAddMonoidHom
    (α := minimalDescentCurve.toAffine.Point) 2).range

/-- A trivial descent image makes multiplication by two surjective on the
minimal model. -/
theorem minimalDoublingRange_eq_top_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := minimalDescentCurve.toAffine)).range = ⊥) :
    minimalDoublingRange = ⊤ := by
  apply top_unique
  intro P _
  have hmemRange :
      WeierstrassCurve.Affine.μ
          (W := minimalDescentCurve.toAffine) (.ofAdd P) ∈
        (WeierstrassCurve.Affine.μ
          (W := minimalDescentCurve.toAffine)).range :=
    ⟨.ofAdd P, rfl⟩
  rw [hmu] at hmemRange
  have hmemKer :
      .ofAdd P ∈
        (WeierstrassCurve.Affine.μ
          (W := minimalDescentCurve.toAffine)).ker := by
    simpa only [MonoidHom.mem_ker, Subgroup.mem_bot] using hmemRange
  rw [WeierstrassCurve.Affine.ker_μ_eq] at hmemKer
  change P ∈
    (nsmulAddMonoidHom
      (α := minimalDescentCurve.toAffine.Point) 2).range
  simpa only [Multiplicative.mem_toSubgroup, toAdd_ofAdd] using hmemKer

/-- The minimal point group is finitely generated once its descent image
is trivial. -/
theorem minimal_point_fg_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := minimalDescentCurve.toAffine)).range = ⊥) :
    AddGroup.FG minimalDescentCurve.toAffine.Point := by
  apply WeierstrassCurve.Affine.fg_point_of_finiteIndex_two
    minimalDescentCurve
  change minimalDoublingRange.FiniteIndex
  rw [minimalDoublingRange_eq_top_of_range_mu_eq_bot hmu]
  infer_instance

/-- The minimal point group has Mordell--Weil rank zero. -/
theorem minimal_point_rank_zero_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := minimalDescentCurve.toAffine)).range = ⊥) :
    Module.finrank ℤ minimalDescentCurve.toAffine.Point = 0 := by
  letI : AddGroup.FG minimalDescentCurve.toAffine.Point :=
    minimal_point_fg_of_range_mu_eq_bot hmu
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg
      minimalDescentCurve.toAffine.Point (by norm_num : (2 : ℕ) ≠ 0)
  have hrange :
      (nsmulAddMonoidHom
        (α := minimalDescentCurve.toAffine.Point) 2).range = ⊤ :=
    minimalDoublingRange_eq_top_of_range_mu_eq_bot hmu
  rw [hrange] at hformula
  have hformula' :
      1 = 2 ^ Module.finrank ℤ minimalDescentCurve.toAffine.Point *
        Nat.card
          (nsmulAddMonoidHom
            (α := minimalDescentCurve.toAffine.Point) 2).ker := by
    simpa only [AddSubgroup.index_top] using hformula
  have hpow :
      2 ^ Module.finrank ℤ minimalDescentCurve.toAffine.Point = 1 :=
    Nat.dvd_one.mp ⟨_, hformula'⟩
  simpa using hpow

/-- Rank zero and finite generation make the minimal point group finite. -/
theorem minimal_point_finite_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := minimalDescentCurve.toAffine)).range = ⊥) :
    Finite minimalDescentCurve.toAffine.Point := by
  letI : AddGroup.FG minimalDescentCurve.toAffine.Point :=
    minimal_point_fg_of_range_mu_eq_bot hmu
  letI : Module.Finite ℤ minimalDescentCurve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr
      (minimal_point_fg_of_range_mu_eq_bot hmu)
  have hmoduleTorsion :
      Module.IsTorsion ℤ minimalDescentCurve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      (minimal_point_rank_zero_of_range_mu_eq_bot hmu)
  exact AddCommGroup.finite_of_fg_torsion
    minimalDescentCurve.toAffine.Point
      (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

/-- Finiteness transports back to the original real-cubic quotient. -/
theorem quotient_point_finite_of_minimal_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := minimalDescentCurve.toAffine)).range = ⊥) :
    Finite quotientCurve.toAffine.Point := by
  letI : Finite minimalDescentCurve.toAffine.Point :=
    minimal_point_finite_of_range_mu_eq_bot hmu
  exact Finite.of_equiv minimalDescentCurve.toAffine.Point
    quotientToMinimalDescentEquiv.symm.toEquiv

/-- Triviality of the dyadic-support minimal descent image excludes every
noncuspidal rational point on the order-eighteen sextic. -/
theorem no_noncuspidal_point_of_minimal_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := minimalDescentCurve.toAffine)).range = ⊥)
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False := by
  letI : Finite quotientCurve.toAffine.Point :=
    quotient_point_finite_of_minimal_range_mu_eq_bot hmu
  exact no_noncuspidal_point_of_finite_quotient x y hx0 hx1 hcurve

/-- The genuine exact-order consumer for the minimal descent boundary. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_minimal_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := minimalDescentCurve.toAffine)).range = ⊥)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 := by
  apply
    MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint
      E Q
  intro x y hx0 hx1 hcurve
  exact no_noncuspidal_point_of_minimal_range_mu_eq_bot
    hmu x y hx0 hx1 hcurve

/-- A completed proof that the concrete descent image is trivial excludes
every noncuspidal rational point on the order-eighteen sextic. -/
theorem no_noncuspidal_point_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥)
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False := by
  letI : Finite quotientCurve.toAffine.Point :=
    quotient_point_finite_of_range_mu_eq_bot hmu
  exact no_noncuspidal_point_of_finite_quotient x y hx0 hx1 hcurve

/-- The same concrete rank-zero input is consumed by the genuine
Tate-normal-form exact-order-eighteen reduction. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 := by
  apply
    MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint
      E Q
  intro x y hx0 hx1 hcurve
  exact no_noncuspidal_point_of_range_mu_eq_bot
    hmu x y hx0 hx1 hcurve

end

end MazurTorsion.XOneEighteenFinalRankZero
