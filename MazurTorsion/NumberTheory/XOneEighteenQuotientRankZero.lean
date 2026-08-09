/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.NaiveHeightDescent
import MazurTorsion.GroupTheory.IndexNSmulFG
import MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel

/-!
# The rank-zero bridge for the `X₁(18)` elliptic quotient

This file isolates the group-theoretic conclusion of the concrete
`x - T` descent.  Its sole arithmetic hypothesis is that the image of the
descent homomorphism on the completed-square model is trivial.  Under that
hypothesis, the kernel theorem makes multiplication by two surjective.
Naive-height descent then gives finite generation, and the index formula for
finitely generated abelian groups forces rank zero and finiteness.

No claim that the descent image is trivial is made here; that is the remaining
explicit Selmer/local arithmetic calculation.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientRankZero

noncomputable section

open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenRealCubicQuotient

/-- The image of multiplication by two on the completed-square descent
model. -/
abbrev descentDoublingRange :
    AddSubgroup descentCurve.toAffine.Point :=
  (nsmulAddMonoidHom (α := descentCurve.toAffine.Point) 2).range

/-- A trivial `x - T` image makes multiplication by two surjective. -/
theorem descentDoublingRange_eq_top_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    descentDoublingRange = ⊤ := by
  apply top_unique
  intro P _
  have hmemRange :
      WeierstrassCurve.Affine.μ
          (W := descentCurve.toAffine) (.ofAdd P) ∈
        (WeierstrassCurve.Affine.μ
          (W := descentCurve.toAffine)).range :=
    ⟨.ofAdd P, rfl⟩
  rw [hμ] at hmemRange
  have hmemKer :
      .ofAdd P ∈
        (WeierstrassCurve.Affine.μ
          (W := descentCurve.toAffine)).ker := by
    simpa only [MonoidHom.mem_ker, Subgroup.mem_bot] using hmemRange
  rw [WeierstrassCurve.Affine.ker_μ_eq] at hmemKer
  change P ∈
    (nsmulAddMonoidHom
      (α := descentCurve.toAffine.Point) 2).range
  simpa only [Multiplicative.mem_toSubgroup, toAdd_ofAdd] using hmemKer

/-- Multiplication by two has finite index when the concrete descent image
is trivial. -/
theorem descent_doubling_finiteIndex_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    descentDoublingRange.FiniteIndex := by
  rw [descentDoublingRange_eq_top_of_range_mu_eq_bot hμ]
  infer_instance

/-- The completed-square point group is finitely generated when the concrete
descent image is trivial. -/
theorem descent_point_fg_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    AddGroup.FG descentCurve.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_two descentCurve
    (descent_doubling_finiteIndex_of_range_mu_eq_bot hμ)

/-- A trivial descent image forces Mordell--Weil rank zero on the
completed-square model. -/
theorem descent_point_rank_zero_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    Module.finrank ℤ descentCurve.toAffine.Point = 0 := by
  letI : AddGroup.FG descentCurve.toAffine.Point :=
    descent_point_fg_of_range_mu_eq_bot hμ
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg
      descentCurve.toAffine.Point (by norm_num : (2 : ℕ) ≠ 0)
  have hrange :
      (nsmulAddMonoidHom
        (α := descentCurve.toAffine.Point) 2).range = ⊤ :=
    descentDoublingRange_eq_top_of_range_mu_eq_bot hμ
  rw [hrange] at hformula
  have hformula' :
      1 = 2 ^ Module.finrank ℤ descentCurve.toAffine.Point *
        Nat.card
          (nsmulAddMonoidHom
            (α := descentCurve.toAffine.Point) 2).ker := by
    simpa only [AddSubgroup.index_top] using hformula
  have hpow : 2 ^ Module.finrank ℤ descentCurve.toAffine.Point = 1 :=
    Nat.dvd_one.mp ⟨_, hformula'⟩
  simpa using hpow

/-- The completed-square point group is finite when the concrete descent
image is trivial. -/
theorem descent_point_finite_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    Finite descentCurve.toAffine.Point := by
  letI : AddGroup.FG descentCurve.toAffine.Point :=
    descent_point_fg_of_range_mu_eq_bot hμ
  letI : Module.Finite ℤ descentCurve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr
      (descent_point_fg_of_range_mu_eq_bot hμ)
  have hmoduleTorsion :
      Module.IsTorsion ℤ descentCurve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      (descent_point_rank_zero_of_range_mu_eq_bot hμ)
  exact AddCommGroup.finite_of_fg_torsion descentCurve.toAffine.Point
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

/-- Finiteness transports back across the checked admissible change of
Weierstrass variables to the original real-cubic quotient. -/
theorem quotient_point_finite_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    Finite quotientCurve.toAffine.Point := by
  letI : Finite descentCurve.toAffine.Point :=
    descent_point_finite_of_range_mu_eq_bot hμ
  exact Finite.of_equiv descentCurve.toAffine.Point
    quotientToDescentEquiv.symm.toEquiv

/-- The original quotient point group is finitely generated under the same
explicit descent-image hypothesis. -/
theorem quotient_point_fg_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    AddGroup.FG quotientCurve.toAffine.Point := by
  letI : Finite quotientCurve.toAffine.Point :=
    quotient_point_finite_of_range_mu_eq_bot hμ
  infer_instance

/-- Rank zero transports across the checked additive equivalence from the
original quotient to the completed-square model. -/
theorem quotient_point_rank_zero_of_range_mu_eq_bot
    (hμ :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥) :
    Module.finrank ℤ quotientCurve.toAffine.Point = 0 := by
  calc
    Module.finrank ℤ quotientCurve.toAffine.Point =
        Module.finrank ℤ descentCurve.toAffine.Point :=
      quotientToDescentEquiv.toIntLinearEquiv.finrank_eq
    _ = 0 := descent_point_rank_zero_of_range_mu_eq_bot hμ

end

end MazurTorsion.XOneEighteenQuotientRankZero
