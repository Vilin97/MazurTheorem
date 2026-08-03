/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.NaiveHeightDescent
import MazurTorsion.GroupTheory.IndexNSmulFG
import MazurTorsion.NumberTheory.OrderThirtyFiveThreeIsogenyDual
import MazurTorsion.NumberTheory.RatNorthcott

/-!
# The exact order-35 three-descent boundary

The explicit candidate maps are most convenient on the normalized model

`Y² + 4XY + 7Y = X³`.

This file isolates the remaining arithmetic output at precisely the strength
needed downstream: every rational point is represented, modulo three times
the point group, by one of `0`, `(0,0)`, and `(0,-7)`.  From that three-coset
certificate we prove finite generation, Mordell--Weil rank zero, and
finiteness for the fixed model expected to be `X₀(35)/w₅`.

No three-coset certificate is asserted here.  Its proof is the outstanding
fixed-number-field three-isogeny Selmer calculation; all consequences below
are checked consumers of the exact proposition it must establish.
-/

open WeierstrassCurve

namespace WeierstrassCurve.Affine

open Height

/-- The approximate parallelogram law runs naïve-height descent with
multiplication by three. -/
theorem fg_point_of_finiteIndex_three
    (W : WeierstrassCurve ℚ) [W.toAffine.IsElliptic]
    (hindex :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 3).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  let h : W.toAffine.Point → ℝ := Point.naiveHeight
  have hnonneg (P : W.toAffine.Point) : 0 ≤ h P := by
    change 0 ≤ P.naiveHeight
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  have htranslate (G P : W.toAffine.Point) :
      h P ≤ 2 * h (G + P) + (2 * h (-G) + C) := by
    have hpar := hC (G + P) (-G)
    have hrest : 0 ≤ h ((G + P) - (-G)) := hnonneg _
    have hsum : (G + P) + (-G) = P := by abel
    rw [hsum] at hpar
    grind
  have hgrowth (P : W.toAffine.Point) :
      9 * h P - (2 * h 0 + 3 * C) ≤ h ((3 : ℕ) • P) := by
    have htwoPar := hC P P
    have htwo :
        4 * h P - (h 0 + C) ≤ h ((2 : ℕ) • P) := by
      have hsum : P + P = (2 : ℕ) • P := by abel
      have hdiff : P - P = 0 := sub_self P
      rw [hsum, hdiff] at htwoPar
      grind
    have hthreePar := hC ((2 : ℕ) • P) P
    have hsum : (2 : ℕ) • P + P = (3 : ℕ) • P := by abel
    have hdiff : (2 : ℕ) • P - P = P := by abel
    rw [hsum, hdiff] at hthreePar
    grind
  letI : Northcott h := by
    dsimp only [h]
    infer_instance
  exact
    AddCommGroup.fg_of_descent
      (n := 3) (h := h) (a := 2) (b := 9)
      (c₀ := 2 * h 0 + 3 * C)
      (c := fun G ↦ 2 * h (-G) + C)
      (by norm_num) (by norm_num) hindex
      htranslate hgrowth

end WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- Multiplication by three on the normalized source model. -/
def normalizedThreeRange : AddSubgroup threeTorsionCurve.toAffine.Point :=
  (nsmulAddMonoidHom
    (α := threeTorsionCurve.toAffine.Point) 3).range

/-- Membership in three times the normalized point group is equivalently
membership in the image of the checked dual-after-candidate composite.  This
is the bridge from the explicit point functions to the Selmer coset
boundary; it uses only the proved composite identity, not unproved
additivity of either factor. -/
theorem mem_normalizedThreeRange_iff_exists_candidateComposite
    (P : threeTorsionCurve.toAffine.Point) :
    P ∈ normalizedThreeRange ↔
      ∃ Q : threeTorsionCurve.toAffine.Point,
        P = veluThreeDualCandidatePointFun
          (veluThreeCandidatePointFun Q) := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    rw [veluThreeDualCandidatePointFun_candidate]
    exact hQ.symm
  · rintro ⟨Q, rfl⟩
    refine ⟨Q, ?_⟩
    exact (veluThreeDualCandidatePointFun_candidate Q).symm

/-- The three visible representatives on the normalized source model. -/
def normalizedThreeRepresentative (i : Fin 3) :
    threeTorsionCurve.toAffine.Point :=
  i.val • threeTorsionOrigin

/-- The exact arithmetic output required from the order-35 three-isogeny
descent: the visible rational subgroup exhausts the quotient by three times
the rational point group. -/
def ThreeCosetBound : Prop :=
  ∀ P : threeTorsionCurve.toAffine.Point,
    ∃ i : Fin 3, ∃ Q : threeTorsionCurve.toAffine.Point,
      P = normalizedThreeRepresentative i + (3 : ℕ) • Q

/-- Multiplication by three on the fixed quotient model. -/
def optimalQuotientModelThreeRange :
    AddSubgroup optimalQuotientModel.toAffine.Point :=
  (nsmulAddMonoidHom
    (α := optimalQuotientModel.toAffine.Point) 3).range

/-- The corresponding visible representatives on the selected fixed
model. -/
def optimalQuotientModelThreeRepresentative (i : Fin 3) :
    optimalQuotientModel.toAffine.Point :=
  i.val • modelThreeTorsion

private theorem optimalQuotientModel_cosets_of_normalized
    (hcosets : ThreeCosetBound) :
    ∀ P : optimalQuotientModel.toAffine.Point,
      ∃ i : Fin 3, ∃ Q : optimalQuotientModel.toAffine.Point,
        P = optimalQuotientModelThreeRepresentative i + (3 : ℕ) • Q := by
  intro P
  obtain ⟨i, Q, hQ⟩ := hcosets (threeTorsionEquiv.symm P)
  refine ⟨i, threeTorsionEquiv Q, ?_⟩
  calc
    P = threeTorsionEquiv (threeTorsionEquiv.symm P) := by
      rw [threeTorsionEquiv.apply_symm_apply]
    _ = threeTorsionEquiv
          (normalizedThreeRepresentative i + (3 : ℕ) • Q) := by
      rw [hQ]
    _ = optimalQuotientModelThreeRepresentative i +
          (3 : ℕ) • threeTorsionEquiv Q := by
      simp only [map_add, map_nsmul, normalizedThreeRepresentative,
        optimalQuotientModelThreeRepresentative,
        threeTorsionEquiv_origin]

/-- A normalized three-coset certificate surjects onto the quotient of the
fixed model by multiplication by three. -/
theorem optimalQuotientModel_three_quotient_surjective
    (hcosets : ThreeCosetBound) :
    Function.Surjective
      (fun i : Fin 3 ↦
        QuotientAddGroup.mk' optimalQuotientModelThreeRange
          (optimalQuotientModelThreeRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective optimalQuotientModelThreeRange c
  obtain ⟨i, Q, hP⟩ :=
    optimalQuotientModel_cosets_of_normalized hcosets P
  refine ⟨i, (QuotientAddGroup.mk'_eq_mk'
    optimalQuotientModelThreeRange).mpr ?_⟩
  refine ⟨(3 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
  exact hP.symm

/-- A normalized three-coset certificate makes tripling have finite index
on the selected fixed model. -/
theorem optimalQuotientModel_three_finiteIndex_of_cosetBound
    (hcosets : ThreeCosetBound) :
    optimalQuotientModelThreeRange.FiniteIndex := by
  letI : Finite
      (optimalQuotientModel.toAffine.Point ⧸
        optimalQuotientModelThreeRange) :=
    Finite.of_surjective _
      (optimalQuotientModel_three_quotient_surjective hcosets)
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The explicit three-fold height descent consumes the normalized Selmer
certificate and proves finite generation of the fixed model. -/
theorem optimalQuotientModel_point_fg_of_cosetBound
    (hcosets : ThreeCosetBound) :
    AddGroup.FG optimalQuotientModel.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_three
    optimalQuotientModel
    (optimalQuotientModel_three_finiteIndex_of_cosetBound hcosets)

/-- The same certificate gives the sharp index bound three. -/
theorem optimalQuotientModel_three_index_le_three_of_cosetBound
    (hcosets : ThreeCosetBound) :
    optimalQuotientModelThreeRange.index ≤ 3 := by
  letI : Finite
      (optimalQuotientModel.toAffine.Point ⧸
        optimalQuotientModelThreeRange) :=
    Finite.of_surjective _
      (optimalQuotientModel_three_quotient_surjective hcosets)
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      (optimalQuotientModel_three_quotient_surjective hcosets)).trans_eq
        (by simp)

private theorem optimalQuotientModel_three_nsmul_of_torsion
    (P : AddCommGroup.torsion optimalQuotientModel.toAffine.Point) :
    (3 : ℕ) • (P : optimalQuotientModel.toAffine.Point) = 0 := by
  obtain ⟨z, rfl⟩ := optimalQuotientModelTorsionEquiv.surjective P
  change
    (((3 : ℕ) •
        (optimalQuotientModelTorsionEquiv z :
          AddCommGroup.torsion optimalQuotientModel.toAffine.Point) :
      AddCommGroup.torsion optimalQuotientModel.toAffine.Point) :
        optimalQuotientModel.toAffine.Point) = 0
  rw [← map_nsmul]
  have hz : (3 : ℕ) • z = 0 := by
    calc
      (3 : ℕ) • z = (3 : ZMod 3) • z :=
        (Nat.cast_smul_eq_nsmul (ZMod 3) 3 z).symm
      _ = 0 := by
        rw [show (3 : ZMod 3) = 0 by decide, zero_smul]
  rw [hz, map_zero]
  rfl

/-- On this fixed model the full rational torsion subgroup is exactly the
kernel of multiplication by three. -/
noncomputable def optimalQuotientModelTorsionEquivThreeKernel :
    AddCommGroup.torsion optimalQuotientModel.toAffine.Point ≃+
      (nsmulAddMonoidHom
        (α := optimalQuotientModel.toAffine.Point) 3).ker where
  toFun P := ⟨P, optimalQuotientModel_three_nsmul_of_torsion P⟩
  invFun P :=
    ⟨P, isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨3, by norm_num, P.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The rational three-torsion kernel on the fixed model has exactly three
elements. -/
theorem optimalQuotientModel_threeKernel_card :
    Nat.card
      (nsmulAddMonoidHom
        (α := optimalQuotientModel.toAffine.Point) 3).ker = 3 := by
  rw [← Nat.card_congr
    optimalQuotientModelTorsionEquivThreeKernel.toEquiv]
  exact optimalQuotientModel_torsion_card_eq_three

/-- The exact three-coset output forces Mordell--Weil rank zero for the
selected fixed model. -/
theorem optimalQuotientModel_point_rank_zero_of_cosetBound
    (hcosets : ThreeCosetBound) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 := by
  letI : AddGroup.FG optimalQuotientModel.toAffine.Point :=
    optimalQuotientModel_point_fg_of_cosetBound hcosets
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg
      optimalQuotientModel.toAffine.Point
      (by norm_num : (3 : ℕ) ≠ 0)
  change
    optimalQuotientModelThreeRange.index =
      3 ^ Module.finrank ℤ optimalQuotientModel.toAffine.Point *
        Nat.card
          (nsmulAddMonoidHom
            (α := optimalQuotientModel.toAffine.Point) 3).ker at hformula
  rw [optimalQuotientModel_threeKernel_card] at hformula
  have hindex : optimalQuotientModelThreeRange.index ≤ 3 :=
    optimalQuotientModel_three_index_le_three_of_cosetBound hcosets
  have hpow :
      3 ^ Module.finrank ℤ optimalQuotientModel.toAffine.Point ≤ 1 := by
    omega
  have hpowequal :
      3 ^ Module.finrank ℤ optimalQuotientModel.toAffine.Point = 1 :=
    le_antisymm hpow (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- Once the exact three cosets are certified, the rational point group of
the selected fixed model is finite. -/
theorem optimalQuotientModel_point_finite_of_cosetBound
    (hcosets : ThreeCosetBound) :
    Finite optimalQuotientModel.toAffine.Point := by
  letI : AddGroup.FG optimalQuotientModel.toAffine.Point :=
    optimalQuotientModel_point_fg_of_cosetBound hcosets
  letI : Module.Finite ℤ optimalQuotientModel.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr
      (optimalQuotientModel_point_fg_of_cosetBound hcosets)
  have hmoduleTorsion :
      Module.IsTorsion ℤ optimalQuotientModel.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      (optimalQuotientModel_point_rank_zero_of_cosetBound hcosets)
  exact
    AddCommGroup.finite_of_fg_torsion
      optimalQuotientModel.toAffine.Point
      (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

end MazurTorsion.OrderThirtyFive
