/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.IntegerPrimeSpecialization
import MazurTorsion.GroupTheory.IndependentCyclicGenerators
import MazurTorsion.NumberTheory.OrderThirtyFiveQuotient

/-!
# Rational torsion on the fixed level-35 model

The fixed Weierstrass model from `OrderThirtyFiveQuotient` has good reduction
at three and exactly
three points after reduction.  The exact-pin reduction theorem is injective
on rational torsion, while `OrderThirtyFiveQuotient` supplies a visible
rational point of exact order three.  We therefore obtain an unconditional
checked equivalence

`E(ℚ)_tors ≃ ZMod 3`.

This is a genuine downstream consumer of the fixed model and its normalized
three-torsion point.  It also proves that the model has no nonidentity
rational two-torsion, so the repository's explicit two-isogeny descent cannot
be used for this curve; the remaining rank-zero proof must use the visible
order-three subgroup (or a full `x-T` two-descent in the irreducible cubic
algebra).  This file does not identify the model with a modular quotient and
does not prove Mordell--Weil rank zero.
-/

open WeierstrassCurve

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Good reduction follows directly from the integral discriminant. -/
theorem modelRedCurve_isElliptic
    {p : ℕ} [Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ optimalQuotientModelIntegral.Δ) :
    (redCurve (integerPrime p)
      optimalQuotientModelIntegral).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (optimalQuotientModelIntegral.map
      (algebraMap ℤ
        (ℤ ⧸ (integerPrime p).asIdeal))).Δ ≠ 0
  rwa [Ne, WeierstrassCurve.map_Δ,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    integerPrime_asIdeal,
    Ideal.mem_span_singleton]

instance :
    (redCurve atThree
      optimalQuotientModelIntegral).IsElliptic :=
  modelRedCurve_isElliptic
    (by norm_num [optimalQuotientModelIntegral_discriminant])

/-- The concrete reduction of the fixed model over `F₃`. -/
def optimalQuotientModelModThree : WeierstrassCurve (ZMod 3) :=
  ⟨0, 1, 1, 9, 1⟩

instance : optimalQuotientModelModThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

private theorem modelBaseChange_modThree :
    ((optimalQuotientModelIntegral.toAffine ⁄ (ZMod 3)) :
      WeierstrassCurve _).toAffine =
        optimalQuotientModelModThree.toAffine := by
  ext <;> decide +kernel

/-- The abstract residue-field point group is the computable group over
`ZMod 3`. -/
noncomputable def modelReducedPointEquiv :
    (redCurve atThree
        optimalQuotientModelIntegral).Point ≃+
      optimalQuotientModelModThree.toAffine.Point :=
  (Point.mapEquiv
      (W' := optimalQuotientModelIntegral.toAffine)
      residueThreeAlgEquiv).trans
    (Point.congr modelBaseChange_modThree)

noncomputable instance :
    Finite
      (redCurve atThree
        optimalQuotientModelIntegral).Point :=
  .of_equiv optimalQuotientModelModThree.toAffine.Point
    modelReducedPointEquiv.symm.toEquiv

/-- The fixed model has exactly three points after reduction modulo
three. -/
theorem card_modelRedCurve_three :
    Nat.card
      (redCurve atThree
        optimalQuotientModelIntegral).Point = 3 := by
  calc
    Nat.card
        (redCurve atThree
          optimalQuotientModelIntegral).Point =
        Fintype.card optimalQuotientModelModThree.toAffine.Point :=
      (Nat.card_congr modelReducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 3 := by decide

/-- Reduction at three, restricted to rational torsion. -/
noncomputable def modelTorsionReduction :
    AddCommGroup.torsion optimalQuotientModel.toAffine.Point →+
      (redCurve atThree
        optimalQuotientModelIntegral).Point :=
  (redHom atThree
      map_optimalQuotientModelIntegral).comp
    (AddSubgroup.subtype
      (AddCommGroup.torsion
        optimalQuotientModel.toAffine.Point))

/-- The exact-pin reduction theorem makes reduction at three injective on
the entire rational torsion subgroup. -/
theorem modelTorsionReduction_injective :
    Function.Injective modelTorsionReduction := by
  intro P Q hPQ
  change
    redHom atThree
        map_optimalQuotientModelIntegral
        (P : optimalQuotientModel.toAffine.Point) =
      redHom atThree
        map_optimalQuotientModelIntegral
        (Q : optimalQuotientModel.toAffine.Point) at hPQ
  let D : AddCommGroup.torsion
      optimalQuotientModel.toAffine.Point := P - Q
  have hDred :
      red atThree
          map_optimalQuotientModelIntegral
          (D : optimalQuotientModel.toAffine.Point) = 0 := by
    change
      redHom atThree
          map_optimalQuotientModelIntegral
          ((P : optimalQuotientModel.toAffine.Point) - Q) = 0
    rw [map_sub, hPQ, sub_self]
  have hDzero : (D : optimalQuotientModel.toAffine.Point) = 0 :=
    eq_zero_of_isOfFinAddOrder_of_red_eq_zero
      atThree map_optimalQuotientModelIntegral
      (by decide) three_mem_atThree
      three_not_mem_atThree_pow_two D.property hDred
  apply Subtype.ext
  exact sub_eq_zero.mp hDzero

noncomputable instance modelTorsion_finite :
    Finite
      (AddCommGroup.torsion
        optimalQuotientModel.toAffine.Point) :=
  Finite.of_injective modelTorsionReduction
    modelTorsionReduction_injective

/-- Reduction gives the sharp upper bound of three on rational torsion. -/
theorem optimalQuotientModel_torsion_card_le_three :
    Nat.card
      (AddCommGroup.torsion
        optimalQuotientModel.toAffine.Point) ≤ 3 := by
  calc
    Nat.card
        (AddCommGroup.torsion
          optimalQuotientModel.toAffine.Point) ≤
        Nat.card
          (redCurve atThree
            optimalQuotientModelIntegral).Point :=
      Nat.card_le_card_of_injective modelTorsionReduction
        modelTorsionReduction_injective
    _ = 3 := card_modelRedCurve_three

/-- The visible point, regarded as an element of the rational torsion
subgroup. -/
def modelTorsionGenerator :
    AddCommGroup.torsion optimalQuotientModel.toAffine.Point :=
  ⟨modelThreeTorsion,
    addOrderOf_pos_iff.mp (by
      rw [addOrderOf_modelThreeTorsion]
      norm_num)⟩

private theorem three_nsmul_modelTorsionGenerator :
    (3 : ℕ) • modelTorsionGenerator = 0 := by
  apply Subtype.ext
  change (3 : ℕ) • modelThreeTorsion = 0
  rw [← addOrderOf_modelThreeTorsion]
  exact addOrderOf_nsmul_eq_zero modelThreeTorsion

/-- The homomorphism from `ZMod 3` generated by the visible torsion point. -/
def modelTorsionZModHom :
    ZMod 3 →+
      AddCommGroup.torsion optimalQuotientModel.toAffine.Point :=
  MazurTorsion.IndependentCyclicGenerators.zmodHom
    3 modelTorsionGenerator
    three_nsmul_modelTorsionGenerator

private theorem addOrderOf_modelTorsionGenerator :
    addOrderOf modelTorsionGenerator = 3 := by
  rw [← addOrderOf_injective
    (AddSubgroup.subtype
      (AddCommGroup.torsion
        optimalQuotientModel.toAffine.Point))
    (AddSubgroup.subtype_injective _)
    modelTorsionGenerator]
  exact addOrderOf_modelThreeTorsion

theorem modelTorsionZModHom_injective :
    Function.Injective modelTorsionZModHom :=
  MazurTorsion.IndependentCyclicGenerators.zmodHom_injective
    3 modelTorsionGenerator
    three_nsmul_modelTorsionGenerator
    addOrderOf_modelTorsionGenerator

/-- The rational torsion subgroup has exactly three elements. -/
theorem optimalQuotientModel_torsion_card_eq_three :
    Nat.card
      (AddCommGroup.torsion
        optimalQuotientModel.toAffine.Point) = 3 := by
  apply le_antisymm optimalQuotientModel_torsion_card_le_three
  simpa using
    Nat.card_le_card_of_injective modelTorsionZModHom
      modelTorsionZModHom_injective

/-- The checked rational torsion classification of the fixed model. -/
noncomputable def optimalQuotientModelTorsionEquiv :
    ZMod 3 ≃+
      AddCommGroup.torsion optimalQuotientModel.toAffine.Point :=
  AddEquiv.ofBijective modelTorsionZModHom
    (modelTorsionZModHom_injective.bijective_of_nat_card_le
      (by
        rw [optimalQuotientModel_torsion_card_eq_three]
        simp))

/-- Every rational torsion point is a multiple of the visible point
`(1,3)`.  This is a downstream consumer of the group equivalence, rather
than a cardinality-only certificate. -/
theorem torsion_point_eq_visible_multiple
    (P : optimalQuotientModel.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    ∃ z : ZMod 3,
      P = ((optimalQuotientModelTorsionEquiv z :
        AddCommGroup.torsion
          optimalQuotientModel.toAffine.Point) :
            optimalQuotientModel.toAffine.Point) := by
  let Ptors : AddCommGroup.torsion
      optimalQuotientModel.toAffine.Point := ⟨P, hP⟩
  exact ⟨optimalQuotientModelTorsionEquiv.symm Ptors,
    congrArg Subtype.val
      (optimalQuotientModelTorsionEquiv.apply_symm_apply Ptors).symm⟩

/-- Every rational torsion point is an explicit integral multiple of the
visible point `(1,3)`.  Unlike the preceding equivalence-valued statement,
this exposes the generator in the conclusion for descent consumers. -/
theorem torsion_point_eq_zsmul_modelThreeTorsion
    (P : optimalQuotientModel.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    ∃ n : ℤ, P = n • modelThreeTorsion := by
  let Ptors : AddCommGroup.torsion
      optimalQuotientModel.toAffine.Point := ⟨P, hP⟩
  obtain ⟨z, hz⟩ := optimalQuotientModelTorsionEquiv.surjective Ptors
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨n, ?_⟩
  have hzval := congrArg Subtype.val hz
  change
    ((modelTorsionZModHom (n : ZMod 3) :
        AddCommGroup.torsion optimalQuotientModel.toAffine.Point) :
      optimalQuotientModel.toAffine.Point) = P at hzval
  simp only [modelTorsionZModHom,
    MazurTorsion.IndependentCyclicGenerators.zmodHom_intCast] at hzval
  change n • modelThreeTorsion = P at hzval
  exact hzval.symm

/-- There is no nonidentity rational point killed by two.  In particular,
the fixed model has no rational subgroup of order two. -/
theorem eq_zero_of_two_nsmul_eq_zero
    (P : optimalQuotientModel.toAffine.Point)
    (hP : (2 : ℕ) • P = 0) :
    P = 0 := by
  have hfin : IsOfFinAddOrder P :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, hP⟩
  obtain ⟨z, hz⟩ := torsion_point_eq_visible_multiple P hfin
  have hzTwo :
      (2 : ℕ) •
          (optimalQuotientModelTorsionEquiv z :
            AddCommGroup.torsion
              optimalQuotientModel.toAffine.Point) = 0 := by
    apply Subtype.ext
    simpa [← hz] using hP
  have hsource : (2 : ℕ) • z = 0 := by
    apply optimalQuotientModelTorsionEquiv.injective
    rw [map_nsmul, hzTwo, map_zero]
  have hz0 : z = 0 := by
    have hthree : (3 : ℕ) • z = 0 := by
      calc
        (3 : ℕ) • z = (3 : ZMod 3) • z :=
          (Nat.cast_smul_eq_nsmul (ZMod 3) 3 z).symm
        _ = 0 := by
          rw [show (3 : ZMod 3) = 0 by decide, zero_smul]
    calc
      z = (3 : ℕ) • z - (2 : ℕ) • z := by abel
      _ = 0 := by rw [hthree, hsource]; simp
  rw [hz, hz0, map_zero]
  rfl

end MazurTorsion.OrderThirtyFive
