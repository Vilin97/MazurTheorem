/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime
import MazurTorsion.GroupTheory.IndependentCyclicGenerators
import MazurTorsion.NumberTheory.OrderThirtyFiveQuotient

/-!
# Rational torsion on the fixed level-35 quotient

The fixed quotient `X₀(35)/w₅` has good reduction at three and exactly
three points after reduction.  The exact-pin reduction theorem is injective
on rational torsion, while `OrderThirtyFiveQuotient` supplies a visible
rational point of exact order three.  We therefore obtain an unconditional
checked equivalence

`E(ℚ)_tors ≃ ZMod 3`.

This is a genuine downstream consumer of the fixed model and its normalized
three-torsion point.  It also proves that the quotient has no nonidentity
rational two-torsion, so the repository's explicit two-isogeny descent cannot
be used for this curve; the remaining rank-zero proof must use the visible
three-isogeny (or a full `x-T` two-descent in the irreducible cubic algebra).
-/

open WeierstrassCurve

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The height-one prime `(p)` of `ℤ`, with a quotient name local to the
fixed order-35 curve. -/
def quotientIntPrime (p : ℕ) [Fact p.Prime] :
    HeightOneSpectrum ℤ :=
  .ofPrime (p := Ideal.span {(p : ℤ)})
    (Ideal.prime_span_singleton_iff.mpr
      (Nat.prime_iff_prime_int.mp Fact.out))

@[simp] theorem quotientIntPrime_asIdeal
    (p : ℕ) [Fact p.Prime] :
    (quotientIntPrime p).asIdeal = Ideal.span {(p : ℤ)} :=
  rfl

noncomputable instance (p : ℕ) [Fact p.Prime] :
    DecidableEq (ℤ ⧸ (quotientIntPrime p).asIdeal) :=
  Classical.decEq _

/-- Good reduction follows directly from the integral discriminant. -/
theorem quotientRedCurve_isElliptic
    {p : ℕ} [Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ optimalQuotientIntegral.Δ) :
    (redCurve (quotientIntPrime p)
      optimalQuotientIntegral).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (optimalQuotientIntegral.map
      (algebraMap ℤ
        (ℤ ⧸ (quotientIntPrime p).asIdeal))).Δ ≠ 0
  rwa [Ne, WeierstrassCurve.map_Δ,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    quotientIntPrime_asIdeal,
    Ideal.mem_span_singleton]

instance :
    (redCurve (quotientIntPrime 3)
      optimalQuotientIntegral).IsElliptic :=
  quotientRedCurve_isElliptic
    (by norm_num [optimalQuotientIntegral_discriminant])

/-- The concrete reduction of the fixed quotient over `F₃`. -/
def optimalQuotientModThree : WeierstrassCurve (ZMod 3) :=
  ⟨0, 1, 1, 9, 1⟩

instance : optimalQuotientModThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

/-- The canonical residue-field identification at three. -/
noncomputable def quotientResidueThreeAlgEquiv :
    (ℤ ⧸ (quotientIntPrime 3).asIdeal) ≃ₐ[ℤ] ZMod 3 :=
  AlgEquiv.ofRingEquiv
    (f := Int.quotientSpanNatEquivZMod 3) fun x ↦ by
      change
        (Int.quotientSpanNatEquivZMod 3 :
          (ℤ ⧸ Ideal.span {((3 : ℕ) : ℤ)}) →+* ZMod 3)
            (Ideal.Quotient.mk
              (Ideal.span {((3 : ℕ) : ℤ)}) x) =
          Int.castRingHom (ZMod 3) x
      simpa only [RingHom.comp_apply] using
        DFunLike.congr_fun
          (Int.quotientSpanNatEquivZMod_comp_Quotient_mk 3) x

private theorem quotientBaseChange_modThree :
    ((optimalQuotientIntegral.toAffine ⁄ (ZMod 3)) :
      WeierstrassCurve _).toAffine =
        optimalQuotientModThree.toAffine := by
  ext <;> decide +kernel

/-- The abstract residue-field point group is the computable group over
`ZMod 3`. -/
noncomputable def quotientReducedPointEquiv :
    (redCurve (quotientIntPrime 3)
        optimalQuotientIntegral).Point ≃+
      optimalQuotientModThree.toAffine.Point :=
  (Point.mapEquiv
      (W' := optimalQuotientIntegral.toAffine)
      quotientResidueThreeAlgEquiv).trans
    (Point.congr quotientBaseChange_modThree)

noncomputable instance :
    Finite
      (redCurve (quotientIntPrime 3)
        optimalQuotientIntegral).Point :=
  .of_equiv optimalQuotientModThree.toAffine.Point
    quotientReducedPointEquiv.symm.toEquiv

/-- The fixed quotient has exactly three points after reduction modulo
three. -/
theorem card_quotientRedCurve_three :
    Nat.card
      (redCurve (quotientIntPrime 3)
        optimalQuotientIntegral).Point = 3 := by
  calc
    Nat.card
        (redCurve (quotientIntPrime 3)
          optimalQuotientIntegral).Point =
        Fintype.card optimalQuotientModThree.toAffine.Point :=
      (Nat.card_congr quotientReducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 3 := by decide

private theorem three_mem_quotientIntPrime :
    (3 : ℤ) ∈ (quotientIntPrime 3).asIdeal :=
  Ideal.mem_span_singleton_self 3

private theorem three_not_mem_quotientIntPrime_sq :
    (3 : ℤ) ∉ (quotientIntPrime 3).asIdeal ^ (3 - 1) := by
  rw [quotientIntPrime_asIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  norm_num

/-- Reduction at three, restricted to rational torsion. -/
noncomputable def quotientTorsionReduction :
    AddCommGroup.torsion optimalQuotient.toAffine.Point →+
      (redCurve (quotientIntPrime 3)
        optimalQuotientIntegral).Point :=
  (redHom (quotientIntPrime 3)
      map_optimalQuotientIntegral).comp
    (AddSubgroup.subtype
      (AddCommGroup.torsion
        optimalQuotient.toAffine.Point))

/-- The exact-pin reduction theorem makes reduction at three injective on
the entire rational torsion subgroup. -/
theorem quotientTorsionReduction_injective :
    Function.Injective quotientTorsionReduction := by
  intro P Q hPQ
  change
    redHom (quotientIntPrime 3)
        map_optimalQuotientIntegral
        (P : optimalQuotient.toAffine.Point) =
      redHom (quotientIntPrime 3)
        map_optimalQuotientIntegral
        (Q : optimalQuotient.toAffine.Point) at hPQ
  let D : AddCommGroup.torsion
      optimalQuotient.toAffine.Point := P - Q
  have hDred :
      red (quotientIntPrime 3)
          map_optimalQuotientIntegral
          (D : optimalQuotient.toAffine.Point) = 0 := by
    change
      redHom (quotientIntPrime 3)
          map_optimalQuotientIntegral
          ((P : optimalQuotient.toAffine.Point) - Q) = 0
    rw [map_sub, hPQ, sub_self]
  have hDzero : (D : optimalQuotient.toAffine.Point) = 0 :=
    eq_zero_of_isOfFinAddOrder_of_red_eq_zero
      (quotientIntPrime 3) map_optimalQuotientIntegral
      (by decide) three_mem_quotientIntPrime
      three_not_mem_quotientIntPrime_sq D.property hDred
  apply Subtype.ext
  exact sub_eq_zero.mp hDzero

noncomputable instance quotientTorsion_finite :
    Finite
      (AddCommGroup.torsion
        optimalQuotient.toAffine.Point) :=
  Finite.of_injective quotientTorsionReduction
    quotientTorsionReduction_injective

/-- Reduction gives the sharp upper bound of three on rational torsion. -/
theorem optimalQuotient_torsion_card_le_three :
    Nat.card
      (AddCommGroup.torsion
        optimalQuotient.toAffine.Point) ≤ 3 := by
  calc
    Nat.card
        (AddCommGroup.torsion
          optimalQuotient.toAffine.Point) ≤
        Nat.card
          (redCurve (quotientIntPrime 3)
            optimalQuotientIntegral).Point :=
      Nat.card_le_card_of_injective quotientTorsionReduction
        quotientTorsionReduction_injective
    _ = 3 := card_quotientRedCurve_three

/-- The visible point, regarded as an element of the rational torsion
subgroup. -/
def quotientTorsionGenerator :
    AddCommGroup.torsion optimalQuotient.toAffine.Point :=
  ⟨quotientThreeTorsion,
    addOrderOf_pos_iff.mp (by
      rw [addOrderOf_quotientThreeTorsion]
      norm_num)⟩

private theorem three_nsmul_quotientTorsionGenerator :
    (3 : ℕ) • quotientTorsionGenerator = 0 := by
  apply Subtype.ext
  change (3 : ℕ) • quotientThreeTorsion = 0
  rw [← addOrderOf_quotientThreeTorsion]
  exact addOrderOf_nsmul_eq_zero quotientThreeTorsion

/-- The homomorphism from `ZMod 3` generated by the visible torsion point. -/
def quotientTorsionZModHom :
    ZMod 3 →+
      AddCommGroup.torsion optimalQuotient.toAffine.Point :=
  MazurTorsion.IndependentCyclicGenerators.zmodHom
    3 quotientTorsionGenerator
    three_nsmul_quotientTorsionGenerator

private theorem addOrderOf_quotientTorsionGenerator :
    addOrderOf quotientTorsionGenerator = 3 := by
  rw [← addOrderOf_injective
    (AddSubgroup.subtype
      (AddCommGroup.torsion
        optimalQuotient.toAffine.Point))
    (AddSubgroup.subtype_injective _)
    quotientTorsionGenerator]
  exact addOrderOf_quotientThreeTorsion

theorem quotientTorsionZModHom_injective :
    Function.Injective quotientTorsionZModHom :=
  MazurTorsion.IndependentCyclicGenerators.zmodHom_injective
    3 quotientTorsionGenerator
    three_nsmul_quotientTorsionGenerator
    addOrderOf_quotientTorsionGenerator

/-- The rational torsion subgroup has exactly three elements. -/
theorem optimalQuotient_torsion_card_eq_three :
    Nat.card
      (AddCommGroup.torsion
        optimalQuotient.toAffine.Point) = 3 := by
  apply le_antisymm optimalQuotient_torsion_card_le_three
  simpa using
    Nat.card_le_card_of_injective quotientTorsionZModHom
      quotientTorsionZModHom_injective

/-- The checked rational torsion classification of the fixed quotient. -/
noncomputable def optimalQuotientTorsionEquiv :
    ZMod 3 ≃+
      AddCommGroup.torsion optimalQuotient.toAffine.Point :=
  AddEquiv.ofBijective quotientTorsionZModHom
    (quotientTorsionZModHom_injective.bijective_of_nat_card_le
      (by
        rw [optimalQuotient_torsion_card_eq_three]
        simp))

/-- Every rational torsion point is a multiple of the visible point
`(1,3)`.  This is a downstream consumer of the group equivalence, rather
than a cardinality-only certificate. -/
theorem torsion_point_eq_visible_multiple
    (P : optimalQuotient.toAffine.Point)
    (hP : IsOfFinAddOrder P) :
    ∃ z : ZMod 3,
      P = ((optimalQuotientTorsionEquiv z :
        AddCommGroup.torsion
          optimalQuotient.toAffine.Point) :
            optimalQuotient.toAffine.Point) := by
  let Ptors : AddCommGroup.torsion
      optimalQuotient.toAffine.Point := ⟨P, hP⟩
  exact ⟨optimalQuotientTorsionEquiv.symm Ptors,
    congrArg Subtype.val
      (optimalQuotientTorsionEquiv.apply_symm_apply Ptors).symm⟩

/-- There is no nonidentity rational point killed by two.  In particular,
the fixed quotient admits no rational degree-two isogeny kernel. -/
theorem eq_zero_of_two_nsmul_eq_zero
    (P : optimalQuotient.toAffine.Point)
    (hP : (2 : ℕ) • P = 0) :
    P = 0 := by
  have hfin : IsOfFinAddOrder P :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, hP⟩
  obtain ⟨z, hz⟩ := torsion_point_eq_visible_multiple P hfin
  have hzTwo :
      (2 : ℕ) •
          (optimalQuotientTorsionEquiv z :
            AddCommGroup.torsion
              optimalQuotient.toAffine.Point) = 0 := by
    apply Subtype.ext
    simpa [← hz] using hP
  have hsource : (2 : ℕ) • z = 0 := by
    apply optimalQuotientTorsionEquiv.injective
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
