/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck
-/

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.NumberField.CMField
import MazurTorsion.NumberTheory.CyclotomicJacobiCharacter

/-!
# The second cyclotomic Jacobi sum

This file specializes Mathlib's Jacobi-sum API to the canonical cyclotomic
power-residue character.  It records Galois covariance, complex conjugation,
the elementary absolute-value identity, semiprimary congruence, and the exact
two-character Gauss-sum relation.  These are the narrow Jacobi-sum inputs
intended for the cyclotomic reciprocity consumer in `KummerArtinProduct`.

The Jacobi-sum definition and general identities come from
`Mathlib.NumberTheory.JacobiSum.Basic`, by Michael Stoll (2024), released under
Apache-2.0 and following Ireland--Rosen, *A Classical Introduction to Modern
Number Theory*, Section 8.3.  No Jacobi ideal factorization, Artin reciprocity,
or cyclotomic reciprocity theorem is asserted here.
-/

open Algebra
open scoped NumberField

namespace NumberTheory.CyclotomicCharacter.InverseExtension

section

variable {p : ℕ} [Fact p.Prime]

local instance : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

private abbrev CyclotomicIntegerRing (p : ℕ) :=
  NumberField.RingOfIntegers (PrimeCyclotomicField p)

/-- Complex conjugation on the integers of the prime cyclotomic field. -/
noncomputable def cyclotomicIntegerComplexConj (p : ℕ) [Fact p.Prime]
    (hp : 2 < p) :
    CyclotomicIntegerRing p ≃+* CyclotomicIntegerRing p := by
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : NumberField.IsCMField (PrimeCyclotomicField p) :=
    IsCyclotomicExtension.Rat.isCMField (PrimeCyclotomicField p)
      ⟨p, Set.mem_singleton p, hp⟩
  exact (NumberField.IsCMField.ringOfIntegersComplexConj
    (PrimeCyclotomicField p)).toRingEquiv

private theorem cyclotomicIntegerComplexConj_zeta (hp : 2 < p) :
    cyclotomicIntegerComplexConj p hp
        (integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) =
      (integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) ^ (p - 1) := by
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : NumberField.IsCMField (PrimeCyclotomicField p) :=
    IsCyclotomicExtension.Rat.isCMField (PrimeCyclotomicField p)
      ⟨p, Set.mem_singleton p, hp⟩
  let ζ := integralCyclotomicZetaUnit p
  let ζt : NumberField.Units.torsion (PrimeCyclotomicField p) :=
    ⟨ζ, by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion,
        isOfFinOrder_iff_pow_eq_one]
      exact ⟨p, (Fact.out : p.Prime).pos,
        (integralCyclotomicZetaUnit_isPrimitiveRoot (p := p)).pow_eq_one⟩⟩
  have hconj := NumberField.IsCMField.unitsComplexConj_torsion
    (PrimeCyclotomicField p) ζt
  have hconj_val := congrArg
    (fun u : (CyclotomicIntegerRing p)ˣ ↦ (u : CyclotomicIntegerRing p)) hconj
  change cyclotomicIntegerComplexConj p hp (ζ : CyclotomicIntegerRing p) =
    ((ζ⁻¹ : (CyclotomicIntegerRing p)ˣ) : CyclotomicIntegerRing p) at hconj_val
  have hpow : ζ ^ (p - 1) = ζ⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    exact (integralCyclotomicZetaUnit_isPrimitiveRoot (p := p)).pow_eq_one
  calc
    cyclotomicIntegerComplexConj p hp (ζ : CyclotomicIntegerRing p) =
        ((ζ⁻¹ : (CyclotomicIntegerRing p)ˣ) : CyclotomicIntegerRing p) := hconj_val
    _ = ((ζ ^ (p - 1) : (CyclotomicIntegerRing p)ˣ) :
        CyclotomicIntegerRing p) := congrArg Units.val hpow.symm
    _ = (ζ : CyclotomicIntegerRing p) ^ (p - 1) :=
      Units.val_pow_eq_pow_val ζ (p - 1)

/-- Complex conjugation sends the canonical power-residue character to its
inverse. -/
theorem cyclotomicPowerResidueChar_ringHomComp_complexConj
    (hp : 2 < p)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    (cyclotomicPowerResidueChar v hpv).ringHomComp
        (cyclotomicIntegerComplexConj p hp).toRingHom =
      (cyclotomicPowerResidueChar v hpv)⁻¹ := by
  letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  have hdiv : p ∣ Fintype.card (CyclotomicIntegerRing p ⧸ v.asIdeal) - 1 := by
    simpa only [← Nat.card_eq_fintype_card, residueField_card_eq_absNorm] using
      prime_dvd_absNorm_sub_one v hpv
  have hcomp := finiteFieldPowerResidueMulChar_ringHomComp_pow_eq
    (cyclotomicResidueZeta v)
    (cyclotomicResidueZeta_isPrimitiveRoot v hpv)
    hdiv
    (integralCyclotomicZetaUnit p)
    (integralCyclotomicZetaUnit_isPrimitiveRoot (p := p))
    (cyclotomicIntegerComplexConj p hp).toRingHom
    (p - 1) (cyclotomicIntegerComplexConj_zeta hp)
  have hpow : cyclotomicPowerResidueChar v hpv ^ (p - 1) =
      (cyclotomicPowerResidueChar v hpv)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    have h := pow_orderOf_eq_one (cyclotomicPowerResidueChar v hpv)
    rwa [orderOf_cyclotomicPowerResidueChar v hpv] at h
  rw [cyclotomicPowerResidueChar]
  exact hcomp.trans hpow

/-- The canonical diagonal Jacobi sum `J(χ_v, χ_v)` at a finite prime
away from `p`. -/
noncomputable def cyclotomicJacobiSumTwo
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    CyclotomicIntegerRing p := by
  letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  exact jacobiSum (cyclotomicPowerResidueChar v hpv)
    (cyclotomicPowerResidueChar v hpv)

/-- Cyclotomic Galois action carries `J(χ_v, χ_v)` to the Jacobi sum of
the corresponding powers of `χ_v`. -/
theorem cyclotomicJacobiSumTwo_galois
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal)
    (σ : Gal(PrimeCyclotomicField p/ℚ)) :
    letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
      Fintype.ofFinite _
    baseIntegerEquiv σ (cyclotomicJacobiSumTwo v hpv) =
      jacobiSum
        (cyclotomicPowerResidueChar v hpv ^
          (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val))
        (cyclotomicPowerResidueChar v hpv ^
          (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val)) := by
  letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  rw [cyclotomicJacobiSumTwo]
  change (baseIntegerEquiv σ).toRingHom
    (jacobiSum (cyclotomicPowerResidueChar v hpv)
      (cyclotomicPowerResidueChar v hpv)) = _
  rw [← jacobiSum_ringHomComp,
    cyclotomicPowerResidueChar_ringHomComp]

/-- Complex conjugation of `J(χ_v, χ_v)` is
`J(χ_v⁻¹, χ_v⁻¹)`. -/
theorem cyclotomicJacobiSumTwo_complexConj
    (hp : 2 < p)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
      Fintype.ofFinite _
    cyclotomicIntegerComplexConj p hp (cyclotomicJacobiSumTwo v hpv) =
      jacobiSum (cyclotomicPowerResidueChar v hpv)⁻¹
        (cyclotomicPowerResidueChar v hpv)⁻¹ := by
  letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  rw [cyclotomicJacobiSumTwo]
  change (cyclotomicIntegerComplexConj p hp).toRingHom
    (jacobiSum (cyclotomicPowerResidueChar v hpv)
      (cyclotomicPowerResidueChar v hpv)) = _
  rw [← jacobiSum_ringHomComp,
    cyclotomicPowerResidueChar_ringHomComp_complexConj hp]

private theorem cyclotomicPowerResidueChar_ne_one
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    cyclotomicPowerResidueChar v hpv ≠ 1 := by
  intro htrivial
  have horder := orderOf_cyclotomicPowerResidueChar v hpv
  rw [htrivial, orderOf_one] at horder
  exact (Fact.out : p.Prime).ne_one horder.symm

private theorem cyclotomicPowerResidueChar_mul_self_ne_one
    (hp : 2 < p)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    cyclotomicPowerResidueChar v hpv *
        cyclotomicPowerResidueChar v hpv ≠ 1 := by
  simpa only [pow_two] using
    (pow_ne_one_of_lt_orderOf
      (x := cyclotomicPowerResidueChar v hpv) (n := 2)
      (by norm_num)
      (by simpa only [orderOf_cyclotomicPowerResidueChar] using hp))

/-- The elementary absolute-value identity
`J(χ_v,χ_v) * conj(J(χ_v,χ_v)) = N(v)`. -/
theorem cyclotomicJacobiSumTwo_mul_complexConj
    (hp : 2 < p)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    cyclotomicJacobiSumTwo v hpv *
        cyclotomicIntegerComplexConj p hp (cyclotomicJacobiSumTwo v hpv) =
      (Ideal.absNorm v.asIdeal : CyclotomicIntegerRing p) := by
  letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  let f := algebraMap (CyclotomicIntegerRing p) (PrimeCyclotomicField p)
  let χ := cyclotomicPowerResidueChar v hpv
  let χK := χ.ringHomComp f
  have hf : Function.Injective f :=
    NumberField.RingOfIntegers.coe_injective
  have hχK : χK ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff hf).mpr
      (cyclotomicPowerResidueChar_ne_one v hpv)
  have hχKtwo : χK * χK ≠ 1 := by
    dsimp only [χK]
    rw [← MulChar.ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hf).mpr
      (cyclotomicPowerResidueChar_mul_self_ne_one hp v hpv)
  have hchar : ringChar (PrimeCyclotomicField p) ≠
      ringChar (CyclotomicIntegerRing p ⧸ v.asIdeal) := by
    simpa only [ringChar.eq_zero] using
      (CharP.ringChar_ne_zero_of_finite
        (CyclotomicIntegerRing p ⧸ v.asIdeal)).symm
  have hnorm := jacobiSum_mul_jacobiSum_inv hchar hχK hχK hχKtwo
  apply hf
  rw [map_mul, map_natCast, cyclotomicJacobiSumTwo_complexConj hp,
    cyclotomicJacobiSumTwo,
    ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp]
  simpa only [χ, χK, MulChar.ringHomComp_inv,
    ← Nat.card_eq_fintype_card,
    residueField_card_eq_absNorm] using hnorm

/-- The canonical diagonal cyclotomic Jacobi sum is nonzero. -/
theorem cyclotomicJacobiSumTwo_ne_zero
    (hp : 2 < p)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    cyclotomicJacobiSumTwo v hpv ≠ 0 := by
  intro hzero
  have hnorm := cyclotomicJacobiSumTwo_mul_complexConj hp v hpv
  rw [hzero, zero_mul] at hnorm
  exact (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)) hnorm.symm

/-- The Jacobi sum satisfies the exact two-character Gauss-sum relation. -/
theorem gaussSum_mul_cyclotomicJacobiSumTwo
    (hp : 2 < p)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal)
    (ψ : AddChar (CyclotomicIntegerRing p ⧸ v.asIdeal)
      (CyclotomicIntegerRing p)) :
    letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
      Fintype.ofFinite _
    gaussSum
        (cyclotomicPowerResidueChar v hpv *
          cyclotomicPowerResidueChar v hpv) ψ *
        cyclotomicJacobiSumTwo v hpv =
      gaussSum (cyclotomicPowerResidueChar v hpv) ψ *
        gaussSum (cyclotomicPowerResidueChar v hpv) ψ := by
  letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  exact jacobiSum_mul_nontrivial
    (cyclotomicPowerResidueChar_mul_self_ne_one hp v hpv) ψ

/-- The canonical diagonal cyclotomic Jacobi sum is semiprimary:
`J(χ_v,χ_v) = -1` modulo `(ζ_p - 1)^2`. -/
theorem cyclotomicJacobiSumTwo_semiprimary
    (hp : 2 < p)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    ∃ z ∈ ℤ[(integralCyclotomicZetaUnit p : CyclotomicIntegerRing p)],
      cyclotomicJacobiSumTwo v hpv =
        -1 + z *
          ((integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) - 1) ^ 2 := by
  letI : Fintype (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field (CyclotomicIntegerRing p ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  have hpow : cyclotomicPowerResidueChar v hpv ^ p = 1 := by
    have h := pow_orderOf_eq_one (cyclotomicPowerResidueChar v hpv)
    rwa [orderOf_cyclotomicPowerResidueChar v hpv] at h
  have hdiv : p ∣ Fintype.card (CyclotomicIntegerRing p ⧸ v.asIdeal) - 1 := by
    simpa only [← Nat.card_eq_fintype_card, residueField_card_eq_absNorm] using
      prime_dvd_absNorm_sub_one v hpv
  simpa only [cyclotomicJacobiSumTwo] using
    exists_jacobiSum_eq_neg_one_add hp hpow hpow hdiv
      (IsPrimitiveRoot.coe_units_iff.mpr
        (integralCyclotomicZetaUnit_isPrimitiveRoot (p := p)))

end

end NumberTheory.CyclotomicCharacter.InverseExtension
