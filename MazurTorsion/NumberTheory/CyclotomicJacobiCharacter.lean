/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import MazurTorsion.NumberTheory.CyclotomicKummerResidueSymbol

/-!
# The cyclotomic power-residue character

This file packages the elementary finite-field power-residue construction as a
`MulChar`, then specializes it to the canonical primitive root in the ring of
integers of the prime cyclotomic field.  It proves the reduction formula, the
exact order of the character, and its covariance under cyclotomic Galois
automorphisms.  The final lemma is the finite-field binomial sum vanishing
needed by the later Jacobi-sum calculation.

The finite-field exponent and `MulChar` bridge are adapted from AINT,
`BernoulliRegular.Reflection.ResidueSymbol.Basic` and
`BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Character`, commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b` (Chris Birkbeck, 2026-07-31),
released under Apache-2.0.  The specialization and its consumers are new to
this project.  No Jacobi ideal factorization or reciprocity theorem is asserted
here.
-/

open scoped BigOperators NumberField

namespace NumberTheory.CyclotomicCharacter.InverseExtension

section FiniteFieldPowerResidue

variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommMonoidWithZero R']
variable {p : ℕ}

/-- The finite-field value `x ^ ((#k - 1) / p)` underlying the `p`-th
power-residue character. -/
def finiteFieldPowerResidueUnit
    (_hdiv : p ∣ Fintype.card k - 1) (x : kˣ) : kˣ :=
  x ^ ((Fintype.card k - 1) / p)

theorem finiteFieldPowerResidueUnit_pow_eq_one
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldPowerResidueUnit hdiv x ^ p = 1 := by
  apply Units.ext
  change ((x : k) ^ ((Fintype.card k - 1) / p)) ^ p = (1 : k)
  rw [← pow_mul, Nat.div_mul_cancel hdiv]
  exact _root_.FiniteField.pow_card_sub_one_eq_one (x : k) x.ne_zero

theorem finiteFieldPowerResidueUnit_mem_zpowers [NeZero p]
    {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    finiteFieldPowerResidueUnit hdiv x ∈ Subgroup.zpowers zeta := by
  rw [hzeta.zpowers_eq, mem_rootsOfUnity]
  exact finiteFieldPowerResidueUnit_pow_eq_one hdiv x

/-- The discrete-log coordinate of the finite-field power-residue value with
respect to a chosen primitive `p`-th root. -/
noncomputable def finiteFieldPowerResidueExponent [NeZero p]
    (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) : ZMod p :=
  hzeta.zmodEquivZPowers.symm
    (Additive.ofMul
      ⟨finiteFieldPowerResidueUnit hdiv x,
        finiteFieldPowerResidueUnit_mem_zpowers hzeta hdiv x⟩)

/-- The exponent coordinate recovers the concrete finite-field power. -/
theorem zeta_pow_finiteFieldPowerResidueExponent_val [NeZero p]
    {zeta : kˣ} (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x : kˣ) :
    zeta ^ (finiteFieldPowerResidueExponent zeta hzeta hdiv x).val =
      finiteFieldPowerResidueUnit hdiv x := by
  have h := hzeta.zmodEquivZPowers.apply_symm_apply
    (Additive.ofMul
      (⟨finiteFieldPowerResidueUnit hdiv x,
          finiteFieldPowerResidueUnit_mem_zpowers hzeta hdiv x⟩ :
        Subgroup.zpowers zeta))
  have happ := congrArg (fun y : Additive (Subgroup.zpowers zeta) ↦
    ((Additive.toMul y : Subgroup.zpowers zeta) : kˣ)) h
  change ((Additive.toMul
      (hzeta.zmodEquivZPowers
        (finiteFieldPowerResidueExponent zeta hzeta hdiv x)) :
      Subgroup.zpowers zeta) : kˣ) =
    finiteFieldPowerResidueUnit hdiv x at happ
  rw [← ZMod.natCast_zmod_val
    (finiteFieldPowerResidueExponent zeta hzeta hdiv x)] at happ
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat] at happ
  exact happ

theorem finiteFieldPowerResidueUnit_mul
    (hdiv : p ∣ Fintype.card k - 1) (x y : kˣ) :
    finiteFieldPowerResidueUnit hdiv (x * y) =
      finiteFieldPowerResidueUnit hdiv x *
        finiteFieldPowerResidueUnit hdiv y := by
  ext
  simp [finiteFieldPowerResidueUnit, mul_pow]

theorem finiteFieldPowerResidueUnit_one
    (hdiv : p ∣ Fintype.card k - 1) :
    finiteFieldPowerResidueUnit hdiv (1 : kˣ) = 1 := by
  ext
  simp [finiteFieldPowerResidueUnit]

theorem finiteFieldPowerResidueExponent_mul [NeZero p]
    (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) (x y : kˣ) :
    finiteFieldPowerResidueExponent zeta hzeta hdiv (x * y) =
      finiteFieldPowerResidueExponent zeta hzeta hdiv x +
        finiteFieldPowerResidueExponent zeta hzeta hdiv y := by
  apply hzeta.zmodEquivZPowers.injective
  rw [map_add]
  simp only [finiteFieldPowerResidueExponent, AddEquiv.apply_symm_apply]
  ext
  exact congrArg (fun u : kˣ ↦ (u : k))
    (finiteFieldPowerResidueUnit_mul hdiv x y)

theorem finiteFieldPowerResidueExponent_one [NeZero p]
    (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta p)
    (hdiv : p ∣ Fintype.card k - 1) :
    finiteFieldPowerResidueExponent zeta hzeta hdiv (1 : kˣ) = 0 := by
  apply hzeta.zmodEquivZPowers.injective
  rw [map_zero]
  simp only [finiteFieldPowerResidueExponent, AddEquiv.apply_symm_apply]
  ext
  simp [finiteFieldPowerResidueUnit_one]

/-- The unit-group homomorphism underlying the power-residue character. -/
noncomputable def finiteFieldPowerResidueUnitHom [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    kˣ →* R'ˣ where
  toFun x := zeta_R ^
    (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val
  map_one' := by
    rw [finiteFieldPowerResidueExponent_one zeta_q hzeta_q hdiv,
      ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rw [finiteFieldPowerResidueExponent_mul zeta_q hzeta_q hdiv,
      ← pow_add, ZMod.val_add]
    have h := pow_mod_orderOf zeta_R
      ((finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val +
        (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv y).val)
    rwa [← hzeta_R.eq_orderOf] at h

/-- The finite-field `p`-th power-residue character with values in any ring
containing a chosen primitive `p`-th root. -/
noncomputable def finiteFieldPowerResidueMulChar [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    MulChar k R' :=
  MulChar.ofUnitHom
    (finiteFieldPowerResidueUnitHom zeta_q hzeta_q hdiv zeta_R hzeta_R)

theorem finiteFieldPowerResidueMulChar_apply_unit [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (x : kˣ) :
    finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
        (x : k) =
      (zeta_R : R') ^
        (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val := by
  rw [finiteFieldPowerResidueMulChar, MulChar.ofUnitHom_coe]
  exact Units.val_pow_eq_pow_val _ _

theorem finiteFieldPowerResidueMulChar_apply_unit_pow_eq_one [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) (x : kˣ) :
    (finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
      (x : k)) ^ p = 1 := by
  rw [finiteFieldPowerResidueMulChar_apply_unit, ← pow_mul, mul_comm,
    pow_mul]
  have hpow : ((zeta_R : R'ˣ) : R') ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hzeta_R.pow_eq_one, Units.val_one]
  rw [hpow, one_pow]

theorem finiteFieldPowerResidueMulChar_pow_eq_one [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R ^ p = 1 := by
  ext x
  rw [MulChar.pow_apply_coe,
    finiteFieldPowerResidueMulChar_apply_unit_pow_eq_one,
    MulChar.one_apply_coe]

private theorem exists_finiteFieldPowerResidueUnit_ne_one
    [Fact p.Prime] (hdiv : p ∣ Fintype.card k - 1) :
    ∃ x : kˣ, finiteFieldPowerResidueUnit hdiv x ≠ 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  refine ⟨g, ?_⟩
  intro heq
  simp only [finiteFieldPowerResidueUnit] at heq
  have horder : orderOf g = Fintype.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, Fintype.card_units]
  have hdvd : orderOf g ∣ (Fintype.card k - 1) / p :=
    orderOf_dvd_of_pow_eq_one heq
  rw [horder] at hdvd
  have hcardpos : 0 < Fintype.card k - 1 := by
    have hcardge : 2 ≤ Fintype.card k := Fintype.one_lt_card
    omega
  have hdivlt : (Fintype.card k - 1) / p < Fintype.card k - 1 :=
    Nat.div_lt_self hcardpos (Fact.out : p.Prime).one_lt
  have hdivpos : 0 < (Fintype.card k - 1) / p :=
    Nat.div_pos (Nat.le_of_dvd hcardpos hdiv) (Fact.out : p.Prime).pos
  have hle : Fintype.card k - 1 ≤ (Fintype.card k - 1) / p :=
    Nat.le_of_dvd hdivpos hdvd
  omega

private theorem finiteFieldPowerResidueMulChar_ne_one
    {R' : Type*} [CommMonoidWithZero R'] [Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_finiteFieldPowerResidueUnit_ne_one hdiv
  intro hchar
  have happ :
      finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R
          (x : k) = 1 := by
    rw [hchar, MulChar.one_apply_coe]
  rw [finiteFieldPowerResidueMulChar_apply_unit] at happ
  have hunits :
      zeta_R ^
          (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using happ
  have hdvd : p ∣
      (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val :=
    hzeta_R.dvd_of_pow_eq_one _ hunits
  have hlt :
      (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val < p :=
    ZMod.val_lt _
  have hzero :
      (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val = 0 := by
    rcases Nat.eq_zero_or_pos
      (finiteFieldPowerResidueExponent zeta_q hzeta_q hdiv x).val with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd h hdvd) (Nat.not_le_of_gt hlt)
  have hrecover :=
    zeta_pow_finiteFieldPowerResidueExponent_val hzeta_q hdiv x
  rw [hzero, pow_zero] at hrecover
  exact hx hrecover.symm

/-- The power-residue character has exact order `p` when `p` is prime. -/
theorem orderOf_finiteFieldPowerResidueMulChar
    {R' : Type*} [CommRing R'] [IsDomain R'] [Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p) :
    orderOf
      (finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) = p :=
  orderOf_eq_prime
    (finiteFieldPowerResidueMulChar_pow_eq_one
      zeta_q hzeta_q hdiv zeta_R hzeta_R)
    (finiteFieldPowerResidueMulChar_ne_one
      zeta_q hzeta_q hdiv zeta_R hzeta_R)

/-- Postcomposition by a map carrying the target primitive root to its `a`-th
power carries the residue character to its `a`-th power. -/
theorem finiteFieldPowerResidueMulChar_ringHomComp_pow_eq
    {R' : Type*} [CommRing R'] [NeZero p]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R') (a : ℕ)
    (hσ : σ (zeta_R : R') = (zeta_R : R') ^ a) :
    (finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R).ringHomComp σ =
      finiteFieldPowerResidueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R ^ a := by
  ext x
  rw [MulChar.ringHomComp_apply, MulChar.pow_apply_coe,
    finiteFieldPowerResidueMulChar_apply_unit, σ.map_pow, hσ,
    ← pow_mul, ← pow_mul, mul_comm]

end FiniteFieldPowerResidue

section CyclotomicSpecialization

variable {p : ℕ} [Fact p.Prime]

local instance : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

private abbrev CyclotomicIntegerRing (p : ℕ) :=
  NumberField.RingOfIntegers (PrimeCyclotomicField p)

/-- The canonical primitive cyclotomic root, regarded as a unit in the ring
of integers. -/
noncomputable def integralCyclotomicZetaUnit (p : ℕ) [Fact p.Prime] :
    (CyclotomicIntegerRing p)ˣ :=
  (((integralRootsOfUnityEquiv p).symm
      (primeCyclotomicZeta_spec p).toRootsOfUnity :
    rootsOfUnity p (CyclotomicIntegerRing p)) :
      (CyclotomicIntegerRing p)ˣ)

theorem integralCyclotomicZetaUnit_isPrimitiveRoot :
    IsPrimitiveRoot (integralCyclotomicZetaUnit p) p := by
  have hzeta : IsPrimitiveRoot
      (primeCyclotomicZeta_spec p).toRootsOfUnity p :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp <|
      IsPrimitiveRoot.coe_units_iff.mp (primeCyclotomicZeta_spec p)
  have hint := hzeta.map_of_injective
    (integralRootsOfUnityEquiv p).symm.injective
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mpr hint

/-- Reduction of the canonical integral cyclotomic root at a finite prime. -/
noncomputable def cyclotomicResidueZeta
    (v : FinitePrime (PrimeCyclotomicField p)) :
    ((CyclotomicIntegerRing p) ⧸ v.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom
    (integralCyclotomicZetaUnit p)

private theorem cyclotomicResidueZeta_eq_rootsOfUnityReductionAt
    (v : FinitePrime (PrimeCyclotomicField p)) :
    cyclotomicResidueZeta v =
      rootsOfUnityReductionAt v
        (primeCyclotomicZeta_spec p).toRootsOfUnity := by
  rfl

theorem cyclotomicResidueZeta_isPrimitiveRoot
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    IsPrimitiveRoot (cyclotomicResidueZeta v) p := by
  have hzeta : IsPrimitiveRoot
      (primeCyclotomicZeta_spec p).toRootsOfUnity p :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp <|
      IsPrimitiveRoot.coe_units_iff.mp (primeCyclotomicZeta_spec p)
  have hred := hzeta.map_of_injective
    (rootsOfUnityReductionAt_injective v hpv)
  rw [← cyclotomicResidueZeta_eq_rootsOfUnityReductionAt] at hred
  exact hred

omit [Fact p.Prime] in
theorem residueField_card_eq_absNorm
    (v : FinitePrime (PrimeCyclotomicField p)) :
    Nat.card ((CyclotomicIntegerRing p) ⧸ v.asIdeal) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem prime_dvd_residueField_card_sub_one
    (v : FinitePrime (PrimeCyclotomicField p))
    [Fintype ((CyclotomicIntegerRing p) ⧸ v.asIdeal)]
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    p ∣ Fintype.card ((CyclotomicIntegerRing p) ⧸ v.asIdeal) - 1 := by
  simpa only [← Nat.card_eq_fintype_card, residueField_card_eq_absNorm] using
    prime_dvd_absNorm_sub_one v hpv

/-- The canonical `p`-th power-residue character at a finite prime away from
`p`, valued in the cyclotomic integer ring. -/
noncomputable def cyclotomicPowerResidueChar
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    MulChar ((CyclotomicIntegerRing p) ⧸ v.asIdeal)
      (CyclotomicIntegerRing p) := by
  letI : Fintype ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  exact finiteFieldPowerResidueMulChar
    (cyclotomicResidueZeta v)
    (cyclotomicResidueZeta_isPrimitiveRoot v hpv)
    (prime_dvd_residueField_card_sub_one v hpv)
    (integralCyclotomicZetaUnit p)
    integralCyclotomicZetaUnit_isPrimitiveRoot

/-- Reduction of the character value recovers
`x ^ ((N v - 1) / p)` in the residue field. -/
theorem quotientMap_cyclotomicPowerResidueChar_apply_unit
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal)
    (x : ((CyclotomicIntegerRing p) ⧸ v.asIdeal)ˣ) :
    Ideal.Quotient.mk v.asIdeal
        (cyclotomicPowerResidueChar v hpv
          (x : (CyclotomicIntegerRing p) ⧸ v.asIdeal)) =
      (x : (CyclotomicIntegerRing p) ⧸ v.asIdeal) ^
        ((Ideal.absNorm v.asIdeal - 1) / p) := by
  letI : Fintype ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  rw [cyclotomicPowerResidueChar,
    finiteFieldPowerResidueMulChar_apply_unit, map_pow]
  change (cyclotomicResidueZeta v :
      (CyclotomicIntegerRing p) ⧸ v.asIdeal) ^
        (finiteFieldPowerResidueExponent
          (cyclotomicResidueZeta v)
          (cyclotomicResidueZeta_isPrimitiveRoot v hpv)
          (prime_dvd_residueField_card_sub_one v hpv) x).val = _
  have hrecover := congrArg Units.val
    (zeta_pow_finiteFieldPowerResidueExponent_val
      (cyclotomicResidueZeta_isPrimitiveRoot v hpv)
      (prime_dvd_residueField_card_sub_one v hpv) x)
  simpa only [finiteFieldPowerResidueUnit, Units.val_pow_eq_pow_val,
    ← Nat.card_eq_fintype_card, residueField_card_eq_absNorm] using hrecover

theorem orderOf_cyclotomicPowerResidueChar
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal) :
    orderOf (cyclotomicPowerResidueChar v hpv) = p := by
  letI : Fintype ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  exact orderOf_finiteFieldPowerResidueMulChar
    (cyclotomicResidueZeta v)
    (cyclotomicResidueZeta_isPrimitiveRoot v hpv)
    (prime_dvd_residueField_card_sub_one v hpv)
    (integralCyclotomicZetaUnit p)
    integralCyclotomicZetaUnit_isPrimitiveRoot

private theorem algebraMap_integralCyclotomicZetaUnit :
    algebraMap (CyclotomicIntegerRing p) (PrimeCyclotomicField p)
        (integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) =
      primeCyclotomicZeta p := by
  simpa only [integralCyclotomicZetaUnit, integralRootsOfUnityEquiv,
    IsPrimitiveRoot.val_toRootsOfUnity_coe] using
    (rootsOfUnityEquivOfPrimitiveRoots_symm_apply
      NumberField.RingOfIntegers.coe_injective
      ⟨(primeCyclotomicZeta_spec p).toInteger,
        (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr
          (primeCyclotomicZeta_spec p).toInteger_isPrimitiveRoot⟩
      (primeCyclotomicZeta_spec p).toRootsOfUnity)

private theorem baseIntegerEquiv_integralCyclotomicZetaUnit
    (σ : Gal(PrimeCyclotomicField p/ℚ)) :
    baseIntegerEquiv σ
        (integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) =
      (integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) ^
        (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val) := by
  apply NumberField.RingOfIntegers.ext
  change σ
      (((integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) :
        PrimeCyclotomicField p)) =
    ((((integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) ^
      (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val)) :
        CyclotomicIntegerRing p) : PrimeCyclotomicField p)
  calc
    σ (((integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) :
        PrimeCyclotomicField p)) =
        σ (primeCyclotomicZeta p) := by
          exact congrArg σ algebraMap_integralCyclotomicZetaUnit
    _ = primeCyclotomicZeta p ^
        (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val) :=
      map_primeCyclotomicZeta σ
    _ = ((((integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) ^
        (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val)) :
          CyclotomicIntegerRing p) : PrimeCyclotomicField p) := by
      change primeCyclotomicZeta p ^
          (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val) =
        algebraMap (CyclotomicIntegerRing p) (PrimeCyclotomicField p)
          ((integralCyclotomicZetaUnit p : CyclotomicIntegerRing p) ^
            (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val))
      rw [map_pow, algebraMap_integralCyclotomicZetaUnit]

/-- Cyclotomic Galois automorphisms postcompose the canonical character by
the corresponding direct-character power. -/
theorem cyclotomicPowerResidueChar_ringHomComp
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : CyclotomicIntegerRing p) ∉ v.asIdeal)
    (σ : Gal(PrimeCyclotomicField p/ℚ)) :
    (cyclotomicPowerResidueChar v hpv).ringHomComp
        (baseIntegerEquiv σ).toRingHom =
      cyclotomicPowerResidueChar v hpv ^
        (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val) := by
  letI : Fintype ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Fintype.ofFinite _
  letI : Field ((CyclotomicIntegerRing p) ⧸ v.asIdeal) :=
    Ideal.Quotient.field v.asIdeal
  exact finiteFieldPowerResidueMulChar_ringHomComp_pow_eq
    (cyclotomicResidueZeta v)
    (cyclotomicResidueZeta_isPrimitiveRoot v hpv)
    (prime_dvd_residueField_card_sub_one v hpv)
    (integralCyclotomicZetaUnit p)
    integralCyclotomicZetaUnit_isPrimitiveRoot
    (baseIntegerEquiv σ).toRingHom
    (((directCharacter p σ : (ZMod p)ˣ) : ZMod p).val)
    (baseIntegerEquiv_integralCyclotomicZetaUnit σ)

end CyclotomicSpecialization

section FiniteFieldBinomialSum

/-- A binomial power sum over a finite field vanishes while every monomial
in its expansion has degree strictly below the size of the unit group. -/
theorem sum_pow_mul_one_sub_pow_eq_zero
    (F : Type*) [Field F] [Fintype F] (d : ℕ)
    (hd : 2 * d < Fintype.card F - 1) :
    ∑ x : F, x ^ d * (1 - x) ^ d = 0 := by
  classical
  calc
    ∑ x : F, x ^ d * (1 - x) ^ d =
        ∑ x : F, ∑ m ∈ Finset.range (d + 1),
          ((-1 : F) ^ (m + d) * (d.choose m : F)) *
            x ^ (d + (d - m)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [sub_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [one_pow, mul_one]
      calc
        x ^ d * ((-1 : F) ^ (m + d) * x ^ (d - m) * (d.choose m : F)) =
            ((-1 : F) ^ (m + d) * (d.choose m : F)) *
              (x ^ d * x ^ (d - m)) := by ring
        _ = ((-1 : F) ^ (m + d) * (d.choose m : F)) *
              x ^ (d + (d - m)) := by rw [pow_add x d (d - m)]
    _ = ∑ m ∈ Finset.range (d + 1),
          ((-1 : F) ^ (m + d) * (d.choose m : F)) *
            ∑ x : F, x ^ (d + (d - m)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [_root_.FiniteField.sum_pow_lt_card_sub_one F _]
      · simp
      · have hmle : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hdegree : d + (d - m) ≤ 2 * d := by omega
        omega

end FiniteFieldBinomialSum

end NumberTheory.CyclotomicCharacter.InverseExtension
