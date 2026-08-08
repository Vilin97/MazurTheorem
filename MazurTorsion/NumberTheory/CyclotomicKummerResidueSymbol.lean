/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.NumberTheory.NumberField.Ideal.Basic
import MazurTorsion.NumberTheory.CyclotomicKummer

/-!
# Prime power-residue coordinates for cyclotomic Kummer extensions

This file defines the prime-level `p`-th power-residue coordinate directly
from reduction modulo a finite prime of the prime cyclotomic field.  It then
compares that coordinate with arithmetic Frobenius on an adjusted integral
Kummer radical.  No global reciprocity law is asserted here.
-/

open scoped NumberField

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]

private lemma absNorm_coprime_prime_of_not_mem
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    (Ideal.absNorm v.asIdeal).Coprime p := by
  rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd]
  intro hp
  let q := Ideal.absNorm (Ideal.under ℤ v.asIdeal)
  letI : v.asIdeal.IsPrime := v.isPrime
  letI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hqprime : q.Prime := by
    exact Nat.absNorm_under_prime v.asIdeal
  have hnorm : q ^ v.asIdeal.inertiaDeg ℤ = Ideal.absNorm v.asIdeal :=
    Ideal.pow_inertiaDeg q v.asIdeal
  have hpq : p ∣ q :=
    (Fact.out : p.Prime).dvd_of_dvd_pow (hnorm.symm ▸ hp)
  have hpq_eq : p = q :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqprime).mp hpq
  apply hpv
  change ((p : ℤ) : NumberField.RingOfIntegers
    (PrimeCyclotomicField p)) ∈ v.asIdeal
  rw [Int.cast_mem_ideal_iff]
  exact_mod_cast (show q ∣ p by simp [hpq_eq])

/-- The \`p\`-th roots of unity in the cyclotomic field are already integral.
This is the canonical equivalence induced by the inclusion of its ring of
integers. -/
noncomputable def integralRootsOfUnityEquiv (p : ℕ) [Fact p.Prime] :
    rootsOfUnity p (NumberField.RingOfIntegers (PrimeCyclotomicField p)) ≃*
      rootsOfUnity p (PrimeCyclotomicField p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact rootsOfUnityEquivOfPrimitiveRoots
    NumberField.RingOfIntegers.coe_injective
    ⟨(primeCyclotomicZeta_spec p).toInteger,
      (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr
        (primeCyclotomicZeta_spec p).toInteger_isPrimitiveRoot⟩

/-- Reduction of cyclotomic \`p\`-th roots of unity at a finite prime. -/
noncomputable def rootsOfUnityReductionAt
    (v : FinitePrime (PrimeCyclotomicField p)) :
    rootsOfUnity p (PrimeCyclotomicField p) →*
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal)ˣ :=
  (Ideal.rootsOfUnityMapQuot v.asIdeal p).comp
    (integralRootsOfUnityEquiv p).symm.toMonoidHom

/-- Away from \`p\`, reduction is injective on the \`p\`-th roots of unity. -/
theorem rootsOfUnityReductionAt_injective
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    Function.Injective (rootsOfUnityReductionAt v) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro ζ ξ hζξ
  apply (integralRootsOfUnityEquiv p).symm.injective
  apply Ideal.rootsOfUnityMapQuot_injective p
    (Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top)
    (absNorm_coprime_prime_of_not_mem v hpv)
  exact hζξ

/-- The residue-field cardinality minus one is divisible by \`p\` at every
finite prime away from \`p\`. -/
theorem prime_dvd_absNorm_sub_one
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    p ∣ Ideal.absNorm v.asIdeal - 1 := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI := Ideal.Quotient.field v.asIdeal
  have hdiv := Subgroup.card_dvd_of_injective
    (Ideal.rootsOfUnityMapQuot v.asIdeal p)
    (Ideal.rootsOfUnityMapQuot_injective p
      (Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top)
      (absNorm_coprime_prime_of_not_mem v hpv))
  rw [(primeCyclotomicZeta_spec p).toInteger_isPrimitiveRoot.card_rootsOfUnity,
    Nat.card_units] at hdiv
  exact hdiv

/-- The nonzero residue class of an integral element at a prime which does
not divide it. -/
noncomputable def residueUnitAt
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal) :
    ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
      v.asIdeal)ˣ := by
  letI := Ideal.Quotient.field v.asIdeal
  exact Units.mk0 (Ideal.Quotient.mk v.asIdeal η)
    (Ideal.Quotient.eq_zero_iff_mem.not.mpr hηv)

omit [Fact p.Prime] in
private theorem residueUnitAt_pow_absNorm_sub_one
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal) :
    residueUnitAt v η hηv ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  letI := Ideal.Quotient.field v.asIdeal
  change residueUnitAt v η hηv ^
    (Nat.card
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal) - 1) = 1
  rw [← Nat.card_units]
  exact pow_card_eq_one' (x := residueUnitAt v η hηv)

/-- The finite-field \`p\`-th power-residue root of a nonzero integral
element.  Its underlying residue unit is
\`η ^ ((N v - 1) / p)\`. -/
noncomputable def residuePowerRootAt
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    rootsOfUnity p
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨residueUnitAt v η hηv ^
    ((Ideal.absNorm v.asIdeal - 1) / p), ?_⟩
  change (residueUnitAt v η hηv ^
    ((Ideal.absNorm v.asIdeal - 1) / p)) ^ p = 1
  rw [← pow_mul, Nat.div_mul_cancel (prime_dvd_absNorm_sub_one v hpv)]
  exact residueUnitAt_pow_absNorm_sub_one v η hηv

@[simp]
theorem residuePowerRootAt_coe
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    (residuePowerRootAt v η hηv hpv :
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal)ˣ) =
      residueUnitAt v η hηv ^
        ((Ideal.absNorm v.asIdeal - 1) / p) :=
  by
    simp only [residuePowerRootAt]

private theorem reduced_cyclotomicZeta_isPrimitiveRoot
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    IsPrimitiveRoot
      (Ideal.Quotient.mk v.asIdeal
        (primeCyclotomicZeta_spec p).toInteger) p := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact (primeCyclotomicZeta_spec p).toInteger_isPrimitiveRoot.idealQuotient_mk
    (Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top)
    (absNorm_coprime_prime_of_not_mem v hpv)

private theorem exists_rootsOfUnityReductionAt_eq_residuePowerRootAt
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    ∃ ζ : rootsOfUnity p (PrimeCyclotomicField p),
      rootsOfUnityReductionAt v ζ =
        (residuePowerRootAt v η hηv hpv :
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
            v.asIdeal)ˣ) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI := Ideal.Quotient.field v.asIdeal
  let ξ := residuePowerRootAt v η hηv hpv
  have hξ :
      (((ξ :
        ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
          v.asIdeal)ˣ) :
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
          v.asIdeal) ^ p) = 1 := by
    have hξunit := ξ.property
    change (ξ :
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal)ˣ) ^ p = 1 at hξunit
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val hξunit
  obtain ⟨i, hi, hpow⟩ :=
    (reduced_cyclotomicZeta_isPrimitiveRoot v hpv).eq_pow_of_pow_eq_one hξ
  let ζint :
      rootsOfUnity p
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)) :=
    (primeCyclotomicZeta_spec p).toInteger_isPrimitiveRoot.toRootsOfUnity
  refine ⟨integralRootsOfUnityEquiv p (ζint ^ i), ?_⟩
  rw [rootsOfUnityReductionAt, MonoidHom.comp_apply]
  change (Ideal.rootsOfUnityMapQuot v.asIdeal p)
      ((integralRootsOfUnityEquiv p).symm
        ((integralRootsOfUnityEquiv p) (ζint ^ i))) = _
  rw [MulEquiv.symm_apply_apply]
  apply Units.ext
  change Ideal.Quotient.mk v.asIdeal
      ((ζint ^ i :
        rootsOfUnity p
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) =
    (ξ :
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal)ˣ)
  simpa [ζint, IsPrimitiveRoot.toRootsOfUnity, map_pow,
    SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val] using hpow

/-- The roots-of-unity-valued prime \`p\`-th power-residue symbol.  It is
characterized without choosing a discrete logarithm: its reduction is the
finite-field root \`η ^ ((N v - 1) / p)\`. -/
noncomputable def pthPowerResidueSymbolAtPrime
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    rootsOfUnity p (PrimeCyclotomicField p) :=
  Classical.choose
    (exists_rootsOfUnityReductionAt_eq_residuePowerRootAt v η hηv hpv)

/-- Defining reduction formula for the prime power-residue symbol. -/
theorem rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    rootsOfUnityReductionAt v
        (pthPowerResidueSymbolAtPrime v η hηv hpv) =
      (residuePowerRootAt v η hηv hpv :
        ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
          v.asIdeal)ˣ) :=
  Classical.choose_spec
    (exists_rootsOfUnityReductionAt_eq_residuePowerRootAt v η hηv hpv)

section FrobeniusComparison

variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

private noncomputable def KummerPresentation.adjustedRadical
    (E : InverseExtension p L) (P : KummerPresentation E)
    (c : (PrimeCyclotomicField p)ˣ) : L :=
  P.radical * algebraMap (PrimeCyclotomicField p) L (c : PrimeCyclotomicField p)

private theorem KummerPresentation.adjustedRadical_pow
    (E : InverseExtension p L) (P : KummerPresentation E)
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η =
        P.radicand * (c : PrimeCyclotomicField p) ^ p) :
    P.adjustedRadical E c ^ p =
      algebraMap
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)) L η := by
  rw [KummerPresentation.adjustedRadical, mul_pow, P.pow_radical,
    ← map_pow, ← map_mul, ← hη]
  exact IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (PrimeCyclotomicField p) L η

private theorem KummerPresentation.adjustedRadical_isIntegral
    (E : InverseExtension p L) (P : KummerPresentation E)
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η =
        P.radicand * (c : PrimeCyclotomicField p) ^ p) :
    IsIntegral ℤ (P.adjustedRadical E c) := by
  apply IsIntegral.of_pow (Fact.out : p.Prime).pos
  rw [P.adjustedRadical_pow E η c hη]
  have h := (NumberField.RingOfIntegers.isIntegral_coe η).map
    (IsScalarTower.toAlgHom ℚ (PrimeCyclotomicField p) L)
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (PrimeCyclotomicField p) L]
  exact h

private theorem KummerPresentation.frobeniusAt_adjustedRadical
    (E : InverseExtension p L) (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ) :
    E.frobeniusAt v (P.adjustedRadical E c) =
      algebraMap (PrimeCyclotomicField p) L
          ((((P.pairing E (E.frobeniusAt v) :
              rootsOfUnity p (PrimeCyclotomicField p)) :
            (PrimeCyclotomicField p)ˣ) :
            PrimeCyclotomicField p)) *
        P.adjustedRadical E c := by
  have hpairing :=
    P.pairing_smul_radical E (E.frobeniusAt v)
  simp only [Subgroup.smul_def, Units.smul_def, Algebra.smul_def] at hpairing
  rw [KummerPresentation.adjustedRadical, map_mul, ← hpairing]
  rw [(E.frobeniusAt v).commutes]
  exact mul_assoc _ _ _

private noncomputable def integralRootOfUnity
    (ζ : rootsOfUnity p (PrimeCyclotomicField p)) :
    NumberField.RingOfIntegers (PrimeCyclotomicField p) :=
  ((((integralRootsOfUnityEquiv p).symm ζ :
      rootsOfUnity p
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
    (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
    NumberField.RingOfIntegers (PrimeCyclotomicField p))

private theorem algebraMap_integralRootOfUnity
    (ζ : rootsOfUnity p (PrimeCyclotomicField p)) :
    algebraMap (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) (integralRootOfUnity ζ) =
      ((ζ : (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := rootsOfUnityEquivOfPrimitiveRoots_symm_apply
    NumberField.RingOfIntegers.coe_injective
    (show
      (primitiveRoots p
        (NumberField.RingOfIntegers
          (PrimeCyclotomicField p))).Nonempty from
      ⟨(primeCyclotomicZeta_spec p).toInteger,
        (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr
          (primeCyclotomicZeta_spec p).toInteger_isPrimitiveRoot⟩)
    ζ
  simpa only [integralRootOfUnity, integralRootsOfUnityEquiv] using h

private noncomputable def KummerPresentation.adjustedRadicalInteger
    (E : InverseExtension p L) (P : KummerPresentation E)
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η =
        P.radicand * (c : PrimeCyclotomicField p) ^ p) :
    NumberField.RingOfIntegers L :=
  ⟨P.adjustedRadical E c, P.adjustedRadical_isIntegral E η c hη⟩

private theorem KummerPresentation.frobeniusAt_adjustedRadicalInteger
    (E : InverseExtension p L) (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η =
        P.radicand * (c : PrimeCyclotomicField p) ^ p) :
    E.frobeniusAt v • P.adjustedRadicalInteger E η c hη =
      algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (NumberField.RingOfIntegers L)
          (integralRootOfUnity (P.pairing E (E.frobeniusAt v))) *
        P.adjustedRadicalInteger E η c hη := by
  apply NumberField.RingOfIntegers.coe_injective
  change E.frobeniusAt v (P.adjustedRadical E c) =
    algebraMap (PrimeCyclotomicField p) L
        (algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p)
          (integralRootOfUnity (P.pairing E (E.frobeniusAt v)))) *
      P.adjustedRadical E c
  rw [P.frobeniusAt_adjustedRadical E v c,
    algebraMap_integralRootOfUnity]

/-- Arithmetic Frobenius in a Kummer presentation is the prime power-residue
symbol of any integral representative of the radicand modulo a \`p\`-th power.
The prime is required to divide neither that representative nor \`p\`. -/
theorem KummerPresentation.pairing_frobeniusAt_eq_pthPowerResidueSymbolAtPrime
    (E : InverseExtension p L) (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p))
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η =
        P.radicand * (c : PrimeCyclotomicField p) ^ p)
    (hηv : η ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    P.pairing E (E.frobeniusAt v) =
      pthPowerResidueSymbolAtPrime v η hηv hpv := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  let Q := (E.primeAbove v).1
  letI : Q.IsPrime := (E.primeAbove v).2.1
  letI : Q.LiesOver v.asIdeal := (E.primeAbove v).2.2
  have hQne : Q ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver v.ne_bot (E.primeAbove v).2
  letI : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQne
  letI := Ideal.Quotient.field Q
  letI := Ideal.Quotient.field v.asIdeal
  let ρ := P.pairing E (E.frobeniusAt v)
  let β := P.adjustedRadicalInteger E η c hη
  let ρint := integralRootOfUnity ρ
  have hβpow :
      β ^ p =
        algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (NumberField.RingOfIntegers L) η := by
    apply NumberField.RingOfIntegers.coe_injective
    exact P.adjustedRadical_pow E η c hη
  have hfrob :=
    (E.frobeniusAt_isArithFrobAt v).mk_apply β
  have hunder :
      Q.under
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)) =
        v.asIdeal :=
    (Ideal.over_def (p := v.asIdeal) (P := Q)).symm
  rw [hunder] at hfrob
  change Ideal.Quotient.mk Q (E.frobeniusAt v • β) =
    (Ideal.Quotient.mk Q β) ^
      Nat.card
        ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
          v.asIdeal) at hfrob
  have hfrobInt :
      E.frobeniusAt v • β =
        algebraMap
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (NumberField.RingOfIntegers L) ρint * β := by
    exact P.frobeniusAt_adjustedRadicalInteger E v η c hη
  rw [hfrobInt, map_mul] at hfrob
  have hβbarpow :
      (Ideal.Quotient.mk Q β) ^ p =
        algebraMap
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
            v.asIdeal)
          ((NumberField.RingOfIntegers L) ⧸ Q)
          (Ideal.Quotient.mk v.asIdeal η) := by
    rw [← map_pow, hβpow,
      Ideal.Quotient.algebraMap_mk_of_liesOver]
  have hβbar :
      Ideal.Quotient.mk Q β ≠ 0 := by
    intro hzero
    have hηzero :
        algebraMap
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
            v.asIdeal)
          ((NumberField.RingOfIntegers L) ⧸ Q)
          (Ideal.Quotient.mk v.asIdeal η) = 0 := by
      rw [← hβbarpow, hzero, zero_pow (Fact.out : p.Prime).ne_zero]
    have hηzero' : Ideal.Quotient.mk v.asIdeal η = 0 := by
      exact (FaithfulSMul.algebraMap_injective
        ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
          v.asIdeal)
        ((NumberField.RingOfIntegers L) ⧸ Q)) (by simpa using hηzero)
    exact hηv (Ideal.Quotient.eq_zero_iff_mem.mp hηzero')
  let e := (Ideal.absNorm v.asIdeal - 1) / p
  have hnormpos : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hnorm :
      Ideal.absNorm v.asIdeal = 1 + p * e := by
    calc
      Ideal.absNorm v.asIdeal =
          (Ideal.absNorm v.asIdeal - 1) + 1 :=
        (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnormpos.ne')).symm
      _ = ((Ideal.absNorm v.asIdeal - 1) / p) * p + 1 := by
        rw [Nat.div_mul_cancel (prime_dvd_absNorm_sub_one v hpv)]
      _ = 1 + p * e := by
        simp only [e, Nat.add_comm, Nat.mul_comm]
  have hfrob' :
      algebraMap
            ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
              v.asIdeal)
            ((NumberField.RingOfIntegers L) ⧸ Q)
            (Ideal.Quotient.mk v.asIdeal ρint) *
          Ideal.Quotient.mk Q β =
        Ideal.Quotient.mk Q β ^
          Ideal.absNorm v.asIdeal := by
    simpa only [Ideal.Quotient.algebraMap_mk_of_liesOver,
      Ideal.absNorm_apply, Submodule.cardQuot_apply] using hfrob
  rw [hnorm, pow_add, pow_one, pow_mul, hβbarpow] at hfrob'
  have hρup :
      algebraMap
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
            v.asIdeal)
          ((NumberField.RingOfIntegers L) ⧸ Q)
          (Ideal.Quotient.mk v.asIdeal ρint) =
        (algebraMap
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
            v.asIdeal)
          ((NumberField.RingOfIntegers L) ⧸ Q)
          (Ideal.Quotient.mk v.asIdeal η)) ^ e := by
    apply mul_right_cancel₀ hβbar
    simpa only [map_pow] using
      (hfrob'.trans (mul_comm _ _))
  have hρ :
      Ideal.Quotient.mk v.asIdeal ρint =
        (Ideal.Quotient.mk v.asIdeal η) ^ e := by
    apply FaithfulSMul.algebraMap_injective
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal)
      ((NumberField.RingOfIntegers L) ⧸ Q)
    simpa only [map_pow] using hρup
  apply rootsOfUnityReductionAt_injective v hpv
  rw [rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime]
  apply Units.ext
  rw [rootsOfUnityReductionAt, MonoidHom.comp_apply]
  change Ideal.Quotient.mk v.asIdeal ρint =
    ((residuePowerRootAt v η hηv hpv :
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal)ˣ) :
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal)
  rw [residuePowerRootAt_coe, Units.val_pow_eq_pow_val]
  change Ideal.Quotient.mk v.asIdeal ρint =
    (Ideal.Quotient.mk v.asIdeal η) ^ e
  exact hρ

end FrobeniusComparison

end NumberTheory.CyclotomicCharacter.InverseExtension
