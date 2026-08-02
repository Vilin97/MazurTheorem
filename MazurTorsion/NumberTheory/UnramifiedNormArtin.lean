/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicUnramified
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Relative ideal norms and unramified Artin symbols

This module constructs the relative norm on nonzero fractional ideals from
Mathlib's prime-ideal norm and proves that an everywhere-unramified abelian
Artin map kills its image. In the inverse-cyclotomic setting the norm map is
also proved not to be surjective, so norm annihilation cannot replace the
missing principal-ideal reciprocity theorem.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped IsMulCommutative NumberField nonZeroDivisors Pointwise

namespace NumberTheory.UnramifiedArtin

universe u v

section LocalNorm

variable {R : Type u} {S G : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [IsGaloisGroup G R S] [IsDomain R] [IsDomain S]
variable [Module.Finite R S] [Module.Flat R S]

/-- At an unramified prime, the order of an arithmetic Frobenius is the
residue degree. -/
theorem orderOf_eq_inertiaDeg_of_isArithFrobAt
    (p : Ideal R) (Q : Ideal S) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
    [Finite (S ⧸ Q)] [PerfectField p.ResidueField]
    [Algebra.IsUnramifiedAt R Q]
    {sigma : G} (hsigma : IsArithFrobAt R sigma Q) :
    orderOf sigma = Q.inertiaDeg R := by
  have hcard : Nat.card (MulAction.stabilizer G Q) = Q.inertiaDeg R := by
    rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank p Q,
      Ideal.card_inertia_eq_ramificationIdxIn p Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx p Q G,
      Ideal.ramificationIdx_eq_one Q R, one_mul]
  rw [← Nat.card_zpowers,
    stabilizer_eq_zpowers_of_isArithFrobAt p Q hsigma, hcard]

/-- The local Artin symbol raised to the residue degree of any prime above it
is trivial. -/
theorem frobeniusAt_pow_inertiaDeg_eq_one
    {K : Type u} {L : Type v} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : FinitePrime K)
    (hunramified : Algebra.IsUnramifiedIn
      (NumberField.RingOfIntegers L) v.asIdeal)
    (Q : Ideal.primesOver v.asIdeal (NumberField.RingOfIntegers L)) :
    frobeniusAt (K := K) (L := L) v ^
      Q.1.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
  letI : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.1 :=
    hunramified Q.1 inferInstance Q.2.2
  rw [frobeniusAt_eq_arithFrobAt v Q,
    ← orderOf_eq_inertiaDeg_of_isArithFrobAt
      v.asIdeal Q.1 (IsArithFrobAt.arithFrobAt
        (NumberField.RingOfIntegers K) Gal(L/K) Q.1)]
  exact pow_orderOf_eq_one _

end LocalNorm

section FractionalIdealNorm

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- The nonzero base fractional ideal obtained by taking the relative ideal
norm of an upper finite prime. -/
noncomputable def relNormPrimeUnit
    (q : FinitePrime L) :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
  Units.mk0
    ((Ideal.relNorm (NumberField.RingOfIntegers K) q.asIdeal :
      Ideal (NumberField.RingOfIntegers K)) :
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr
      (Ideal.relNorm_eq_bot_iff.not.mpr q.ne_bot))

/-- The relative norm on nonzero fractional ideals, defined from Mathlib's
relative norm on upper prime ideals and the free-abelian factorization of the
fractional-ideal group. -/
noncomputable def fractionalIdealRelNorm :
    (FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)ˣ →*
      (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
  fractionalIdealHom (R := NumberField.RingOfIntegers L) (K := L)
    (relNormPrimeUnit (K := K) (L := L))

omit [IsGalois K L] in
/-- The fractional relative norm has Mathlib's integral relative norm as its
value on every upper prime. -/
@[simp]
theorem fractionalIdealRelNorm_prime (q : FinitePrime L) :
    fractionalIdealRelNorm (K := K) (L := L)
      (primeFractionalIdealUnit (K := L) q) =
      relNormPrimeUnit (K := K) (L := L) q :=
  fractionalIdealHom_prime _ q

omit [IsGalois K L] in
/-- The norm of an upper prime is the lower prime to the residue degree. -/
theorem relNormPrimeUnit_eq_pow (q : FinitePrime L) :
    relNormPrimeUnit (K := K) (L := L) q =
      primeFractionalIdealUnit (K := K)
        (q.under (NumberField.RingOfIntegers K)) ^
          q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  let v : HeightOneSpectrum R := q.under R
  have hqmax : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  letI : q.asIdeal.IsMaximal := hqmax
  have hvmax : v.asIdeal.IsMaximal := Ideal.IsMaximal.under R q.asIdeal
  letI : v.asIdeal.IsMaximal := hvmax
  haveI : q.asIdeal.LiesOver v.asIdeal := by
    change q.asIdeal.LiesOver (q.asIdeal.under R)
    infer_instance
  apply Units.ext
  change ((Ideal.relNorm R q.asIdeal : Ideal R) : FractionalIdeal R⁰ K) =
    ((v.asIdeal : FractionalIdeal R⁰ K) ^
      q.asIdeal.inertiaDeg R)
  simpa only [FractionalIdeal.coeIdeal_pow] using congrArg
    (fun J : Ideal R => (J : FractionalIdeal R⁰ K))
    (Ideal.relNorm_eq_pow_of_isMaximal q.asIdeal v.asIdeal)

/-- In an everywhere-unramified abelian extension, the ideal Artin map kills
the relative norm of every nonzero fractional ideal of the extension. -/
theorem fractionalArtin_fractionalIdealRelNorm_eq_one
    [IsMulCommutative Gal(L/K)]
    (hunramified : ∀ v : FinitePrime K,
      Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) v.asIdeal)
    (I : (FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)ˣ) :
    fractionalArtin (K := K) (L := L)
      (fractionalIdealRelNorm (K := K) (L := L) I) = 1 := by
  have hhom :
      (fractionalArtin (K := K) (L := L)).comp
          (fractionalIdealRelNorm (K := K) (L := L)) = 1 := by
    refine fractionalIdealMonoidHom_ext
      (R := NumberField.RingOfIntegers L) (K := L)
      (f := (fractionalArtin (K := K) (L := L)).comp
        (fractionalIdealRelNorm (K := K) (L := L)))
      (g := 1) ?_
    intro q
    let R := NumberField.RingOfIntegers K
    let S := NumberField.RingOfIntegers L
    let v : FinitePrime K := q.under R
    let Q : Ideal.primesOver v.asIdeal S :=
      ⟨q.asIdeal, q.isPrime, by
        change q.asIdeal.LiesOver (q.asIdeal.under R)
        infer_instance⟩
    change fractionalArtin (K := K) (L := L)
      (fractionalIdealRelNorm (K := K) (L := L)
        (primeFractionalIdealUnit (K := L) q)) = 1
    rw [fractionalIdealRelNorm_prime, relNormPrimeUnit_eq_pow, map_pow,
      show primeFractionalIdealUnit (K := K) v =
        Units.mk0
          (v.asIdeal : FractionalIdeal
            (NumberField.RingOfIntegers K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) by rfl,
      fractionalArtin_prime]
    exact frobeniusAt_pow_inertiaDeg_eq_one v (hunramified v) Q
  exact DFunLike.congr_fun hhom I

end FractionalIdealNorm

end NumberTheory.UnramifiedArtin

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- The inverse-cyclotomic Artin map, in its canonical cyclic coordinate,
kills every relative ideal norm. -/
theorem fractionalArtin_fractionalIdealRelNorm_eq_one
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (I : (FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)ˣ) :
    E.fractionalArtin
      (NumberTheory.UnramifiedArtin.fractionalIdealRelNorm
        (K := PrimeCyclotomicField p) (L := L) I) = 1 := by
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  letI : IsMulCommutative Gal(L/PrimeCyclotomicField p) :=
    IsMulCommutative.of_comm fun sigma tau => by
      apply E.galEquiv.injective
      simp only [map_mul]
      exact mul_comm _ _
  have hhom :
      E.fractionalArtin.comp
          (NumberTheory.UnramifiedArtin.fractionalIdealRelNorm
            (K := PrimeCyclotomicField p) (L := L)) = 1 := by
    refine NumberTheory.UnramifiedArtin.fractionalIdealMonoidHom_ext
      (R := NumberField.RingOfIntegers L) (K := L)
      (f := E.fractionalArtin.comp
        (NumberTheory.UnramifiedArtin.fractionalIdealRelNorm
          (K := PrimeCyclotomicField p) (L := L)))
      (g := 1) ?_
    intro q
    let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
    let S := NumberField.RingOfIntegers L
    let v : FinitePrime (PrimeCyclotomicField p) := q.under R
    let Q : Ideal.primesOver v.asIdeal S :=
      ⟨q.asIdeal, q.isPrime, by
        change q.asIdeal.LiesOver (q.asIdeal.under R)
        infer_instance⟩
    change E.fractionalArtin
      (NumberTheory.UnramifiedArtin.fractionalIdealRelNorm
        (K := PrimeCyclotomicField p) (L := L)
        (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
          (K := L) q)) = 1
    rw [NumberTheory.UnramifiedArtin.fractionalIdealRelNorm_prime,
      NumberTheory.UnramifiedArtin.relNormPrimeUnit_eq_pow, map_pow,
      show NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
          (K := PrimeCyclotomicField p) v =
        Units.mk0
          (v.asIdeal : FractionalIdeal R⁰ (PrimeCyclotomicField p))
          (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) by rfl,
      E.fractionalArtin_prime]
    change (E.galEquiv (E.frobeniusAt v)) ^ q.asIdeal.inertiaDeg R = 1
    rw [← map_pow]
    have hfrob :=
      NumberTheory.UnramifiedArtin.frobeniusAt_pow_inertiaDeg_eq_one
        v (hunramified v) Q
    have hfrobE :
        E.frobeniusAt v ^ q.asIdeal.inertiaDeg R = 1 := by
      change NumberTheory.UnramifiedArtin.frobeniusAt
        (K := PrimeCyclotomicField p) (L := L) v ^
          Q.1.inertiaDeg (NumberField.RingOfIntegers
            (PrimeCyclotomicField p)) = 1
      exact hfrob
    rw [hfrobE, map_one]
  exact DFunLike.congr_fun hhom I

/-- The relative ideal norm cannot be onto in a nontrivial inverse-cyclotomic
extension.  In particular, the direct shortcut from triviality on ideal norms
to triviality on all fractional ideals is unavailable; a separate global
argument about principal ideals is still necessary. -/
theorem not_surjective_fractionalIdealRelNorm
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    ¬ Function.Surjective
      (NumberTheory.UnramifiedArtin.fractionalIdealRelNorm
        (K := PrimeCyclotomicField p) (L := L)) := by
  intro hsurjective
  obtain ⟨v, hv⟩ := E.hasNonSplitFinitePrime hunramified
  have hfrob : E.frobeniusAt v ≠ 1 := fun h =>
    hv (E.ncard_primesOver_eq_finrank_of_frobeniusAt_eq_one
      v (hunramified v) h)
  have hartin : E.artinSymbol v ≠ 1 := by
    intro h
    apply hfrob
    apply E.galEquiv.injective
    simpa only [artinSymbol, map_one] using h
  obtain ⟨I, hI⟩ := hsurjective
    (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
      (K := PrimeCyclotomicField p) v)
  have hnorm := E.fractionalArtin_fractionalIdealRelNorm_eq_one
    hunramified I
  rw [hI] at hnorm
  exact hartin (by
    simpa only [
      NumberTheory.UnramifiedArtin.primeFractionalIdealUnit,
      E.fractionalArtin_prime] using hnorm)

end NumberTheory.CyclotomicCharacter.InverseExtension
