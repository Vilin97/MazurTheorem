/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import MazurTorsion.NumberTheory.CyclotomicUnramified

/-!
# Kummer classes of inverse-cyclotomic extensions

This file extracts a Kummer presentation of an inverse-cyclotomic extension
and proves its finite-place consequence.  When the extension is everywhere
unramified, every valuation of the Kummer radicand is divisible by `p`.
Consequently the radicand gives a nontrivial element of the empty-support
`p`-Selmer group of the cyclotomic field.

The resulting Selmer class is not identified here with an inverse-character
class-group quotient.  That passage is the global reciprocity/reflection step,
and keeping it separate avoids silently replacing class field theory by a
different eigenspace assertion.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

omit [Fact p.Prime] in
/-- The exponent of a principal fractional ideal is the negative logarithm
of the corresponding normalized finite-place valuation.  This reconciles the
factorization and valuation APIs used by the Kummer local condition. -/
theorem count_spanSingleton_eq_neg_valuationLog
    (a : PrimeCyclotomicField p) (ha : a ≠ 0)
    (v : FinitePrime (PrimeCyclotomicField p)) :
    FractionalIdeal.count (PrimeCyclotomicField p) v
      (FractionalIdeal.spanSingleton
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))) a) =
      -WithZero.log (v.valuation (PrimeCyclotomicField p) a) := by
  let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
  let x : (PrimeCyclotomicField p)ˣ := Units.mk0 a ha
  let s := IsLocalization.sec R⁰ (x : PrimeCyclotomicField p)
  have hs : IsLocalization.mk' (PrimeCyclotomicField p) s.1 s.2 = x :=
    IsLocalization.mk'_sec (PrimeCyclotomicField p) x
  have hI : FractionalIdeal.spanSingleton R⁰ (x : PrimeCyclotomicField p) =
      FractionalIdeal.spanSingleton R⁰
          ((algebraMap R (PrimeCyclotomicField p)) (s.2 : R))⁻¹ *
        (Ideal.span {s.1} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg
    rw [← hs, IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hcount := FractionalIdeal.count_well_defined
    (PrimeCyclotomicField p) v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) hI
  have hval := congrArg WithZero.log
    (IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun_eq v x)
  dsimp only [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun,
    x, s, R] at hval hcount ⊢
  simp only [Units.val_mk0] at hval hcount ⊢
  change
    (-((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {(IsLocalization.sec
              (nonZeroDivisors
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))) a).1})).factors : ℤ) -
      -((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {((IsLocalization.sec
              (nonZeroDivisors
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))) a).2 :
                  NumberField.RingOfIntegers (PrimeCyclotomicField p))})).factors : ℤ)) =
        WithZero.log (v.valuation (PrimeCyclotomicField p) a) at hval
  rw [hcount]
  omega

/-- The relative degree of an inverse extension is the prime `p`. -/
theorem finrank_eq_prime (E : InverseExtension p L) :
    Module.finrank (PrimeCyclotomicField p) L = p := by
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  calc
    Module.finrank (PrimeCyclotomicField p) L =
        Nat.card Gal(L/PrimeCyclotomicField p) :=
      (IsGalois.card_aut_eq_finrank (PrimeCyclotomicField p) L).symm
    _ = Nat.card (Multiplicative (ZMod p)) :=
      Nat.card_congr E.galEquiv.toEquiv
    _ = p := by simp

/-- The prime cyclotomic field contains a primitive `p`-th root of unity. -/
theorem primitiveRoots_nonempty (p : ℕ) [Fact p.Prime] :
    (primitiveRoots p (PrimeCyclotomicField p)).Nonempty := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact ⟨IsCyclotomicExtension.zeta p ℚ (PrimeCyclotomicField p),
    (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr
      (IsCyclotomicExtension.zeta_spec p ℚ (PrimeCyclotomicField p))⟩

/-- A simple Kummer presentation `L = K(α)` with `α ^ p = a`. -/
structure KummerPresentation (E : InverseExtension p L) where
  /-- A Kummer generator of the extension. -/
  radical : L
  /-- The base-field radicand. -/
  radicand : PrimeCyclotomicField p
  /-- The defining Kummer equation. -/
  pow_radical : radical ^ p = algebraMap (PrimeCyclotomicField p) L radicand
  /-- The radical generates the whole extension. -/
  adjoin_radical :
    IntermediateField.adjoin (PrimeCyclotomicField p) {radical} = ⊤

/-- Every inverse extension has a Kummer presentation over the cyclotomic
base. -/
noncomputable def kummerPresentation (E : InverseExtension p L) :
    KummerPresentation E := by
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  letI : IsCyclic Gal(L/PrimeCyclotomicField p) :=
    isCyclic_of_surjective E.galEquiv.symm E.galEquiv.symm.surjective
  have hroots :
      (primitiveRoots (Module.finrank (PrimeCyclotomicField p) L)
        (PrimeCyclotomicField p)).Nonempty := by
    rw [E.finrank_eq_prime]
    exact primitiveRoots_nonempty p
  let hex := exists_root_adjoin_eq_top_of_isCyclic
    (PrimeCyclotomicField p) L hroots
  let alpha := Classical.choose hex
  have halpha := Classical.choose_spec hex
  let a := Classical.choose halpha.1
  have ha := Classical.choose_spec halpha.1
  refine ⟨alpha, a, ?_, halpha.2⟩
  calc
    alpha ^ p = alpha ^ Module.finrank (PrimeCyclotomicField p) L :=
      congrArg (fun n => alpha ^ n) E.finrank_eq_prime.symm
    _ = algebraMap (PrimeCyclotomicField p) L a := ha.symm

/-- The Kummer polynomial attached to a presentation is irreducible. -/
theorem KummerPresentation.irreducible (E : InverseExtension p L)
    (P : KummerPresentation E) :
    Irreducible (Polynomial.X ^ p - Polynomial.C P.radicand) := by
  have hpow : P.radical ^ Module.finrank (PrimeCyclotomicField p) L =
      algebraMap (PrimeCyclotomicField p) L P.radicand := by
    rw [E.finrank_eq_prime]
    exact P.pow_radical
  have h := irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    hpow P.adjoin_radical
  simpa only [E.finrank_eq_prime] using h

/-- A Kummer presentation of a nontrivial prime-degree extension has a
nonzero radicand. -/
theorem KummerPresentation.radicand_ne_zero (E : InverseExtension p L)
    (P : KummerPresentation E) : P.radicand ≠ 0 :=
  ne_zero_of_irreducible_X_pow_sub_C'
    ((Fact.out : p.Prime).ne_one : p ≠ 1) (P.irreducible E)

/-- Regard the selected prime above `v` as a finite prime of the extension. -/
noncomputable def finitePrimeAbove (E : InverseExtension p L)
    (v : FinitePrime (PrimeCyclotomicField p)) : FinitePrime L := by
  let Q := E.primeAbove v
  exact ⟨Q.1, inferInstance,
    Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.2⟩

section FiniteCompletionMap

universe w

variable {K : Type u} [Field K] [NumberField K]
variable {F : Type w} [Field F] [NumberField F] [Algebra K F]
variable (vK : FinitePrime K) (wF : FinitePrime F)
variable [wF.asIdeal.LiesOver vK.asIdeal]

/-- The canonical map between finite completions at primes lying over one
another.  Mathlib supplies uniform continuity of the global field embedding;
the universal property of completion then supplies this map. -/
noncomputable def finiteCompletionMap :
    vK.adicCompletion K →+* wF.adicCompletion F :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv F wF).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (vK.valuation K))
        (WithVal (wF.valuation F)))
      (vK.uniformContinuous_algebraMap_liesOver K F wF).continuous).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K vK).toRingHom)

/-- The finite-completion map extends the original global field embedding. -/
theorem finiteCompletionMap_algebraMap (x : K) :
    finiteCompletionMap vK wF
        (algebraMap K (vK.adicCompletion K) x) =
      algebraMap F (wF.adicCompletion F) (algebraMap K F x) := by
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  change ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv F wF).symm
      ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (vK.valuation K))
          (WithVal (wF.valuation F)))
        (vK.uniformContinuous_algebraMap_liesOver K F wF).continuous)
        ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K vK)
          (algebraMap K (vK.adicCompletion K) x)))).toCompletion = _
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion]
  rw [show (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K vK)
      (algebraMap K (vK.adicCompletion K) x) =
        (WithVal.toVal (vK.valuation K) x :
          (vK.valuation K).Completion) by rfl]
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

end FiniteCompletionMap

/-- Surjectivity of the canonical local completion map makes the Kummer
radicand a `p`-th power in the base completion. -/
theorem KummerPresentation.radicand_isPow_in_completion_of_surjective
    (E : InverseExtension p L) (P : KummerPresentation E)
    (vK : FinitePrime (PrimeCyclotomicField p))
    (wL : FinitePrime L) [wL.asIdeal.LiesOver vK.asIdeal]
    (hsurjective : Function.Surjective (finiteCompletionMap vK wL)) :
    ∃ x : vK.adicCompletion (PrimeCyclotomicField p),
      x ^ p = algebraMap (PrimeCyclotomicField p)
        (vK.adicCompletion (PrimeCyclotomicField p)) P.radicand := by
  obtain ⟨x, hx⟩ := hsurjective
    (algebraMap L (wL.adicCompletion L) P.radical)
  refine ⟨x, ?_⟩
  apply (finiteCompletionMap vK wL).injective
  rw [map_pow, hx, finiteCompletionMap_algebraMap]
  rw [← map_pow, P.pow_radical]

/-- Complete splitting already forces both ideal-theoretic local invariants
to be one.  The remaining gap is specifically the comparison with finite
completions, not ramification or residue-degree arithmetic. -/
theorem cyclotomicPrime_ramificationIdxIn_inertiaDegIn_eq_one_of_split
    (E : InverseExtension p L)
    (hsplit :
      (Ideal.primesOver (cyclotomicPrime p).asIdeal
        (NumberField.RingOfIntegers L)).ncard =
          Module.finrank (PrimeCyclotomicField p) L) :
    (cyclotomicPrime p).asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers L) = 1 ∧
      (cyclotomicPrime p).asIdeal.inertiaDegIn
          (NumberField.RingOfIntegers L) = 1 := by
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (cyclotomicPrime p).asIdeal
      (NumberField.RingOfIntegers L)
      Gal(L/PrimeCyclotomicField p)
  have hcard : Nat.card Gal(L/PrimeCyclotomicField p) =
      Module.finrank (PrimeCyclotomicField p) L :=
    IsGalois.card_aut_eq_finrank (PrimeCyclotomicField p) L
  rw [hcard, hsplit] at hfund
  have hdegree : 0 < Module.finrank (PrimeCyclotomicField p) L := by
    rw [E.finrank_eq_prime]
    exact (Fact.out : p.Prime).pos
  have hprod :
      (cyclotomicPrime p).asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers L) *
        (cyclotomicPrime p).asIdeal.inertiaDegIn
          (NumberField.RingOfIntegers L) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hdegree
    simpa using hfund
  exact mul_eq_one.mp hprod

/-- The exact local-completion assertion needed after complete splitting at
the unique prime above `p`. -/
noncomputable def CyclotomicPrimeCompletionSurjective
    (E : InverseExtension p L) : Prop := by
  let vK := cyclotomicPrime p
  let wL := E.finitePrimeAbove vK
  letI : wL.asIdeal.LiesOver vK.asIdeal := by
    exact (E.primeAbove vK).2.2
  exact Function.Surjective (finiteCompletionMap vK wL)

/-- Precise missing local-degree principle: complete splitting at the
cyclotomic prime forces the corresponding map of finite completions to be
onto. -/
noncomputable def SplitCyclotomicPrimeCompletionPrinciple
    (E : InverseExtension p L) : Prop :=
  (Ideal.primesOver (cyclotomicPrime p).asIdeal
      (NumberField.RingOfIntegers L)).ncard =
      Module.finrank (PrimeCyclotomicField p) L →
    E.CyclotomicPrimeCompletionSurjective

/-- Once the missing completion-surjectivity bridge is supplied, complete
splitting turns the canonical Kummer radicand into a `p`-th power in the
cyclotomic-prime completion. -/
theorem cyclotomicPrime_radicand_isPow_of_completionPrinciple
    (hp : 2 < p) (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (hcompletion : E.SplitCyclotomicPrimeCompletionPrinciple) :
    ∃ x : (cyclotomicPrime p).adicCompletion
        (PrimeCyclotomicField p),
      x ^ p = algebraMap (PrimeCyclotomicField p)
        ((cyclotomicPrime p).adicCompletion
          (PrimeCyclotomicField p))
        E.kummerPresentation.radicand := by
  let vK := cyclotomicPrime p
  let wL := E.finitePrimeAbove vK
  letI : wL.asIdeal.LiesOver vK.asIdeal := by
    exact (E.primeAbove vK).2.2
  have hsplit := E.cyclotomicPrime_splitsCompletely hp hunramified
  have hsurjective : Function.Surjective (finiteCompletionMap vK wL) := by
    have h := hcompletion hsplit
    change Function.Surjective (finiteCompletionMap vK wL) at h
    exact h
  simpa only [vK] using
    E.kummerPresentation.radicand_isPow_in_completion_of_surjective
      E vK wL hsurjective

/-- At every unramified finite prime, the valuation of a Kummer radicand is
a `p`-th power in the multiplicative value group. -/
theorem valuation_radicand_isPow (E : InverseExtension p L)
    (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hunramified : E.IsUnramifiedAtFinitePlace v) :
    ∃ gamma : WithZero (Multiplicative ℤ),
      v.valuation (PrimeCyclotomicField p) P.radicand = gamma ^ p := by
  let w := E.finitePrimeAbove v
  have hover : w.asIdeal.LiesOver v.asIdeal := by
    exact (E.primeAbove v).2.2
  letI : w.asIdeal.LiesOver v.asIdeal := hover
  have hram : Ideal.ramificationIdx w.asIdeal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)) = 1 :=
    (E.isUnramifiedAtFinitePlace_iff_ramificationIdx_eq_one v).mp
      hunramified w.asIdeal hover
  have hram' : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
    exact hram
  refine ⟨w.valuation L P.radical, ?_⟩
  have hval := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
    L v w P.radicand
  rw [hram', pow_one, ← P.pow_radical] at hval
  simpa using hval

/-- Additively, every finite-prime exponent of an unramified Kummer
radicand is a multiple of `p`. -/
theorem valuationLog_radicand_eq_prime_mul (E : InverseExtension p L)
    (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hunramified : E.IsUnramifiedAtFinitePlace v) :
    ∃ n : ℤ, WithZero.log
        (v.valuation (PrimeCyclotomicField p) P.radicand) = (p : ℤ) * n := by
  obtain ⟨gamma, hgamma⟩ := E.valuation_radicand_isPow P v hunramified
  refine ⟨WithZero.log gamma, ?_⟩
  rw [hgamma, WithZero.log_pow, nsmul_eq_mul]

/-- Divisibility form of `valuationLog_radicand_eq_prime_mul`. -/
theorem prime_dvd_valuationLog_radicand (E : InverseExtension p L)
    (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hunramified : E.IsUnramifiedAtFinitePlace v) :
    (p : ℤ) ∣ WithZero.log
      (v.valuation (PrimeCyclotomicField p) P.radicand) :=
  E.valuationLog_radicand_eq_prime_mul P v hunramified

/-- Equivalently, the Kummer radicand satisfies the empty-support Selmer
local condition at every finite prime. -/
theorem valuationOfNeZeroMod_radicand_eq_one (E : InverseExtension p L)
    (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hunramified : E.IsUnramifiedAtFinitePlace v) :
    v.valuationOfNeZeroMod p
        (QuotientGroup.mk (Units.mk0 P.radicand (P.radicand_ne_zero E))) = 1 := by
  obtain ⟨gamma, hgamma⟩ := E.valuation_radicand_isPow P v hunramified
  have hgamma_ne : gamma ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Fact.out : p.Prime).ne_zero] at hgamma
    exact (Valuation.ne_zero_iff _).2 (P.radicand_ne_zero E) hgamma
  lift gamma to Multiplicative ℤ using hgamma_ne with delta
  have hvalue :
      v.valuationOfNeZero (Units.mk0 P.radicand (P.radicand_ne_zero E)) = delta ^ p := by
    rw [← WithZero.coe_inj,
      IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
    exact hgamma
  erw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod,
    MonoidHom.comp_apply, ← QuotientGroup.coe_mk', QuotientGroup.map_mk']
  rw [hvalue, QuotientGroup.mk_pow]
  erw [map_pow]
  apply Multiplicative.toAdd.injective
  simp

/-- An everywhere-unramified Kummer radicand defines an element of the
empty-support `p`-Selmer group of the cyclotomic field. -/
theorem radicand_mem_selmerGroup (E : InverseExtension p L)
    (P : KummerPresentation E)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    QuotientGroup.mk (Units.mk0 P.radicand (P.radicand_ne_zero E)) ∈
      (IsDedekindDomain.selmerGroup
        (K := PrimeCyclotomicField p)
        (S := (∅ : Set (FinitePrime (PrimeCyclotomicField p))))
        (n := p)) := by
  intro v _
  exact E.valuationOfNeZeroMod_radicand_eq_one P v (hunramified v)

/-- The radicand class is nontrivial modulo `p`-th powers; otherwise its
Kummer polynomial could not be irreducible. -/
theorem radicandClass_ne_one (E : InverseExtension p L)
    (P : KummerPresentation E) :
    QuotientGroup.mk (s :=
      (powMonoidHom p :
        (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range)
      (Units.mk0 P.radicand (P.radicand_ne_zero E)) ≠ 1 := by
  intro htrivial
  rcases (QuotientGroup.eq_one_iff _).mp htrivial with ⟨x, hx⟩
  have hpow : (x : PrimeCyclotomicField p) ^ p = P.radicand := by
    simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0] using
      congrArg Units.val hx
  exact pow_ne_of_irreducible_X_pow_sub_C
    (P.irreducible E) dvd_rfl (Fact.out : p.Prime).ne_one
      (x : PrimeCyclotomicField p) hpow

/-- The everywhere-unramified Kummer radicand as an actual element of the
empty-support `p`-Selmer group. -/
noncomputable def radicandSelmerClass (E : InverseExtension p L)
    (P : KummerPresentation E)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    IsDedekindDomain.selmerGroup
      (K := PrimeCyclotomicField p)
      (S := (∅ : Set (FinitePrime (PrimeCyclotomicField p))))
      (n := p) :=
  ⟨QuotientGroup.mk (Units.mk0 P.radicand (P.radicand_ne_zero E)),
    E.radicand_mem_selmerGroup P hunramified⟩

/-- The Selmer class supplied by a Kummer presentation is nontrivial. -/
theorem radicandSelmerClass_ne_one (E : InverseExtension p L)
    (P : KummerPresentation E)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    E.radicandSelmerClass P hunramified ≠ 1 := by
  intro h
  apply E.radicandClass_ne_one P
  exact congrArg Subtype.val h

/-- The canonical nontrivial empty-support Selmer class attached to an
everywhere-unramified inverse extension. -/
noncomputable def unramifiedRadicandSelmerClass (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    IsDedekindDomain.selmerGroup
      (K := PrimeCyclotomicField p)
      (S := (∅ : Set (FinitePrime (PrimeCyclotomicField p))))
      (n := p) :=
  E.radicandSelmerClass E.kummerPresentation hunramified

/-- The canonical empty-support Selmer class attached to an inverse extension
is nontrivial. -/
theorem unramifiedRadicandSelmerClass_ne_one (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    E.unramifiedRadicandSelmerClass hunramified ≠ 1 :=
  E.radicandSelmerClass_ne_one E.kummerPresentation hunramified

/-- Every exponent of the canonical Kummer radicand's principal ideal is
divisible by `p` when the extension is everywhere unramified. -/
theorem prime_dvd_count_unramifiedRadicand (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (v : FinitePrime (PrimeCyclotomicField p)) :
    (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
      (FractionalIdeal.spanSingleton
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        E.kummerPresentation.radicand) := by
  rw [count_spanSingleton_eq_neg_valuationLog
    E.kummerPresentation.radicand
    (E.kummerPresentation.radicand_ne_zero E) v]
  obtain ⟨n, hn⟩ := E.valuationLog_radicand_eq_prime_mul
    E.kummerPresentation v (hunramified v)
  refine ⟨-n, ?_⟩
  rw [hn]
  ring

/-- Divide the canonical radicand divisor by `p`, prime by prime. -/
noncomputable def unramifiedRadicandIdealRoot (E : InverseExtension p L) :
    FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p) :=
  ∏ᶠ v : FinitePrime (PrimeCyclotomicField p),
    (v.asIdeal : FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p)) ^
      (FractionalIdeal.count (PrimeCyclotomicField p) v
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand) / (p : ℤ))

/-- The canonical divisor root is nonzero. -/
theorem unramifiedRadicandIdealRoot_ne_zero (E : InverseExtension p L) :
    E.unramifiedRadicandIdealRoot ≠ 0 := by
  apply finprod_ne_zero
  intro v
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The canonical divisor root has `p`-th power equal to the radicand's
principal fractional ideal. -/
theorem unramifiedRadicandIdealRoot_pow_eq (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    E.unramifiedRadicandIdealRoot ^ p =
      FractionalIdeal.spanSingleton
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        E.kummerPresentation.radicand := by
  let I : FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p) :=
    FractionalIdeal.spanSingleton
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      E.kummerPresentation.radicand
  let exps : FinitePrime (PrimeCyclotomicField p) → ℤ := fun v ↦
    FractionalIdeal.count (PrimeCyclotomicField p) v I / (p : ℤ)
  have hexps : ∀ᶠ v : FinitePrime (PrimeCyclotomicField p) in Filter.cofinite,
      exps v = 0 :=
    (FractionalIdeal.finite_factors I).mono fun v hv ↦ by simp [exps, hv]
  have hI_ne : I ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (E.kummerPresentation.radicand_ne_zero E)
  change E.unramifiedRadicandIdealRoot ^ p = I
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      (PrimeCyclotomicField p)
      (pow_ne_zero p E.unramifiedRadicandIdealRoot_ne_zero),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      (PrimeCyclotomicField p) hI_ne]
  apply finprod_congr
  intro v
  apply congrArg
  rw [FractionalIdeal.count_pow,
    show FractionalIdeal.count (PrimeCyclotomicField p) v
        E.unramifiedRadicandIdealRoot = exps v by
      simpa only [unramifiedRadicandIdealRoot, exps, I] using
        FractionalIdeal.count_finprod
          (PrimeCyclotomicField p) v exps hexps]
  exact Int.mul_ediv_cancel'
    (E.prime_dvd_count_unramifiedRadicand hunramified v)

/-- The nonzero canonical divisor root, packaged as a unit fractional ideal
so that it maps to the class group. -/
noncomputable def unramifiedRadicandRootIdeal (E : InverseExtension p L) :
    (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ :=
  Units.mk0 E.unramifiedRadicandIdealRoot
    E.unramifiedRadicandIdealRoot_ne_zero

/-- The unit fractional ideal still satisfies the defining `p`-th power
identity. -/
theorem unramifiedRadicandRootIdeal_pow_eq (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    E.unramifiedRadicandRootIdeal ^ p =
      toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Units.mk0 E.kummerPresentation.radicand
          (E.kummerPresentation.radicand_ne_zero E)) := by
  apply Units.ext
  simpa only [unramifiedRadicandRootIdeal, Units.val_pow_eq_pow_val,
    Units.val_mk0, coe_toPrincipalIdeal] using
    E.unramifiedRadicandIdealRoot_pow_eq hunramified

/-- The canonical ideal root defines a `p`-torsion class. -/
theorem unramifiedRadicandClass_pow_eq_one (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    (ClassGroup.mk (PrimeCyclotomicField p)
      E.unramifiedRadicandRootIdeal) ^ p = 1 := by
  rw [← map_pow, E.unramifiedRadicandRootIdeal_pow_eq hunramified]
  apply ClassGroup.mk_eq_one_iff.mpr
  apply (FractionalIdeal.isPrincipal_iff
    (toPrincipalIdeal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p)
      (Units.mk0 E.kummerPresentation.radicand
        (E.kummerPresentation.radicand_ne_zero E)) :
      FractionalIdeal
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        (PrimeCyclotomicField p))).mpr
  exact ⟨E.kummerPresentation.radicand, coe_toPrincipalIdeal _⟩

/-- If the canonical root ideal has trivial class, the Kummer radicand is a
global unit times a `p`-th power. -/
theorem unramifiedRadicand_eq_unit_mul_pow_of_class_eq_one
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (hclass : ClassGroup.mk (PrimeCyclotomicField p)
      E.unramifiedRadicandRootIdeal = 1) :
    ∃ (u : (NumberField.RingOfIntegers
          (PrimeCyclotomicField p))ˣ)
        (y : (PrimeCyclotomicField p)ˣ),
      E.kummerPresentation.radicand =
        algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) (u : _) *
          (y : PrimeCyclotomicField p) ^ p := by
  let I := E.unramifiedRadicandRootIdeal
  let a : (PrimeCyclotomicField p)ˣ :=
    Units.mk0 E.kummerPresentation.radicand
      (E.kummerPresentation.radicand_ne_zero E)
  have hI : I ^ p =
      toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) a := by
    simpa only [I, a] using
      E.unramifiedRadicandRootIdeal_pow_eq hunramified
  have hprincipal : Submodule.IsPrincipal
      (I : Submodule
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)) :=
    ClassGroup.mk_eq_one_iff.mp hclass
  obtain ⟨y, hy⟩ := hprincipal.principal
  have hy0 : y ≠ 0 := by
    intro hy0
    subst y
    have hzero : (I : FractionalIdeal
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        (PrimeCyclotomicField p)) = 0 := by
      rw [← FractionalIdeal.coeToSubmodule_inj]
      rw [hy, Submodule.span_zero_singleton]
      change (⊥ : Submodule
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)) =
          (0 : FractionalIdeal
            (nonZeroDivisors
              (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
            (PrimeCyclotomicField p))
      exact FractionalIdeal.coe_zero.symm
    exact I.ne_zero hzero
  let yu : (PrimeCyclotomicField p)ˣ := Units.mk0 y hy0
  have hIyu : I =
      toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) yu := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    rw [← FractionalIdeal.coeToSubmodule_inj]
    simpa only [FractionalIdeal.coe_spanSingleton, yu, Units.val_mk0] using hy
  have hprincipalEq :
      toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) (yu ^ p) =
        toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) a := by
    rw [map_pow, ← hIyu]
    exact hI
  have hspan :
      FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          ((yu : PrimeCyclotomicField p) ^ p) =
        FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          (a : PrimeCyclotomicField p) := by
    simpa only [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val] using
      congrArg Units.val hprincipalEq
  obtain ⟨u, hu⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  refine ⟨u, yu, ?_⟩
  simpa only [a, Units.val_mk0, Units.smul_def, Algebra.smul_def] using hu.symm

/-- The exact elementary output of the unramified Kummer construction:
either its canonical `p`-torsion ideal class is nontrivial, or the radicand
comes from a global unit modulo `p`-th powers. -/
theorem unramifiedRadicand_class_or_unit (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    (ClassGroup.mk (PrimeCyclotomicField p)
      E.unramifiedRadicandRootIdeal) ^ p = 1 ∧
      (ClassGroup.mk (PrimeCyclotomicField p)
          E.unramifiedRadicandRootIdeal ≠ 1 ∨
        ∃ (u : (NumberField.RingOfIntegers
              (PrimeCyclotomicField p))ˣ)
            (y : (PrimeCyclotomicField p)ˣ),
          E.kummerPresentation.radicand =
            algebraMap
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))
              (PrimeCyclotomicField p) (u : _) *
              (y : PrimeCyclotomicField p) ^ p) := by
  refine ⟨E.unramifiedRadicandClass_pow_eq_one hunramified, ?_⟩
  by_cases hclass : ClassGroup.mk (PrimeCyclotomicField p)
      E.unramifiedRadicandRootIdeal = 1
  · exact Or.inr
      (E.unramifiedRadicand_eq_unit_mul_pow_of_class_eq_one
        hunramified hclass)
  · exact Or.inl hclass

/-- Semilinearly transport a Kummer presentation by a chosen lift of a
cyclotomic automorphism. -/
noncomputable def KummerPresentation.transport
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) : KummerPresentation E where
  radical := E.lift sigma P.radical
  radicand := sigma P.radicand
  pow_radical := by
    rw [← map_pow, P.pow_radical, E.lift_algebraMap]
  adjoin_radical := by
    apply top_unique
    intro x _
    have hy : (E.lift sigma).symm x ∈
        IntermediateField.adjoin (PrimeCyclotomicField p) {P.radical} := by
      rw [P.adjoin_radical]
      exact Set.mem_univ _
    have htransport : E.lift sigma ((E.lift sigma).symm x) ∈
        IntermediateField.adjoin (PrimeCyclotomicField p)
          {E.lift sigma P.radical} := by
      apply IntermediateField.adjoin_induction
        (PrimeCyclotomicField p) (p := fun y _ =>
          E.lift sigma y ∈ IntermediateField.adjoin
            (PrimeCyclotomicField p) {E.lift sigma P.radical})
      · intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact IntermediateField.mem_adjoin_simple_self _ _
      · intro y
        rw [E.lift_algebraMap]
        exact (IntermediateField.adjoin
          (PrimeCyclotomicField p) {E.lift sigma P.radical}).algebraMap_mem _
      · intro y z _ _ hy hz
        rw [map_add]
        exact add_mem hy hz
      · intro y _ hy
        rw [map_inv₀]
        exact inv_mem hy
      · intro y z _ _ hy hz
        rw [map_mul]
        exact mul_mem hy hz
      · exact hy
    simpa using htransport

private theorem KummerPresentation.splittingField
    (E : InverseExtension p L) (P : KummerPresentation E) :
    Polynomial.IsSplittingField (PrimeCyclotomicField p) L
      (Polynomial.X ^ p - Polynomial.C P.radicand) := by
  have hroots :
      (primitiveRoots (Module.finrank (PrimeCyclotomicField p) L)
        (PrimeCyclotomicField p)).Nonempty := by
    rw [E.finrank_eq_prime]
    exact primitiveRoots_nonempty p
  have hpow : P.radical ^ Module.finrank (PrimeCyclotomicField p) L =
      algebraMap (PrimeCyclotomicField p) L P.radicand := by
    rw [E.finrank_eq_prime]
    exact P.pow_radical
  have h := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
    hroots hpow P.adjoin_radical
  simpa only [E.finrank_eq_prime] using h

/-- The Kummer pairing attached to a presentation, with values in the
`p`-th roots of unity of the cyclotomic base. -/
noncomputable def KummerPresentation.pairing
    (E : InverseExtension p L) (P : KummerPresentation E) :
    Gal(L/PrimeCyclotomicField p) ≃*
      rootsOfUnity p (PrimeCyclotomicField p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Polynomial.IsSplittingField (PrimeCyclotomicField p) L
      (Polynomial.X ^ p - Polynomial.C P.radicand) :=
    P.splittingField E
  exact autEquivRootsOfUnity (primitiveRoots_nonempty p)
    (P.irreducible E) L

/-- Evaluation formula for the presentation's Kummer pairing. -/
theorem KummerPresentation.pairing_smul_radical
    (E : InverseExtension p L) (P : KummerPresentation E)
    (tau : Gal(L/PrimeCyclotomicField p)) :
    P.pairing E tau • P.radical = tau P.radical := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Polynomial.IsSplittingField (PrimeCyclotomicField p) L
      (Polynomial.X ^ p - Polynomial.C P.radicand) :=
    P.splittingField E
  exact autEquivRootsOfUnity_smul (primitiveRoots_nonempty p)
    (P.irreducible E) L P.pow_radical tau

/-- The Kummer pairing is covariant under semilinear transport: conjugating
the relative automorphism and transporting the radical applies the
cyclotomic automorphism to the root-of-unity value. -/
theorem KummerPresentation.pairing_transport_conjugate
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (tau : Gal(L/PrimeCyclotomicField p)) :
    ((((P.transport E sigma).pairing E (E.conjugate sigma tau) :
          rootsOfUnity p (PrimeCyclotomicField p)) :
        (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) =
      sigma ((((P.pairing E tau :
          rootsOfUnity p (PrimeCyclotomicField p)) :
        (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p)) := by
  let beta := E.lift sigma P.radical
  let qtransport :=
    (P.transport E sigma).pairing E (E.conjugate sigma tau)
  let q := P.pairing E tau
  have hleft :=
    (P.transport E sigma).pairing_smul_radical E
      (E.conjugate sigma tau)
  rw [E.conjugate_apply] at hleft
  change _ = E.lift sigma
      (tau ((E.lift sigma).symm (E.lift sigma P.radical))) at hleft
  rw [(E.lift sigma).symm_apply_apply] at hleft
  change qtransport • beta = E.lift sigma (tau P.radical) at hleft
  simp only [Subgroup.smul_def, Units.smul_def, Algebra.smul_def] at hleft
  have hright := congrArg (E.lift sigma)
    (P.pairing_smul_radical E tau)
  simp only [Subgroup.smul_def, Units.smul_def, Algebra.smul_def] at hright
  change algebraMap (PrimeCyclotomicField p) L
      (((qtransport : rootsOfUnity p (PrimeCyclotomicField p)) :
        (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) * beta =
      E.lift sigma (tau P.radical) at hleft
  change E.lift sigma
      (algebraMap (PrimeCyclotomicField p) L
        (((q : rootsOfUnity p (PrimeCyclotomicField p)) :
          (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) *
        P.radical) =
      E.lift sigma (tau P.radical) at hright
  rw [map_mul, E.lift_algebraMap] at hright
  have hbeta : beta ≠ 0 := by
    dsimp only [beta]
    rw [map_ne_zero]
    intro halpha
    have hpowe := P.pow_radical
    rw [halpha, zero_pow (Fact.out : p.Prime).ne_zero] at hpowe
    exact P.radicand_ne_zero E
      ((algebraMap (PrimeCyclotomicField p) L).injective
        (hpowe.symm.trans (map_zero _).symm))
  apply (algebraMap (PrimeCyclotomicField p) L).injective
  apply mul_right_cancel₀ hbeta
  exact hleft.trans hright.symm

/-- The ordinary cyclotomic character is the inverse of `inverseCharacter`:
it gives the power by which a cyclotomic automorphism acts on every
`p`-th root of unity. -/
theorem cyclotomic_apply_rootOfUnity
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (q : rootsOfUnity p (PrimeCyclotomicField p)) :
    sigma (((q : (PrimeCyclotomicField p)ˣ) :
      PrimeCyclotomicField p)) =
      (((q : (PrimeCyclotomicField p)ˣ) :
        PrimeCyclotomicField p) ^
        ((((inverseCharacter p sigma)⁻¹ : (ZMod p)ˣ) :
          ZMod p).val)) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let zeta := IsCyclotomicExtension.zeta p ℚ
    (PrimeCyclotomicField p)
  have hzeta : IsPrimitiveRoot zeta p :=
    IsCyclotomicExtension.zeta_spec p ℚ (PrimeCyclotomicField p)
  let zetau : (PrimeCyclotomicField p)ˣ :=
    (hzeta.isUnit (Fact.out : p.Prime).ne_zero).unit'
  have hzetau : IsPrimitiveRoot zetau p :=
    hzeta.isUnit_unit' (Fact.out : p.Prime).ne_zero
  obtain ⟨i, _hi, hqi⟩ :=
    hzetau.eq_pow_of_mem_rootsOfUnity q.property
  have hcharacter :
      (inverseCharacter p sigma)⁻¹ =
        IsCyclotomicExtension.autEquivPow (PrimeCyclotomicField p)
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)) sigma := by
    change (((IsCyclotomicExtension.autEquivPow
      (PrimeCyclotomicField p)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)) sigma)⁻¹)⁻¹) = _
    exact inv_inv _
  have hzeta_action :=
    (IsCyclotomicExtension.zeta_spec p ℚ
      (PrimeCyclotomicField p)).autToPow_spec ℚ sigma
  have hzeta_action' :
      zeta ^ (((IsCyclotomicExtension.autEquivPow
          (PrimeCyclotomicField p)
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)) sigma :
        (ZMod p)ˣ) : ZMod p).val) = sigma zeta := by
    rw [IsCyclotomicExtension.autEquivPow_apply]
    exact hzeta_action
  rw [← hcharacter] at hzeta_action'
  have hqi_field : zeta ^ i =
      (((q : (PrimeCyclotomicField p)ˣ) :
        PrimeCyclotomicField p)) := by
    exact congrArg Units.val hqi
  rw [← hqi_field, map_pow, ← hzeta_action', ← pow_mul,
    mul_comm, pow_mul]

/-- Actual conjugation is the power map prescribed by the inverse
cyclotomic character. -/
theorem conjugate_eq_pow_inverseCharacter
    (E : InverseExtension p L)
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (tau : Gal(L/PrimeCyclotomicField p)) :
    E.conjugate sigma tau =
      tau ^ ((inverseCharacter p sigma : (ZMod p)ˣ) : ZMod p).val := by
  apply E.galEquiv.injective
  change Multiplicative.toAdd (E.galEquiv (E.conjugate sigma tau)) =
    Multiplicative.toAdd
      (E.galEquiv
        (tau ^ ((inverseCharacter p sigma : (ZMod p)ˣ) : ZMod p).val))
  rw [E.inverse_action, map_pow]
  change (inverseCharacter p sigma : ZMod p) *
      Multiplicative.toAdd (E.galEquiv tau) =
    ((inverseCharacter p sigma : (ZMod p)ˣ) : ZMod p).val •
      Multiplicative.toAdd (E.galEquiv tau)
  simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- The canonical primitive root used to coordinatize the Kummer character. -/
noncomputable def primeCyclotomicZeta (p : ℕ) [Fact p.Prime] :
    PrimeCyclotomicField p := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact IsCyclotomicExtension.zeta p ℚ (PrimeCyclotomicField p)

/-- The canonical cyclotomic root is primitive. -/
theorem primeCyclotomicZeta_spec (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (primeCyclotomicZeta p) p := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact IsCyclotomicExtension.zeta_spec p ℚ (PrimeCyclotomicField p)

/-- The chosen Kummer radical is nonzero. -/
theorem KummerPresentation.radical_ne_zero
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.radical ≠ 0 := by
  intro hzero
  have hpow := P.pow_radical
  rw [hzero, zero_pow (Fact.out : p.Prime).ne_zero] at hpow
  exact P.radicand_ne_zero E
    ((algebraMap (PrimeCyclotomicField p) L).injective
      (by simpa using hpow.symm))

/-- The relative automorphism whose Kummer eigenvalue is the canonical
cyclotomic root of unity. -/
noncomputable def KummerPresentation.generator
    (E : InverseExtension p L) (P : KummerPresentation E) :
    Gal(L/PrimeCyclotomicField p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact (P.pairing E).symm
    (primeCyclotomicZeta_spec p).toRootsOfUnity

/-- The Kummer generator acts on the radical by the canonical cyclotomic
root. -/
theorem KummerPresentation.generator_apply
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.generator E P.radical =
      algebraMap (PrimeCyclotomicField p) L
        (primeCyclotomicZeta p) * P.radical := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  rw [← P.pairing_smul_radical E]
  simp only [generator, MulEquiv.apply_symm_apply]
  simp only [Subgroup.smul_def, Units.smul_def, Algebra.smul_def,
    IsPrimitiveRoot.val_toRootsOfUnity_coe]

/-- Every power of the Kummer generator acts through the matching power of
the canonical cyclotomic root. -/
theorem KummerPresentation.generator_pow_apply
    (E : InverseExtension p L) (P : KummerPresentation E) (m : ℕ) :
    ((P.generator E) ^ m) P.radical =
      algebraMap (PrimeCyclotomicField p) L
        ((primeCyclotomicZeta p) ^ m) * P.radical := by
  rw [← P.pairing_smul_radical E]
  simp only [map_pow, generator, MulEquiv.apply_symm_apply,
    rootsOfUnity.coe_pow, IsPrimitiveRoot.val_toRootsOfUnity_coe,
    Subgroup.smul_def, Units.smul_def, Algebra.smul_def, map_pow]

/-- The direct mod-`p` cyclotomic character, inverse to the character used
in the packaged conjugation law. -/
noncomputable def directCharacter (p : ℕ) [Fact p.Prime] :
    Gal(PrimeCyclotomicField p/ℚ) →* (ZMod p)ˣ :=
  invMonoidHom.comp (inverseCharacter p)

/-- A cyclotomic automorphism acts on the canonical primitive root through
the direct character. -/
theorem map_primeCyclotomicZeta
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    sigma (primeCyclotomicZeta p) =
      primeCyclotomicZeta p ^
        ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let hcyclo := Polynomial.cyclotomic.irreducible_rat
    (n := p) (Fact.out : p.Prime).pos
  have hchar : directCharacter p sigma =
      IsCyclotomicExtension.autEquivPow
        (PrimeCyclotomicField p) hcyclo sigma := by
    change ((IsCyclotomicExtension.autEquivPow
      (PrimeCyclotomicField p) _ sigma)⁻¹)⁻¹ = _
    rw [inv_inv]
  have hspec := (primeCyclotomicZeta_spec p).autToPow_spec ℚ sigma
  calc
    sigma (primeCyclotomicZeta p) =
        primeCyclotomicZeta p ^
          ((IsPrimitiveRoot.autToPow ℚ (primeCyclotomicZeta_spec p) sigma :
              (ZMod p)ˣ) : ZMod p).val := hspec.symm
    _ = primeCyclotomicZeta p ^
          ((IsCyclotomicExtension.autEquivPow
            (PrimeCyclotomicField p) hcyclo sigma : (ZMod p)ˣ) : ZMod p).val := by
      apply congrArg (fun t : (ZMod p)ˣ =>
        primeCyclotomicZeta p ^ ((t : ZMod p).val))
      exact (IsCyclotomicExtension.autEquivPow_apply
        (PrimeCyclotomicField p) hcyclo sigma).symm
    _ = _ := by rw [hchar]

/-- The Kummer generator is nontrivial. -/
theorem KummerPresentation.generator_ne_one
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.generator E ≠ 1 := by
  intro hgen
  have himage := congrArg (P.pairing E) hgen
  have hzetaRoots :
      (primeCyclotomicZeta_spec p).toRootsOfUnity =
        (1 : rootsOfUnity p (PrimeCyclotomicField p)) := by
    simpa only [generator, MulEquiv.apply_symm_apply, map_one] using himage
  have hzeta : primeCyclotomicZeta p = 1 := by
    have hcoe := congrArg
      (fun z : rootsOfUnity p (PrimeCyclotomicField p) =>
        ((z : (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p)) hzetaRoots
    simpa using hcoe
  exact (primeCyclotomicZeta_spec p).ne_one
    (Fact.out : p.Prime).one_lt hzeta

/-- The Kummer generator generates the relative prime-order Galois group. -/
theorem KummerPresentation.mem_zpowers_generator
    (E : InverseExtension p L) (P : KummerPresentation E)
    (tau : Gal(L/PrimeCyclotomicField p)) :
    tau ∈ Subgroup.zpowers (P.generator E) := by
  apply mem_zpowers_of_prime_card (p := p) _ P.generator_ne_one
  calc
    Nat.card Gal(L/PrimeCyclotomicField p) =
        Nat.card (Multiplicative (ZMod p)) :=
      Nat.card_congr E.galEquiv.toEquiv
    _ = p := by simp

/-- It is enough to check invariance under the Kummer generator. -/
theorem KummerPresentation.fixed_of_generator_fixed
    (E : InverseExtension p L) (P : KummerPresentation E)
    {x : L} (hx : P.generator E x = x)
    (tau : Gal(L/PrimeCyclotomicField p)) : tau x = x := by
  have h := smul_eq_self_of_mem_zpowers
    (P.mem_zpowers_generator E tau) (a := x) (by
      simpa only [AlgEquiv.smul_def] using hx)
  simpa only [AlgEquiv.smul_def] using h

/-- Conjugating the direct-character power of the Kummer generator gives
back the generator.  This is the inverse-action law in generator
coordinates. -/
theorem KummerPresentation.conjugate_generator_pow_direct
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    E.conjugate sigma
        ((P.generator E) ^
          ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) =
      P.generator E := by
  apply E.galEquiv.injective
  apply Multiplicative.toAdd.injective
  rw [E.inverse_action]
  rw [map_pow, toAdd_pow, nsmul_eq_mul]
  have hval :
      (((((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val : ℕ) :
          ZMod p)) =
        ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p) := by
    simpa only [ZMod.cast_id] using
      ZMod.natCast_val
        (R := ZMod p)
        ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p)
  rw [hval]
  change ((inverseCharacter p sigma : (ZMod p)ˣ) : ZMod p) *
      ((((inverseCharacter p sigma : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) *
        Multiplicative.toAdd (E.galEquiv (P.generator E))) =
      Multiplicative.toAdd (E.galEquiv (P.generator E))
  simp only [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- The lifted radical is an eigenvector for the Kummer generator with
eigenvalue given by the square of the direct cyclotomic character. -/
theorem KummerPresentation.generator_apply_lift_radical
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    P.generator E (E.lift sigma P.radical) =
      algebraMap (PrimeCyclotomicField p) L
          ((primeCyclotomicZeta p) ^
            (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
              ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val)) *
        E.lift sigma P.radical := by
  let m := ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val
  have hconj := P.conjugate_generator_pow_direct E sigma
  calc
    P.generator E (E.lift sigma P.radical) =
        E.conjugate sigma ((P.generator E) ^ m)
          (E.lift sigma P.radical) := by rw [hconj]
    _ = E.lift sigma (((P.generator E) ^ m) P.radical) := by
      rw [E.conjugate_apply]
      simp
    _ = E.lift sigma
        (algebraMap (PrimeCyclotomicField p) L
          ((primeCyclotomicZeta p) ^ m) * P.radical) := by
      rw [P.generator_pow_apply E]
    _ = algebraMap (PrimeCyclotomicField p) L
          (sigma ((primeCyclotomicZeta p) ^ m)) *
        E.lift sigma P.radical := by
      rw [map_mul, E.lift_algebraMap]
    _ = algebraMap (PrimeCyclotomicField p) L
          ((primeCyclotomicZeta p) ^ (m * m)) *
        E.lift sigma P.radical := by
      rw [map_pow, map_primeCyclotomicZeta]
      simp only [m]
      rw [pow_mul]

/-- Dividing the lifted radical by the direct-character-square power of the
original radical gives an element fixed by the Kummer generator. -/
theorem KummerPresentation.generator_fixed_lift_div_pow
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    P.generator E
        (E.lift sigma P.radical /
          P.radical ^
            (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
              ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val)) =
      E.lift sigma P.radical /
        P.radical ^
          (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
            ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
  have hmapPow : P.generator E
      (P.radical ^
        (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
          ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val)) =
      (P.generator E P.radical) ^
        (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
          ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
    exact map_pow (P.generator E) _ _
  rw [map_div₀, P.generator_apply_lift_radical E,
    hmapPow, P.generator_apply]
  rw [mul_pow, ← map_pow]
  apply mul_div_mul_left
  exact (map_ne_zero (algebraMap (PrimeCyclotomicField p) L)).mpr
    (pow_ne_zero _ ((primeCyclotomicZeta_spec p).ne_zero
      (Fact.out : p.Prime).ne_zero))

/-- The lift of a Kummer radical is a base scalar times its
direct-character-square power. -/
theorem KummerPresentation.exists_lift_radical_eq_mul_pow
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    ∃ b : PrimeCyclotomicField p,
      E.lift sigma P.radical =
        algebraMap (PrimeCyclotomicField p) L b *
          P.radical ^
            (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
              ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  let n := ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
    ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val
  let x := E.lift sigma P.radical / P.radical ^ n
  have hfixed : ∀ tau : Gal(L/PrimeCyclotomicField p), tau x = x := by
    intro tau
    apply P.fixed_of_generator_fixed E
    exact P.generator_fixed_lift_div_pow E sigma
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfixed
  refine ⟨b, ?_⟩
  have hden : P.radical ^ n ≠ 0 := pow_ne_zero _ (P.radical_ne_zero E)
  exact ((eq_div_iff hden).mp hb).symm

/-- The Kummer radicand transforms by the square of the direct cyclotomic
character, up to a `p`-th power in the base field. -/
theorem KummerPresentation.exists_map_radicand_eq_pow_mul_pow
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    ∃ b : PrimeCyclotomicField p,
      sigma P.radicand =
        P.radicand ^
            (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
              ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) *
          b ^ p := by
  let n := ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
    ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val
  obtain ⟨b, hb⟩ := P.exists_lift_radical_eq_mul_pow E sigma
  refine ⟨b, ?_⟩
  apply (algebraMap (PrimeCyclotomicField p) L).injective
  calc
    algebraMap (PrimeCyclotomicField p) L (sigma P.radicand) =
        E.lift sigma
          (algebraMap (PrimeCyclotomicField p) L P.radicand) :=
      (E.lift_algebraMap sigma P.radicand).symm
    _ = E.lift sigma (P.radical ^ p) := by rw [P.pow_radical]
    _ = (E.lift sigma P.radical) ^ p := by rw [map_pow]
    _ = (algebraMap (PrimeCyclotomicField p) L b * P.radical ^ n) ^ p := by
      rw [hb]
    _ = algebraMap (PrimeCyclotomicField p) L
        (P.radicand ^ n * b ^ p) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm n p, pow_mul, P.pow_radical,
        ← map_pow, ← map_pow, ← map_mul, mul_comm]

/-- Quotient-group form of the Kummer-line character theorem: the radicand
class transforms through the square of the direct cyclotomic character. -/
theorem KummerPresentation.map_radicandClass_eq_pow
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    QuotientGroup.mk
        (Units.map sigma.toRingEquiv.toMonoidHom
          (Units.mk0 P.radicand (P.radicand_ne_zero E))) =
      (QuotientGroup.mk
        (Units.mk0 P.radicand (P.radicand_ne_zero E)) :
          (PrimeCyclotomicField p)ˣ ⧸
            (powMonoidHom p :
              (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range) ^
        (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
          ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
  let n := ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
    ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val
  obtain ⟨b, hb⟩ := P.exists_map_radicand_eq_pow_mul_pow E sigma
  have hb_ne : b ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero] at hb
    exact P.radicand_ne_zero E (sigma.injective (by simpa using hb))
  let aunit : (PrimeCyclotomicField p)ˣ :=
    Units.mk0 P.radicand (P.radicand_ne_zero E)
  let bunit : (PrimeCyclotomicField p)ˣ := Units.mk0 b hb_ne
  have hunits :
      Units.map sigma.toRingEquiv.toMonoidHom aunit =
        aunit ^ n * bunit ^ p := by
    apply Units.ext
    change sigma P.radicand = P.radicand ^ n * b ^ p
    simpa only [n] using hb
  rw [hunits, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  have hbtrivial :
      (QuotientGroup.mk (s :=
          (powMonoidHom p :
            (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range)
        (bunit ^ p) :
          (PrimeCyclotomicField p)ˣ ⧸
            (powMonoidHom p :
              (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨bunit, rfl⟩
  rw [hbtrivial]
  exact mul_one
    ((QuotientGroup.mk (s :=
        (powMonoidHom p :
          (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range)
      aunit :
        (PrimeCyclotomicField p)ˣ ⧸
          (powMonoidHom p :
            (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range) ^ n)

/-- Exact character-valued version: the exponent is the canonical natural
representative of the square of the direct cyclotomic character. -/
theorem KummerPresentation.map_radicandClass_eq_directCharacter_sq
    (E : InverseExtension p L) (P : KummerPresentation E)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    QuotientGroup.mk
        (Units.map sigma.toRingEquiv.toMonoidHom
          (Units.mk0 P.radicand (P.radicand_ne_zero E))) =
      (QuotientGroup.mk
        (Units.mk0 P.radicand (P.radicand_ne_zero E)) :
          (PrimeCyclotomicField p)ˣ ⧸
            (powMonoidHom p :
              (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range) ^
        (((((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p)).val) := by
  rw [P.map_radicandClass_eq_pow E sigma]
  let c := ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p)
  let q : (PrimeCyclotomicField p)ˣ ⧸
      (powMonoidHom p :
        (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range :=
    QuotientGroup.mk
      (Units.mk0 P.radicand (P.radicand_ne_zero E))
  have hmod :
      (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
          ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) ≡
        ((((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p)).val
          [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id,
      Units.val_pow_eq_pow_val]
    rw [pow_two]
  have hq : q ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨Units.mk0 P.radicand (P.radicand_ne_zero E), rfl⟩
  exact pow_eq_pow_of_modEq hmod hq

/-- Canonical-presentation consumer of the square-character theorem. -/
theorem map_canonicalRadicandClass_eq_directCharacter_sq
    (E : InverseExtension p L)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    QuotientGroup.mk
        (Units.map sigma.toRingEquiv.toMonoidHom
          (Units.mk0 E.kummerPresentation.radicand
            (E.kummerPresentation.radicand_ne_zero E))) =
      (QuotientGroup.mk
        (Units.mk0 E.kummerPresentation.radicand
          (E.kummerPresentation.radicand_ne_zero E)) :
          (PrimeCyclotomicField p)ˣ ⧸
            (powMonoidHom p :
              (PrimeCyclotomicField p)ˣ →* (PrimeCyclotomicField p)ˣ).range) ^
        (((((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p)).val) :=
  E.kummerPresentation.map_radicandClass_eq_directCharacter_sq E sigma

end NumberTheory.CyclotomicCharacter.InverseExtension
