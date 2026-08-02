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

end NumberTheory.CyclotomicCharacter.InverseExtension
