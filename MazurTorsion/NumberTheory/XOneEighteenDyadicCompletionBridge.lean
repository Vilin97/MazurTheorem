/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenDyadicLocalImage
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes

/-!
# The dyadic completion behind the `X₁(18)` local certificate

The finite calculation in `XOneEighteenDyadicLocalImage` takes place in the
unramified cubic ring modulo `2⁷`.  This file begins the arithmetic bridge
to that ring.  It constructs the actual prime above `2` in the full ring of
integers of the real cubic coefficient field and proves, at arbitrary
precision, that quotienting before or after adic completion gives the same
ring.

No conclusion about the local descent image is drawn merely from this
higher-residue comparison.  The remaining bridge must still identify the
chosen polynomial presentation modulo `2⁷`, lift the selected simple root
of the two-division cubic, and treat both integral and nonintegral local
points.
-/

open Polynomial IsDedekindDomain WithZero

namespace MazurTorsion.XOneEighteenDyadicCompletionBridge

noncomputable section

open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid
open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! ## The actual dyadic prime of the coefficient field -/

private theorem coefficient_not_dvd_exponent_two :
    ¬ 2 ∣ RingOfIntegers.exponent coefficientInteger := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {(81 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (𝓞 Q.K))
        (conductor ℤ coefficientInteger) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact coefficient_discriminant_mem_conductor
  exact ((Ideal.isCoprime_span_singleton_iff (81 : ℤ) 2).mpr
    (by norm_num)).codisjoint.mono_left hspan

private theorem coefficientPolynomialMod_two_irreducible :
    Irreducible (coefficientPolynomialMod 2) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdegree : (coefficientPolynomialMod 2).natDegree = 3 := by
      simp only [coefficientPolynomialMod]
      compute_degree!
    rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
      eval_mul, eval_ofNat, eval_one]
    fin_cases z <;> decide

private theorem coefficientPolynomialInt_mem_monicFactors_two :
    coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)) ∈
      RingOfIntegers.monicFactorsMod coefficientInteger 2 := by
  change coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)) ∈
    (normalizedFactors
      ((minpoly ℤ coefficientInteger).map
        (Int.castRingHom (ZMod 2)))).toFinset
  rw [coefficientInteger_minpoly]
  have hmonic :
      (coefficientPolynomialInt.map
        (Int.castRingHom (ZMod 2))).Monic :=
    coefficientPolynomialInt_monic.map _
  rw [normalizedFactors_irreducible]
  · simp only [hmonic.normalize_eq_self, Multiset.toFinset_singleton,
      Finset.mem_singleton]
  · rw [coefficientPolynomialInt_map_zmod]
    exact coefficientPolynomialMod_two_irreducible

/-- The Kummer--Dedekind prime selected by the irreducible cubic factor
modulo `2`. -/
def coefficientPrimeTwoIdeal : Ideal (𝓞 Q.K) :=
  (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_two).symm
    ⟨coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)),
      coefficientPolynomialInt_mem_monicFactors_two⟩

theorem coefficientPrimeTwo_mem_primesOver :
    coefficientPrimeTwoIdeal ∈
      Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 Q.K) :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_two).symm
    ⟨coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)),
      coefficientPolynomialInt_mem_monicFactors_two⟩).property

private instance coefficientPrimeTwoIdeal_isPrime :
    coefficientPrimeTwoIdeal.IsPrime :=
  coefficientPrimeTwo_mem_primesOver.1

private instance coefficientPrimeTwoIdeal_liesOver :
    coefficientPrimeTwoIdeal.LiesOver (Ideal.span {(2 : ℤ)}) :=
  coefficientPrimeTwo_mem_primesOver.2

/-- The unique height-one prime represented by the irreducible factor of
the coefficient polynomial modulo `2`. -/
def coefficientPrimeTwo : HeightOneSpectrum (𝓞 Q.K) :=
  .ofPrime (Ideal.prime_of_mem_primesOver
    (by norm_num) coefficientPrimeTwo_mem_primesOver)

@[simp] theorem coefficientPrimeTwo_asIdeal :
    coefficientPrimeTwo.asIdeal = coefficientPrimeTwoIdeal :=
  rfl

theorem coefficientPrimeTwoIdeal_eq_span :
    coefficientPrimeTwoIdeal = Ideal.span {(2 : 𝓞 Q.K)} := by
  rw [coefficientPrimeTwoIdeal]
  rw [NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    coefficient_not_dvd_exponent_two
    coefficientPolynomialInt_mem_monicFactors_two]
  have hzero : Polynomial.aeval coefficientInteger
      coefficientPolynomialInt = 0 := by
    rw [← coefficientInteger_minpoly]
    exact minpoly.aeval ℤ coefficientInteger
  rw [hzero]
  simp

@[simp] theorem coefficientPrimeTwo_span :
    coefficientPrimeTwo.asIdeal = Ideal.span {(2 : 𝓞 Q.K)} := by
  rw [coefficientPrimeTwo_asIdeal, coefficientPrimeTwoIdeal_eq_span]

/-! ## Quotients commute with adic completion -/

section CompletionQuotient

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Approximation by a global integer at an arbitrary integral adic
precision.  This is the higher-precision form of
`HeightOneSpectrum.exists_valued_sub_lt_one`. -/
theorem exists_valued_sub_lt_exp_neg
    (v : HeightOneSpectrum R) (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : R,
      Valued.v ((x : v.adicCompletion K) -
          algebraMap R (v.adicCompletion K) a) < exp (-(n : ℤ)) := by
  have hball :
      {y : v.adicCompletion K |
          Valued.v (y - (x : v.adicCompletion K)) < exp (-(n : ℤ))} ∈
        nhds (x : v.adicCompletion K) := by
    obtain ⟨w, hw⟩ :=
      v.valuedAdicCompletion_surjective K (exp (-(n : ℤ)))
    have hwne : w ≠ 0 := by
      intro hwzero
      rw [hwzero, map_zero] at hw
      exact exp_ne_zero hw.symm
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 (Valued.v.restrict w)
      (Valued.v.restrict.ne_zero_iff.mpr hwne), ?_⟩
    intro y hy
    simpa only [Valuation.restrict_lt_iff_lt_embedding, Units.val_mk0,
      Valuation.embedding_restrict, hw] using hy
  obtain ⟨_, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        (K := K) v _) _ hball
  rw [Set.mem_setOf_eq] at hwball
  have hexp_le_one : exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by
    rw [← exp_zero, exp_le_exp]
    omega
  have hz1 : v.valuation K z ≤ 1 := by
    rw [show v.valuation K z =
      Valued.v (algebraMap K (v.adicCompletion K) z) from
        (v.valuedAdicCompletion_eq_valuation' z).symm]
    calc
      Valued.v (algebraMap K (v.adicCompletion K) z) =
          Valued.v
            (algebraMap K (v.adicCompletion K) z -
                (x : v.adicCompletion K) + (x : v.adicCompletion K)) := by
            ring_nf
      _ ≤ max
          (Valued.v (algebraMap K (v.adicCompletion K) z -
            (x : v.adicCompletion K)))
          (Valued.v (x : v.adicCompletion K)) :=
        Valuation.map_add _ _ _
      _ ≤ 1 := max_le (hwball.le.trans hexp_le_one) x.2
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz1
    (WithZero.expOrderIso (-(n : ℤ)))
  refine ⟨a, ?_⟩
  have ha' :
      Valued.v (algebraMap K (v.adicCompletion K) z -
          algebraMap R (v.adicCompletion K) a) < exp (-(n : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      show Valued.v
          (algebraMap K (v.adicCompletion K)
            (z - algebraMap R K a)) =
          v.valuation K (z - algebraMap R K a) from
        v.valuedAdicCompletion_eq_valuation' _,
      Valuation.map_sub_swap]
    exact ha
  calc
    Valued.v ((x : v.adicCompletion K) -
        algebraMap R (v.adicCompletion K) a) =
      Valued.v
        (((x : v.adicCompletion K) -
            algebraMap K (v.adicCompletion K) z) +
          (algebraMap K (v.adicCompletion K) z -
            algebraMap R (v.adicCompletion K) a)) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < exp (-(n : ℤ)) :=
      max_lt (by rwa [Valuation.map_sub_swap] at hwball) ha'

/-- The canonical map from a global prime-power quotient to the
corresponding quotient of the completion's integers. -/
def completionQuotientMap (v : HeightOneSpectrum R) (n : ℕ) :
    R ⧸ v.asIdeal ^ n →+*
      v.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :=
  Ideal.quotientMap
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
    (algebraMap R (v.adicCompletionIntegers K)) (by
      intro r hr
      exact (v.algebraMap_mem_maximalIdeal_pow_iff (K := K)).2 hr)

theorem completionQuotientMap_bijective
    (v : HeightOneSpectrum R) (n : ℕ) :
    Function.Bijective (completionQuotientMap (K := K) v n) := by
  constructor
  · apply Ideal.quotientMap_injective'
    intro r hr
    exact (v.algebraMap_mem_maximalIdeal_pow_iff (K := K)).1 hr
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_valued_sub_lt_exp_neg v x n
    refine ⟨Ideal.Quotient.mk (v.asIdeal ^ n) a, ?_⟩
    change
      Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
          (algebraMap R (v.adicCompletionIntegers K) a) =
        Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) x
    apply Ideal.Quotient.eq.mpr
    apply (v.mem_maximalIdeal_pow_iff (K := K)).2
    change Valued.v
      (algebraMap R (v.adicCompletion K) a -
        (x : v.adicCompletion K)) ≤ exp (-(n : ℤ))
    rw [Valuation.map_sub_swap]
    exact ha.le

/-- Quotienting a Dedekind domain by `v^n` is canonically equivalent to
quotienting the integer ring of its adic completion by `m_v^n`. -/
noncomputable def completionQuotientEquiv
    (v : HeightOneSpectrum R) (n : ℕ) :
    R ⧸ v.asIdeal ^ n ≃+*
      v.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :=
  RingEquiv.ofBijective (completionQuotientMap (K := K) v n)
    (completionQuotientMap_bijective (K := K) v n)

@[simp] theorem completionQuotientEquiv_mk
    (v : HeightOneSpectrum R) (n : ℕ) (r : R) :
    completionQuotientEquiv (K := K) v n
        (Ideal.Quotient.mk (v.asIdeal ^ n) r) =
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (algebraMap R (v.adicCompletionIntegers K) r) := by
  rfl

end CompletionQuotient

/-! ## The coefficient completion modulo `2⁷` -/

open MazurTorsion.XOneEighteenDyadicLocalImage

/-- The seventh-power quotient at the genuine dyadic prime. -/
abbrev CoefficientDyadicQuotient :=
  𝓞 Q.K ⧸ coefficientPrimeTwo.asIdeal ^ 7

theorem coefficientPrimeTwo_pow_seven :
    coefficientPrimeTwo.asIdeal ^ 7 = Ideal.span {(128 : 𝓞 Q.K)} := by
  rw [coefficientPrimeTwo_span, Ideal.span_singleton_pow]
  norm_num

private theorem span_one_twenty_eight_le_comap :
    Ideal.span {(128 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (𝓞 Q.K))
        (coefficientPrimeTwo.asIdeal ^ 7) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
    coefficientPrimeTwo_pow_seven]
  exact Ideal.subset_span (Set.mem_singleton 128)

/-- The canonical scalar map from `ZMod 128` into the global dyadic
quotient. -/
def coefficientBaseMod128 : ZMod 128 →+* CoefficientDyadicQuotient :=
  (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
      (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap).comp
    ((Int.quotientSpanNatEquivZMod 128).symm :
      ZMod 128 →+* ℤ ⧸ Ideal.span {(128 : ℤ)})

@[simp] theorem coefficientBaseMod128_intCast (z : ℤ) :
    coefficientBaseMod128 (z : ZMod 128) =
      Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)
        (algebraMap ℤ (𝓞 Q.K) z) := by
  change
    (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
        (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap)
      ((Int.quotientSpanNatEquivZMod 128).symm (z : ZMod 128)) = _
  have hz := congrArg
    (fun f : ℤ →+* ℤ ⧸ Ideal.span {(128 : ℤ)} ↦ f z)
    (Int.quotientSpanNatEquivZMod_comp_castRingHom 128)
  simp only [RingHom.comp_apply] at hz
  change
    (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
        (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap)
      ((Int.quotientSpanNatEquivZMod 128).symm
        ((Int.castRingHom (ZMod 128)) z)) = _
  calc
    _ = (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
          (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap)
        (Ideal.Quotient.mk (Ideal.span {(128 : ℤ)}) z) :=
      congrArg _ hz
    _ = _ := Ideal.quotientMap_mk

private theorem coefficientBaseMod128_comp_intCast :
    coefficientBaseMod128.comp (Int.castRingHom (ZMod 128)) =
      (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)).comp
        (algebraMap ℤ (𝓞 Q.K)) := by
  ext z
  exact coefficientBaseMod128_intCast z

/-- The image of the coefficient-field generator in the dyadic quotient. -/
def coefficientTauMod128 : CoefficientDyadicQuotient :=
  Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7) coefficientInteger

private theorem coefficientInteger_cubic :
    coefficientInteger ^ 3 - 3 * coefficientInteger - 1 = 0 := by
  have hmin := minpoly.aeval ℤ coefficientInteger
  rw [coefficientInteger_minpoly] at hmin
  simpa only [coefficientPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat, map_one] using hmin

theorem coefficientTauMod128_cubic :
    coefficientTauMod128 ^ 3 - 3 * coefficientTauMod128 - 1 = 0 := by
  simp only [coefficientTauMod128]
  rw [← map_pow, ← map_ofNat
      (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)) 3,
    ← map_mul, ← map_one
      (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)),
    ← map_sub, ← map_sub, coefficientInteger_cubic, map_zero]

private theorem cubicPolynomial128_eval₂_coefficientTau :
    cubicPolynomial128.eval₂ coefficientBaseMod128 coefficientTauMod128 = 0 := by
  simp only [cubicPolynomial128, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_mul, eval₂_ofNat, eval₂_one]
  exact coefficientTauMod128_cubic

/-- Evaluation of the monogenic cubic order in the global dyadic
quotient. -/
def cubicToGlobalDyadic : CubicResidue128 →+* CoefficientDyadicQuotient :=
  AdjoinRoot.lift coefficientBaseMod128 coefficientTauMod128
    cubicPolynomial128_eval₂_coefficientTau

@[simp] theorem cubicToGlobalDyadic_root :
    cubicToGlobalDyadic (AdjoinRoot.root cubicPolynomial128) =
      coefficientTauMod128 := by
  exact AdjoinRoot.lift_root cubicPolynomial128_eval₂_coefficientTau

theorem cubicToGlobalDyadic_mk_map_int
    (p : Polynomial ℤ) :
    cubicToGlobalDyadic
        (AdjoinRoot.mk cubicPolynomial128
          (p.map (Int.castRingHom (ZMod 128)))) =
      Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)
        (Polynomial.aeval coefficientInteger p) := by
  rw [cubicToGlobalDyadic, AdjoinRoot.lift_mk, Polynomial.eval₂_map,
    coefficientBaseMod128_comp_intCast]
  exact (Polynomial.hom_eval₂ p
    (algebraMap ℤ (𝓞 Q.K))
    (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7))
    coefficientInteger).symm

theorem cubicToGlobalDyadic_surjective :
    Function.Surjective cubicToGlobalDyadic := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h81x : (81 : 𝓞 Q.K) * x ∈
      Algebra.adjoin ℤ {coefficientInteger} :=
    (mem_conductor_iff.mp coefficient_discriminant_mem_conductor) x
  obtain ⟨p, hp⟩ :=
    Algebra.adjoin_mem_exists_aeval ℤ coefficientInteger h81x
  refine ⟨AdjoinRoot.mk cubicPolynomial128
    ((C (49 : ℤ) * p).map (Int.castRingHom (ZMod 128))), ?_⟩
  rw [cubicToGlobalDyadic_mk_map_int]
  apply Ideal.Quotient.eq.mpr
  rw [coefficientPrimeTwo_pow_seven, Ideal.mem_span_singleton]
  refine ⟨31 * x, ?_⟩
  simp only [aeval_mul, aeval_C, hp]
  norm_num
  ring

private theorem cubicPolynomial128_monic' : cubicPolynomial128.Monic := by
  simp only [cubicPolynomial128]
  monicity <;> norm_num

private theorem cubicPolynomial128_natDegree' :
    cubicPolynomial128.natDegree = 3 := by
  simp only [cubicPolynomial128]
  compute_degree!

private def cubicResiduePowerBasis : PowerBasis (ZMod 128) CubicResidue128 :=
  AdjoinRoot.powerBasis' cubicPolynomial128_monic'

theorem cubicResidue128_card : Nat.card CubicResidue128 = 128 ^ 3 := by
  calc
    Nat.card CubicResidue128 =
        Nat.card (Fin cubicResiduePowerBasis.dim →₀ ZMod 128) :=
      Nat.card_congr cubicResiduePowerBasis.basis.repr.toEquiv
    _ = 128 ^ 3 := by
      simp only [cubicResiduePowerBasis, AdjoinRoot.powerBasis'_dim,
        cubicPolynomial128_natDegree']
      simp

noncomputable instance cubicResidue128_finite : Finite CubicResidue128 :=
  Nat.finite_of_card_ne_zero (by rw [cubicResidue128_card]; norm_num)

theorem coefficientDyadicQuotient_card :
    Nat.card CoefficientDyadicQuotient = 128 ^ 3 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    coefficientPrimeTwo_pow_seven]
  calc
    Ideal.absNorm (Ideal.span {(128 : 𝓞 Q.K)}) =
        128 ^ Module.finrank ℤ (𝓞 Q.K) :=
      Ideal.absNorm_span_natCast 128
    _ = 128 ^ 3 := by
      rw [RingOfIntegers.rank, coefficientPowerBasis.finrank,
        coefficientPowerBasis_dim]

noncomputable instance coefficientDyadicQuotient_finite :
    Finite CoefficientDyadicQuotient :=
  Nat.finite_of_card_ne_zero (by
    rw [coefficientDyadicQuotient_card]
    norm_num)

theorem cubicToGlobalDyadic_bijective :
    Function.Bijective cubicToGlobalDyadic :=
  (Nat.bijective_iff_surjective_and_card cubicToGlobalDyadic).2
    ⟨cubicToGlobalDyadic_surjective, by
      rw [cubicResidue128_card, coefficientDyadicQuotient_card]⟩

/-- The actual seventh-power quotient of the coefficient field is the
explicit cubic residue ring used by the finite local certificate. -/
noncomputable def cubicResidue128EquivGlobal :
    CubicResidue128 ≃+* CoefficientDyadicQuotient :=
  RingEquiv.ofBijective cubicToGlobalDyadic cubicToGlobalDyadic_bijective

@[simp] theorem cubicResidue128EquivGlobal_root :
    cubicResidue128EquivGlobal (AdjoinRoot.root cubicPolynomial128) =
      coefficientTauMod128 := by
  exact cubicToGlobalDyadic_root

/-- Genuine reduction from the integer ring of the coefficient-field
completion to the explicit cubic ring modulo `2⁷`. -/
noncomputable def completionReduction :
    coefficientPrimeTwo.adicCompletionIntegers Q.K →+* CubicResidue128 :=
  cubicResidue128EquivGlobal.symm.toRingHom.comp
    ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm.toRingHom.comp
      (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal
          (coefficientPrimeTwo.adicCompletionIntegers Q.K) ^ 7)))

theorem cubicResidue128EquivGlobal_completionReduction_algebraMap
    (r : 𝓞 Q.K) :
    cubicResidue128EquivGlobal
        (completionReduction
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) r)) =
      Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7) r := by
  calc
    cubicResidue128EquivGlobal
        (completionReduction
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) r)) =
      (completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) ^ 7)
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) r)) := by
        change cubicResidue128EquivGlobal
          (cubicResidue128EquivGlobal.symm _) = _
        exact RingEquiv.apply_symm_apply _ _
    _ = Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7) r := by
      rw [← completionQuotientEquiv_mk]
      exact RingEquiv.symm_apply_apply _ _

theorem completionReduction_coefficientInteger :
    completionReduction
        (algebraMap (𝓞 Q.K)
          (coefficientPrimeTwo.adicCompletionIntegers Q.K)
          coefficientInteger) =
      AdjoinRoot.root cubicPolynomial128 := by
  apply cubicResidue128EquivGlobal.injective
  rw [cubicResidue128EquivGlobal_root]
  calc
    cubicResidue128EquivGlobal
        (completionReduction
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K)
            coefficientInteger)) =
      (completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) ^ 7)
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K)
            coefficientInteger)) := by
        change cubicResidue128EquivGlobal
          (cubicResidue128EquivGlobal.symm _) = _
        exact RingEquiv.apply_symm_apply _ _
    _ = Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)
        coefficientInteger := by
      rw [← completionQuotientEquiv_mk]
      exact RingEquiv.symm_apply_apply _ _
    _ = coefficientTauMod128 := rfl

/-! ## The selected simple root of the local two-division cubic -/

abbrev CoefficientCompletionIntegers :=
  coefficientPrimeTwo.adicCompletionIntegers Q.K

/-- The two-division cubic over the integers of the coefficient
completion. -/
def localTwoDivisionPolynomial : Polynomial CoefficientCompletionIntegers :=
  X ^ 3 - 3 * X - 10

private theorem localTwoDivisionPolynomial_monic :
    localTwoDivisionPolynomial.Monic := by
  simp only [localTwoDivisionPolynomial]
  monicity <;> norm_num

private theorem ten_mem_coefficientPrimeTwo :
    (10 : 𝓞 Q.K) ∈ coefficientPrimeTwo.asIdeal := by
  rw [coefficientPrimeTwo_span, Ideal.mem_span_singleton]
  exact ⟨5, by norm_num⟩

private theorem three_not_mem_coefficientPrimeTwo :
    (3 : 𝓞 Q.K) ∉ coefficientPrimeTwo.asIdeal := by
  intro hthree
  have hthree' : algebraMap ℤ (𝓞 Q.K) (3 : ℤ) ∈
      coefficientPrimeTwoIdeal := by
    simpa only [coefficientPrimeTwo_asIdeal, map_ofNat] using hthree
  have hz : (3 : ℤ) ∈ Ideal.span {(2 : ℤ)} := by
    exact (Ideal.mem_of_liesOver (P := coefficientPrimeTwoIdeal)
      (p := Ideal.span {(2 : ℤ)}) 3).2 hthree'
  rw [Ideal.mem_span_singleton] at hz
  obtain ⟨a, ha⟩ := hz
  omega

private theorem ten_mem_completionMaximalIdeal :
    (10 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (10 : 𝓞 Q.K)) (n := 1)).2 (by
      simpa only [pow_one] using ten_mem_coefficientPrimeTwo)
  simpa only [pow_one, map_ofNat] using h

private theorem three_not_mem_completionMaximalIdeal :
    (3 : CoefficientCompletionIntegers) ∉
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  intro hthree
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (3 : 𝓞 Q.K)) (n := 1)).1 (by
      simpa only [pow_one, map_ofNat] using hthree)
  exact three_not_mem_coefficientPrimeTwo (by
    simpa only [pow_one] using h)

private theorem exists_localTwoDivisionRoot_aux :
    ∃ sHat : CoefficientCompletionIntegers,
      localTwoDivisionPolynomial.IsRoot sHat ∧
        sHat ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  have hvalue : localTwoDivisionPolynomial.eval 0 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    have heval : localTwoDivisionPolynomial.eval 0 =
        (-10 : CoefficientCompletionIntegers) := by
      norm_num [localTwoDivisionPolynomial]
    rw [heval]
    exact (IsLocalRing.maximalIdeal CoefficientCompletionIntegers).neg_mem
      ten_mem_completionMaximalIdeal
  have hderivative :
      IsUnit (localTwoDivisionPolynomial.derivative.eval 0) := by
    have hthreeUnit : IsUnit (3 : CoefficientCompletionIntegers) :=
      IsLocalRing.notMem_maximalIdeal.mp
        three_not_mem_completionMaximalIdeal
    have hderiv : localTwoDivisionPolynomial.derivative.eval 0 =
        (-3 : CoefficientCompletionIntegers) := by
      norm_num [localTwoDivisionPolynomial]
    rw [hderiv]
    exact hthreeUnit.neg
  obtain ⟨sHat, hsHat, hsHatmem⟩ :=
    HenselianLocalRing.is_henselian localTwoDivisionPolynomial
      localTwoDivisionPolynomial_monic 0 hvalue hderivative
  exact ⟨sHat, hsHat, by simpa only [sub_zero] using hsHatmem⟩

/-- The Hensel lift of the simple root `0` modulo the dyadic maximal
ideal. -/
noncomputable def localTwoDivisionRoot : CoefficientCompletionIntegers :=
  Classical.choose exists_localTwoDivisionRoot_aux

theorem localTwoDivisionRoot_isRoot :
    localTwoDivisionPolynomial.IsRoot localTwoDivisionRoot :=
  (Classical.choose_spec exists_localTwoDivisionRoot_aux).1

theorem localTwoDivisionRoot_mem_maximalIdeal :
    localTwoDivisionRoot ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers :=
  (Classical.choose_spec exists_localTwoDivisionRoot_aux).2

private theorem seventyFour_mem_completionMaximalIdeal :
    (74 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  have hglobal : (74 : 𝓞 Q.K) ∈ coefficientPrimeTwo.asIdeal := by
    rw [coefficientPrimeTwo_span, Ideal.mem_span_singleton]
    exact ⟨37, by norm_num⟩
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (74 : 𝓞 Q.K)) (n := 1)).2 (by
      simpa only [pow_one] using hglobal)
  simpa only [pow_one, map_ofNat] using h

private def localTwoDivisionRootCofactor : CoefficientCompletionIntegers :=
  localTwoDivisionRoot ^ 2 + 74 * localTwoDivisionRoot + 74 ^ 2 - 3

private theorem localTwoDivisionRootCofactor_isUnit :
    IsUnit localTwoDivisionRootCofactor := by
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
  have hrest : localTwoDivisionRoot ^ 2 +
      74 * localTwoDivisionRoot + 74 ^ 2 ∈ I := by
    apply I.add_mem
    · apply I.add_mem
      · simpa only [pow_two] using
          I.mul_mem_left localTwoDivisionRoot
            localTwoDivisionRoot_mem_maximalIdeal
      · exact I.mul_mem_left 74 localTwoDivisionRoot_mem_maximalIdeal
    · simpa only [pow_two] using
        I.mul_mem_left 74 seventyFour_mem_completionMaximalIdeal
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hcofactor
  have hnegthree : (-3 : CoefficientCompletionIntegers) ∈ I := by
    have hsub := I.sub_mem hcofactor hrest
    change localTwoDivisionRootCofactor -
      (localTwoDivisionRoot ^ 2 + 74 * localTwoDivisionRoot + 74 ^ 2) ∈ I at hsub
    have heq : localTwoDivisionRootCofactor -
        (localTwoDivisionRoot ^ 2 + 74 * localTwoDivisionRoot + 74 ^ 2) =
          (-3 : CoefficientCompletionIntegers) := by
      simp only [localTwoDivisionRootCofactor]
      ring
    rw [heq] at hsub
    exact hsub
  have hthree : (3 : CoefficientCompletionIntegers) ∈ I := by
    simpa only [neg_neg] using I.neg_mem hnegthree
  exact three_not_mem_completionMaximalIdeal hthree

private theorem oneTwentyEight_mem_completionMaximalIdeal_pow_seven :
    (128 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 := by
  have hglobal : (128 : 𝓞 Q.K) ∈ coefficientPrimeTwo.asIdeal ^ 7 := by
    rw [coefficientPrimeTwo_pow_seven]
    exact Ideal.subset_span (Set.mem_singleton 128)
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (128 : 𝓞 Q.K)) (n := 7)).2 hglobal
  simpa only [map_ofNat] using h

/-- The chosen Hensel root has the certified residue `74` modulo `2⁷`.
The proof uses the exact factorization of the difference of the two cubic
values and cancellation of a unit, rather than uniqueness as an oracle. -/
theorem localTwoDivisionRoot_sub_seventyFour_mem_pow_seven :
    localTwoDivisionRoot - 74 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 := by
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7
  have hroot : localTwoDivisionRoot ^ 3 -
      3 * localTwoDivisionRoot - 10 = 0 := by
    simpa only [Polynomial.IsRoot, localTwoDivisionPolynomial,
      eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat] using
      localTwoDivisionRoot_isRoot
  have hfactor :
      (localTwoDivisionRoot - 74) * localTwoDivisionRootCofactor =
        -(128 * 3164) := by
    simp only [localTwoDivisionRootCofactor]
    linear_combination hroot
  have hrhs : (-(128 * 3164) : CoefficientCompletionIntegers) ∈ I := by
    exact I.neg_mem
      (I.mul_mem_right 3164
        oneTwentyEight_mem_completionMaximalIdeal_pow_seven)
  have hproduct :
      (localTwoDivisionRoot - 74) * localTwoDivisionRootCofactor ∈ I := by
    rw [hfactor]
    exact hrhs
  exact (I.mul_unit_mem_iff_mem
    localTwoDivisionRootCofactor_isUnit).mp hproduct

private theorem completionReduction_seventyFour :
    completionReduction (74 : CoefficientCompletionIntegers) =
      (74 : CubicResidue128) := by
  apply cubicResidue128EquivGlobal.injective
  have hseventyFour : (74 : CoefficientCompletionIntegers) =
      algebraMap (𝓞 Q.K) CoefficientCompletionIntegers (74 : 𝓞 Q.K) := by
    simp only [map_ofNat]
  rw [hseventyFour,
    cubicResidue128EquivGlobal_completionReduction_algebraMap]
  simp only [map_ofNat]

/-- Under the genuine completion reduction, the Hensel-lifted
two-division root specializes to the checked scalar root `74`. -/
theorem completionReduction_localTwoDivisionRoot :
    completionReduction localTwoDivisionRoot = 74 := by
  rw [← completionReduction_seventyFour]
  change
    cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7)
            localTwoDivisionRoot)) =
      cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) 74))
  apply congrArg (fun q ↦ cubicResidue128EquivGlobal.symm
    ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm q))
  exact Ideal.Quotient.eq.mpr
    localTwoDivisionRoot_sub_seventyFour_mem_pow_seven

/-! ## The unramified dyadic uniformizer and square lifting -/

/-- The rational integer `2` is a uniformizer in the selected completion.
This is where unramifiedness of the coefficient-field prime is used. -/
theorem coefficientCompletion_maximalIdeal_eq_span_two :
    IsLocalRing.maximalIdeal CoefficientCompletionIntegers =
      Ideal.span {(2 : CoefficientCompletionIntegers)} := by
  have h := coefficientPrimeTwo.span_singleton_eq_maximalIdeal_pow
    (K := Q.K) (x := (2 : CoefficientCompletionIntegers)) (e := 1) (by
      simp only [map_ofNat]
      calc
        Valued.v (2 : coefficientPrimeTwo.adicCompletion Q.K) =
            Valued.v (algebraMap Q.K
              (coefficientPrimeTwo.adicCompletion Q.K) (2 : Q.K)) := by
          exact congrArg Valued.v (by simp only [map_ofNat])
        _ = coefficientPrimeTwo.valuation Q.K (2 : Q.K) := by
          rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
            (𝓞 Q.K) Q.K coefficientPrimeTwo]
          exact coefficientPrimeTwo.valuedAdicCompletion_eq_valuation'
            (2 : Q.K)
        _ = coefficientPrimeTwo.intValuation (2 : 𝓞 Q.K) := by
          simpa only [map_ofNat] using
            coefficientPrimeTwo.valuation_of_algebraMap
              (K := Q.K) (2 : 𝓞 Q.K)
        _ = exp (-1) := by
          rw [coefficientPrimeTwo.intValuation_eq_exp_neg_multiplicity
              (by norm_num),
            coefficientPrimeTwo_span]
          simp)
  simpa only [pow_one] using h.symm

private theorem coefficientCompletion_maximalIdeal_pow_eq_span_two_pow
    (n : ℕ) :
    IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ n =
      Ideal.span {(2 ^ n : CoefficientCompletionIntegers)} := by
  rw [coefficientCompletion_maximalIdeal_eq_span_two,
    Ideal.span_singleton_pow]

private theorem completionReduction_surjective :
    Function.Surjective completionReduction :=
  cubicResidue128EquivGlobal.symm.surjective.comp
    ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm.surjective.comp
      Ideal.Quotient.mk_surjective)

private theorem completionReduction_eq_iff
    (x y : CoefficientCompletionIntegers) :
    completionReduction x = completionReduction y ↔
      x - y ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 := by
  change
    cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) x)) =
      cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) y)) ↔ _
  rw [cubicResidue128EquivGlobal.symm.injective.eq_iff,
    (completionQuotientEquiv
      (K := Q.K) coefficientPrimeTwo 7).symm.injective.eq_iff,
    Ideal.Quotient.eq]

private theorem exists_eq_eight_mul_of_mem_maximalIdeal_pow_seven
    {x : CoefficientCompletionIntegers}
    (hx : x ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) :
    ∃ a : CoefficientCompletionIntegers, x = 8 * a := by
  have hxthree : x ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 3 :=
    (Ideal.pow_le_pow_right (by norm_num : 3 ≤ 7)) hx
  rw [coefficientCompletion_maximalIdeal_pow_eq_span_two_pow,
    show (2 : CoefficientCompletionIntegers) ^ 3 = 8 by norm_num,
    Ideal.mem_span_singleton] at hxthree
  obtain ⟨a, ha⟩ := hxthree
  exact ⟨a, by simpa only [mul_comm] using ha⟩

/-- A unit square modulo `2³` lifts to a square in the Henselian dyadic
integer ring.  Replacing `z` by `z + 2t` turns the nonsimple square-root
equation into a monic polynomial with unit derivative. -/
private theorem isSquare_of_eq_sq_add_eight_mul
    {u z a : CoefficientCompletionIntegers} (hz : IsUnit z)
    (hu : u = z ^ 2 + 8 * a) : IsSquare u := by
  let f : Polynomial CoefficientCompletionIntegers :=
    X ^ 2 + C z * X - C (2 * a)
  have hfmonic : f.Monic := by
    dsimp only [f]
    monicity <;> norm_num
  have hfzero : f.eval 0 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    have htwo : (2 : CoefficientCompletionIntegers) ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
      rw [coefficientCompletion_maximalIdeal_eq_span_two,
        Ideal.mem_span_singleton]
    have hmem := (IsLocalRing.maximalIdeal
      CoefficientCompletionIntegers).mul_mem_right a htwo
    have heval : f.eval 0 = -(2 * a) := by
      norm_num [f]
    rw [heval]
    exact (IsLocalRing.maximalIdeal
      CoefficientCompletionIntegers).neg_mem hmem
  have hfderiv : IsUnit (f.derivative.eval 0) := by
    have heval : f.derivative.eval 0 = z := by
      norm_num [f]
    rw [heval]
    exact hz
  obtain ⟨t, ht, -⟩ := HenselianLocalRing.is_henselian
    f hfmonic 0 hfzero hfderiv
  refine ⟨z + 2 * t, ?_⟩
  have hroot : t ^ 2 + z * t - 2 * a = 0 := by
    simpa only [Polynomial.IsRoot, f, eval_sub, eval_add, eval_pow,
      eval_X, eval_mul, eval_C] using ht
  rw [hu]
  linear_combination -4 * hroot

/-! ## The normalized projected curve over the integer ring -/

/-- The integral quadratic coefficient after translating to the selected
two-division root and scaling the abscissa by `4`. -/
def localNormalizedA : CoefficientCompletionIntegers :=
  9 * (localTwoDivisionRoot ^ 2 - 2 * localTwoDivisionRoot - 2)

/-- The integral constant coefficient in the same normalized model. -/
def localNormalizedB : CoefficientCompletionIntegers :=
  81 * (localTwoDivisionRoot ^ 2 + 2 * localTwoDivisionRoot - 7)

private theorem scalar_one_twenty_eight_eq_zero :
    (128 : CubicResidue128) = 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 128]
  have h : (128 : ZMod 128) = 0 := by decide
  rw [h, map_zero]

@[simp] theorem completionReduction_localNormalizedA :
    completionReduction localNormalizedA = 62 := by
  simp only [localNormalizedA, map_mul, map_sub, map_pow,
    map_ofNat, completionReduction_localTwoDivisionRoot]
  linear_combination 374 * scalar_one_twenty_eight_eq_zero

@[simp] theorem completionReduction_localNormalizedB :
    completionReduction localNormalizedB = 65 := by
  simp only [localNormalizedB, map_mul, map_sub, map_add, map_pow,
    map_ofNat, completionReduction_localTwoDivisionRoot]
  linear_combination 3554 * scalar_one_twenty_eight_eq_zero

private theorem normalizedQuadratic_reduction_eq_square
    (x : CoefficientCompletionIntegers) :
    completionReduction
        (x ^ 2 + localNormalizedA * x + localNormalizedB) =
      completionReduction (x + 31) ^ 2 := by
  simp only [map_add, map_mul, map_pow,
    completionReduction_localNormalizedA,
    completionReduction_localNormalizedB, map_ofNat]
  linear_combination -7 * scalar_one_twenty_eight_eq_zero

private theorem isUnit_of_add_mem_maximalIdeal
    {u m : CoefficientCompletionIntegers} (hu : IsUnit u)
    (hm : m ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers) :
    IsUnit (u + m) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hum
  have huMem := (IsLocalRing.maximalIdeal
    CoefficientCompletionIntegers).sub_mem hum hm
  have huNotMem := IsLocalRing.notMem_maximalIdeal.mpr hu
  exact huNotMem (by simpa only [add_sub_cancel_right] using huMem)

private theorem isSquare_of_isUnit_of_reduction_isSquare
    {x : CoefficientCompletionIntegers} (hx : IsUnit x)
    (hred : IsSquare (completionReduction x)) : IsSquare x := by
  obtain ⟨zBar, hzBar⟩ := hred
  obtain ⟨z, hz⟩ := completionReduction_surjective zBar
  have hredEq : completionReduction x = completionReduction (z ^ 2) := by
    rw [map_pow, hz]
    simpa only [pow_two] using hzBar
  have hdiff : x - z ^ 2 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 :=
    (completionReduction_eq_iff x (z ^ 2)).1 hredEq
  obtain ⟨a, ha⟩ :=
    exists_eq_eight_mul_of_mem_maximalIdeal_pow_seven hdiff
  have hzUnit : IsUnit z := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hzMem
    let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
    have hzSqMem : z ^ 2 ∈ I := by
      simpa only [pow_two] using I.mul_mem_left z hzMem
    have hdiffMem : x - z ^ 2 ∈ I := by
      change x - z ^ 2 ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers
      simpa only [pow_one] using
        (Ideal.pow_le_pow_right (by norm_num : 1 ≤ 7)) hdiff
    have hxMem : x ∈ I := by
      have hsum := I.add_mem hzSqMem hdiffMem
      have heq : z ^ 2 + (x - z ^ 2) = x := by ring
      rwa [heq] at hsum
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx) hxMem
  exact isSquare_of_eq_sq_add_eight_mul hzUnit (a := a) (by
    linear_combination ha)

private theorem thirtyOne_isUnit :
    IsUnit (31 : CoefficientCompletionIntegers) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h31
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
  have htwo : (2 : CoefficientCompletionIntegers) ∈ I := by
    change (2 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers
    rw [coefficientCompletion_maximalIdeal_eq_span_two,
      Ideal.mem_span_singleton]
  have hthirty : (30 : CoefficientCompletionIntegers) ∈ I := by
    have h := I.mul_mem_right 15 htwo
    norm_num at h
    exact h
  have hone : (1 : CoefficientCompletionIntegers) ∈ I := by
    have hsub := I.sub_mem h31 hthirty
    norm_num at hsub
    exact hsub
  exact (IsLocalRing.maximalIdeal.isMaximal
    CoefficientCompletionIntegers).ne_top
      ((Ideal.eq_top_iff_one _).mpr hone)

private theorem normalizedQuadratic_isSquare_of_nonunit
    {x : CoefficientCompletionIntegers} (hx : ¬ IsUnit x) :
    IsSquare (x ^ 2 + localNormalizedA * x + localNormalizedB) := by
  let q := x ^ 2 + localNormalizedA * x + localNormalizedB
  let z := x + 31
  have hxMem : x ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    by_contra hxNotMem
    exact hx (IsLocalRing.notMem_maximalIdeal.mp hxNotMem)
  have hzUnit : IsUnit z := by
    simpa only [z, add_comm] using
      isUnit_of_add_mem_maximalIdeal thirtyOne_isUnit hxMem
  have hred : completionReduction q = completionReduction (z ^ 2) := by
    rw [map_pow]
    simpa only [q, z] using normalizedQuadratic_reduction_eq_square x
  have hdiff : q - z ^ 2 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 :=
    (completionReduction_eq_iff q (z ^ 2)).1 hred
  obtain ⟨a, ha⟩ :=
    exists_eq_eight_mul_of_mem_maximalIdeal_pow_seven hdiff
  exact isSquare_of_eq_sq_add_eight_mul hzUnit (a := a) (by
    dsimp only [q, z]
    dsimp only [q, z] at ha
    linear_combination ha)

private theorem normalizedQuadratic_isUnit_of_nonunit
    {x : CoefficientCompletionIntegers} (hx : ¬ IsUnit x) :
    IsUnit (x ^ 2 + localNormalizedA * x + localNormalizedB) := by
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
  have hxMem : x ∈ I := by
    by_contra hxNotMem
    exact hx (IsLocalRing.notMem_maximalIdeal.mp hxNotMem)
  have hrest : x ^ 2 + localNormalizedA * x ∈ I := by
    apply I.add_mem
    · simpa only [pow_two] using I.mul_mem_left x hxMem
    · exact I.mul_mem_left localNormalizedA hxMem
  have hBUnit : IsUnit localNormalizedB := by
    have hsixtyFive : IsUnit (65 : CoefficientCompletionIntegers) := by
      have hsixtyFour : (64 : CoefficientCompletionIntegers) ∈ I := by
        have htwo : (2 : CoefficientCompletionIntegers) ∈ I := by
          change (2 : CoefficientCompletionIntegers) ∈
            IsLocalRing.maximalIdeal CoefficientCompletionIntegers
          rw [coefficientCompletion_maximalIdeal_eq_span_two,
            Ideal.mem_span_singleton]
        have h := I.mul_mem_right 32 htwo
        norm_num at h
        exact h
      have h := isUnit_of_add_mem_maximalIdeal isUnit_one hsixtyFour
      norm_num at h
      exact h
    have hred : completionReduction localNormalizedB =
        completionReduction (65 : CoefficientCompletionIntegers) := by
      rw [completionReduction_localNormalizedB, map_ofNat]
    have hdiffPow : localNormalizedB - 65 ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 :=
      (completionReduction_eq_iff localNormalizedB 65).1 hred
    have hdiff : localNormalizedB - 65 ∈ I := by
      change localNormalizedB - 65 ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers
      simpa only [pow_one] using
        (Ideal.pow_le_pow_right (by norm_num : 1 ≤ 7)) hdiffPow
    have hsum := isUnit_of_add_mem_maximalIdeal hsixtyFive hdiff
    have heq : (65 : CoefficientCompletionIntegers) +
        (localNormalizedB - 65) = localNormalizedB := by ring
    rwa [heq] at hsum
  have hsum := isUnit_of_add_mem_maximalIdeal hBUnit hrest
  have heq : localNormalizedB +
      (x ^ 2 + localNormalizedA * x) =
        x ^ 2 + localNormalizedA * x + localNormalizedB := by ring
  rwa [heq] at hsum

/-- The adjusted value at the selected two-torsion abscissa is a square.
Its residue is `65 = 33²` modulo `2⁷`, and the unit square lifts by the
Henselian lemma above. -/
theorem localNormalizedB_isSquare : IsSquare localNormalizedB := by
  have hBUnit : IsUnit localNormalizedB := by
    have h := normalizedQuadratic_isUnit_of_nonunit
      (x := (0 : CoefficientCompletionIntegers)) not_isUnit_zero
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero,
      zero_add] using h
  apply isSquare_of_isUnit_of_reduction_isSquare hBUnit
  refine ⟨(33 : CubicResidue128), ?_⟩
  rw [completionReduction_localNormalizedB]
  linear_combination -8 * scalar_one_twenty_eight_eq_zero

/-- Every integral point of the genuinely normalized projected curve has
square first coordinate in the completion's integer ring. -/
theorem normalized_integral_curve_isSquare
    (x y : CoefficientCompletionIntegers)
    (hcurve : y ^ 2 =
      x * (x ^ 2 + localNormalizedA * x + localNormalizedB)) :
    IsSquare x := by
  by_cases hx : IsUnit x
  · apply isSquare_of_isUnit_of_reduction_isSquare hx
    apply XOneEighteenDyadicLocalImage.integral_cubic_mod128
      (completionReduction x) (completionReduction y)
    have hred := congrArg completionReduction hcurve
    simpa only [map_pow, map_mul, map_add,
      completionReduction_localNormalizedA,
      completionReduction_localNormalizedB] using hred
  · have hqSquare := normalizedQuadratic_isSquare_of_nonunit hx
    have hqUnit := normalizedQuadratic_isUnit_of_nonunit hx
    obtain ⟨w, hw⟩ := hqSquare
    have hwUnit : IsUnit w := by
      have hwwUnit : IsUnit (w * w) := by
        rw [← hw]
        exact hqUnit
      exact (IsUnit.mul_iff.mp hwwUnit).1
    let wInv : CoefficientCompletionIntegers := ↑(hwUnit.unit⁻¹)
    have hwwInv : w * wInv = 1 := by
      dsimp only [wInv]
      calc
        w * (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) =
            (↑hwUnit.unit : CoefficientCompletionIntegers) *
              (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) := by
          rw [hwUnit.unit_spec]
        _ = 1 := by simp
    have hy : y ^ 2 = x * w ^ 2 := by
      calc
        y ^ 2 = x *
            (x ^ 2 + localNormalizedA * x + localNormalizedB) := hcurve
        _ = x * (w * w) := by rw [hw]
        _ = x * w ^ 2 := by rw [pow_two]
    refine ⟨y * wInv, ?_⟩
    calc
      x = x * (w * wInv) ^ 2 := by rw [hwwInv]; ring
      _ = (x * w ^ 2) * wInv ^ 2 := by ring
      _ = y ^ 2 * wInv ^ 2 := by rw [hy]
      _ = (y * wInv) * (y * wInv) := by ring

/-! ## Passage to the completion field -/

/-- The selected dyadic completion of the coefficient field. -/
abbrev CoefficientCompletion := coefficientPrimeTwo.adicCompletion Q.K

private theorem field_isSquare_of_integer_isSquare
    (x : CoefficientCompletionIntegers) (hx : IsSquare x) :
    IsSquare (x : CoefficientCompletion) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨(z : CoefficientCompletion), ?_⟩
  exact congrArg Subtype.val hz

private theorem integer_ordinate_of_integer_abscissa
    (x : CoefficientCompletionIntegers) (y : CoefficientCompletion)
    (hcurve : y ^ 2 =
      (x : CoefficientCompletion) *
        ((x : CoefficientCompletion) ^ 2 +
          (localNormalizedA : CoefficientCompletion) * x +
          localNormalizedB)) :
    ∃ yInt : CoefficientCompletionIntegers, (yInt : CoefficientCompletion) = y := by
  let rhs : CoefficientCompletionIntegers :=
    x * (x ^ 2 + localNormalizedA * x + localNormalizedB)
  have hySqLe : Valued.v (y ^ 2) ≤ (1 : ℤᵐ⁰) := by
    rw [hcurve]
    change Valued.v (rhs : CoefficientCompletion) ≤ (1 : ℤᵐ⁰)
    exact rhs.2
  have hyLe : Valued.v y ≤ (1 : ℤᵐ⁰) := by
    apply (sq_le_one_iff₀ bot_le).mp
    rw [← map_pow]
    exact hySqLe
  exact ⟨⟨y, hyLe⟩, rfl⟩

private theorem normalized_curve_isSquare_of_integral_abscissa
    (x y : CoefficientCompletion)
    (hx : Valued.v x ≤ (1 : ℤᵐ⁰))
    (hcurve : y ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)) :
    IsSquare x := by
  let xInt : CoefficientCompletionIntegers := ⟨x, hx⟩
  obtain ⟨yInt, hyInt⟩ := integer_ordinate_of_integer_abscissa xInt y (by
    simpa only [xInt] using hcurve)
  have hcurveInt : yInt ^ 2 =
      xInt * (xInt ^ 2 + localNormalizedA * xInt + localNormalizedB) := by
    apply Subtype.ext
    change (yInt : CoefficientCompletion) ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)
    rw [hyInt]
    exact hcurve
  have hxSquare := normalized_integral_curve_isSquare xInt yInt hcurveInt
  simpa only [xInt] using field_isSquare_of_integer_isSquare xInt hxSquare

private theorem exists_localNormalizedA_eq_two_mul :
    ∃ a : CoefficientCompletionIntegers, localNormalizedA = 2 * a := by
  have hs : localTwoDivisionRoot ∈
      Ideal.span {(2 : CoefficientCompletionIntegers)} := by
    rw [← coefficientCompletion_maximalIdeal_eq_span_two]
    exact localTwoDivisionRoot_mem_maximalIdeal
  rw [Ideal.mem_span_singleton] at hs
  obtain ⟨c, hc⟩ := hs
  refine ⟨9 * (2 * c ^ 2 - 2 * c - 1), ?_⟩
  simp only [localNormalizedA]
  rw [hc]
  ring

private theorem isSquare_of_sq_eq_mul_square_of_isUnit
    {u v q : CoefficientCompletionIntegers}
    (hcurve : v ^ 2 = u * q) (hqSquare : IsSquare q)
    (hqUnit : IsUnit q) : IsSquare u := by
  obtain ⟨w, hw⟩ := hqSquare
  have hwUnit : IsUnit w := by
    have hwwUnit : IsUnit (w * w) := by
      rw [← hw]
      exact hqUnit
    exact (IsUnit.mul_iff.mp hwwUnit).1
  let wInv : CoefficientCompletionIntegers := ↑(hwUnit.unit⁻¹)
  have hwwInv : w * wInv = 1 := by
    dsimp only [wInv]
    calc
      w * (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) =
          (↑hwUnit.unit : CoefficientCompletionIntegers) *
            (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) := by
        rw [hwUnit.unit_spec]
      _ = 1 := by simp
  have hv : v ^ 2 = u * w ^ 2 := by
    calc
      v ^ 2 = u * q := hcurve
      _ = u * (w * w) := by rw [hw]
      _ = u * w ^ 2 := by rw [pow_two]
  refine ⟨v * wInv, ?_⟩
  calc
    u = u * (w * wInv) ^ 2 := by rw [hwwInv]; ring
    _ = (u * w ^ 2) * wInv ^ 2 := by ring
    _ = v ^ 2 * wInv ^ 2 := by rw [hv]
    _ = (v * wInv) * (v * wInv) := by ring

private theorem normalized_curve_isSquare_of_pole
    (x y : CoefficientCompletion)
    (hx : 1 < Valued.v x)
    (hcurve : y ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)) :
    IsSquare x := by
  have hxne : x ≠ 0 := by
    rintro rfl
    simp at hx
  have huValLt : Valued.v x⁻¹ < (1 : ℤᵐ⁰) := by
    rw [map_inv₀, inv_lt_one_iff₀]
    exact Or.inr hx
  let uInt : CoefficientCompletionIntegers := ⟨x⁻¹, huValLt.le⟩
  have huMem : uInt ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro huUnit
    have huValEq : Valued.v (uInt : CoefficientCompletion) = 1 :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
        huUnit
    exact (ne_of_lt huValLt) huValEq
  let qInt : CoefficientCompletionIntegers :=
    1 + localNormalizedA * uInt + localNormalizedB * uInt ^ 2
  have hqUnit : IsUnit qInt := by
    have hrest : localNormalizedA * uInt +
        localNormalizedB * uInt ^ 2 ∈
          IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
      apply (IsLocalRing.maximalIdeal
        CoefficientCompletionIntegers).add_mem
      · exact (IsLocalRing.maximalIdeal
          CoefficientCompletionIntegers).mul_mem_left localNormalizedA huMem
      · apply (IsLocalRing.maximalIdeal
          CoefficientCompletionIntegers).mul_mem_left localNormalizedB
        simpa only [pow_two] using
          (IsLocalRing.maximalIdeal
            CoefficientCompletionIntegers).mul_mem_left uInt huMem
    have hunit := isUnit_of_add_mem_maximalIdeal isUnit_one hrest
    have heq : qInt = 1 +
        (localNormalizedA * uInt + localNormalizedB * uInt ^ 2) := by
      dsimp only [qInt]
      ring
    rw [heq]
    exact hunit
  let vField : CoefficientCompletion := y * x⁻¹ ^ 2
  have htrans : vField ^ 2 =
      (uInt : CoefficientCompletion) * (qInt : CoefficientCompletion) := by
    dsimp only [vField, uInt, qInt]
    calc
      (y * x⁻¹ ^ 2) ^ 2 = y ^ 2 * x⁻¹ ^ 4 := by ring
      _ = (x * (x ^ 2 +
          (localNormalizedA : CoefficientCompletion) * x +
            localNormalizedB)) * x⁻¹ ^ 4 := by rw [hcurve]
      _ = x⁻¹ * (1 +
          (localNormalizedA : CoefficientCompletion) * x⁻¹ +
            (localNormalizedB : CoefficientCompletion) * x⁻¹ ^ 2) := by
        field_simp [hxne]
  have hvSqLe : Valued.v (vField ^ 2) ≤ (1 : ℤᵐ⁰) := by
    rw [htrans]
    change Valued.v ((uInt * qInt : CoefficientCompletionIntegers) :
      CoefficientCompletion) ≤ (1 : ℤᵐ⁰)
    exact (uInt * qInt).2
  have hvLe : Valued.v vField ≤ (1 : ℤᵐ⁰) := by
    apply (sq_le_one_iff₀ bot_le).mp
    rw [← map_pow]
    exact hvSqLe
  let vInt : CoefficientCompletionIntegers := ⟨vField, hvLe⟩
  have hcurveInt : vInt ^ 2 = uInt * qInt := by
    apply Subtype.ext
    exact htrans
  have huNe : uInt ≠ 0 := by
    intro hu
    apply inv_ne_zero hxne
    exact congrArg Subtype.val hu
  have hvNe : vInt ≠ 0 := by
    intro hv
    have hzero : (0 : CoefficientCompletionIntegers) = uInt * qInt := by
      simpa only [hv, zero_pow (by norm_num : 2 ≠ 0)] using hcurveInt
    rcases mul_eq_zero.mp hzero.symm with hu | hq
    · exact huNe hu
    · exact hqUnit.ne_zero hq
  have htwoIrr : Irreducible (2 : CoefficientCompletionIntegers) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer 2).2
      coefficientCompletion_maximalIdeal_eq_span_two
  obtain ⟨n, uUnit, huEq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible huNe htwoIrr
  obtain ⟨m, vUnit, hvEq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hvNe htwoIrr
  have huVal : IsDiscreteValuationRing.addVal CoefficientCompletionIntegers uInt = n := by
    rw [huEq]
    exact IsDiscreteValuationRing.addVal_def' uUnit htwoIrr n
  have hvVal : IsDiscreteValuationRing.addVal CoefficientCompletionIntegers vInt = m := by
    rw [hvEq]
    exact IsDiscreteValuationRing.addVal_def' vUnit htwoIrr m
  have hqVal : IsDiscreteValuationRing.addVal CoefficientCompletionIntegers qInt = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hqUnit
  have hadd := congrArg
    (IsDiscreteValuationRing.addVal CoefficientCompletionIntegers) hcurveInt
  have hadd' : ((2 : ℕ) : ℕ∞) * (m : ℕ∞) = (n : ℕ∞) := by
    simpa only [IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_mul, hvVal, huVal, hqVal, add_zero,
      nsmul_eq_mul] using hadd
  have hnm : n = 2 * m := by
    exact_mod_cast hadd'.symm
  have hnNe : n ≠ 0 := by
    intro hn
    have huUnit : IsUnit uInt := by
      rw [huEq, hn, pow_zero, mul_one]
      exact uUnit.isUnit
    exact (IsLocalRing.notMem_maximalIdeal.mpr huUnit) huMem
  have hmNe : m ≠ 0 := by
    intro hm
    apply hnNe
    rw [hnm, hm, mul_zero]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmNe
  have huFour : ∃ c : CoefficientCompletionIntegers, uInt = 4 * c := by
    refine ⟨(uUnit : CoefficientCompletionIntegers) * 2 ^ (2 * k), ?_⟩
    rw [huEq, hnm, hk]
    ring_nf
    rw [Nat.succ_mul, pow_add]
    norm_num
    ring
  obtain ⟨c, hc⟩ := huFour
  obtain ⟨a, ha⟩ := exists_localNormalizedA_eq_two_mul
  have hqForm : qInt = 1 + 8 *
      (a * c + 2 * localNormalizedB * c ^ 2) := by
    dsimp only [qInt]
    rw [ha, hc]
    ring
  have hqSquare : IsSquare qInt :=
    isSquare_of_eq_sq_add_eight_mul (z := 1)
      (a := a * c + 2 * localNormalizedB * c ^ 2) isUnit_one (by
      rw [hqForm]
      ring)
  have huSquare := isSquare_of_sq_eq_mul_square_of_isUnit
    hcurveInt hqSquare hqUnit
  obtain ⟨z, hz⟩ := huSquare
  have hzNe : (z : CoefficientCompletion) ≠ 0 := by
    intro hz0
    have hu0 : uInt = 0 := by
      rw [hz]
      apply Subtype.ext
      change (z : CoefficientCompletion) * z = 0
      rw [hz0, zero_mul]
    exact huNe hu0
  refine ⟨((z : CoefficientCompletion)⁻¹), ?_⟩
  have huField : (x⁻¹ : CoefficientCompletion) =
      (z : CoefficientCompletion) * z := congrArg Subtype.val hz
  calc
    x = (x⁻¹)⁻¹ := (inv_inv x).symm
    _ = ((z : CoefficientCompletion) * z)⁻¹ :=
      congrArg (fun w : CoefficientCompletion => w⁻¹) huField
    _ = (z : CoefficientCompletion)⁻¹ *
        (z : CoefficientCompletion)⁻¹ := by
      rw [mul_inv_rev]

/-- Every point on the normalized projected curve over the genuine
dyadic completion has square abscissa.  The proof treats integral
abscissae through the checked residue certificate and poles by an
even-valuation argument in the completion's discrete valuation ring. -/
theorem normalized_local_curve_isSquare
    (x y : CoefficientCompletion)
    (hcurve : y ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)) :
    IsSquare x := by
  by_cases hx : Valued.v x ≤ (1 : ℤᵐ⁰)
  · exact normalized_curve_isSquare_of_integral_abscissa x y hx hcurve
  · exact normalized_curve_isSquare_of_pole x y (lt_of_not_ge hx) hcurve

end

end MazurTorsion.XOneEighteenDyadicCompletionBridge
