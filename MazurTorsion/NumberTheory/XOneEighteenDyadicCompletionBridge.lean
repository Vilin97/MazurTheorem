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

end

end MazurTorsion.XOneEighteenDyadicCompletionBridge
