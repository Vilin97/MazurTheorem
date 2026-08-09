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

end

end MazurTorsion.XOneEighteenDyadicCompletionBridge
