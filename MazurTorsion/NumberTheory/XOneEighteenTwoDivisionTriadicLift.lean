/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionTriadicPrime

/-!
# The triadic prime in the `X₁(18)` two-division compositum

The normalized integral generator has a relative cubic polynomial over the
real cubic coefficient field.  Its discriminant is `-8`, so reduction at the
unique coefficient prime above `3` is controlled by Kummer--Dedekind.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicLift

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The relative normalized polynomial -/

/-- The relative cubic polynomial of the normalized generator over the
coefficient field. -/
def normalizedRelativePolynomial : Polynomial Q.K :=
  X ^ 3 + C (Q.tau ^ 2 - 3) * X ^ 2 +
    C (-2 * Q.tau ^ 2 + Q.tau + 4) * X - 1

theorem normalizedRelativePolynomial_monic :
    normalizedRelativePolynomial.Monic := by
  simp only [normalizedRelativePolynomial]
  monicity <;> norm_num

theorem normalizedRelativePolynomial_natDegree :
    normalizedRelativePolynomial.natDegree = 3 := by
  simp only [normalizedRelativePolynomial]
  compute_degree!

private def normalizedRelativeExpression : Polynomial ℚ :=
  X ^ 3 + (coefficientPolynomial ^ 2 - 3) * X ^ 2 +
    (-2 * coefficientPolynomial ^ 2 + coefficientPolynomial + 4) * X - 1

private def normalizedRelativeReductionQuotient : Polynomial ℚ :=
  X ^ 9 - 7 * X ^ 8 + 21 * X ^ 7 - 36 * X ^ 6 +
    39 * X ^ 5 - 28 * X ^ 4 + 13 * X ^ 3 -
    2 * X ^ 2 - X + 1

private theorem normalizedRelative_reduction_identity :
    normalizedRelativeExpression =
      normalizedRelativeReductionQuotient * normalizedPolynomial := by
  simp only [normalizedRelativeExpression,
    normalizedRelativeReductionQuotient, coefficientPolynomial,
    normalizedPolynomial]
  ring

private theorem normalizedRelativeExpression_root :
    Polynomial.aeval normalizedElement normalizedRelativeExpression = 0 := by
  rw [normalizedRelative_reduction_identity]
  simp only [map_mul, normalizedElement_root, mul_zero]

/-- The normalized generator satisfies the displayed relative cubic. -/
theorem normalizedElement_relative_root :
    Polynomial.aeval normalizedElement normalizedRelativePolynomial = 0 := by
  simp only [normalizedRelativePolynomial, map_sub, map_add, map_mul,
    map_pow, aeval_X, aeval_C, map_neg, map_one, map_ofNat]
  change normalizedElement ^ 3 +
      (t ^ 2 - 3) * normalizedElement ^ 2 +
      (-2 * t ^ 2 + t + 4) * normalizedElement - 1 = 0
  rw [coefficientGenerator_formula]
  simpa only [normalizedRelativeExpression, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_neg, map_one, aeval_X] using
    normalizedRelativeExpression_root

/-- The normalized generator also generates the compositum over the
coefficient field. -/
theorem normalizedElement_adjoin_coefficient_eq_top :
    Algebra.adjoin Q.K ({normalizedElement} : Set M) = ⊤ := by
  apply top_unique
  intro z hz
  have hzRat : z ∈ Algebra.adjoin ℚ ({normalizedElement} : Set M) := by
    rw [normalizedElement_adjoin_eq_top]
    trivial
  have hle : Algebra.adjoin ℚ ({normalizedElement} : Set M) ≤
      (Algebra.adjoin Q.K ({normalizedElement} : Set M)).restrictScalars ℚ := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Algebra.subset_adjoin (R := Q.K) (Set.mem_singleton normalizedElement)
  exact hle hzRat

private def normalizedRelativePowerBasis : PowerBasis Q.K M :=
  PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite Q.K normalizedElement)
    normalizedElement_adjoin_coefficient_eq_top

@[simp]
private theorem normalizedRelativePowerBasis_gen :
    normalizedRelativePowerBasis.gen = normalizedElement := by
  rw [normalizedRelativePowerBasis, PowerBasis.ofAdjoinEqTop_gen]

private theorem normalizedElement_relative_minpoly_natDegree :
    (minpoly Q.K normalizedElement).natDegree = 3 := by
  calc
    (minpoly Q.K normalizedElement).natDegree =
        normalizedRelativePowerBasis.dim := by
      simpa only [normalizedRelativePowerBasis_gen] using
        normalizedRelativePowerBasis.natDegree_minpoly
    _ = Module.finrank Q.K M := normalizedRelativePowerBasis.finrank.symm
    _ = 3 := finrank_M_over_K

/-- The displayed relative cubic is exactly the minimal polynomial of the
normalized generator over the coefficient field. -/
theorem normalizedElement_minpoly_relative :
    minpoly Q.K normalizedElement = normalizedRelativePolynomial := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite Q.K normalizedElement))
    normalizedRelativePolynomial_monic
    (minpoly.dvd Q.K normalizedElement normalizedElement_relative_root)
    (by rw [normalizedRelativePolynomial_natDegree,
      normalizedElement_relative_minpoly_natDegree])).symm

theorem normalizedRelativePolynomial_irreducible :
    Irreducible normalizedRelativePolynomial := by
  rw [← normalizedElement_minpoly_relative]
  exact minpoly.irreducible (IsIntegral.of_finite Q.K normalizedElement)

private instance normalizedRelativePolynomial_irreducibleFact :
    Fact (Irreducible normalizedRelativePolynomial) :=
  ⟨normalizedRelativePolynomial_irreducible⟩

/-- The relative cubic has discriminant `-8`. -/
theorem normalizedRelativePolynomial_discriminant :
    normalizedRelativePolynomial.discr = -8 := by
  have hcoeffZero : normalizedRelativePolynomial.coeff 0 = -1 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffOne : normalizedRelativePolynomial.coeff 1 =
      -2 * Q.tau ^ 2 + Q.tau + 4 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffTwo : normalizedRelativePolynomial.coeff 2 =
      Q.tau ^ 2 - 3 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffThree : normalizedRelativePolynomial.coeff 3 = 1 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  rw [Polynomial.discr_of_degree_eq_three]
  · rw [hcoeffZero, hcoeffOne, hcoeffTwo, hcoeffThree]
    ring_nf
    linear_combination
      (4 * Q.tau ^ 5 - 4 * Q.tau ^ 4 + 9 * Q.tau ^ 3 -
        24 * Q.tau ^ 2 - 3 * Q.tau + 23) * Q.tau_cubic
  · rw [degree_eq_natDegree normalizedRelativePolynomial_monic.ne_zero,
      normalizedRelativePolynomial_natDegree]
    norm_num

/-! ## A relative power basis with discriminant `-8` -/

private theorem normalizedRelativeRoot_satisfies_minpoly :
    Polynomial.aeval (AdjoinRoot.root normalizedRelativePolynomial)
      (minpoly Q.K normalizedRelativePowerBasis.gen) = 0 := by
  rw [normalizedRelativePowerBasis_gen,
    normalizedElement_minpoly_relative]
  rw [aeval_def, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root normalizedRelativePolynomial

private theorem normalizedRelativePowerBasis_root :
    Polynomial.aeval normalizedRelativePowerBasis.gen
      normalizedRelativePolynomial = 0 := by
  rw [normalizedRelativePowerBasis_gen]
  exact normalizedElement_relative_root

private def normalizedRelativeAdjoinRootEquiv :
    AdjoinRoot normalizedRelativePolynomial ≃ₐ[Q.K] M :=
  AdjoinRoot.equiv' normalizedRelativePolynomial normalizedRelativePowerBasis
    normalizedRelativeRoot_satisfies_minpoly
    normalizedRelativePowerBasis_root

@[simp]
private theorem normalizedRelativeAdjoinRootEquiv_root :
    normalizedRelativeAdjoinRootEquiv
        (AdjoinRoot.root normalizedRelativePolynomial) =
      normalizedElement := by
  change normalizedRelativeAdjoinRootEquiv.toAlgHom
      (AdjoinRoot.root normalizedRelativePolynomial) = normalizedElement
  rw [normalizedRelativeAdjoinRootEquiv, AdjoinRoot.equiv'_toAlgHom]
  calc
    _ = normalizedRelativePowerBasis.gen :=
      AdjoinRoot.liftAlgHom_root normalizedRelativePolynomial _ _ _
    _ = normalizedElement := normalizedRelativePowerBasis_gen

private def normalizedRelativeRootPowerBasis :
    PowerBasis Q.K (AdjoinRoot normalizedRelativePolynomial) :=
  AdjoinRoot.powerBasis normalizedRelativePolynomial_monic.ne_zero

private theorem normalizedRelativePolynomial_derivative_natDegree :
    normalizedRelativePolynomial.derivative.natDegree =
      normalizedRelativePolynomial.natDegree - 1 := by
  have hderivative : normalizedRelativePolynomial.derivative.natDegree = 2 := by
    simp only [normalizedRelativePolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_C,
      zero_mul, mul_one, Nat.cast_ofNat, derivative_one, sub_zero]
    compute_degree!
  rw [hderivative, normalizedRelativePolynomial_natDegree]

private theorem normalizedRelativeRootPowerBasis_discriminant :
    Algebra.discr Q.K normalizedRelativeRootPowerBasis.basis =
      normalizedRelativePolynomial.discr := by
  letI : Module.Finite Q.K (AdjoinRoot normalizedRelativePolynomial) :=
    normalizedRelativePolynomial_monic.finite_adjoinRoot
  letI : Algebra.IsAlgebraic Q.K
      (AdjoinRoot normalizedRelativePolynomial) :=
    ⟨fun x ↦ (IsIntegral.of_finite Q.K x).isAlgebraic⟩
  letI : Algebra.IsSeparable Q.K
      (AdjoinRoot normalizedRelativePolynomial) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AdjoinRoot.discr_powerBasis_eq_discr
    normalizedRelativePolynomial_monic
    normalizedRelativePolynomial_derivative_natDegree

/-- A relative power basis of the compositum, obtained from the explicit
relative cubic presentation. -/
def normalizedRelativeMappedPowerBasis : PowerBasis Q.K M :=
  normalizedRelativeRootPowerBasis.map normalizedRelativeAdjoinRootEquiv

@[simp]
theorem normalizedRelativeMappedPowerBasis_gen :
    normalizedRelativeMappedPowerBasis.gen = normalizedElement := by
  rw [normalizedRelativeMappedPowerBasis, PowerBasis.map_gen,
    normalizedRelativeRootPowerBasis, AdjoinRoot.powerBasis_gen,
    normalizedRelativeAdjoinRootEquiv_root]

/-- The explicit relative power basis has discriminant `-8`. -/
theorem normalizedRelativeMappedPowerBasis_discriminant :
    Algebra.discr Q.K normalizedRelativeMappedPowerBasis.basis = -8 := by
  rw [← normalizedRelativePolynomial_discriminant,
    ← normalizedRelativeRootPowerBasis_discriminant]
  exact (Algebra.discr_eq_discr_of_algEquiv
    normalizedRelativeRootPowerBasis.basis
    normalizedRelativeAdjoinRootEquiv).symm

/-! ## The integral relative polynomial -/

/-- The same relative polynomial over the coefficient ring of integers. -/
def normalizedRelativePolynomialInteger :
    Polynomial (NumberField.RingOfIntegers Q.K) :=
  X ^ 3 + C (coefficientInteger ^ 2 - 3) * X ^ 2 +
    C (-2 * coefficientInteger ^ 2 + coefficientInteger + 4) * X - 1

theorem normalizedRelativePolynomialInteger_monic :
    normalizedRelativePolynomialInteger.Monic := by
  simp only [normalizedRelativePolynomialInteger]
  monicity <;> norm_num

theorem normalizedRelativePolynomialInteger_map :
    normalizedRelativePolynomialInteger.map
        (algebraMap (NumberField.RingOfIntegers Q.K) Q.K) =
      normalizedRelativePolynomial := by
  have hcoefficient :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K
          coefficientInteger = Q.tau := rfl
  have htwo :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 2 = 2 := by
    exact map_ofNat _ 2
  have hthree :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 3 = 3 := by
    exact map_ofNat _ 3
  have hfour :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 4 = 4 := by
    exact map_ofNat _ 4
  simp [normalizedRelativePolynomialInteger,
    normalizedRelativePolynomial, hcoefficient, htwo, hthree, hfour]

/-- The displayed integral cubic is the minimal polynomial of the normalized
integer over the coefficient ring of integers. -/
theorem normalizedInteger_minpoly_relative :
    minpoly (NumberField.RingOfIntegers Q.K) normalizedInteger =
      normalizedRelativePolynomialInteger := by
  apply Polynomial.map_injective
    (algebraMap (NumberField.RingOfIntegers Q.K) Q.K)
    RingOfIntegers.coe_injective
  rw [normalizedRelativePolynomialInteger_map]
  have hInt : IsIntegral (NumberField.RingOfIntegers Q.K)
      normalizedInteger :=
    Algebra.IsIntegral.isIntegral (R := NumberField.RingOfIntegers Q.K)
      normalizedInteger
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions Q.K M
    hInt
  rw [← hfield]
  change minpoly Q.K normalizedElement = normalizedRelativePolynomial
  exact normalizedElement_minpoly_relative

/-! ## Relative conductor control at the coefficient prime -/

/-- The relative discriminant belongs to the conductor of the normalized
integral order. -/
theorem relative_discriminant_mem_conductor :
    algebraMap (NumberField.RingOfIntegers Q.K)
        (NumberField.RingOfIntegers M) (-8) ∈
      conductor (NumberField.RingOfIntegers Q.K) normalizedInteger := by
  have hfield :
      algebraMap (NumberField.RingOfIntegers M) M
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M) (-8)) ∈
        IsLocalization.coeSubmodule M
          (conductor (NumberField.RingOfIntegers Q.K)
            normalizedInteger) := by
    rw [mem_coeSubmodule_conductor]
    intro z
    have hgen : IsIntegral (NumberField.RingOfIntegers Q.K)
        normalizedRelativeMappedPowerBasis.gen := by
      rw [normalizedRelativeMappedPowerBasis_gen]
      exact normalizedElement_isIntegral_int.tower_top
    have hz : IsIntegral (NumberField.RingOfIntegers Q.K) (z : M) :=
      (RingOfIntegers.isIntegral_coe z).tower_top
    have hdisc := Algebra.discr_mul_isIntegral_mem_adjoin Q.K
      (B := normalizedRelativeMappedPowerBasis) hgen hz
    rw [normalizedRelativeMappedPowerBasis_discriminant] at hdisc
    simpa only [normalizedRelativeMappedPowerBasis_gen,
      normalizedInteger_coe, Algebra.smul_def,
      RingOfIntegers.coe_eq_algebraMap, map_intCast, map_neg, map_ofNat,
      IsScalarTower.algebraMap_apply ℤ Q.K M,
      IsScalarTower.algebraMap_apply
        (NumberField.RingOfIntegers Q.K)
        (NumberField.RingOfIntegers M) M] using hdisc
  obtain ⟨z, hz, hzmap⟩ :=
    (IsLocalization.mem_coeSubmodule M
      (conductor (NumberField.RingOfIntegers Q.K)
        normalizedInteger)).mp hfield
  have hz' : z = algebraMap (NumberField.RingOfIntegers Q.K)
      (NumberField.RingOfIntegers M) (-8) :=
    RingOfIntegers.coe_injective hzmap
  simpa only [hz'] using hz

/-- The normalized relative order has conductor coprime to the unique
coefficient prime above `3`. -/
theorem relative_conductor_coprime_at_three :
    (conductor (NumberField.RingOfIntegers Q.K) normalizedInteger).comap
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M)) ⊔
        Ideal.span {coefficientTriadicUniformizer} = ⊤ := by
  let I : Ideal (NumberField.RingOfIntegers Q.K) :=
    Ideal.span {coefficientTriadicUniformizer}
  have hIne : I ≠ ⊥ := by
    intro hbot
    have hnorm := coefficientTriadicPrime_absNorm
    change Ideal.absNorm I = 3 at hnorm
    rw [hbot, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm
  have hImax : I.IsMaximal :=
    coefficientTriadicPrime_isPrime.isMaximal hIne
  have hminusEightComap :
      (-8 : NumberField.RingOfIntegers Q.K) ∈
        (conductor (NumberField.RingOfIntegers Q.K)
          normalizedInteger).comap
            (algebraMap (NumberField.RingOfIntegers Q.K)
              (NumberField.RingOfIntegers M)) :=
    relative_discriminant_mem_conductor
  have hthree : (3 : NumberField.RingOfIntegers Q.K) ∈ I := by
    apply (Ideal.span_singleton_le_iff_mem I).mp
    rw [coefficient_span_three_eq_uniformizer_cube]
    exact Ideal.pow_le_self (by norm_num)
  have hminusEightNot :
      (-8 : NumberField.RingOfIntegers Q.K) ∉ I := by
    intro hminusEight
    have hnine : (9 : NumberField.RingOfIntegers Q.K) ∈ I := by
      convert I.mul_mem_left 3 hthree using 1
      norm_num
    have hone : (1 : NumberField.RingOfIntegers Q.K) ∈ I := by
      convert I.add_mem hnine hminusEight using 1
      norm_num
    exact coefficientTriadicPrime_isPrime.ne_top
      ((Ideal.eq_top_iff_one I).mpr hone)
  by_contra hsup
  have heq : I =
      (conductor (NumberField.RingOfIntegers Q.K)
          normalizedInteger).comap
            (algebraMap (NumberField.RingOfIntegers Q.K)
              (NumberField.RingOfIntegers M)) ⊔ I :=
    hImax.eq_of_le hsup le_sup_right
  apply hminusEightNot
  have hle :
      (conductor (NumberField.RingOfIntegers Q.K)
          normalizedInteger).comap
            (algebraMap (NumberField.RingOfIntegers Q.K)
              (NumberField.RingOfIntegers M)) ≤ I := by
    rw [heq]
    exact le_sup_left
  exact hle hminusEightComap

/-! ## Irreducible reduction at the triadic coefficient prime -/

private theorem coefficientTriadicIdeal_ne_bot :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)) ≠ ⊥ := by
  intro hbot
  have hnorm := coefficientTriadicPrime_absNorm
  rw [hbot, Ideal.absNorm_bot] at hnorm
  norm_num at hnorm

private instance coefficientTriadicIdeal_isMaximal :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).IsMaximal :=
  coefficientTriadicPrime_isPrime.isMaximal coefficientTriadicIdeal_ne_bot

/-- The residue field of the coefficient field at its unique triadic prime. -/
abbrev CoefficientTriadicResidue :=
  NumberField.RingOfIntegers Q.K ⧸
    Ideal.span {coefficientTriadicUniformizer}

noncomputable instance coefficientTriadicResidue_fintype :
    Fintype CoefficientTriadicResidue := Fintype.ofFinite _

private theorem coefficientTriadicResidue_card :
    Fintype.card CoefficientTriadicResidue = 3 := by
  rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply]
  exact coefficientTriadicPrime_absNorm

/-- The coefficient residue field is canonically identified with `ZMod 3`. -/
noncomputable def coefficientTriadicResidueEquiv :
    ZMod 3 ≃+* CoefficientTriadicResidue :=
  ZMod.ringEquivOfPrime CoefficientTriadicResidue Nat.prime_three
    coefficientTriadicResidue_card

private instance coefficientTriadicResidue_charP :
    CharP CoefficientTriadicResidue 3 :=
  CharP.of_ringHom_of_ne_zero
    coefficientTriadicResidueEquiv.toRingHom 3 (by norm_num)

private theorem coefficientInteger_mod_triadic :
    Ideal.Quotient.mk (Ideal.span {coefficientTriadicUniformizer})
        coefficientInteger = 1 := by
  apply Ideal.Quotient.eq.mpr
  change coefficientInteger - 1 ∈
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K))
  exact Ideal.mem_span_singleton_self coefficientTriadicUniformizer

/-- The irreducible cubic obtained by reducing the relative polynomial at
the coefficient prime above `3`. -/
def triadicResiduePolynomial : Polynomial (ZMod 3) :=
  X ^ 3 + X ^ 2 - 1

theorem triadicResiduePolynomial_irreducible :
    Irreducible triadicResiduePolynomial := by
  have hdegree : triadicResiduePolynomial.natDegree = 3 := by
    simp only [triadicResiduePolynomial]
    compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := triadicResiduePolynomial) ?_ ?_
  · rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [triadicResiduePolynomial, eval_sub, eval_add, eval_pow,
      eval_X, eval_one]
    fin_cases z <;> decide

/-- Exact reduction of the relative integral minimal polynomial at the
triadic coefficient prime. -/
theorem normalizedInteger_minpoly_mod_triadic :
    Polynomial.map
        (Ideal.Quotient.mk
          (Ideal.span {coefficientTriadicUniformizer}))
        (minpoly (NumberField.RingOfIntegers Q.K) normalizedInteger) =
      Polynomial.mapEquiv coefficientTriadicResidueEquiv
        triadicResiduePolynomial := by
  rw [normalizedInteger_minpoly_relative]
  simp only [normalizedRelativePolynomialInteger,
    triadicResiduePolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X,
    Polynomial.map_C, Polynomial.mapEquiv_apply]
  simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  rw [coefficientInteger_mod_triadic]
  simp only [one_pow, mul_one, C_1]
  linear_combination
    (X - X ^ 2) *
      (CharP.cast_eq_zero (Polynomial CoefficientTriadicResidue) 3)

/-- The reduced relative minimal polynomial is irreducible. -/
theorem normalizedInteger_minpoly_mod_triadic_irreducible :
    Irreducible
      (Polynomial.map
        (Ideal.Quotient.mk
          (Ideal.span {coefficientTriadicUniformizer}))
        (minpoly (NumberField.RingOfIntegers Q.K) normalizedInteger)) := by
  rw [normalizedInteger_minpoly_mod_triadic]
  exact triadicResiduePolynomial_irreducible.map
    (Polynomial.mapEquiv coefficientTriadicResidueEquiv)

/-! ## The unique triadic prime in the compositum -/

/-- The coefficient prime remains irreducible after extension to the
compositum. -/
theorem coefficientTriadicIdeal_map_irreducible :
    Irreducible
      ((Ideal.span {coefficientTriadicUniformizer} :
        Ideal (NumberField.RingOfIntegers Q.K)).map
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M))) := by
  exact KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly
    coefficientTriadicIdeal_isMaximal coefficientTriadicIdeal_ne_bot
    relative_conductor_coprime_at_three
    (Algebra.IsIntegral.isIntegral
      (R := NumberField.RingOfIntegers Q.K) normalizedInteger)
    normalizedInteger_minpoly_mod_triadic_irreducible

/-- The extended coefficient prime is a prime ideal of the compositum. -/
theorem coefficientTriadicIdeal_map_isPrime :
    ((Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).map
        (algebraMap (NumberField.RingOfIntegers Q.K)
          (NumberField.RingOfIntegers M))).IsPrime := by
  apply Ideal.isPrime_of_prime
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
    coefficientTriadicIdeal_map_irreducible

/-- Extending the coefficient prime gives exactly the principal ideal
generated by `rho`. -/
theorem coefficientTriadicIdeal_map_eq_span_rho :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).map
        (algebraMap (NumberField.RingOfIntegers Q.K)
          (NumberField.RingOfIntegers M)) =
      Ideal.span {rhoInteger} := by
  have hmap := congrArg
    (Ideal.map (algebraMap (NumberField.RingOfIntegers Q.K)
      (NumberField.RingOfIntegers M)))
    coefficient_span_three_eq_uniformizer_cube
  have hcubes :
      ((Ideal.span {coefficientTriadicUniformizer} :
        Ideal (NumberField.RingOfIntegers Q.K)).map
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M))) ^ 3 =
        Ideal.span {rhoInteger} ^ 3 := by
    calc
      _ = Ideal.span {(3 : NumberField.RingOfIntegers M)} := by
        symm
        simpa only [Ideal.map_span, Set.image_singleton, map_ofNat,
          Ideal.map_pow] using hmap
      _ = Ideal.span {rhoInteger} ^ 3 :=
        span_three_eq_span_rho_cube
  exact pow_left_injective (by norm_num : 3 ≠ 0) hcubes

/-- Every prime of the compositum above `3` is the displayed principal
ideal generated by `rho`. -/
theorem compositum_prime_over_three_eq_span_rho
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(3 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    P = Ideal.span {rhoInteger} := by
  have hprime : Prime P :=
    Ideal.prime_of_mem_primesOver (by norm_num) hP
  letI : (Ideal.span {(3 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 3
  have hPthree : P ∣
      Ideal.span {(3 : NumberField.RingOfIntegers M)} := by
    have hmap := (Ideal.liesOver_iff_dvd_map hP.1.ne_top).mp hP.2
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hmap
  rw [span_three_eq_span_rho_cube] at hPthree
  have hPrho : P ∣ Ideal.span {rhoInteger} :=
    hprime.dvd_of_dvd_pow hPthree
  have hspanPrime : (Ideal.span {rhoInteger} :
      Ideal (NumberField.RingOfIntegers M)).IsPrime := by
    rw [← coefficientTriadicIdeal_map_eq_span_rho]
    exact coefficientTriadicIdeal_map_isPrime
  have hspanNeBot : (Ideal.span {rhoInteger} :
      Ideal (NumberField.RingOfIntegers M)) ≠ ⊥ := by
    rw [← coefficientTriadicIdeal_map_eq_span_rho]
    exact (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      coefficientTriadicIdeal_map_irreducible).ne_zero
  exact (hspanPrime.isMaximal hspanNeBot).eq_of_le hP.1.ne_top
    (Ideal.dvd_iff_le.mp hPrho) |>.symm

end

end MazurTorsion.XOneEighteenTwoDivisionTriadicLift
