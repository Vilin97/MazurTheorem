/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionMinkowski
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes

/-!
# Principal ideals above the small ramified primes in the `X₁(18)` compositum

The integral quotients constructed in
`XOneEighteenTwoDivisionIntegralElements` are units.  This is verified by
explicit integral Bezout inverses modulo the normalized degree-nine
polynomial.  Consequently the advertised element factorizations give exact
ideal identities

`(2) = (alpha) * (beta)^2` and `(3) = (rho)^3`.

No maximal-order assertion about the normalized power order is used.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## Explicit inverses for the two integral quotients -/

/-- An inverse of `beta^2 * alpha / 2` in the normalized integral order. -/
def dyadicQuotientInversePolynomialInt : Polynomial ℤ :=
  4 * X ^ 8 - 14 * X ^ 7 + 7 * X ^ 6 + 25 * X ^ 5 -
    26 * X ^ 4 - 22 * X ^ 3 + 24 * X ^ 2 + 10 * X - 5

private def dyadicQuotientBezoutPolynomialInt : Polynomial ℤ :=
  -8 * X ^ 7 + 28 * X ^ 6 - 22 * X ^ 5 - 26 * X ^ 4 +
    44 * X ^ 3 + 7 * X ^ 2 - 15 * X + 6

private theorem dyadicQuotient_bezout_identity :
    dyadicQuotientPolynomialInt * dyadicQuotientInversePolynomialInt =
      1 + dyadicQuotientBezoutPolynomialInt * normalizedPolynomialInt := by
  simp only [dyadicQuotientPolynomialInt,
    dyadicQuotientInversePolynomialInt,
    dyadicQuotientBezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-- The explicit inverse of the dyadic quotient in the full ring of
integers. -/
def dyadicQuotientInverseInteger : NumberField.RingOfIntegers M :=
  Polynomial.aeval normalizedInteger dyadicQuotientInversePolynomialInt

private theorem dyadicQuotientInteger_eq_aeval :
    dyadicQuotientInteger =
      Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change (dyadicQuotientInteger : M) =
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      (Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      normalizedInteger dyadicQuotientPolynomialInt]
  simpa only [dyadicQuotientInteger_coe, normalizedInteger_coe,
    IsScalarTower.toAlgHom_apply] using beta_sq_mul_alpha_div_two_formula

theorem dyadicQuotientInteger_mul_inverse :
    dyadicQuotientInteger * dyadicQuotientInverseInteger = 1 := by
  rw [dyadicQuotientInteger_eq_aeval, dyadicQuotientInverseInteger,
    ← map_mul, dyadicQuotient_bezout_identity]
  simp only [map_add, map_one, map_mul, normalizedInteger_aeval,
    mul_zero, add_zero]

/-- The integral quotient `beta^2 * alpha / 2` is a unit. -/
theorem dyadicQuotientInteger_isUnit : IsUnit dyadicQuotientInteger := by
  exact ⟨⟨dyadicQuotientInteger, dyadicQuotientInverseInteger,
    dyadicQuotientInteger_mul_inverse,
    by rw [mul_comm, dyadicQuotientInteger_mul_inverse]⟩, rfl⟩

/-- An inverse of `rho^3 / 3` in the normalized integral order. -/
def triadicQuotientInversePolynomialInt : Polynomial ℤ :=
  X ^ 8 - 4 * X ^ 7 + 4 * X ^ 6 + 3 * X ^ 5 -
    7 * X ^ 4 - X ^ 3 + 5 * X ^ 2 - 1

private def triadicQuotientBezoutPolynomialInt : Polynomial ℤ :=
  -3 * X ^ 7 + 13 * X ^ 6 - 16 * X ^ 5 - 5 * X ^ 4 +
    25 * X ^ 3 - 8 * X ^ 2 - 11 * X + 4

private theorem triadicQuotient_bezout_identity :
    triadicQuotientPolynomialInt * triadicQuotientInversePolynomialInt =
      1 + triadicQuotientBezoutPolynomialInt * normalizedPolynomialInt := by
  simp only [triadicQuotientPolynomialInt,
    triadicQuotientInversePolynomialInt,
    triadicQuotientBezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-- The explicit inverse of the triadic quotient in the full ring of
integers. -/
def triadicQuotientInverseInteger : NumberField.RingOfIntegers M :=
  Polynomial.aeval normalizedInteger triadicQuotientInversePolynomialInt

private theorem triadicQuotientInteger_eq_aeval :
    triadicQuotientInteger =
      Polynomial.aeval normalizedInteger triadicQuotientPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change (triadicQuotientInteger : M) =
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      (Polynomial.aeval normalizedInteger triadicQuotientPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      normalizedInteger triadicQuotientPolynomialInt]
  simpa only [triadicQuotientInteger_coe, normalizedInteger_coe,
    IsScalarTower.toAlgHom_apply] using rho_cube_div_three_formula

theorem triadicQuotientInteger_mul_inverse :
    triadicQuotientInteger * triadicQuotientInverseInteger = 1 := by
  rw [triadicQuotientInteger_eq_aeval, triadicQuotientInverseInteger,
    ← map_mul, triadicQuotient_bezout_identity]
  simp only [map_add, map_one, map_mul, normalizedInteger_aeval,
    mul_zero, add_zero]

/-- The integral quotient `rho^3 / 3` is a unit. -/
theorem triadicQuotientInteger_isUnit : IsUnit triadicQuotientInteger := by
  exact ⟨⟨triadicQuotientInteger, triadicQuotientInverseInteger,
    triadicQuotientInteger_mul_inverse,
    by rw [mul_comm, triadicQuotientInteger_mul_inverse]⟩, rfl⟩

/-! ## Exact principal-ideal factorizations -/

private theorem dyadic_element_factorization :
    betaInteger ^ 2 * alphaInteger =
      dyadicQuotientInteger * (2 : NumberField.RingOfIntegers M) := by
  apply RingOfIntegers.coe_injective
  simp only [map_mul, map_pow, betaInteger_coe, alphaInteger_coe,
    dyadicQuotientInteger_coe, map_ofNat]
  field_simp

/-- Exact factorization of the rational dyadic ideal in the compositum. -/
theorem span_two_eq_span_alpha_mul_span_beta_sq :
    Ideal.span {(2 : NumberField.RingOfIntegers M)} =
      Ideal.span {alphaInteger} * Ideal.span {betaInteger} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
    mul_comm alphaInteger (betaInteger ^ 2), dyadic_element_factorization]
  exact (Ideal.span_singleton_mul_left_unit dyadicQuotientInteger_isUnit 2).symm

private theorem triadic_element_factorization :
    rhoInteger ^ 3 =
      triadicQuotientInteger * (3 : NumberField.RingOfIntegers M) := by
  apply RingOfIntegers.coe_injective
  simp only [map_pow, rhoInteger_coe, triadicQuotientInteger_coe, map_mul,
    map_ofNat]
  field_simp

/-- Exact total-cube factorization of the rational triadic ideal in the
compositum. -/
theorem span_three_eq_span_rho_cube :
    Ideal.span {(3 : NumberField.RingOfIntegers M)} =
      Ideal.span {rhoInteger} ^ 3 := by
  rw [Ideal.span_singleton_pow, triadic_element_factorization]
  exact (Ideal.span_singleton_mul_left_unit triadicQuotientInteger_isUnit 3).symm

/-! ## Absolute norms of the three generators -/

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim]

private theorem absolute_norm_alpha : Algebra.norm ℚ alpha = 8 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := Q.K), norm_alpha]
  change Algebra.norm ℚ (algebraMap ℚ Q.K 2) = 8
  rw [Algebra.norm_algebraMap, coefficientField_finrank]
  norm_num

private theorem integer_norm_alphaInteger :
    Algebra.norm ℤ alphaInteger = 8 := by
  apply Rat.intCast_inj.mp
  rw [Algebra.coe_norm_int]
  simpa only [alphaInteger_coe, Int.cast_ofNat] using absolute_norm_alpha

/-- The first dyadic principal ideal has absolute norm `8`. -/
theorem absNorm_span_alpha :
    Ideal.absNorm (Ideal.span {alphaInteger}) = 8 := by
  rw [Ideal.absNorm_span_singleton, integer_norm_alphaInteger]
  norm_num

/-- The second dyadic principal ideal also has absolute norm `8`. -/
theorem absNorm_span_beta :
    Ideal.absNorm (Ideal.span {betaInteger}) = 8 := by
  have htwo : Ideal.absNorm
      (Ideal.span {(2 : NumberField.RingOfIntegers M)}) = 512 := by
    calc
      Ideal.absNorm
          (Ideal.span {(2 : NumberField.RingOfIntegers M)}) =
        2 ^ Module.finrank ℤ (NumberField.RingOfIntegers M) := by
          simpa using
            (Ideal.absNorm_span_natCast
              (S := NumberField.RingOfIntegers M) 2)
      _ = 512 := by
        rw [RingOfIntegers.rank, finrank_M_over_rat]
        norm_num
  have h := congrArg Ideal.absNorm span_two_eq_span_alpha_mul_span_beta_sq
  rw [htwo, map_mul, map_pow, absNorm_span_alpha] at h
  have hpow : Ideal.absNorm (Ideal.span {betaInteger}) ^ 2 = 8 ^ 2 := by
    norm_num at h ⊢
    omega
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) hpow

/-- The triadic principal ideal has absolute norm `27`. -/
theorem absNorm_span_rho :
    Ideal.absNorm (Ideal.span {rhoInteger}) = 27 := by
  have hthree : Ideal.absNorm
      (Ideal.span {(3 : NumberField.RingOfIntegers M)}) = 19683 := by
    calc
      Ideal.absNorm
          (Ideal.span {(3 : NumberField.RingOfIntegers M)}) =
        3 ^ Module.finrank ℤ (NumberField.RingOfIntegers M) := by
          simpa using
            (Ideal.absNorm_span_natCast
              (S := NumberField.RingOfIntegers M) 3)
      _ = 19683 := by
        rw [RingOfIntegers.rank, finrank_M_over_rat]
        norm_num
  have h := congrArg Ideal.absNorm span_three_eq_span_rho_cube
  rw [hthree, map_pow] at h
  have hpow : Ideal.absNorm (Ideal.span {rhoInteger}) ^ 3 = 27 ^ 3 := by
    norm_num at h ⊢
    exact h.symm
  exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) hpow

/-! ## Dyadic inertia -/

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_two_irreducible :
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

private theorem coefficient_exponent_not_dvd_two :
    ¬ 2 ∣ RingOfIntegers.exponent coefficientInteger := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {(81 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers Q.K))
        (conductor ℤ coefficientInteger) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact coefficient_discriminant_mem_conductor
  exact ((Ideal.isCoprime_span_singleton_iff (81 : ℤ) (2 : ℤ)).mpr
    (by norm_num)).codisjoint.mono_left hspan

private theorem coefficient_inertiaDeg_eq_three_at_two
    (P : Ideal (NumberField.RingOfIntegers Q.K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers Q.K)) :
    P.inertiaDeg ℤ = 3 := by
  have hirr : Irreducible
      ((minpoly ℤ coefficientInteger).map (Int.castRingHom (ZMod 2))) := by
    rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod]
    exact coefficientPolynomialMod_two_irreducible
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    coefficient_exponent_not_dvd_two
  have hfactor := (e ⟨P, hP⟩).2
  have hdegree :=
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      coefficient_exponent_not_dvd_two hfactor
  simp only [Subtype.coe_eta] at hdegree
  change (e ⟨P, hP⟩ : Polynomial (ZMod 2)) ∈
      (normalizedFactors
        ((minpoly ℤ coefficientInteger).map
          (Int.castRingHom (ZMod 2)))).toFinset at hfactor
  rw [normalizedFactors_irreducible hirr,
    (minpoly.monic coefficientInteger.isIntegral).map
      (Int.castRingHom (ZMod 2)) |>.normalize_eq_self] at hfactor
  simp only [Multiset.toFinset_singleton, Finset.mem_singleton] at hfactor
  rw [hfactor] at hdegree
  have heq := e.symm_apply_apply ⟨P, hP⟩
  have hideal : ((e.symm (e ⟨P, hP⟩)).1 :
      Ideal (NumberField.RingOfIntegers Q.K)) = P :=
    congrArg Subtype.val heq
  rw [hideal] at hdegree
  rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod] at hdegree
  have hnatDegree : (coefficientPolynomialMod 2).natDegree = 3 := by
    simp only [coefficientPolynomialMod]
    compute_degree!
  exact hdegree.trans hnatDegree

/-- Every prime of the compositum above `2` has inertia degree at least
three. -/
theorem compositum_inertiaDeg_ge_three_at_two
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    3 ≤ P.inertiaDeg ℤ := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  let QP : Ideal (NumberField.RingOfIntegers Q.K) :=
    P.under (NumberField.RingOfIntegers Q.K)
  have hQP : QP ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers Q.K) := ⟨inferInstance, inferInstance⟩
  have hdegree : QP.inertiaDeg ℤ = 3 :=
    coefficient_inertiaDeg_eq_three_at_two QP hQP
  have htower := Ideal.inertiaDeg_tower (R := ℤ) QP P
  rw [hdegree] at htower
  exact Nat.le_of_dvd (P.inertiaDeg_pos ℤ)
    ⟨P.inertiaDeg (NumberField.RingOfIntegers Q.K), htower⟩

/-- Every prime of the compositum above `2` has absolute norm at least
`8`. -/
theorem eight_le_absNorm_of_mem_primesOver_two
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    8 ≤ P.absNorm := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg 2 P]
  exact pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ))
    (compositum_inertiaDeg_ge_three_at_two P hP)

private theorem eq_of_dvd_of_eight_le_absNorm
    {P I : Ideal (NumberField.RingOfIntegers M)}
    (hdiv : P ∣ I) (hP : 8 ≤ P.absNorm) (hI : I.absNorm = 8) :
    P = I := by
  have hle : I ≤ P := Ideal.dvd_iff_le.mp hdiv
  have hnormDvd : P.absNorm ∣ I.absNorm :=
    Ideal.absNorm_dvd_absNorm_of_le hle
  have hPupper : P.absNorm ≤ 8 := by
    rw [← hI]
    exact Nat.le_of_dvd (hI.symm ▸ by norm_num) hnormDvd
  have hPnorm : P.absNorm = 8 := le_antisymm hPupper hP
  obtain ⟨J, hJ⟩ := hdiv
  have hnorm := congrArg Ideal.absNorm hJ
  rw [map_mul, hPnorm, hI] at hnorm
  have hJnorm : J.absNorm = 1 := by omega
  have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJnorm
  rw [hJtop, mul_top] at hJ
  exact hJ.symm

/-- The two displayed principal ideals are all the primes of the compositum
above `2`. -/
theorem prime_over_two_eq_span_alpha_or_beta
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    P = Ideal.span {alphaInteger} ∨ P = Ideal.span {betaInteger} := by
  have hprime : Prime P :=
    Ideal.prime_of_mem_primesOver (by norm_num) hP
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  have hPtwo : P ∣ Ideal.span
      {(2 : NumberField.RingOfIntegers M)} := by
    have hmap :=
      (Ideal.liesOver_iff_dvd_map hP.1.ne_top).mp hP.2
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hmap
  have hprod : P ∣
      Ideal.span {alphaInteger} * Ideal.span {betaInteger} ^ 2 := by
    rw [← span_two_eq_span_alpha_mul_span_beta_sq]
    exact hPtwo
  have hlower := eight_le_absNorm_of_mem_primesOver_two P hP
  rcases hprime.dvd_or_dvd hprod with hAlpha | hBetaSq
  · exact Or.inl
      (eq_of_dvd_of_eight_le_absNorm hAlpha hlower absNorm_span_alpha)
  · have hBeta : P ∣ Ideal.span {betaInteger} :=
      hprime.dvd_of_dvd_pow hBetaSq
    exact Or.inr
      (eq_of_dvd_of_eight_le_absNorm hBeta hlower absNorm_span_beta)

end

end MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
