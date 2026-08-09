/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionClassNumber
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-!
# Small rational primes in the `X₁(18)` two-division compositum

This file gives the tame part of a class-number certificate for the
degree-nine two-division compositum.  For each rational prime between `5`
and `31`, one of the two cubic subfields is inert.  Contraction to that
subfield and multiplicativity of inertia degrees therefore show that every
prime of the compositum above it has inertia degree at least three.

The use of Kummer--Dedekind is unconditional: the two exact rational
power-basis discriminants are first put in the relevant conductors, which
proves that the Kummer--Dedekind exponents are prime to every prime under
consideration.  No maximal-order or class-number computation is assumed.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The two rational cubic power bases -/

theorem coefficientPolynomial_monic : Q.cubicPolynomial.Monic := by
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  monicity <;> norm_num

/-- The rational power basis of the real cubic coefficient field. -/
def coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic

theorem twoDivisionPolynomial_monic : twoDivisionPolynomial.Monic := by
  simp only [twoDivisionPolynomial]
  monicity <;> norm_num

/-- The rational power basis of the two-division cubic field. -/
def twoDivisionPowerBasis : PowerBasis ℚ F :=
  AdjoinRoot.powerBasis' twoDivisionPolynomial_monic

theorem coefficientPowerBasis_minpolyGen :
    coefficientPowerBasis.minpolyGen = Q.cubicPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval Q.tau Q.cubicPolynomial = 0 := by
    simp only [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
    linear_combination Q.tau_cubic
  exact (minpoly.eq_of_irreducible_of_monic Q.cubicPolynomial_irreducible
    hroot coefficientPolynomial_monic).symm

theorem twoDivisionPowerBasis_minpolyGen :
    twoDivisionPowerBasis.minpolyGen = twoDivisionPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval sigma twoDivisionPolynomial = 0 := by
    simp only [twoDivisionPolynomial, map_sub, map_pow, aeval_X,
      map_mul, map_ofNat]
    linear_combination sigma_cubic
  exact (minpoly.eq_of_irreducible_of_monic twoDivisionPolynomial_irreducible
    hroot twoDivisionPolynomial_monic).symm

theorem coefficientPowerBasis_dim : coefficientPowerBasis.dim = 3 := by
  rw [coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!

theorem twoDivisionPowerBasis_dim : twoDivisionPowerBasis.dim = 3 := by
  rw [twoDivisionPowerBasis, AdjoinRoot.powerBasis'_dim]
  exact twoDivisionPolynomial_natDegree

private theorem norm_cubic_derivative
    {L : Type*} [CommRing L] [Algebra ℚ L]
    (pb : PowerBasis ℚ L) (hdim : pb.dim = 3) (d : ℚ)
    (hmin : pb.minpolyGen = X ^ 3 - 3 * X - C d) :
    Algebra.norm ℚ (3 * pb.gen ^ 2 - 3) = 27 * (d ^ 2 - 4) := by
  rw [Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [pb.leftMulMatrix, hmin]
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) ℚ :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -(X ^ 3 - 3 * X - C d).coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3 *
        companion ^ 2 -
      algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3) = _
  have hcompanion :
      Matrix.reindexAlgEquiv ℚ ℚ e companion =
        !![0, 0, d; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, coeff_sub, coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv ℚ (R := ℚ) e]
  rw [map_sub, map_mul, map_pow]
  rw [(Matrix.reindexAlgEquiv ℚ ℚ e).commutes 3, hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring

/-- The exact rational power-basis discriminant of the coefficient cubic. -/
theorem coefficientPowerBasis_discriminant :
    Algebra.discr ℚ coefficientPowerBasis.basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, coefficientPowerBasis_minpolyGen]
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
    derivative_sub, derivative_pow, derivative_X, derivative_mul,
    derivative_ofNat, derivative_one, mul_one, Nat.cast_ofNat,
    zero_mul, sub_zero]
  rw [show coefficientPowerBasis.gen = Q.tau by rfl]
  have hnorm := norm_cubic_derivative coefficientPowerBasis
    coefficientPowerBasis_dim 1 (by
      simpa only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
        C_1] using coefficientPowerBasis_minpolyGen)
  rw [show coefficientPowerBasis.gen = Q.tau by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]
  norm_num

/-- The exact rational power-basis discriminant of the two-division cubic. -/
theorem twoDivisionPowerBasis_discriminant :
    Algebra.discr ℚ twoDivisionPowerBasis.basis = -2592 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [twoDivisionPowerBasis.finrank, twoDivisionPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, twoDivisionPowerBasis_minpolyGen]
  simp only [twoDivisionPolynomial, derivative_sub, derivative_pow,
    derivative_X, derivative_mul, derivative_ofNat, mul_one,
    Nat.cast_ofNat, zero_mul, sub_zero]
  rw [show twoDivisionPowerBasis.gen = sigma by rfl]
  have hnorm := norm_cubic_derivative twoDivisionPowerBasis
    twoDivisionPowerBasis_dim 10 (by
      simpa only [twoDivisionPolynomial, Polynomial.C_ofNat] using
        twoDivisionPowerBasis_minpolyGen)
  rw [show twoDivisionPowerBasis.gen = sigma by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]

/-! ## Integral generators and their conductors -/

/-- The integral polynomial `X³ - 3X - 1`. -/
def coefficientPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 1

theorem coefficientPolynomialInt_monic : coefficientPolynomialInt.Monic := by
  simp only [coefficientPolynomialInt]
  monicity <;> norm_num

theorem coefficientPolynomialInt_irreducible :
    Irreducible coefficientPolynomialInt := by
  apply coefficientPolynomialInt_monic.irreducible_of_irreducible_map
    (algebraMap ℤ ℚ)
  rw [show coefficientPolynomialInt.map (algebraMap ℤ ℚ) =
    Q.cubicPolynomial by
      norm_num [coefficientPolynomialInt, Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]]
  exact Q.cubicPolynomial_irreducible

private theorem coefficientPolynomialInt_aeval_tau :
    Polynomial.aeval Q.tau coefficientPolynomialInt = 0 := by
  simp only [coefficientPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat, map_one]
  linear_combination Q.tau_cubic

/-- The coefficient-field generator as an algebraic integer. -/
def coefficientInteger : 𝓞 Q.K :=
  ⟨Q.tau, ⟨coefficientPolynomialInt, coefficientPolynomialInt_monic,
    coefficientPolynomialInt_aeval_tau⟩⟩

theorem coefficientInteger_minpoly :
    minpoly ℤ coefficientInteger = coefficientPolynomialInt := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions ℚ Q.K
    coefficientInteger.isIntegral
  have hmin := coefficientPowerBasis_minpolyGen
  rw [PowerBasis.minpolyGen_eq] at hmin
  change minpoly ℚ Q.tau = Q.cubicPolynomial at hmin
  rw [← hfield]
  change minpoly ℚ Q.tau = _
  rw [hmin]
  norm_num [coefficientInteger, coefficientPolynomialInt, Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]

/-- The integral polynomial `X³ - 3X - 10`. -/
def twoDivisionPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 10

theorem twoDivisionPolynomialInt_monic : twoDivisionPolynomialInt.Monic := by
  simp only [twoDivisionPolynomialInt]
  monicity <;> norm_num

theorem twoDivisionPolynomialInt_irreducible :
    Irreducible twoDivisionPolynomialInt := by
  apply twoDivisionPolynomialInt_monic.irreducible_of_irreducible_map
    (algebraMap ℤ ℚ)
  rw [show twoDivisionPolynomialInt.map (algebraMap ℤ ℚ) =
    twoDivisionPolynomial by
      norm_num [twoDivisionPolynomialInt, twoDivisionPolynomial]]
  exact twoDivisionPolynomial_irreducible

private theorem twoDivisionPolynomialInt_aeval_sigma :
    Polynomial.aeval sigma twoDivisionPolynomialInt = 0 := by
  simp only [twoDivisionPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat]
  linear_combination sigma_cubic

/-- The two-division generator as an algebraic integer. -/
def twoDivisionInteger : 𝓞 F :=
  ⟨sigma, ⟨twoDivisionPolynomialInt, twoDivisionPolynomialInt_monic,
    twoDivisionPolynomialInt_aeval_sigma⟩⟩

theorem twoDivisionInteger_minpoly :
    minpoly ℤ twoDivisionInteger = twoDivisionPolynomialInt := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions ℚ F
    twoDivisionInteger.isIntegral
  have hmin := twoDivisionPowerBasis_minpolyGen
  rw [PowerBasis.minpolyGen_eq] at hmin
  change minpoly ℚ sigma = twoDivisionPolynomial at hmin
  rw [← hfield]
  change minpoly ℚ sigma = _
  rw [hmin]
  norm_num [twoDivisionInteger, twoDivisionPolynomialInt, twoDivisionPolynomial]

private theorem integer_discriminant_mem_conductor
    {L : Type*} [Field L] [NumberField L]
    (B : PowerBasis ℚ L) (theta : 𝓞 L)
    (hgen : B.gen = (theta : L)) (d : ℤ)
    (hdisc : Algebra.discr ℚ B.basis = (d : ℚ)) :
    (d : 𝓞 L) ∈ conductor ℤ theta := by
  have hfield :
      algebraMap (𝓞 L) L (d : 𝓞 L) ∈
        IsLocalization.coeSubmodule L (conductor ℤ theta) := by
    rw [mem_coeSubmodule_conductor]
    intro z
    have hz := Algebra.discr_mul_isIntegral_mem_adjoin ℚ
      (B := B) (by simpa only [hgen] using theta.isIntegral_coe)
      z.isIntegral_coe
    rw [hdisc] at hz
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_intCast,
      hgen, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ ℚ L] using hz
  obtain ⟨z, hz, hzmap⟩ :=
    (IsLocalization.mem_coeSubmodule L (conductor ℤ theta)).mp hfield
  have hz' : z = (d : 𝓞 L) := RingOfIntegers.coe_injective hzmap
  simpa only [hz'] using hz

/-- The integer `81` lies in the conductor of `ℤ[τ]` in the coefficient
field's full ring of integers. -/
theorem coefficient_discriminant_mem_conductor :
    (81 : 𝓞 Q.K) ∈ conductor ℤ coefficientInteger := by
  apply integer_discriminant_mem_conductor coefficientPowerBasis
    coefficientInteger (by rfl) 81
  exact coefficientPowerBasis_discriminant

/-- The integer `-2592` lies in the conductor of `ℤ[σ]` in the
two-division field's full ring of integers. -/
theorem twoDivision_discriminant_mem_conductor :
    ((-2592 : ℤ) : 𝓞 F) ∈ conductor ℤ twoDivisionInteger := by
  apply integer_discriminant_mem_conductor twoDivisionPowerBasis
    twoDivisionInteger (by rfl) (-2592)
  exact twoDivisionPowerBasis_discriminant

private theorem not_dvd_exponent_of_mem_conductor_of_isCoprime
    {L : Type*} [Field L] [NumberField L] (theta : 𝓞 L)
    {p : ℕ} [Fact p.Prime] (d : ℤ)
    (hd : (d : 𝓞 L) ∈ conductor ℤ theta)
    (hcop : IsCoprime d (p : ℤ)) :
    ¬ p ∣ RingOfIntegers.exponent theta := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {d} ≤
      Ideal.comap (algebraMap ℤ (𝓞 L)) (conductor ℤ theta) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    change algebraMap ℤ (𝓞 L) d ∈ conductor ℤ theta at hd
    exact hd
  exact ((Ideal.isCoprime_span_singleton_iff d (p : ℤ)).mpr hcop).codisjoint.mono_left hspan

/-! ## Exact finite-field irreducibility certificates -/

def coefficientPolynomialMod (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 - 3 * X - 1

def twoDivisionPolynomialMod (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 - 3 * X - 10

theorem coefficientPolynomialInt_map_zmod (p : ℕ) :
    coefficientPolynomialInt.map (Int.castRingHom (ZMod p)) =
      coefficientPolynomialMod p := by
  norm_num [coefficientPolynomialInt, coefficientPolynomialMod]

theorem twoDivisionPolynomialInt_map_zmod (p : ℕ) :
    twoDivisionPolynomialInt.map (Int.castRingHom (ZMod p)) =
      twoDivisionPolynomialMod p := by
  norm_num [twoDivisionPolynomialInt, twoDivisionPolynomialMod]

private theorem coefficientPolynomialMod_irreducible_of_no_root
    {p : ℕ} [Fact p.Prime]
    (hroot : ∀ z : ZMod p, ¬ Polynomial.IsRoot (coefficientPolynomialMod p) z) :
    Irreducible (coefficientPolynomialMod p) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ hroot
  have hdegree : (coefficientPolynomialMod p).natDegree = 3 := by
    simp only [coefficientPolynomialMod]
    compute_degree!
  rw [hdegree]
  norm_num

private theorem twoDivisionPolynomialMod_irreducible_of_no_root
    {p : ℕ} [Fact p.Prime]
    (hroot : ∀ z : ZMod p, ¬ Polynomial.IsRoot (twoDivisionPolynomialMod p) z) :
    Irreducible (twoDivisionPolynomialMod p) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ hroot
  have hdegree : (twoDivisionPolynomialMod p).natDegree = 3 := by
    simp only [twoDivisionPolynomialMod]
    compute_degree!
  rw [hdegree]
  norm_num

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_five_irreducible :
    Irreducible (coefficientPolynomialMod 5) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_seven_irreducible :
    Irreducible (coefficientPolynomialMod 7) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_eleven_irreducible :
    Irreducible (coefficientPolynomialMod 11) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_thirteen_irreducible :
    Irreducible (coefficientPolynomialMod 13) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem twoDivisionPolynomialMod_seventeen_irreducible :
    Irreducible (twoDivisionPolynomialMod 17) := by
  apply twoDivisionPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [twoDivisionPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

theorem twoDivisionPolynomialMod_nineteen_irreducible :
    Irreducible (twoDivisionPolynomialMod 19) := by
  apply twoDivisionPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [twoDivisionPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_twentythree_irreducible :
    Irreducible (coefficientPolynomialMod 23) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_twentynine_irreducible :
    Irreducible (coefficientPolynomialMod 29) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_thirtyone_irreducible :
    Irreducible (coefficientPolynomialMod 31) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

/-! ## Kummer--Dedekind and inertia in the compositum -/

private theorem inertiaDeg_eq_natDegree_of_irreducible_mod
    {L : Type*} [Field L] [NumberField L] (theta : 𝓞 L)
    {p : ℕ} [Fact p.Prime]
    (hexponent : ¬ p ∣ RingOfIntegers.exponent theta)
    (hirr : Irreducible
      ((minpoly ℤ theta).map (Int.castRingHom (ZMod p))))
    (P : Ideal (𝓞 L))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)) :
    P.inertiaDeg ℤ =
      ((minpoly ℤ theta).map (Int.castRingHom (ZMod p))).natDegree := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexponent
  have hfactor := (e ⟨P, hP⟩).2
  have hdegree :=
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      hexponent hfactor
  simp only [Subtype.coe_eta] at hdegree
  change (e ⟨P, hP⟩ : Polynomial (ZMod p)) ∈
      (normalizedFactors
        ((minpoly ℤ theta).map (Int.castRingHom (ZMod p)))).toFinset at hfactor
  rw [normalizedFactors_irreducible hirr,
    (minpoly.monic theta.isIntegral).map
      (Int.castRingHom (ZMod p)) |>.normalize_eq_self] at hfactor
  simp only [Multiset.toFinset_singleton, Finset.mem_singleton] at hfactor
  rw [hfactor] at hdegree
  have heq := e.symm_apply_apply ⟨P, hP⟩
  have hideal :
      ((e.symm (e ⟨P, hP⟩)).1 : Ideal (𝓞 L)) = P :=
    congrArg Subtype.val heq
  rw [hideal] at hdegree
  exact hdegree

private theorem coefficient_inertiaDeg_eq_three
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime (81 : ℤ) (p : ℤ))
    (hirr : Irreducible (coefficientPolynomialMod p))
    (P : Ideal (𝓞 Q.K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 Q.K)) :
    P.inertiaDeg ℤ = 3 := by
  have hexponent : ¬ p ∣ RingOfIntegers.exponent coefficientInteger :=
    not_dvd_exponent_of_mem_conductor_of_isCoprime coefficientInteger 81
      coefficient_discriminant_mem_conductor hcop
  have hirr' : Irreducible
      ((minpoly ℤ coefficientInteger).map (Int.castRingHom (ZMod p))) := by
    rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod]
    exact hirr
  have hdegree := inertiaDeg_eq_natDegree_of_irreducible_mod
    coefficientInteger hexponent hirr' P hP
  rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod] at hdegree
  have hnatDegree : (coefficientPolynomialMod p).natDegree = 3 := by
    simp only [coefficientPolynomialMod]
    compute_degree!
  exact hdegree.trans hnatDegree

private theorem twoDivision_inertiaDeg_eq_three
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime ((-2592 : ℤ)) (p : ℤ))
    (hirr : Irreducible (twoDivisionPolynomialMod p))
    (P : Ideal (𝓞 F))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)) :
    P.inertiaDeg ℤ = 3 := by
  have hexponent : ¬ p ∣ RingOfIntegers.exponent twoDivisionInteger :=
    not_dvd_exponent_of_mem_conductor_of_isCoprime twoDivisionInteger (-2592)
      twoDivision_discriminant_mem_conductor hcop
  have hirr' : Irreducible
      ((minpoly ℤ twoDivisionInteger).map (Int.castRingHom (ZMod p))) := by
    rw [twoDivisionInteger_minpoly, twoDivisionPolynomialInt_map_zmod]
    exact hirr
  have hdegree := inertiaDeg_eq_natDegree_of_irreducible_mod
    twoDivisionInteger hexponent hirr' P hP
  rw [twoDivisionInteger_minpoly, twoDivisionPolynomialInt_map_zmod] at hdegree
  have hnatDegree : (twoDivisionPolynomialMod p).natDegree = 3 := by
    simp only [twoDivisionPolynomialMod]
    compute_degree!
  exact hdegree.trans hnatDegree

private theorem s_isRoot_twoDivisionPolynomial :
    Polynomial.aeval s twoDivisionPolynomial = 0 := by
  simp only [twoDivisionPolynomial, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat]
  linear_combination s_cubic

/-- The canonical embedding of the rational two-division cubic field into
the degree-nine compositum. -/
def twoDivisionEmbedding : F →ₐ[ℚ] M :=
  AdjoinRoot.liftAlgHom twoDivisionPolynomial (Algebra.ofId ℚ M) s
    s_isRoot_twoDivisionPolynomial

private theorem compositum_inertiaDeg_ge_three_via_coefficient
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime (81 : ℤ) (p : ℤ))
    (hirr : Irreducible (coefficientPolynomialMod p))
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    3 ≤ P.inertiaDeg ℤ := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  let QP : Ideal (𝓞 Q.K) := P.under (𝓞 Q.K)
  have hQP : QP ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 Q.K) :=
    ⟨inferInstance, inferInstance⟩
  have hdegree : QP.inertiaDeg ℤ = 3 :=
    coefficient_inertiaDeg_eq_three hcop hirr QP hQP
  have htower := Ideal.inertiaDeg_tower (R := ℤ) QP P
  rw [hdegree] at htower
  exact Nat.le_of_dvd (P.inertiaDeg_pos ℤ) ⟨P.inertiaDeg (𝓞 Q.K), htower⟩

private theorem compositum_inertiaDeg_ge_three_via_twoDivision
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime (-2592 : ℤ) (p : ℤ))
    (hirr : Irreducible (twoDivisionPolynomialMod p))
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    3 ≤ P.inertiaDeg ℤ := by
  letI : Algebra F M := twoDivisionEmbedding.toRingHom.toAlgebra
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom twoDivisionEmbedding
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  let QP : Ideal (𝓞 F) := P.under (𝓞 F)
  have hQP : QP ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F) :=
    ⟨inferInstance, inferInstance⟩
  have hdegree : QP.inertiaDeg ℤ = 3 :=
    twoDivision_inertiaDeg_eq_three hcop hirr QP hQP
  have htower := Ideal.inertiaDeg_tower (R := ℤ) QP P
  rw [hdegree] at htower
  exact Nat.le_of_dvd (P.inertiaDeg_pos ℤ) ⟨P.inertiaDeg (𝓞 F), htower⟩

/-- Every prime of the compositum over a rational prime in `[5,31]` has
inertia degree at least three. -/
theorem compositum_inertiaDeg_ge_three
    (p : ℕ) (hpIcc : p ∈ Finset.Icc 5 31) (hp : p.Prime)
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    3 ≤ P.inertiaDeg ℤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpLower : 5 ≤ p := Finset.mem_Icc.mp hpIcc |>.1
  have hpUpper : p ≤ 31 := Finset.mem_Icc.mp hpIcc |>.2
  interval_cases p <;> norm_num at hp
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_five_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_seven_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_eleven_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_thirteen_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_twoDivision
      (by norm_num) twoDivisionPolynomialMod_seventeen_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_twoDivision
      (by norm_num) twoDivisionPolynomialMod_nineteen_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_twentythree_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_twentynine_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_thirtyone_irreducible P hP

/-- Consequently, no prime ideal over a rational prime in `[5,31]` can
have absolute norm at most `31`. -/
theorem thirtyone_lt_absNorm_of_mem_primesOver
    (p : ℕ) (hpIcc : p ∈ Finset.Icc 5 31) (hp : p.Prime)
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    31 < P.absNorm := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg p P]
  have hdegree := compositum_inertiaDeg_ge_three p hpIcc hp P hP
  have hpge : 5 ≤ p := Finset.mem_Icc.mp hpIcc |>.1
  calc
    31 < p ^ 3 := lt_of_lt_of_le (by norm_num : 31 < 5 ^ 3)
      (Nat.pow_le_pow_left hpge 3)
    _ ≤ p ^ P.inertiaDeg ℤ := pow_le_pow_right' (by omega) hdegree

end

end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
