/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import EllipticCurves.X18SelmerCardinality
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionExactSignature
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionNorms
import MazurTorsion.NumberTheory.XOneEighteenUnitSquareclasses
import MazurTorsion.NumberTheory.XOneEighteenMinimalTwoDescentModel
import MazurTorsion.NumberTheory.XOneEighteenCoefficientDyadicSelmer
import MazurTorsion.NumberTheory.XOneEighteenSelmerSieve

/-!
# Global Selmer bookkeeping for the `X₁(18)` two-descent

This module connects the arithmetic of the explicit degree-nine
two-division field to the generic supported-Selmer cardinality package.
The remaining prime and local-image calculations enter through narrow
certificate hypotheses: the theorem below does not assume a Selmer or
Mordell--Weil conclusion.
-/

open IsDedekindDomain NumberField Polynomial

namespace MazurTorsion.XOneEighteenGlobalSelmerBridge

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionExactSignature
open MazurTorsion.XOneEighteenDescentAlgebraEquiv
open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenSelmerSieve
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

/-- The integral closure occurring in the unique irreducible field factor
of the generic descent algebra. -/
abbrev RelativeIntegers := integralClosure (𝓞 K) M

instance relativeIntegersIsDedekindDomain :
    IsDedekindDomain RelativeIntegers :=
  IsIntegralClosure.isDedekindDomain (𝓞 K) K M _

instance relativeIntegersIsFractionRing :
    IsFractionRing RelativeIntegers M :=
  IsIntegralClosure.isFractionRing_of_finite_extension (𝓞 K) K M _

/-- The relative integral closure is canonically the absolute ring of
integers of the same degree-nine field. -/
def relativeIntegersEquiv : RelativeIntegers ≃+* 𝓞 M :=
  (IsIntegralClosure.equiv (𝓞 K) RelativeIntegers M (𝓞 M)).toRingEquiv

/-- The induced equivalence on integral-unit square classes. -/
def relativeUnitSquareclassEquiv :
    Units.modPow RelativeIntegers 2 ≃* Units.modPow (𝓞 M) 2 :=
  Units.modPow.congr relativeIntegersEquiv.toMulEquiv 2

/-- The integral closure used by the relative descent has exactly `64`
unit square classes. -/
theorem natCard_relativeUnitsModSq :
    Nat.card (Units.modPow RelativeIntegers 2) = 64 := by
  rw [Nat.card_congr relativeUnitSquareclassEquiv.toEquiv]
  exact
    MazurTorsion.XOneEighteenDescent.natCard_unitsModSq_of_degree_nine_of_nrRealPlaces_eq_three
      M finrank_M_over_rat nrRealPlaces_eq_three

/-! ## The exact dyadic support -/

/-- The primes in the degree-nine field lying above the even places of the
coefficient field.  This is the support used by the explicit descent. -/
def compositumDyadicSupport : Set (HeightOneSpectrum RelativeIntegers) :=
  HeightOneSpectrum.primesAbove (𝓞 K) RelativeIntegers
    coefficientDyadicSupport

/-- Square classes in the degree-nine field supported at the dyadic
primes. -/
abbrev DyadicSelmerM :=
  selmerGroup (R := RelativeIntegers) (K := M)
    (S := compositumDyadicSupport) (n := 2)

/-! ## The minimal model has genuinely dyadic bad support -/

private theorem tau_mem_valuationInteger
    (v : HeightOneSpectrum (𝓞 K)) :
    MazurTorsion.XOneEighteenRealCubicQuotient.tau ∈
      (v.valuation K).integer := by
  change v.valuation K
      MazurTorsion.XOneEighteenRealCubicQuotient.tau ≤ 1
  have h := v.valuation_le_one (K := K) coefficientInteger
  change v.valuation K (coefficientInteger : K) ≤ 1 at h
  have hcoe : (coefficientInteger : K) =
      MazurTorsion.XOneEighteenRealCubicQuotient.tau := rfl
  rwa [hcoe] at h

private theorem valuation_two_eq_one_of_notMem_coefficientDyadicSupport
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K 2 = 1 := by
  simpa only [coefficientDyadicSupport, Set.mem_setOf_eq, not_not] using hv

private theorem inv_two_mem_valuationInteger
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    (2 : K)⁻¹ ∈ (v.valuation K).integer := by
  change v.valuation K (2 : K)⁻¹ ≤ 1
  rw [map_inv₀,
    valuation_two_eq_one_of_notMem_coefficientDyadicSupport v hv]
  simp

private theorem inv_four_mem_valuationInteger
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    (4 : K)⁻¹ ∈ (v.valuation K).integer := by
  change v.valuation K (4 : K)⁻¹ ≤ 1
  rw [show (4 : K) = 2 ^ 2 by norm_num, map_inv₀, map_pow,
    valuation_two_eq_one_of_notMem_coefficientDyadicSupport v hv]
  simp

/-- The quadratic coefficient of the minimal completed-square model is
integral away from the dyadic support. -/
theorem minimalDescentCurve_valuation_a₂_le_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.a₂ ≤ 1 := by
  rw [minimalDescentCurve_eq]
  change MazurTorsion.XOneEighteenRealCubicQuotient.tau ^ 2 +
      MazurTorsion.XOneEighteenRealCubicQuotient.tau - (11 : K) / 4 ∈
    (v.valuation K).integer
  exact (v.valuation K).integer.sub_mem
    ((v.valuation K).integer.add_mem
      ((v.valuation K).integer.pow_mem (tau_mem_valuationInteger v) 2)
      (tau_mem_valuationInteger v))
    ((v.valuation K).integer.mul_mem (ofNat_mem _ 11)
      (inv_four_mem_valuationInteger v hv))

/-- The linear coefficient of the minimal completed-square model is
integral away from the dyadic support. -/
theorem minimalDescentCurve_valuation_a₄_le_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.a₄ ≤ 1 := by
  rw [minimalDescentCurve_eq]
  change (-MazurTorsion.XOneEighteenRealCubicQuotient.tau ^ 2 +
      MazurTorsion.XOneEighteenRealCubicQuotient.tau + (7 : K)) / 2 ∈
    (v.valuation K).integer
  rw [div_eq_mul_inv]
  exact (v.valuation K).integer.mul_mem
    ((v.valuation K).integer.add_mem
      ((v.valuation K).integer.add_mem
        ((v.valuation K).integer.neg_mem
          ((v.valuation K).integer.pow_mem (tau_mem_valuationInteger v) 2))
        (tau_mem_valuationInteger v))
      (ofNat_mem _ 7))
    (inv_two_mem_valuationInteger v hv)

/-- The constant coefficient of the minimal completed-square model is
integral away from the dyadic support. -/
theorem minimalDescentCurve_valuation_a₆_le_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.a₆ ≤ 1 := by
  rw [minimalDescentCurve_eq]
  change (2 * MazurTorsion.XOneEighteenRealCubicQuotient.tau ^ 2 +
      MazurTorsion.XOneEighteenRealCubicQuotient.tau - (5 : K)) / 4 ∈
    (v.valuation K).integer
  rw [div_eq_mul_inv]
  exact (v.valuation K).integer.mul_mem
    ((v.valuation K).integer.sub_mem
      ((v.valuation K).integer.add_mem
        ((v.valuation K).integer.mul_mem
          (ofNat_mem _ 2)
          ((v.valuation K).integer.pow_mem (tau_mem_valuationInteger v) 2))
        (tau_mem_valuationInteger v))
      (ofNat_mem _ 5))
    (inv_four_mem_valuationInteger v hv)

/-- The minimal cubic discriminant is a unit away from the dyadic
support. -/
theorem minimalDescentCurve_valuation_discr_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ coefficientDyadicSupport) :
    v.valuation K minimalDescentCurve.toAffine.f.discr = 1 := by
  rw [minimalDescentCurve_discr_f]
  have htwo :=
    valuation_two_eq_one_of_notMem_coefficientDyadicSupport v hv
  rw [show (8 : K) = 2 ^ 3 by norm_num, map_div₀,
    Valuation.map_neg, map_one, map_pow, htwo]
  simp

/-- The generic `x - T` map for the minimal completed-square model has
dyadically supported image.  This is the concrete global containment that
fails for the scale-three rational model. -/
theorem minimalDescentCurve_range_μ_le_dyadicSelmerGroupA :
    (minimalDescentCurve.toAffine.μ).range ≤
      minimalDescentCurve.toAffine.selmerGroupA (𝓞 K)
        coefficientDyadicSupport := by
  exact minimalDescentCurve.toAffine.range_μ_le_selmerGroupA
    (𝓞 K) coefficientDyadicSupport
    minimalDescentCurve_valuation_a₂_le_one
    minimalDescentCurve_valuation_a₄_le_one
    minimalDescentCurve_valuation_a₆_le_one
    minimalDescentCurve_valuation_discr_eq_one

/-! ## Relative norm and its four checked kernel generators -/

/-- The relative norm from the degree-nine field to the real cubic field,
on square classes. -/
def relativeNormSquareclasses :
    Units.modPow M 2 →* Units.modPow K 2 :=
  Units.modPow.map (Algebra.norm K) 2

/-- Restriction of squareclasses from the real cubic field to the
degree-nine compositum. -/
def relativeRestrictionSquareclasses :
    Units.modPow K 2 →* Units.modPow M 2 :=
  Units.modPow.map (algebraMap K M).toMonoidHom 2

/-- Relative norm followed by restriction is the identity on squareclasses:
the extension has odd degree three. -/
theorem relativeNorm_comp_relativeRestriction :
    relativeNormSquareclasses.comp relativeRestrictionSquareclasses =
      MonoidHom.id (Units.modPow K 2) := by
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H u =>
      have hunit :
          Units.map (Algebra.norm K)
              (Units.map (algebraMap K M).toMonoidHom u) = u ^ 3 := by
        apply Units.ext
        simp only [Units.coe_map, Units.val_pow_eq_pow_val]
        change Algebra.norm K (algebraMap K M (u : K)) = (u : K) ^ 3
        rw [Algebra.norm_algebraMap, finrank_M_over_K]
      change
        QuotientGroup.mk
            (Units.map (Algebra.norm K)
              (Units.map (algebraMap K M).toMonoidHom u)) =
          QuotientGroup.mk u
      rw [hunit, QuotientGroup.mk_pow]
      calc
        (QuotientGroup.mk u : Units.modPow K 2) ^ 3 =
            (QuotientGroup.mk u : Units.modPow K 2) ^ 2 *
              QuotientGroup.mk u := by rw [show 3 = 2 + 1 by norm_num, pow_succ]
        _ = 1 * QuotientGroup.mk u := by rw [Units.modPow.pow_eq_one]
        _ = QuotientGroup.mk u := one_mul _

/-- The squareclass of a nonzero field element. -/
def fieldSquareclass (x : M) (hx : x ≠ 0) : Units.modPow M 2 :=
  QuotientGroup.mk (Units.mk0 x hx)

private theorem h1_ne_zero : h1 ≠ 0 := by
  intro hz
  have h : Algebra.norm K h1 = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_h1] at h
  norm_num at h

private theorem h2_ne_zero : h2 ≠ 0 := by
  intro hz
  have h : Algebra.norm K h2 = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_h2] at h
  norm_num at h

private theorem h3_ne_zero : h3 ≠ 0 := by
  intro hz
  have h : Algebra.norm K h3 = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_h3] at h
  norm_num at h

private theorem tau_sq_ne_two : Q.tau ^ 2 ≠ 2 := by
  intro hsq
  have htau : Q.tau = -1 := by
    have hc := Q.tau_cubic
    rw [show Q.tau ^ 3 = Q.tau * Q.tau ^ 2 by ring, hsq] at hc
    have hadd : Q.tau + 1 = 0 := by linear_combination -hc
    linear_combination hadd
  rw [htau] at hsq
  norm_num at hsq

private theorem h4_ne_zero : h4 ≠ 0 := by
  intro hz
  have hzero : Algebra.norm K h4 = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_h4_eq_square] at hzero
  have hsquare : (2 * (Q.tau ^ 2 - 2)) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (mul_ne_zero (by norm_num) (sub_ne_zero.mpr tau_sq_ne_two))
  exact hsquare hzero

private theorem alpha_ne_zero : alpha ≠ 0 := by
  intro hz
  have h : Algebra.norm K alpha = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_alpha] at h
  norm_num at h

private theorem beta_ne_zero : beta ≠ 0 := by
  intro hz
  have h : Algebra.norm K beta = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_beta] at h
  have htau : Q.tau + 1 ≠ 0 := by
    have ht :=
      MazurTorsion.XOneEighteenRealCubicQuotient.rational_add_tau_ne_zero
        (1 : ℚ)
    change (1 : K) + Q.tau ≠ 0 at ht
    simpa only [add_comm] using ht
  apply htau
  linear_combination (1 / 2) * h

/-- The actual squareclass of the first dyadic generator `alpha`. -/
def alphaSquareclass : Units.modPow M 2 :=
  fieldSquareclass alpha alpha_ne_zero

/-- The actual squareclass of the second dyadic generator `beta`. -/
def betaSquareclass : Units.modPow M 2 :=
  fieldSquareclass beta beta_ne_zero

/-- The four explicit squareclasses with square relative norm. -/
def kernelGenerator : Fin 4 → Units.modPow M 2
  | 0 => fieldSquareclass h1 h1_ne_zero
  | 1 => fieldSquareclass h2 h2_ne_zero
  | 2 => fieldSquareclass h3 h3_ne_zero
  | 3 => fieldSquareclass h4 h4_ne_zero

private theorem relativeNorm_fieldSquareclass_eq_one
    (x : M) (hx : x ≠ 0) (hsq : IsSquare (Algebra.norm K x)) :
    relativeNormSquareclasses (fieldSquareclass x hx) = 1 := by
  rw [relativeNormSquareclasses, fieldSquareclass,
    Units.modPow.map_mk, Units.modPow.mk_eq_one_iff_isSquare]
  simpa only [Units.coe_map, Units.val_mk0] using hsq

/-- Every explicit generator lies in the relative norm kernel. -/
theorem kernelGenerator_mem (i : Fin 4) :
    kernelGenerator i ∈ relativeNormSquareclasses.ker := by
  rw [MonoidHom.mem_ker]
  fin_cases i
  · exact relativeNorm_fieldSquareclass_eq_one h1 h1_ne_zero
      ⟨1, by simpa using norm_h1⟩
  · exact relativeNorm_fieldSquareclass_eq_one h2 h2_ne_zero
      ⟨1, by simpa using norm_h2⟩
  · exact relativeNorm_fieldSquareclass_eq_one h3 h3_ne_zero
      ⟨2, by rw [norm_h3]; norm_num⟩
  · exact relativeNorm_fieldSquareclass_eq_one h4 h4_ne_zero
      ⟨2 * (Q.tau ^ 2 - 2), by rw [norm_h4_eq_square, pow_two]⟩

/-- The product selected by the four low bits of a mask. -/
def kernelRepresentative (mask : Fin 16) : Units.modPow M 2 :=
  (if mask.val.testBit 0 then kernelGenerator 0 else 1) *
  (if mask.val.testBit 1 then kernelGenerator 1 else 1) *
  (if mask.val.testBit 2 then kernelGenerator 2 else 1) *
  (if mask.val.testBit 3 then kernelGenerator 3 else 1)

/-- Every masked product remains in the relative norm kernel. -/
theorem kernelRepresentative_mem (mask : Fin 16) :
    kernelRepresentative mask ∈ relativeNormSquareclasses.ker := by
  simp only [MonoidHom.mem_ker, kernelRepresentative, map_mul]
  have hgen (i : Fin 4) : relativeNormSquareclasses (kernelGenerator i) = 1 :=
    MonoidHom.mem_ker.mp (kernelGenerator_mem i)
  split_ifs <;> simp [hgen]

/-- The masked products, regarded as elements of the norm kernel. -/
def kernelRepresentativeInKernel (mask : Fin 16) :
    relativeNormSquareclasses.ker :=
  ⟨kernelRepresentative mask, kernelRepresentative_mem mask⟩

/-! ## Cardinality from genuine arithmetic certificates -/

/-- A two-prime valuation certificate records the two actual dyadic
places and the valuation-parity matrix of the classes of `alpha` and
`beta`.  Surjectivity is derived from the matrix, not stored in the
certificate. -/
structure DyadicValuationCertificate where
  places : Fin 2 ≃ compositumDyadicSupport
  alpha_mem : alphaSquareclass ∈ DyadicSelmerM
  beta_mem : betaSquareclass ∈ DyadicSelmerM
  alpha_at_zero :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨alphaSquareclass, alpha_mem⟩ (places 0) = parityOne
  alpha_at_one :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨alphaSquareclass, alpha_mem⟩ (places 1) = 1
  beta_at_zero :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨betaSquareclass, beta_mem⟩ (places 0) = 1
  beta_at_one :
    supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 ⟨betaSquareclass, beta_mem⟩ (places 1) = parityOne

/-- The valuation matrix gives every parity vector at the two dyadic
primes. -/
theorem DyadicValuationCertificate.surjective
    (C : DyadicValuationCertificate) :
    Function.Surjective
      (supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2) :=
  supportValuation_surjective_of_two_generators
    (R := RelativeIntegers) (K := M) compositumDyadicSupport
      C.places ⟨alphaSquareclass, C.alpha_mem⟩
        ⟨betaSquareclass, C.beta_mem⟩ C.alpha_at_zero C.alpha_at_one
        C.beta_at_zero C.beta_at_one

/-- The exact supported-Selmer and split-norm cardinalities.  The PID
certificate is the pending class-number endpoint; the norm target and its
section are explicit maps, while only their independently checked target
cardinality is supplied here. -/
theorem dyadicSelmer_card_and_splitNormKernel
    (hprincipal : IsPrincipalIdealRing (𝓞 M))
    (C : DyadicValuationCertificate)
    {H : Type*} [Group H]
    (N : DyadicSelmerM →* H)
    (res : H →* DyadicSelmerM)
    (hsplit : N.comp res = MonoidHom.id H)
    (hH : Nat.card H = 16) :
    Nat.card DyadicSelmerM = 256 ∧ Nat.card N.ker = 16 := by
  letI : Subsingleton (ClassGroup RelativeIntegers) :=
    NumberField.subsingleton_classGroup_integralClosure K M hprincipal
  have hsupport : Nat.card compositumDyadicSupport = 2 := by
    simpa using (Nat.card_congr C.places).symm
  exact concrete_twoSelmer_and_splitNorm_kernel
    compositumDyadicSupport hsupport
      natCard_relativeUnitsModSq C.surjective N res hsplit hH

/-! ## The actual ambient relative norm -/

/-- The dyadically supported source mapped by relative norm to the full
coefficient-field squareclass group.  No unsupported claim that relative
norm preserves dyadic support is needed. -/
def fullDyadicRelativeNorm :
    DyadicSelmerM →* Units.modPow K 2 :=
  relativeNormSquareclasses.comp DyadicSelmerM.subtype

private theorem relativeRestriction_field_comp :
    (algebraMap RelativeIntegers M).comp
        (algebraMap (𝓞 K) RelativeIntegers) =
      (algebraMap K M).comp (algebraMap (𝓞 K) K) := by
  ext x
  rfl

/-- Scalar extension of a dyadically supported coefficient-field class
is supported at the primes above the dyadic places. -/
theorem relativeRestriction_mem_dyadicSelmer
    (x : DyadicSelmerK) :
    relativeRestrictionSquareclasses x ∈ DyadicSelmerM := by
  obtain ⟨x, hx⟩ := x
  induction x using QuotientGroup.induction_on with
  | H u =>
      intro w hw
      rw [relativeRestrictionSquareclasses, Units.modPow.map_mk,
        HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
      have hv : w.below (𝓞 K) ∉ coefficientDyadicSupport := by
        intro hv
        apply hw
        exact (HeightOneSpectrum.mem_primesAbove_iff
          (𝓞 K) RelativeIntegers coefficientDyadicSupport w).mpr hv
      exact HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
        (algebraMap K M) (algebraMap (𝓞 K) RelativeIntegers)
        relativeRestriction_field_comp w
        (Ideal.IsIntegral.comap_ne_bot (𝓞 K) w.ne_bot) u
        ((HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
          (w.below (𝓞 K)) 2 u).mp (hx _ hv))

/-- Scalar extension restricted to the two dyadic supported groups. -/
def dyadicRelativeRestriction :
    DyadicSelmerK →* DyadicSelmerM :=
  (relativeRestrictionSquareclasses.comp DyadicSelmerK.subtype).codRestrict
    DyadicSelmerM relativeRestriction_mem_dyadicSelmer

/-- Ambient relative norm after supported scalar extension is the
underlying coefficient-field squareclass. -/
theorem fullDyadicRelativeNorm_comp_restriction :
    fullDyadicRelativeNorm.comp dyadicRelativeRestriction =
      DyadicSelmerK.subtype := by
  apply MonoidHom.ext
  intro x
  exact DFunLike.congr_fun relativeNorm_comp_relativeRestriction
    (x : Units.modPow K 2)

/-- The supported coefficient-field group injects into the range of the
ambient relative norm. -/
def dyadicBaseIntoFullNormRange
    (x : DyadicSelmerK) : fullDyadicRelativeNorm.range :=
  ⟨fullDyadicRelativeNorm (dyadicRelativeRestriction x),
    ⟨dyadicRelativeRestriction x, rfl⟩⟩

theorem dyadicBaseIntoFullNormRange_injective :
    Function.Injective dyadicBaseIntoFullNormRange := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg Subtype.val hxy
  change fullDyadicRelativeNorm (dyadicRelativeRestriction x) =
    fullDyadicRelativeNorm (dyadicRelativeRestriction y) at h
  have hx := DFunLike.congr_fun
    fullDyadicRelativeNorm_comp_restriction x
  have hy := DFunLike.congr_fun
    fullDyadicRelativeNorm_comp_restriction y
  exact hx.symm.trans (h.trans hy)

/-- The dyadic Selmer group of the degree-nine field has cardinality
`256`, from the checked two-place valuation certificate and the relative
integral-unit calculation. -/
theorem natCard_dyadicSelmerM
    (hprincipal : IsPrincipalIdealRing (𝓞 M))
    (V : DyadicValuationCertificate) :
    Nat.card DyadicSelmerM = 256 := by
  letI : Subsingleton (ClassGroup RelativeIntegers) :=
    NumberField.subsingleton_classGroup_integralClosure K M hprincipal
  have hsupport : Nat.card compositumDyadicSupport = 2 := by
    simpa using (Nat.card_congr V.places).symm
  letI : Finite compositumDyadicSupport :=
    Nat.finite_of_card_ne_zero (hsupport.trans_ne (by norm_num))
  letI : Fact (0 < (2 : ℕ)) := ⟨by norm_num⟩
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  letI : Finite (Units.modPow RelativeIntegers 2) :=
    Nat.finite_of_card_ne_zero
      (natCard_relativeUnitsModSq.trans_ne (by norm_num))
  have hempty :
      Nat.card
          (selmerGroup (R := RelativeIntegers) (K := M)
            (S := (∅ : Set (HeightOneSpectrum RelativeIntegers)))
            (n := 2)) = 64 :=
    (natCard_emptySelmer_eq_unitsModPow
      (R := RelativeIntegers) (K := M) 2).trans
        natCard_relativeUnitsModSq
  letI : Finite
      (selmerGroup (R := RelativeIntegers) (K := M)
        (S := (∅ : Set (HeightOneSpectrum RelativeIntegers)))
        (n := 2)) :=
    Nat.finite_of_card_ne_zero (hempty.trans_ne (by norm_num))
  rw [natCard_supportedSelmer_eq_of_valuation_surjective
    (R := RelativeIntegers) (K := M) compositumDyadicSupport 2
      V.surjective,
    hempty, hsupport]
  norm_num

/-- Membership of the four explicit norm-kernel generators in the dyadic
Selmer group.  This is the global support certificate consumed by the
masked-product enumeration. -/
structure KernelGeneratorSupportCertificate where
  generator_mem : ∀ i : Fin 4, kernelGenerator i ∈ DyadicSelmerM

/-- Every masked product is dyadically supported once the four generators
are. -/
theorem kernelRepresentative_mem_dyadicSelmer
    (C : KernelGeneratorSupportCertificate) (mask : Fin 16) :
    kernelRepresentative mask ∈ DyadicSelmerM := by
  simp only [kernelRepresentative]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;>
    split <;> simp [C.generator_mem]

/-- The sixteen explicit products as elements of the supported relative
norm kernel. -/
def dyadicKernelRepresentative
    (C : KernelGeneratorSupportCertificate) (mask : Fin 16) :
    fullDyadicRelativeNorm.ker := by
  refine ⟨⟨kernelRepresentative mask,
    kernelRepresentative_mem_dyadicSelmer C mask⟩, ?_⟩
  change relativeNormSquareclasses (kernelRepresentative mask) =
    (1 : Units.modPow K 2)
  exact MonoidHom.mem_ker.mp (kernelRepresentative_mem mask)

/-- Opposing injections of sixteen explicit classes into the kernel and
of the coefficient dyadic group into the range exhaust the ambient norm
kernel. -/
theorem dyadicKernelRepresentative_bijective
    (hprincipal : IsPrincipalIdealRing (𝓞 M))
    (V : DyadicValuationCertificate)
    (C : KernelGeneratorSupportCertificate)
    (hinjective : Function.Injective kernelRepresentative) :
    Function.Bijective (dyadicKernelRepresentative C) := by
  apply kernel_representatives_bijective_of_card_256
    fullDyadicRelativeNorm (dyadicKernelRepresentative C)
      dyadicBaseIntoFullNormRange
      (natCard_dyadicSelmerM hprincipal V) natCard_dyadicSelmerK
  · intro a b hab
    apply hinjective
    exact congrArg (fun z : fullDyadicRelativeNorm.ker ↦
      ((z : DyadicSelmerM) : Units.modPow M 2)) hab
  · exact dyadicBaseIntoFullNormRange_injective

/-! ## The global subgroup consumed by the Selmer sieve -/

/-- On the minimal generic descent algebra, the global dyadic norm kernel
is the intersection of dyadic support (transported through the explicit
algebra equivalence) and the generic relative-norm kernel. -/
def descentDyadicNormKernel : Subgroup minimalDescentCurve.toAffine.M :=
  DyadicSelmerM.comap minimalDescentSquareclassEquiv.toMonoidHom ⊓
    minimalDescentCurve.toAffine.normM.ker

/-- The zero mask represents the identity squareclass. -/
theorem kernelRepresentative_zero : kernelRepresentative 0 = 1 := by
  simp [kernelRepresentative]

/-! ## The unique generic descent factor -/

local instance minimalDescentFactorsUnique :
    Unique minimalDescentCurve.toAffine.f.Factors :=
  Polynomial.Factors.unique minimalDescentPolynomial_irreducible
    minimalDescentCurve.toAffine.monic_f

/-- For the irreducible two-division polynomial, the product decomposition
of squareclasses has only its distinguished field factor. -/
def singleFactorSquareclassEquiv :
    minimalDescentCurve.toAffine.M ≃*
      Units.modPow (AdjoinRoot
        ((default : minimalDescentCurve.toAffine.f.Factors) : K[X])) 2 :=
  (AdjoinRoot.modPowEquivPiFactors minimalDescentCurve.toAffine.f_ne_zero
    minimalDescentCurve.toAffine.squarefree_f 2).trans
      (MulEquiv.piUnique fun p : minimalDescentCurve.toAffine.f.Factors ↦
        Units.modPow (AdjoinRoot (p : K[X])) 2)

private theorem projFactor_default_eq_id :
    AdjoinRoot.projFactor minimalDescentCurve.toAffine.f_ne_zero
        minimalDescentCurve.toAffine.squarefree_f default =
      RingHom.id minimalDescentCurve.toAffine.A := by
  apply AdjoinRoot.ringHom_ext <;> rfl

/-- Evaluating the unique-factor product decomposition at its sole factor
is the identity squareclass map. -/
theorem singleFactorSquareclassEquiv_eq_refl :
    singleFactorSquareclassEquiv =
      MulEquiv.refl minimalDescentCurve.toAffine.M := by
  apply MulEquiv.ext
  intro m
  induction m using QuotientGroup.induction_on with
  | H u =>
      change
        AdjoinRoot.modPowEquivPiFactors minimalDescentCurve.toAffine.f_ne_zero
            minimalDescentCurve.toAffine.squarefree_f 2 (QuotientGroup.mk u) default =
          QuotientGroup.mk u
      rw [AdjoinRoot.modPowEquivPiFactors_mk, projFactor_default_eq_id]
      rfl

/-- The explicit algebra equivalence commutes with the relative norm on
squareclasses. -/
theorem relativeNorm_minimalDescentSquareclassEquiv
    (m : minimalDescentCurve.toAffine.M) :
    relativeNormSquareclasses (minimalDescentSquareclassEquiv m) =
      minimalDescentCurve.toAffine.normM m := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply, relativeNormSquareclasses,
    minimalDescentSquareclassEquiv]
  exact congrArg QuotientGroup.mk <| Units.ext <|
    norm_minimalDescentAlgebraEquiv (u : minimalDescentCurve.toAffine.A)

/-! ## Integral-closure transport for the unique factor -/

private abbrev MinimalFactorField :=
  AdjoinRoot
    ((default : minimalDescentCurve.toAffine.f.Factors) : K[X])

private abbrev MinimalFactorIntegers :=
  minimalDescentCurve.toAffine.ringOfIntegersFactor (𝓞 K) default

private theorem minimalDescentAlgebraEquiv_comp_base :
    (algebraMap (𝓞 K) M).comp (RingHom.id (𝓞 K)) =
      minimalDescentAlgebraEquiv.toRingEquiv.toRingHom.comp
        (algebraMap (𝓞 K) minimalDescentCurve.toAffine.A) := by
  ext x
  change algebraMap K M (algebraMap (𝓞 K) K x) =
    minimalDescentAlgebraEquiv
      (algebraMap K minimalDescentCurve.toAffine.A
        (algebraMap (𝓞 K) K x))
  rw [minimalDescentAlgebraEquiv.commutes]

private theorem minimalDescentAlgebraEquiv_symm_comp_base :
    (algebraMap (𝓞 K) minimalDescentCurve.toAffine.A).comp
        (RingHom.id (𝓞 K)) =
      minimalDescentAlgebraEquiv.symm.toRingEquiv.toRingHom.comp
        (algebraMap (𝓞 K) M) := by
  ext x
  change algebraMap K minimalDescentCurve.toAffine.A
      (algebraMap (𝓞 K) K x) =
    minimalDescentAlgebraEquiv.symm
      (algebraMap K M (algebraMap (𝓞 K) K x))
  rw [minimalDescentAlgebraEquiv.symm.commutes]

/-- The algebra equivalence restricts to the corresponding integral
closures over the coefficient ring. -/
private def minimalFactorIntegersEquiv :
    MinimalFactorIntegers ≃+* RelativeIntegers where
  toFun x := ⟨minimalDescentAlgebraEquiv x,
    IsIntegral.map_of_comp_eq (RingHom.id (𝓞 K))
      minimalDescentAlgebraEquiv.toRingEquiv.toRingHom
      minimalDescentAlgebraEquiv_comp_base x.property⟩
  invFun x := ⟨minimalDescentAlgebraEquiv.symm x,
    IsIntegral.map_of_comp_eq (RingHom.id (𝓞 K))
      minimalDescentAlgebraEquiv.symm.toRingEquiv.toRingHom
      minimalDescentAlgebraEquiv_symm_comp_base x.property⟩
  left_inv x :=
    Subtype.ext (minimalDescentAlgebraEquiv.symm_apply_apply x)
  right_inv x :=
    Subtype.ext (minimalDescentAlgebraEquiv.apply_symm_apply x)
  map_mul' x y := Subtype.ext
    (map_mul minimalDescentAlgebraEquiv
      (x : minimalDescentCurve.toAffine.A)
      (y : minimalDescentCurve.toAffine.A))
  map_add' x y := Subtype.ext
    (map_add minimalDescentAlgebraEquiv
      (x : minimalDescentCurve.toAffine.A)
      (y : minimalDescentCurve.toAffine.A))

/-- The same field equivalence with the unique factor exposed in its
source type. -/
private def minimalFactorToCompositumEquiv :
    MinimalFactorField ≃+* M :=
  minimalDescentAlgebraEquiv.toRingEquiv

private theorem minimalFactor_field_comp :
    (algebraMap RelativeIntegers M).comp
        minimalFactorIntegersEquiv.toRingHom =
      minimalFactorToCompositumEquiv.toRingHom.comp
        (algebraMap MinimalFactorIntegers MinimalFactorField) := by
  ext x
  rfl

private theorem minimalFactorIntegersEquiv_algebraMap (x : 𝓞 K) :
    minimalFactorIntegersEquiv
        (algebraMap (𝓞 K) MinimalFactorIntegers x) =
      algebraMap (𝓞 K) RelativeIntegers x := by
  apply Subtype.ext
  change minimalDescentAlgebraEquiv
      (algebraMap K minimalDescentCurve.toAffine.A
        (algebraMap (𝓞 K) K x)) =
    algebraMap K M (algebraMap (𝓞 K) K x)
  exact minimalDescentAlgebraEquiv.commutes _

private theorem minimalFactorIntegersEquiv_comp_base :
    minimalFactorIntegersEquiv.toRingHom.comp
        (algebraMap (𝓞 K) MinimalFactorIntegers) =
      algebraMap (𝓞 K) RelativeIntegers := by
  ext x
  exact congrArg Subtype.val
    (minimalFactorIntegersEquiv_algebraMap x)

private theorem below_comap_minimalFactorIntegersEquiv
    (w : HeightOneSpectrum RelativeIntegers)
    (hne : w.asIdeal.comap minimalFactorIntegersEquiv.toRingHom ≠ ⊥) :
    (HeightOneSpectrum.comapOfNeBot
        minimalFactorIntegersEquiv.toRingHom w hne).below (𝓞 K) =
      w.below (𝓞 K) := by
  apply HeightOneSpectrum.ext
  change
    (w.asIdeal.comap minimalFactorIntegersEquiv.toRingHom).comap
        (algebraMap (𝓞 K) MinimalFactorIntegers) =
      w.asIdeal.comap (algebraMap (𝓞 K) RelativeIntegers)
  rw [Ideal.comap_comap, minimalFactorIntegersEquiv_comp_base]

private theorem minimalDescentSquareclassEquiv_eq_factorMap
    (m : Units.modPow MinimalFactorField 2) :
    minimalDescentSquareclassEquiv m =
      Units.modPow.map minimalFactorToCompositumEquiv.toMonoidHom 2 m := by
  induction m using QuotientGroup.induction_on with
  | H u => rfl

/-- Valuation support transports from the unique generic factor to the
explicit degree-nine field through the integral-closure equivalence. -/
private theorem minimalFactorSelmer_mem_dyadicSelmerM
    (m : Units.modPow MinimalFactorField 2)
    (hm : m ∈ minimalDescentCurve.toAffine.selmerGroupFactor (𝓞 K)
      coefficientDyadicSupport default) :
    minimalDescentSquareclassEquiv m ∈ DyadicSelmerM := by
  induction m using QuotientGroup.induction_on with
  | H u =>
      intro w hw
      rw [minimalDescentSquareclassEquiv_eq_factorMap,
        Units.modPow.map_mk,
        HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
      have hne :
          w.asIdeal.comap minimalFactorIntegersEquiv.toRingHom ≠ ⊥ := by
        intro hbot
        apply w.ne_bot
        rw [← Ideal.map_comap_of_surjective
          minimalFactorIntegersEquiv.toRingHom
          minimalFactorIntegersEquiv.surjective w.asIdeal,
          hbot, Ideal.map_bot]
      let v : HeightOneSpectrum MinimalFactorIntegers :=
        HeightOneSpectrum.comapOfNeBot
          minimalFactorIntegersEquiv.toRingHom w hne
      have hv : v ∉ HeightOneSpectrum.primesAbove (𝓞 K)
          MinimalFactorIntegers coefficientDyadicSupport := by
        rw [HeightOneSpectrum.mem_primesAbove_iff]
        rw [show v.below (𝓞 K) = w.below (𝓞 K) from
          below_comap_minimalFactorIntegersEquiv w hne]
        intro hwbelow
        apply hw
        exact (HeightOneSpectrum.mem_primesAbove_iff
          (𝓞 K) RelativeIntegers coefficientDyadicSupport w).mpr hwbelow
      exact HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
        minimalFactorToCompositumEquiv.toRingHom
        minimalFactorIntegersEquiv.toRingHom minimalFactor_field_comp
        w hne u
        ((HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v 2 u).mp
          (hm v hv))

/-- The generic `selmerGroupA` is membership in its unique irreducible
factor, with no residual product condition. -/
theorem mem_selmerGroupA_iff_singleFactor
    (m : minimalDescentCurve.toAffine.M) :
    m ∈ minimalDescentCurve.toAffine.selmerGroupA (𝓞 K)
        coefficientDyadicSupport ↔
      singleFactorSquareclassEquiv m ∈
        minimalDescentCurve.toAffine.selmerGroupFactor (𝓞 K)
          coefficientDyadicSupport default := by
  rw [minimalDescentCurve.toAffine.mem_selmerGroupA_iff]
  constructor
  · intro h
    exact h default
  · intro h p
    have hp : p = default := Subsingleton.elim _ _
    subst p
    exact h

/-- The generic supported group embeds in the explicit dyadic supported
squareclasses under the minimal descent-algebra equivalence. -/
theorem minimalDescentCurve_selmerGroupA_le_dyadicSelmerM :
    minimalDescentCurve.toAffine.selmerGroupA (𝓞 K)
        coefficientDyadicSupport ≤
      DyadicSelmerM.comap minimalDescentSquareclassEquiv.toMonoidHom := by
  intro m hm
  have hfactor :
      singleFactorSquareclassEquiv m ∈
        minimalDescentCurve.toAffine.selmerGroupFactor (𝓞 K)
          coefficientDyadicSupport default :=
    (mem_selmerGroupA_iff_singleFactor m).mp hm
  rw [singleFactorSquareclassEquiv_eq_refl] at hfactor
  exact minimalFactorSelmer_mem_dyadicSelmerM m hfactor

/-- Every global `x - T` descent class belongs to the explicit dyadic
relative-norm kernel. -/
theorem minimalDescentCurve_range_μ_le_descentDyadicNormKernel :
    (minimalDescentCurve.toAffine.μ).range ≤
      descentDyadicNormKernel := by
  intro m hm
  constructor
  · exact minimalDescentCurve_selmerGroupA_le_dyadicSelmerM
      (minimalDescentCurve_range_μ_le_dyadicSelmerGroupA hm)
  · exact minimalDescentCurve.toAffine.range_μ_le_ker_normM hm

end

end MazurTorsion.XOneEighteenGlobalSelmerBridge
