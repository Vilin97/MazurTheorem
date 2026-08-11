/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenDyadicCompletionBridge
import MazurTorsion.NumberTheory.XOneEighteenDyadicGeneratorRingCertificate
import MazurTorsion.NumberTheory.XOneEighteenGlobalSelmerBridge

/-!
# Dyadic separation of the global `X₁(18)` norm-kernel generators

The selected dyadic factor reduces the normalized degree-nine generator to
`7 + 10τ + τ²` modulo `16`.  Consequently the fifteen nonidentity products
of the four global norm-kernel generators have the nonsquare reductions
certified in `XOneEighteenDyadicGeneratorRingCertificate`.

The raw residue products do not separate arbitrary pairs of masks: even
integral representatives can acquire zero divisors modulo `16`.  Pairwise
separation is instead deduced from the abstract exponent-two squareclass
identity and bitwise XOR, after proving that every nonzero mask has
nonidentity local squareclass.
-/

open Polynomial NumberField

namespace MazurTorsion.XOneEighteenDyadicKernelSeparation

noncomputable section

open MazurTorsion.XOneEighteenDyadicCompletionBridge
open MazurTorsion.XOneEighteenDyadicCubicCertificate
open MazurTorsion.XOneEighteenDyadicGeneratorCertificate
open MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate
open MazurTorsion.XOneEighteenDyadicLocalImage
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicLift

/-! ## Reduction of the genuine completion modulo `16` -/

private def residueBaseReduction16 : ZMod 128 →+* ZMod 16 :=
  ZMod.castHom (by norm_num : 16 ∣ 128) (ZMod 16)

private theorem cubicPolynomial128_map_residueBaseReduction16 :
    cubicPolynomial128.map residueBaseReduction16 = cubicPolynomial16 := by
  norm_num [cubicPolynomial128, cubicPolynomial16, residueBaseReduction16]

/-- Reduction from the explicit cubic ring modulo `128` to the same cubic
ring modulo `16`. -/
def residueReduction16 : CubicResidue128 →+* CubicRing16 :=
  AdjoinRoot.map residueBaseReduction16 cubicPolynomial128 cubicPolynomial16
    (by rw [cubicPolynomial128_map_residueBaseReduction16])

@[simp] theorem residueReduction16_root :
    residueReduction16 (AdjoinRoot.root cubicPolynomial128) = tau16 := by
  exact AdjoinRoot.map_root _ _ _ _

/-- Genuine reduction of the selected coefficient completion's integer
ring to the cubic coefficient ring modulo `16`. -/
def completionReduction16 : CoefficientCompletionIntegers →+* CubicRing16 :=
  residueReduction16.comp completionReduction

@[simp] theorem completionReduction16_coefficientInteger :
    completionReduction16
        (algebraMap (NumberField.RingOfIntegers Q.K)
          CoefficientCompletionIntegers
          coefficientInteger) = tau16 := by
  rw [completionReduction16, RingHom.comp_apply,
    completionReduction_coefficientInteger, residueReduction16_root]

/-! ## The normalized integral generator in the selected completion -/

/-- The integral relative cubic, base changed to the selected completion's
integer ring. -/
def localNormalizedRelativePolynomial :
    Polynomial CoefficientCompletionIntegers :=
  normalizedRelativePolynomialInteger.map
    (algebraMap (NumberField.RingOfIntegers Q.K)
      CoefficientCompletionIntegers)

theorem localNormalizedRelativePolynomial_monic :
    localNormalizedRelativePolynomial.Monic :=
  normalizedRelativePolynomialInteger_monic.map _

private theorem localProjectedNormalized_root :
    Polynomial.aeval (localRelativeProjection normalizedElement)
      localNormalizedRelativePolynomial = 0 := by
  letI : IsScalarTower (NumberField.RingOfIntegers Q.K)
      CoefficientCompletionIntegers CoefficientCompletion :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  calc
    Polynomial.aeval (localRelativeProjection normalizedElement)
        localNormalizedRelativePolynomial =
      Polynomial.aeval (localRelativeProjection normalizedElement)
        normalizedRelativePolynomialInteger := by
          rw [localNormalizedRelativePolynomial,
            Polynomial.aeval_map_algebraMap]
    _ = Polynomial.aeval (localRelativeProjection normalizedElement)
        (normalizedRelativePolynomialInteger.map
          (algebraMap (NumberField.RingOfIntegers Q.K) Q.K)) := by
          rw [Polynomial.aeval_map_algebraMap]
    _ = Polynomial.aeval (localRelativeProjection normalizedElement)
        normalizedRelativePolynomial := by
          rw [normalizedRelativePolynomialInteger_map]
    _ = localRelativeProjection
        (Polynomial.aeval normalizedElement normalizedRelativePolynomial) :=
      Polynomial.aeval_algHom_apply
        localRelativeProjection normalizedElement _
    _ = 0 := by rw [normalizedElement_relative_root, map_zero]

private theorem localProjectedNormalized_isIntegral :
    IsIntegral CoefficientCompletionIntegers
      (localRelativeProjection normalizedElement) :=
  ⟨localNormalizedRelativePolynomial,
    localNormalizedRelativePolynomial_monic,
    localProjectedNormalized_root⟩

private theorem exists_localProjectedNormalizedInteger :
    ∃ z : CoefficientCompletionIntegers,
      algebraMap CoefficientCompletionIntegers CoefficientCompletion z =
        localRelativeProjection normalizedElement :=
  IsIntegrallyClosed.isIntegral_iff.mp localProjectedNormalized_isIntegral

/-- The integral lift of the projected normalized degree-nine generator. -/
def localProjectedNormalizedInteger : CoefficientCompletionIntegers :=
  Classical.choose exists_localProjectedNormalizedInteger

@[simp] theorem localProjectedNormalizedInteger_coe :
    (localProjectedNormalizedInteger : CoefficientCompletion) =
      localRelativeProjection normalizedElement :=
  Classical.choose_spec exists_localProjectedNormalizedInteger

private theorem localProjectedNormalizedInteger_root :
    Polynomial.aeval localProjectedNormalizedInteger
      localNormalizedRelativePolynomial = 0 := by
  apply (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
    (R := CoefficientCompletionIntegers)
    (A := CoefficientCompletionIntegers)
    (B := CoefficientCompletion)
    (FaithfulSMul.algebraMap_injective
      CoefficientCompletionIntegers CoefficientCompletion)).mp
  change Polynomial.aeval
    (localProjectedNormalizedInteger : CoefficientCompletion)
      localNormalizedRelativePolynomial = 0
  rw [localProjectedNormalizedInteger_coe]
  exact localProjectedNormalized_root

/-- The selected normalized generator reduces to `7 + 10τ + τ²` modulo
`16`. -/
theorem completionReduction16_localProjectedNormalizedInteger :
    completionReduction16 localProjectedNormalizedInteger =
      fromVec normalizedGenerator := by
  have hEval :
      Polynomial.aeval localProjectedNormalizedInteger
          normalizedRelativePolynomialInteger = 0 := by
    simpa only [localNormalizedRelativePolynomial,
      Polynomial.aeval_map_algebraMap] using
        localProjectedNormalizedInteger_root
  have h := congrArg completionReduction16 hEval
  have hroot :
      (completionReduction16 localProjectedNormalizedInteger) ^ 3 +
          (tau16 ^ 2 - 3) *
            (completionReduction16 localProjectedNormalizedInteger) ^ 2 +
        (-2 * tau16 ^ 2 + tau16 + 4) *
            completionReduction16 localProjectedNormalizedInteger - 1 = 0 := by
    simpa only [normalizedRelativePolynomialInteger, aeval_add, aeval_sub,
      aeval_mul, aeval_X_pow, aeval_X, aeval_C, aeval_one, map_add, map_sub,
      map_mul, map_pow, map_neg, map_zero, map_one, map_ofNat,
      completionReduction16_coefficientInteger] using h
  exact normalizedRelativeCubic_root_eq _ hroot

/-! ## Reductions of the four explicit generators -/

private def generatorPolynomial : Fin 4 → Polynomial ℤ
  | 0 => h1PolynomialInt
  | 1 => h2PolynomialInt
  | 2 => h3PolynomialInt
  | 3 => h4PolynomialInt

/-- The four projected global generators, as genuine integers in the
selected coefficient completion. -/
def localProjectedGeneratorInteger (i : Fin 4) :
    CoefficientCompletionIntegers :=
  Polynomial.aeval localProjectedNormalizedInteger
    ((generatorPolynomial i).map
      (algebraMap ℤ CoefficientCompletionIntegers))

private theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B]
    (f : A →+* B) (x : A) (p : Polynomial ℤ) :
    f (Polynomial.aeval x p) = Polynomial.aeval (f x) p := by
  have hA : algebraMap ℤ A = Int.castRingHom A := Subsingleton.elim _ _
  have hB : algebraMap ℤ B = Int.castRingHom B := Subsingleton.elim _ _
  have hcomp : f.comp (Int.castRingHom A) = Int.castRingHom B :=
    Subsingleton.elim _ _
  rw [Polynomial.aeval_def, Polynomial.aeval_def, hA, hB,
    Polynomial.hom_eval₂, hcomp]

private theorem localProjectedInteger_aeval_coe (p : Polynomial ℤ) :
    ((Polynomial.aeval localProjectedNormalizedInteger
        (p.map (algebraMap ℤ CoefficientCompletionIntegers)) :
          CoefficientCompletionIntegers) : CoefficientCompletion) =
      localRelativeProjection (Polynomial.aeval normalizedElement p) := by
  calc
    ((Polynomial.aeval localProjectedNormalizedInteger
        (p.map (algebraMap ℤ CoefficientCompletionIntegers)) :
          CoefficientCompletionIntegers) : CoefficientCompletion) =
      ((Polynomial.aeval localProjectedNormalizedInteger p :
          CoefficientCompletionIntegers) : CoefficientCompletion) := by
        exact congrArg
          (fun x : CoefficientCompletionIntegers ↦
            (x : CoefficientCompletion))
          (Polynomial.aeval_map_algebraMap
            CoefficientCompletionIntegers
            localProjectedNormalizedInteger p)
    _ = Polynomial.aeval
        (localProjectedNormalizedInteger : CoefficientCompletion) p :=
      map_aeval_int
        (algebraMap CoefficientCompletionIntegers CoefficientCompletion)
        localProjectedNormalizedInteger p
    _ = Polynomial.aeval
        (localRelativeProjection normalizedElement) p := by
      rw [localProjectedNormalizedInteger_coe]
    _ = localRelativeProjection
        (Polynomial.aeval normalizedElement p) :=
      (map_aeval_int localRelativeProjection.toRingHom
        normalizedElement p).symm

@[simp] theorem localProjectedGeneratorInteger_coe (i : Fin 4) :
    (localProjectedGeneratorInteger i : CoefficientCompletion) =
      localRelativeProjection
        (match i with
        | 0 => h1
        | 1 => h2
        | 2 => h3
        | 3 => h4) := by
  fin_cases i
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h1_formula] using localProjectedInteger_aeval_coe h1PolynomialInt
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h2_formula] using localProjectedInteger_aeval_coe h2PolynomialInt
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h3_formula] using localProjectedInteger_aeval_coe h3PolynomialInt
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h4_formula] using localProjectedInteger_aeval_coe h4PolynomialInt

@[simp] theorem completionReduction16_localProjectedGeneratorInteger
    (i : Fin 4) :
    completionReduction16 (localProjectedGeneratorInteger i) =
      fromVec (generator i) := by
  have hmap (p : Polynomial ℤ) :
      completionReduction16
          (Polynomial.aeval localProjectedNormalizedInteger
            (p.map (algebraMap ℤ CoefficientCompletionIntegers))) =
        Polynomial.aeval (fromVec normalizedGenerator) p := by
    calc
      completionReduction16
          (Polynomial.aeval localProjectedNormalizedInteger
            (p.map (algebraMap ℤ CoefficientCompletionIntegers))) =
        completionReduction16
          (Polynomial.aeval localProjectedNormalizedInteger p) := by
            exact congrArg completionReduction16
              (Polynomial.aeval_map_algebraMap
                CoefficientCompletionIntegers
                localProjectedNormalizedInteger p)
      _ = Polynomial.aeval
          (completionReduction16 localProjectedNormalizedInteger) p :=
        map_aeval_int completionReduction16
          localProjectedNormalizedInteger p
      _ = Polynomial.aeval (fromVec normalizedGenerator) p := by
        rw [completionReduction16_localProjectedNormalizedInteger]
  fin_cases i
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h1PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.firstGenerator
    rw [hmap]
    simpa only [h1PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_firstGenerator.symm
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h2PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.secondGenerator
    rw [hmap]
    simpa only [h2PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_secondGenerator.symm
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h3PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.thirdGenerator
    rw [hmap]
    simpa only [h3PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_thirdGenerator.symm
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h4PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.fourthGenerator
    rw [hmap]
    simpa only [h4PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_fourthGenerator.symm

private theorem localProjectedGeneratorInteger_ne_zero (i : Fin 4) :
    (localProjectedGeneratorInteger i : CoefficientCompletion) ≠ 0 := by
  intro hi
  have hiInt : localProjectedGeneratorInteger i = 0 := by
    apply Subtype.ext
    exact hi
  have hred := congrArg completionReduction16 hiInt
  rw [completionReduction16_localProjectedGeneratorInteger, map_zero] at hred
  have hgen : generator i = (0 : Fin 3 → ZMod 16) := by
    apply fromVec.injective
    simpa only [map_zero] using hred
  have hgen_ne : generator i ≠ (0 : Fin 3 → ZMod 16) := by
    rw [generator_eq]
    fin_cases i <;> decide
  exact hgen_ne hgen

private def localProjectedGeneratorUnit (i : Fin 4) :
    CoefficientCompletionˣ :=
  Units.mk0 (localProjectedGeneratorInteger i : CoefficientCompletion)
    (localProjectedGeneratorInteger_ne_zero i)

private theorem localRelativeSquareclassProjection_kernelGenerator
    (i : Fin 4) :
    localRelativeSquareclassProjection (kernelGenerator i) =
      QuotientGroup.mk (localProjectedGeneratorUnit i) := by
  fin_cases i
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h1 =
      (localProjectedGeneratorInteger 0 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 0).symm
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h2 =
      (localProjectedGeneratorInteger 1 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 1).symm
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h3 =
      (localProjectedGeneratorInteger 2 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 2).symm
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h4 =
      (localProjectedGeneratorInteger 3 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 3).symm

private def localProjectedRepresentativeInteger (mask : Fin 16) :
    CoefficientCompletionIntegers :=
  (if mask.val.testBit 0 then localProjectedGeneratorInteger 0 else 1) *
  (if mask.val.testBit 1 then localProjectedGeneratorInteger 1 else 1) *
  (if mask.val.testBit 2 then localProjectedGeneratorInteger 2 else 1) *
  (if mask.val.testBit 3 then localProjectedGeneratorInteger 3 else 1)

private def localProjectedRepresentativeUnit (mask : Fin 16) :
    CoefficientCompletionˣ :=
  (if mask.val.testBit 0 then localProjectedGeneratorUnit 0 else 1) *
  (if mask.val.testBit 1 then localProjectedGeneratorUnit 1 else 1) *
  (if mask.val.testBit 2 then localProjectedGeneratorUnit 2 else 1) *
  (if mask.val.testBit 3 then localProjectedGeneratorUnit 3 else 1)

private theorem localProjectedRepresentativeUnit_val (mask : Fin 16) :
    (localProjectedRepresentativeUnit mask : CoefficientCompletion) =
      (localProjectedRepresentativeInteger mask : CoefficientCompletion) := by
  unfold localProjectedRepresentativeUnit localProjectedRepresentativeInteger
  split_ifs <;> rfl

private theorem completionReduction16_localProjectedRepresentativeInteger
    (mask : Fin 16) :
    completionReduction16 (localProjectedRepresentativeInteger mask) =
      fromVec (maskedProduct mask) := by
  unfold localProjectedRepresentativeInteger maskedProduct
  split_ifs <;>
    simp only [map_mul, map_one,
      completionReduction16_localProjectedGeneratorInteger,
      fromVec_mul, fromVec_one, mul_assoc, mul_one, one_mul]

private theorem localRelativeSquareclassProjection_kernelRepresentative
    (mask : Fin 16) :
    localRelativeSquareclassProjection (kernelRepresentative mask) =
      QuotientGroup.mk (localProjectedRepresentativeUnit mask) := by
  unfold kernelRepresentative localProjectedRepresentativeUnit
  split_ifs <;>
    simp only [map_mul, map_one, QuotientGroup.mk_mul, QuotientGroup.mk_one,
      localRelativeSquareclassProjection_kernelGenerator]

private theorem completionReduction16_isSquare_of_field_isSquare
    (x : CoefficientCompletionIntegers)
    (hx : IsSquare (x : CoefficientCompletion)) :
    IsSquare (completionReduction16 x) := by
  obtain ⟨z, hz⟩ := hx
  have hzIntegral : IsIntegral CoefficientCompletionIntegers z := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [pow_two, ← hz]
    exact isIntegral_algebraMap
  obtain ⟨zInt, hzInt⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp hzIntegral
  refine ⟨completionReduction16 zInt, ?_⟩
  rw [← map_mul]
  apply congrArg completionReduction16
  apply Subtype.ext
  have hzInt' : (zInt : CoefficientCompletion) = z := hzInt
  change (x : CoefficientCompletion) =
    (zInt : CoefficientCompletion) * zInt
  exact hz.trans (congrArg₂ (· * ·) hzInt'.symm hzInt'.symm)

private theorem exists_nonzeroMask_index {mask : Fin 16} (hmask : mask ≠ 0) :
    ∃ i : Fin 15, nonzeroMask i = mask := by
  have hval : mask.val ≠ 0 := by
    intro hzero
    apply hmask
    exact Fin.ext hzero
  let i : Fin 15 := ⟨mask.val - 1, by omega⟩
  refine ⟨i, Fin.ext ?_⟩
  simp only [nonzeroMask, i]
  omega

/-- A global masked product has trivial selected local squareclass exactly
when the mask is zero. -/
theorem localRelativeSquareclassProjection_kernelRepresentative_eq_one_iff
    (mask : Fin 16) :
    localRelativeSquareclassProjection (kernelRepresentative mask) = 1 ↔
      mask = 0 := by
  constructor
  · intro hlocal
    rw [localRelativeSquareclassProjection_kernelRepresentative,
      Units.modPow.mk_eq_one_iff_isSquare] at hlocal
    have hfield :
        IsSquare
          (localProjectedRepresentativeInteger mask : CoefficientCompletion) := by
      simpa only [localProjectedRepresentativeUnit_val] using hlocal
    have hred := completionReduction16_isSquare_of_field_isSquare
      (localProjectedRepresentativeInteger mask) hfield
    rw [completionReduction16_localProjectedRepresentativeInteger] at hred
    by_contra hmask
    obtain ⟨i, hi⟩ := exists_nonzeroMask_index hmask
    rw [← hi] at hred
    exact fromVec_maskedProduct_nonsquare i hred
  · rintro rfl
    rw [kernelRepresentative_zero, map_one]

/-! ## Abstract exponent-two XOR and global injectivity -/

private def maskXor (a b : Fin 16) : Fin 16 :=
  ⟨a.val ^^^ b.val, by
    have ha : a.val < 2 ^ 4 := by omega
    have hb : b.val < 2 ^ 4 := by omega
    simpa using Nat.xor_lt_two_pow ha hb⟩

private theorem maskXor_eq_zero_iff (a b : Fin 16) :
    maskXor a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hval := congrArg (fun z : Fin 16 ↦ z.val) h
    change a.val ^^^ b.val = 0 at hval
    apply Fin.ext
    calc
      a.val = (a.val ^^^ b.val) ^^^ b.val :=
        (Nat.xor_xor_cancel_right _ _).symm
      _ = 0 ^^^ b.val := by rw [hval]
      _ = b.val := Nat.zero_xor _
  · intro hab
    subst b
    apply Fin.ext
    change a.val ^^^ a.val = 0
    exact Nat.xor_self _

private theorem kernelRepresentative_mul_eq_xor :
    ∀ a b : Fin 16,
      kernelRepresentative a * kernelRepresentative b =
        kernelRepresentative (maskXor a b) := by
  intro a b
  have hsq (x : Units.modPow M 2) : x * x = 1 := by
    simpa only [pow_two] using
      (Units.modPow.pow_eq_one (n := 2) x)
  have hselect (g : Units.modPow M 2) (u v : Bool) :
      (if u then g else 1) * (if v then g else 1) =
        (if u ^^ v then g else 1) := by
    cases u <;> cases v <;> simp [hsq]
  let factor (mask : Fin 16) (i : Fin 4) : Units.modPow M 2 :=
    if mask.val.testBit i.val then kernelGenerator i else 1
  have hfactor (i : Fin 4) :
      factor a i * factor b i = factor (maskXor a b) i := by
    simpa only [factor, maskXor, Nat.testBit_xor] using
      hselect (kernelGenerator i)
        (a.val.testBit i.val) (b.val.testBit i.val)
  change
    (factor a 0 * factor a 1 * factor a 2 * factor a 3) *
        (factor b 0 * factor b 1 * factor b 2 * factor b 3) =
      factor (maskXor a b) 0 * factor (maskXor a b) 1 *
        factor (maskXor a b) 2 * factor (maskXor a b) 3
  calc
    _ = (factor a 0 * factor b 0) *
        (factor a 1 * factor b 1) *
        (factor a 2 * factor b 2) *
        (factor a 3 * factor b 3) := by ac_rfl
    _ = _ := by rw [hfactor 0, hfactor 1, hfactor 2, hfactor 3]

/-- The sixteen global masked products are pairwise distinct.  The proof
uses the nonidentity local certificate only after abstractly cancelling
repeated generators in the exponent-two squareclass group. -/
theorem kernelRepresentative_injective :
    Function.Injective kernelRepresentative := by
  intro a b hab
  have hxor : kernelRepresentative (maskXor a b) = 1 := by
    rw [← kernelRepresentative_mul_eq_xor]
    rw [hab]
    simpa only [pow_two] using
      (Units.modPow.pow_eq_one (n := 2) (kernelRepresentative b))
  have hlocal :
      localRelativeSquareclassProjection
          (kernelRepresentative (maskXor a b)) = 1 := by
    rw [hxor, map_one]
  have hzero :=
    (localRelativeSquareclassProjection_kernelRepresentative_eq_one_iff
      (maskXor a b)).mp hlocal
  exact (maskXor_eq_zero_iff a b).mp hzero

end

end MazurTorsion.XOneEighteenDyadicKernelSeparation
