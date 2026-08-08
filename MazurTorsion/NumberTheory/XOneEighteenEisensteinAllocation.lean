/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenEisensteinIntegers
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Two-adic allocation for the `X₁(18)` Eisenstein descent

The two split factors in the cyclic-cubic identity have forced powers of
the inert rational prime `2`.  This file removes exactly those powers and
proves that the resulting factors are coprime.  Unique factorization in the
third cyclotomic ring then allocates each normalized factor to an associated
cube, leaving only the finite Eisenstein-unit cases.
-/

open NumberField Polynomial

namespace MazurTorsion.XOneEighteenDescent

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- The rational prime `2` is inert, hence prime, in the Eisenstein
integers.  The proof identifies the quotient with the adjoin-root ring of
`X²+X+1` over `𝔽₂` and checks that polynomial has no root. -/
theorem splitEisensteinTwo_prime
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (hζ : IsPrimitiveRoot ζ 3) :
    Prime (2 : 𝓞 K) := by
  let pb : PowerBasis ℤ (𝓞 K) := hζ.integralPowerBasis
  let I : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let e : (ℤ ⧸ I) ≃+* ZMod 2 := by
    simpa [I] using Int.quotientSpanNatEquivZMod 2
  have hirrTwo : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    have hdegree : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by
      compute_degree
      decide
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [hdegree]; norm_num)
    intro x
    unfold Polynomial.IsRoot
    rw [eval_add, eval_add, eval_pow, eval_X, eval_one]
    fin_cases x
    · change ¬ ((0 : ZMod 2) ^ 2 + 0 + 1 = 0)
      decide
    · change ¬ ((1 : ZMod 2) ^ 2 + 1 + 1 = 0)
      decide
  have hminpoly : minpoly ℤ pb.gen = Polynomial.cyclotomic 3 ℤ := by
    change minpoly ℤ hζ.integralPowerBasis.gen = _
    rw [← hζ.integralPowerBasis.minpolyGen_eq]
    rw [IsPrimitiveRoot.integralPowerBasis, PowerBasis.minpolyGen_map]
    rw [PowerBasis.minpolyGen_eq]
    rw [← Algebra.adjoin.powerBasis'_minpoly_gen]
    exact (Polynomial.cyclotomic_eq_minpoly hζ (by norm_num)).symm
  have hmap :
      Polynomial.mapEquiv e
          ((minpoly ℤ pb.gen).map (Ideal.Quotient.mk I)) =
        (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    simp only [Polynomial.mapEquiv_apply, Polynomial.map_map, hminpoly]
    rw [Polynomial.cyclotomic_three]
    simp [e, I]
  have hirr :
      Irreducible ((minpoly ℤ pb.gen).map (Ideal.Quotient.mk I)) := by
    apply (MulEquiv.irreducible_iff
      (Polynomial.mapEquiv e).toMulEquiv).mp
    change Irreducible (Polynomial.mapEquiv e
      ((minpoly ℤ pb.gen).map (Ideal.Quotient.mk I)))
    rw [hmap]
    exact hirrTwo
  have hprimeIdeal : (I.map (algebraMap ℤ (𝓞 K))).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    letI : I.IsMaximal := by
      change (Ideal.span {(2 : ℤ)}).IsMaximal
      exact @Int.ideal_span_isMaximal_of_prime 2 ⟨Nat.prime_two⟩
    letI : Field (ℤ ⧸ I) := Ideal.Quotient.field I
    letI : IsDomain ((ℤ ⧸ I)[X] ⧸ Ideal.span {
        (minpoly ℤ pb.gen).map (Ideal.Quotient.mk I)}) :=
      AdjoinRoot.isDomain_of_prime hirr.prime
    let eqv := pb.quotientEquivQuotientMinpolyMap I
    exact eqv.toRingEquiv.toMulEquiv.isDomain _
  have hmapIdeal : I.map (algebraMap ℤ (𝓞 K)) =
      Ideal.span {(2 : 𝓞 K)} := by
    simp [I, Ideal.map_span]
  rw [← Ideal.span_singleton_prime (by norm_num : (2 : 𝓞 K) ≠ 0)]
  rw [← hmapIdeal]
  exact hprimeIdeal

/-- The first split factor after removing its forced factor of `2`. -/
def splitHalfFirstFactor (m n : ℤ) : 𝓞 K :=
  (((m + n) / 2 : ℤ) : 𝓞 K) + (n : 𝓞 K) * hζ.toInteger

/-- In the `k = ±4` cases, the second split factor after removing its
forced factor of `2`. -/
def splitHalfSecondFactor (m n : ℤ) : 𝓞 K :=
  ((m + n : ℤ) : 𝓞 K) + (((n - m) / 2 : ℤ) : 𝓞 K) * hζ.toInteger

/-- In the `k = ±8` cases, the second split factor after removing its
forced factor of `4`. -/
def splitQuarterSecondFactor (m n : ℤ) : 𝓞 K :=
  (((m + n) / 2 : ℤ) : 𝓞 K) +
    (((n - m) / 4 : ℤ) : 𝓞 K) * hζ.toInteger

/-- Oddness of both parameters supplies the exact factor `2` in the first
split factor. -/
theorem splitFirstEisensteinFactor_eq_two_mul_half
    (m n : ℤ) (hm : Odd m) (hn : Odd n) :
    splitFirstEisensteinFactor hζ m n =
      2 * splitHalfFirstFactor hζ m n := by
  obtain ⟨u, hu⟩ := hm
  obtain ⟨v, hv⟩ := hn
  have hsum : 2 * ((m + n) / 2) = m + n := by omega
  have hsumO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) hsum
  push_cast at hsumO
  simp only [splitFirstEisensteinFactor, splitHalfFirstFactor]
  push_cast
  rw [← hsumO]
  ring

/-- Oddness of both parameters supplies a factor `2` in the second split
factor. -/
theorem splitSecondEisensteinFactor_eq_two_mul_half
    (m n : ℤ) (hm : Odd m) (hn : Odd n) :
    splitSecondEisensteinFactor hζ m n =
      2 * splitHalfSecondFactor hζ m n := by
  obtain ⟨u, hu⟩ := hm
  obtain ⟨v, hv⟩ := hn
  have hdiff : 2 * ((n - m) / 2) = n - m := by omega
  have hdiffO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) hdiff
  push_cast at hdiffO
  simp only [splitSecondEisensteinFactor, splitHalfSecondFactor]
  push_cast
  rw [← hdiffO]
  ring

/-- Equality of the two odd parameters modulo four supplies the exact
visible factor `4` in the second split factor. -/
theorem splitSecondEisensteinFactor_eq_four_mul_quarter
    (m n : ℤ) (hm : Odd m) (hn : Odd n)
    (hmod : (m : ZMod 4) = (n : ZMod 4)) :
    splitSecondEisensteinFactor hζ m n =
      4 * splitQuarterSecondFactor hζ m n := by
  have hfour : (4 : ℤ) ∣ n - m :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub m n 4).mp hmod
  obtain ⟨u, hu⟩ := hm
  obtain ⟨v, hv⟩ := hn
  obtain ⟨w, hw⟩ := hfour
  have hsum : 2 * ((m + n) / 2) = m + n := by omega
  have hdiff : 4 * ((n - m) / 4) = n - m := by omega
  have hsumO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) hsum
  have hdiffO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) hdiff
  push_cast at hsumO hdiffO
  simp only [splitSecondEisensteinFactor, splitQuarterSecondFactor]
  push_cast
  rw [← hsumO, ← hdiffO]
  ring

/-- The first normalized split factor has exact two-adic depth zero. -/
theorem splitHalfFirstFactor_two_not_dvd
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hn : Odd n) :
    ¬ (2 : 𝓞 K) ∣ splitHalfFirstFactor hζ m n := by
  intro hdiv
  have hcoords := int_dvd_splitEisensteinCoords
    hζ 2 ((m + n) / 2) n
    (by
      convert hdiv using 1
      · norm_num
      · rfl)
  exact (Int.not_even_iff_odd.mpr hn)
    (even_iff_two_dvd.mpr hcoords.2)

/-- In the unequal-modulo-four branch, the second normalized split factor
has exact two-adic depth zero. -/
theorem splitHalfSecondFactor_two_not_dvd
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hm : Odd m) (hn : Odd n)
    (hmod : (m : ZMod 4) ≠ (n : ZMod 4)) :
    ¬ (2 : 𝓞 K) ∣ splitHalfSecondFactor hζ m n := by
  intro hdiv
  have hcoords := int_dvd_splitEisensteinCoords
    hζ 2 (m + n) ((n - m) / 2)
    (by
      convert hdiv using 1
      · norm_num
      · rfl)
  obtain ⟨u, hu⟩ := hm
  obtain ⟨v, hv⟩ := hn
  obtain ⟨w, hw⟩ := hcoords.2
  have hdiff : 2 * ((n - m) / 2) = n - m := by omega
  have hfour : (4 : ℤ) ∣ n - m := by
    refine ⟨w, ?_⟩
    omega
  exact hmod ((ZMod.intCast_eq_intCast_iff_dvd_sub m n 4).mpr hfour)

/-- In the equal-modulo-four branch, the second split factor has exact
two-adic depth two. -/
theorem splitQuarterSecondFactor_two_not_dvd
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hm : Odd m) (hn : Odd n)
    (hmod : (m : ZMod 4) = (n : ZMod 4)) :
    ¬ (2 : 𝓞 K) ∣ splitQuarterSecondFactor hζ m n := by
  intro hdiv
  have hcoords := int_dvd_splitEisensteinCoords
    hζ 2 ((m + n) / 2) ((n - m) / 4)
    (by
      convert hdiv using 1
      · norm_num
      · rfl)
  have hfour : (4 : ℤ) ∣ n - m :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub m n 4).mp hmod
  obtain ⟨u, hu⟩ := hm
  obtain ⟨v, hv⟩ := hn
  obtain ⟨w, hw⟩ := hcoords.1
  obtain ⟨t, ht⟩ := hfour
  have hsum : 2 * ((m + n) / 2) = m + n := by omega
  have hevenN : Even n := by
    refine ⟨w - t, ?_⟩
    omega
  obtain ⟨q, hq⟩ := hevenN
  omega

/-- After removing the forced scalar in a `k = ±4` branch, the two
normalized split factors are coprime. -/
theorem splitHalfFactors_isCoprime
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hm : Odd m) (hn : Odd n)
    (hsupport : ∀ p : 𝓞 K,
      Prime p →
      p ∣ splitFirstEisensteinFactor hζ m n →
      p ∣ splitSecondEisensteinFactor hζ m n →
      p ∣ (2 : 𝓞 K)) :
    IsCoprime (splitHalfFirstFactor hζ m n)
      (splitHalfSecondFactor hζ m n) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  have hfirstScale :=
    splitFirstEisensteinFactor_eq_two_mul_half hζ m n hm hn
  have hsecondScale :=
    splitSecondEisensteinFactor_eq_two_mul_half hζ m n hm hn
  have hfirstNot := splitHalfFirstFactor_two_not_dvd hζ m n hn
  have htwoPrime : Prime (2 : 𝓞 K) := splitEisensteinTwo_prime hζ
  apply isCoprime_of_prime_dvd
  · rintro ⟨hzero, -⟩
    apply hfirstNot
    rw [hzero]
    exact dvd_zero 2
  · intro p hp hpFirst hpSecond
    have hpFirstRaw : p ∣ splitFirstEisensteinFactor hζ m n := by
      rw [hfirstScale]
      exact dvd_mul_of_dvd_right hpFirst 2
    have hpSecondRaw : p ∣ splitSecondEisensteinFactor hζ m n := by
      rw [hsecondScale]
      exact dvd_mul_of_dvd_right hpSecond 2
    have hpTwo := hsupport p hp hpFirstRaw hpSecondRaw
    have hpAssoc : Associated p (2 : 𝓞 K) :=
      hp.associated_of_dvd htwoPrime hpTwo
    exact hfirstNot (hpAssoc.dvd_iff_dvd_left.mp hpFirst)

/-- After removing the forced scalar in a `k = ±8` branch, the two
normalized split factors are coprime. -/
theorem splitQuarterFactors_isCoprime
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hm : Odd m) (hn : Odd n)
    (hmod : (m : ZMod 4) = (n : ZMod 4))
    (hsupport : ∀ p : 𝓞 K,
      Prime p →
      p ∣ splitFirstEisensteinFactor hζ m n →
      p ∣ splitSecondEisensteinFactor hζ m n →
      p ∣ (2 : 𝓞 K)) :
    IsCoprime (splitHalfFirstFactor hζ m n)
      (splitQuarterSecondFactor hζ m n) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  have hfirstScale :=
    splitFirstEisensteinFactor_eq_two_mul_half hζ m n hm hn
  have hsecondScale :=
    splitSecondEisensteinFactor_eq_four_mul_quarter hζ m n hm hn hmod
  have hfirstNot := splitHalfFirstFactor_two_not_dvd hζ m n hn
  have htwoPrime : Prime (2 : 𝓞 K) := splitEisensteinTwo_prime hζ
  apply isCoprime_of_prime_dvd
  · rintro ⟨hzero, -⟩
    apply hfirstNot
    rw [hzero]
    exact dvd_zero 2
  · intro p hp hpFirst hpSecond
    have hpFirstRaw : p ∣ splitFirstEisensteinFactor hζ m n := by
      rw [hfirstScale]
      exact dvd_mul_of_dvd_right hpFirst 2
    have hpSecondRaw : p ∣ splitSecondEisensteinFactor hζ m n := by
      rw [hsecondScale]
      exact dvd_mul_of_dvd_right hpSecond 4
    have hpTwo := hsupport p hp hpFirstRaw hpSecondRaw
    have hpAssoc : Associated p (2 : 𝓞 K) :=
      hp.associated_of_dvd htwoPrime hpTwo
    exact hfirstNot (hpAssoc.dvd_iff_dvd_left.mp hpFirst)

/-- In either `k = ±4` scalar case, both normalized split factors are
associated to cubes. -/
theorem exists_associated_cubes_of_four_scalar
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n a b k : ℤ) (hm : Odd m) (hn : Odd n)
    (hsupport : ∀ p : 𝓞 K,
      Prime p →
      p ∣ splitFirstEisensteinFactor hζ m n →
      p ∣ splitSecondEisensteinFactor hζ m n →
      p ∣ (2 : 𝓞 K))
    (hfactor :
      hζ.toInteger * splitFirstEisensteinFactor hζ m n *
          splitSecondEisensteinFactor hζ m n =
        (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3)
    (hk : k = -4 ∨ k = 4) :
    ∃ x y : 𝓞 K,
      Associated (x ^ 3) (splitHalfFirstFactor hζ m n) ∧
      Associated (y ^ 3) (splitHalfSecondFactor hζ m n) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  let z : 𝓞 K := ((a : ℤ) : 𝓞 K) + b * hζ.toInteger
  let first := splitHalfFirstFactor hζ m n
  let second := splitHalfSecondFactor hζ m n
  have hfirstScale : splitFirstEisensteinFactor hζ m n = 2 * first :=
    splitFirstEisensteinFactor_eq_two_mul_half hζ m n hm hn
  have hsecondScale : splitSecondEisensteinFactor hζ m n = 2 * second :=
    splitSecondEisensteinFactor_eq_two_mul_half hζ m n hm hn
  have hcoprime : IsCoprime first second :=
    splitHalfFactors_isCoprime hζ m n hm hn hsupport
  have hη : IsUnit hζ.toInteger :=
    hζ.toInteger_isPrimitiveRoot.isUnit (by decide)
  have hproduct : ∃ w : 𝓞 K, Associated (w ^ 3) (first * second) := by
    rcases hk with rfl | rfl
    · refine ⟨-z, ?_⟩
      have hscaled : hζ.toInteger * first * second = (-z) ^ 3 := by
        apply mul_left_cancel₀ (show (4 : 𝓞 K) ≠ 0 by norm_num)
        calc
          (4 : 𝓞 K) * (hζ.toInteger * first * second) =
              hζ.toInteger * (2 * first) * (2 * second) := by ring
          _ = (((-4 : ℤ) : 𝓞 K)) * z ^ 3 := by
            simpa only [hfirstScale, hsecondScale, z] using hfactor
          _ = (4 : 𝓞 K) * (-z) ^ 3 := by ring
      rw [← hscaled]
      simpa only [mul_assoc] using
        associated_unit_mul_left (first * second) hζ.toInteger hη
    · refine ⟨z, ?_⟩
      have hscaled : hζ.toInteger * first * second = z ^ 3 := by
        apply mul_left_cancel₀ (show (4 : 𝓞 K) ≠ 0 by norm_num)
        calc
          (4 : 𝓞 K) * (hζ.toInteger * first * second) =
              hζ.toInteger * (2 * first) * (2 * second) := by ring
          _ = (((4 : ℤ) : 𝓞 K)) * z ^ 3 := by
            simpa only [hfirstScale, hsecondScale, z] using hfactor
          _ = (4 : 𝓞 K) * z ^ 3 := by norm_num
      rw [← hscaled]
      simpa only [mul_assoc] using
        associated_unit_mul_left (first * second) hζ.toInteger hη
  obtain ⟨w, hw⟩ := hproduct
  obtain ⟨x, hx⟩ :=
    exists_associated_pow_of_associated_pow_mul hcoprime hw
  have hw' : Associated (w ^ 3) (second * first) := by
    simpa only [mul_comm] using hw
  obtain ⟨y, hy⟩ :=
    exists_associated_pow_of_associated_pow_mul hcoprime.symm hw'
  exact ⟨x, y, hx, hy⟩

/-- In either `k = ±8` scalar case, both normalized split factors are
associated to cubes. -/
theorem exists_associated_cubes_of_eight_scalar
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n a b k : ℤ) (hm : Odd m) (hn : Odd n)
    (hmod : (m : ZMod 4) = (n : ZMod 4))
    (hsupport : ∀ p : 𝓞 K,
      Prime p →
      p ∣ splitFirstEisensteinFactor hζ m n →
      p ∣ splitSecondEisensteinFactor hζ m n →
      p ∣ (2 : 𝓞 K))
    (hfactor :
      hζ.toInteger * splitFirstEisensteinFactor hζ m n *
          splitSecondEisensteinFactor hζ m n =
        (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3)
    (hk : k = -8 ∨ k = 8) :
    ∃ x y : 𝓞 K,
      Associated (x ^ 3) (splitHalfFirstFactor hζ m n) ∧
      Associated (y ^ 3) (splitQuarterSecondFactor hζ m n) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  let z : 𝓞 K := ((a : ℤ) : 𝓞 K) + b * hζ.toInteger
  let first := splitHalfFirstFactor hζ m n
  let second := splitQuarterSecondFactor hζ m n
  have hfirstScale : splitFirstEisensteinFactor hζ m n = 2 * first :=
    splitFirstEisensteinFactor_eq_two_mul_half hζ m n hm hn
  have hsecondScale : splitSecondEisensteinFactor hζ m n = 4 * second :=
    splitSecondEisensteinFactor_eq_four_mul_quarter hζ m n hm hn hmod
  have hcoprime : IsCoprime first second :=
    splitQuarterFactors_isCoprime hζ m n hm hn hmod hsupport
  have hη : IsUnit hζ.toInteger :=
    hζ.toInteger_isPrimitiveRoot.isUnit (by decide)
  have hproduct : ∃ w : 𝓞 K, Associated (w ^ 3) (first * second) := by
    rcases hk with rfl | rfl
    · refine ⟨-z, ?_⟩
      have hscaled : hζ.toInteger * first * second = (-z) ^ 3 := by
        apply mul_left_cancel₀ (show (8 : 𝓞 K) ≠ 0 by norm_num)
        calc
          (8 : 𝓞 K) * (hζ.toInteger * first * second) =
              hζ.toInteger * (2 * first) * (4 * second) := by ring
          _ = (((-8 : ℤ) : 𝓞 K)) * z ^ 3 := by
            simpa only [hfirstScale, hsecondScale, z] using hfactor
          _ = (8 : 𝓞 K) * (-z) ^ 3 := by ring
      rw [← hscaled]
      simpa only [mul_assoc] using
        associated_unit_mul_left (first * second) hζ.toInteger hη
    · refine ⟨z, ?_⟩
      have hscaled : hζ.toInteger * first * second = z ^ 3 := by
        apply mul_left_cancel₀ (show (8 : 𝓞 K) ≠ 0 by norm_num)
        calc
          (8 : 𝓞 K) * (hζ.toInteger * first * second) =
              hζ.toInteger * (2 * first) * (4 * second) := by ring
          _ = (((8 : ℤ) : 𝓞 K)) * z ^ 3 := by
            simpa only [hfirstScale, hsecondScale, z] using hfactor
          _ = (8 : 𝓞 K) * z ^ 3 := by norm_num
      rw [← hscaled]
      simpa only [mul_assoc] using
        associated_unit_mul_left (first * second) hζ.toInteger hη
  obtain ⟨w, hw⟩ := hproduct
  obtain ⟨x, hx⟩ :=
    exists_associated_pow_of_associated_pow_mul hcoprime hw
  have hw' : Associated (w ^ 3) (second * first) := by
    simpa only [mul_comm] using hw
  obtain ⟨y, hy⟩ :=
    exists_associated_pow_of_associated_pow_mul hcoprime.symm hw'
  exact ⟨x, y, hx, hy⟩

/-- Membership in one of the three cube-unit classes represented by `1`,
`ζ₃`, and `ζ₃²`. -/
def EisensteinCubeUnitClass (A : 𝓞 K) : Prop :=
  ∃ x : 𝓞 K,
    A = x ^ 3 ∨
    A = hζ.toInteger * x ^ 3 ∨
    A = hζ.toInteger ^ 2 * x ^ 3

/-- An associated cube in the third cyclotomic ring belongs to one of the
three cube-unit classes.  The signs of the six units are absorbed into the
cube root. -/
theorem eq_cube_or_zeta_mul_cube_or_zeta_sq_mul_cube_of_associated
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {A z : 𝓞 K} (hassociated : Associated (z ^ 3) A) :
    EisensteinCubeUnitClass hζ A := by
  obtain ⟨u, hu⟩ := hassociated
  have hfactor : A = (u : 𝓞 K) * z ^ 3 := by
    rw [← hu]
    ring
  let η : (𝓞 K)ˣ :=
    (IsPrimitiveRoot.isUnit hζ.toInteger_isPrimitiveRoot (by decide)).unit
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  change u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h <;> subst u
  all_goals
    simp only [η, Units.val_one, Units.val_neg,
      Units.val_pow_eq_pow_val,
      IsCyclotomicExtension.Rat.Three.coe_eta] at hfactor
  · exact ⟨z, Or.inl (by simpa using hfactor)⟩
  · refine ⟨-z, Or.inl ?_⟩
    rw [Odd.neg_pow (by decide : Odd 3)]
    simpa using hfactor
  · exact ⟨z, Or.inr (Or.inl hfactor)⟩
  · refine ⟨-z, Or.inr (Or.inl ?_)⟩
    rw [Odd.neg_pow (by decide : Odd 3)]
    simpa using hfactor
  · exact ⟨z, Or.inr (Or.inr hfactor)⟩
  · refine ⟨-z, Or.inr (Or.inr ?_)⟩
    rw [Odd.neg_pow (by decide : Odd 3)]
    simpa using hfactor

/-! ## Integral coordinates for the three unit classes -/

/-- The real coordinate of the cube of `x+yζ₃`. -/
def eisensteinCubeReal (x y : ℤ) : ℤ :=
  x ^ 3 - 3 * x * y ^ 2 + y ^ 3

/-- The `ζ₃` coordinate of the cube of `x+yζ₃`. -/
def eisensteinCubeEta (x y : ℤ) : ℤ :=
  3 * (x * y * (x - y))

/-- The integral coordinates of a literal Eisenstein cube. -/
theorem eisensteinCube_eq_coords (x y : ℤ) :
    (((x : ℤ) : 𝓞 K) + y * hζ.toInteger) ^ 3 =
      ((eisensteinCubeReal x y : ℤ) : 𝓞 K) +
        eisensteinCubeEta x y * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  simp only [eisensteinCubeReal, eisensteinCubeEta]
  push_cast
  ring_nf
  linear_combination
    (3 * (x : 𝓞 K) * (y : 𝓞 K) ^ 2) * hroot +
      (y : 𝓞 K) ^ 3 * hcube

/-- Coordinates of a cube in the `ζ₃` unit class. -/
theorem zeta_mul_eisensteinCube_eq_coords (x y : ℤ) :
    hζ.toInteger *
        ((((x : ℤ) : 𝓞 K) + y * hζ.toInteger) ^ 3) =
      ((-eisensteinCubeEta x y : ℤ) : 𝓞 K) +
        (eisensteinCubeReal x y - eisensteinCubeEta x y) *
          hζ.toInteger := by
  rw [eisensteinCube_eq_coords]
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  push_cast
  linear_combination (eisensteinCubeEta x y : 𝓞 K) * hroot

/-- Coordinates of a cube in the `ζ₃²` unit class. -/
theorem zeta_sq_mul_eisensteinCube_eq_coords (x y : ℤ) :
    hζ.toInteger ^ 2 *
        ((((x : ℤ) : 𝓞 K) + y * hζ.toInteger) ^ 3) =
      ((eisensteinCubeEta x y - eisensteinCubeReal x y : ℤ) :
          𝓞 K) +
        (-eisensteinCubeReal x y) * hζ.toInteger := by
  rw [eisensteinCube_eq_coords]
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  push_cast
  linear_combination
    (eisensteinCubeReal x y : 𝓞 K) * hroot +
      (eisensteinCubeEta x y : 𝓞 K) * hcube

/-- The three sign-free Eisenstein cube-unit classes. -/
inductive EisensteinCubeUnitIndex
  | one
  | zeta
  | zetaSq
  deriving DecidableEq

/-- Integral coordinates of a cube after multiplication by the indicated
unit-class representative. -/
def eisensteinCubeUnitCoords {R : Type*} [CommRing R]
    (j : EisensteinCubeUnitIndex) (x y : R) : R × R :=
  let real := x ^ 3 - 3 * x * y ^ 2 + y ^ 3
  let eta := 3 * (x * y * (x - y))
  match j with
  | .one => (real, eta)
  | .zeta => (-eta, real - eta)
  | .zetaSq => (eta - real, -real)

/-- A ring element presented in integral coordinates in one of the three
cube-unit classes. -/
def EisensteinCubeCoordinateClass (A : 𝓞 K) : Prop :=
  ∃ (j : EisensteinCubeUnitIndex) (x y : ℤ),
    A = ((eisensteinCubeUnitCoords j x y).1 : ℤ) +
      (eisensteinCubeUnitCoords j x y).2 * hζ.toInteger

/-- The abstract three-unit-class certificate has an integral-coordinate
presentation. -/
theorem eisensteinCubeCoordinateClass_of_unitClass
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {A : 𝓞 K} (hclass : EisensteinCubeUnitClass hζ A) :
    EisensteinCubeCoordinateClass hζ A := by
  obtain ⟨z, h | h | h⟩ := hclass
  all_goals
    obtain ⟨x, y, hxy⟩ := exists_splitEisensteinCoords hζ z
  · refine ⟨EisensteinCubeUnitIndex.one, x, y, ?_⟩
    calc
      A = z ^ 3 := h
      _ = (((x : ℤ) : 𝓞 K) + y * hζ.toInteger) ^ 3 := by rw [hxy]
      _ = _ := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal,
          eisensteinCubeEta] using eisensteinCube_eq_coords hζ x y
  · refine ⟨EisensteinCubeUnitIndex.zeta, x, y, ?_⟩
    calc
      A = hζ.toInteger * z ^ 3 := h
      _ = hζ.toInteger *
          ((((x : ℤ) : 𝓞 K) + y * hζ.toInteger) ^ 3) := by rw [hxy]
      _ = _ := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal,
          eisensteinCubeEta] using
            zeta_mul_eisensteinCube_eq_coords hζ x y
  · refine ⟨EisensteinCubeUnitIndex.zetaSq, x, y, ?_⟩
    calc
      A = hζ.toInteger ^ 2 * z ^ 3 := h
      _ = hζ.toInteger ^ 2 *
          ((((x : ℤ) : 𝓞 K) + y * hζ.toInteger) ^ 3) := by rw [hxy]
      _ = _ := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal,
          eisensteinCubeEta] using
            zeta_sq_mul_eisensteinCube_eq_coords hζ x y

private def fourScalarSecondCoords {R : Type*} [CommRing R]
    (z : R × R) : R × R :=
  (2 * z.1, z.2 - z.1)

private def eightScalarSecondDoubledCoords {R : Type*} [CommRing R]
    (z : R × R) : R × R :=
  (z.1, z.2 - z.1)

private def doubleSecondCoord {R : Type*} [CommRing R]
    (z : R × R) : R × R :=
  (z.1, 2 * z.2)

private theorem false_of_first_cubeCoords_zero_mod
    (p : ℕ) (hp : p.Prime)
    {m n x y : ℤ} {j : EisensteinCubeUnitIndex}
    (hmn : IsCoprime m n) (hm : Odd m) (hn : Odd n)
    (hfirst : ((m + n) / 2, n) = eisensteinCubeUnitCoords j x y)
    (hzero : eisensteinCubeUnitCoords j (x : ZMod p) (y : ZMod p) =
      (0, 0)) :
    False := by
  have hfirstMod :
      ((((m + n) / 2 : ℤ) : ZMod p), (n : ZMod p)) =
        eisensteinCubeUnitCoords j (x : ZMod p) (y : ZMod p) := by
    have hcast := congrArg
      (fun z : ℤ × ℤ ↦ ((z.1 : ZMod p), (z.2 : ZMod p))) hfirst
    cases j <;> simpa [eisensteinCubeUnitCoords] using hcast
  rw [hzero] at hfirstMod
  have hr : (((m + n) / 2 : ℤ) : ZMod p) = 0 := by
    simpa using congrArg Prod.fst hfirstMod
  have hnzero : (n : ZMod p) = 0 := by
    simpa using congrArg Prod.snd hfirstMod
  obtain ⟨r, hrm⟩ := hm
  obtain ⟨s, hsn⟩ := hn
  have hsum : 2 * ((m + n) / 2) = m + n := by omega
  have hsumMod := congrArg (fun z : ℤ ↦ (z : ZMod p)) hsum
  push_cast at hsumMod
  have hmzero : (m : ZMod p) = 0 := by
    rw [hr, hnzero] at hsumMod
    simpa using hsumMod.symm
  have hpm : (p : ℤ) ∣ m := by
    simpa using
      (ZMod.intCast_eq_intCast_iff_dvd_sub 0 m p).mp (by
        simpa only [Int.cast_zero] using hmzero.symm)
  have hpn : (p : ℤ) ∣ n := by
    simpa using
      (ZMod.intCast_eq_intCast_iff_dvd_sub 0 n p).mp (by
        simpa only [Int.cast_zero] using hnzero.symm)
  have hunit : IsUnit (p : ℤ) := hmn.isUnit_of_dvd' hpm hpn
  rw [Int.isUnit_iff] at hunit
  have hpge : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  rcases hunit with hunit | hunit <;> omega

private theorem cast_fourScalar_relation
    (p : ℕ) {x y u v : ℤ} {j l : EisensteinCubeUnitIndex}
    (hrel : fourScalarSecondCoords (eisensteinCubeUnitCoords j x y) =
      eisensteinCubeUnitCoords l u v) :
    fourScalarSecondCoords
        (eisensteinCubeUnitCoords j (x : ZMod p) (y : ZMod p)) =
      eisensteinCubeUnitCoords l (u : ZMod p) (v : ZMod p) := by
  have hcast := congrArg
    (fun z : ℤ × ℤ ↦ ((z.1 : ZMod p), (z.2 : ZMod p))) hrel
  cases j <;> cases l <;>
    simpa [fourScalarSecondCoords, eisensteinCubeUnitCoords] using hcast

private theorem cast_eightScalar_relation
    (p : ℕ) {x y u v : ℤ} {j l : EisensteinCubeUnitIndex}
    (hrel : eightScalarSecondDoubledCoords
        (eisensteinCubeUnitCoords j x y) =
      doubleSecondCoord (eisensteinCubeUnitCoords l u v)) :
    eightScalarSecondDoubledCoords
        (eisensteinCubeUnitCoords j (x : ZMod p) (y : ZMod p)) =
      doubleSecondCoord
        (eisensteinCubeUnitCoords l (u : ZMod p) (v : ZMod p)) := by
  have hcast := congrArg
    (fun z : ℤ × ℤ ↦ ((z.1 : ZMod p), (z.2 : ZMod p))) hrel
  cases j <;> cases l <;>
    simpa [eightScalarSecondDoubledCoords, doubleSecondCoord,
      eisensteinCubeUnitCoords] using hcast

private theorem fourScalar_bad_unit_indices_local
    (j l : EisensteinCubeUnitIndex)
    (hbad : (j, l) ≠
      (EisensteinCubeUnitIndex.zeta, EisensteinCubeUnitIndex.zeta)) :
    ∃ p : ℕ, p.Prime ∧
      ∀ x y u v : ZMod p,
        fourScalarSecondCoords (eisensteinCubeUnitCoords j x y) =
            eisensteinCubeUnitCoords l u v →
          eisensteinCubeUnitCoords j x y = (0, 0) := by
  cases j <;> cases l
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact False.elim (hbad rfl)
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨7, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩

private theorem eightScalar_bad_unit_indices_local
    (j l : EisensteinCubeUnitIndex)
    (hbad : (j, l) ≠
      (EisensteinCubeUnitIndex.zetaSq, EisensteinCubeUnitIndex.one)) :
    ∃ p : ℕ, p.Prime ∧
      ∀ x y u v : ZMod p,
        eightScalarSecondDoubledCoords
            (eisensteinCubeUnitCoords j x y) =
          doubleSecondCoord (eisensteinCubeUnitCoords l u v) →
        eisensteinCubeUnitCoords j x y = (0, 0) := by
  cases j <;> cases l
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨7, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact False.elim (hbad rfl)
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩

private theorem fourScalar_cubeCoords_relation
    {m n x y u v : ℤ} {j l : EisensteinCubeUnitIndex}
    (hm : Odd m) (hn : Odd n)
    (hfirst : ((m + n) / 2, n) = eisensteinCubeUnitCoords j x y)
    (hsecond : (m + n, (n - m) / 2) =
      eisensteinCubeUnitCoords l u v) :
    fourScalarSecondCoords (eisensteinCubeUnitCoords j x y) =
      eisensteinCubeUnitCoords l u v := by
  obtain ⟨r, hr⟩ := hm
  obtain ⟨s, hs⟩ := hn
  rw [← hfirst, ← hsecond]
  ext <;> simp only [fourScalarSecondCoords]
  all_goals omega

private theorem eightScalar_cubeCoords_relation
    {m n x y u v : ℤ} {j l : EisensteinCubeUnitIndex}
    (hm : Odd m) (hn : Odd n)
    (hmod : (m : ZMod 4) = (n : ZMod 4))
    (hfirst : ((m + n) / 2, n) = eisensteinCubeUnitCoords j x y)
    (hsecond : ((m + n) / 2, (n - m) / 4) =
      eisensteinCubeUnitCoords l u v) :
    eightScalarSecondDoubledCoords
        (eisensteinCubeUnitCoords j x y) =
      doubleSecondCoord (eisensteinCubeUnitCoords l u v) := by
  have hfour : (4 : ℤ) ∣ n - m :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub m n 4).mp hmod
  obtain ⟨r, hr⟩ := hm
  obtain ⟨s, hs⟩ := hn
  obtain ⟨t, ht⟩ := hfour
  rw [← hfirst, ← hsecond]
  ext <;>
    simp only [eightScalarSecondDoubledCoords, doubleSecondCoord]
  all_goals omega

/-- In a `k = ±4` branch, local checks modulo `3`, `5`, and `7` eliminate
eight of the nine pairs of cube-unit classes.  Only `(ζ₃,ζ₃)` is
compatible with primitive odd parameters. -/
theorem fourScalar_unit_indices_eq
    {m n x y u v : ℤ} {j l : EisensteinCubeUnitIndex}
    (hmn : IsCoprime m n) (hm : Odd m) (hn : Odd n)
    (hfirst : ((m + n) / 2, n) = eisensteinCubeUnitCoords j x y)
    (hsecond : (m + n, (n - m) / 2) =
      eisensteinCubeUnitCoords l u v) :
    j = EisensteinCubeUnitIndex.zeta ∧
      l = EisensteinCubeUnitIndex.zeta := by
  have hrel := fourScalar_cubeCoords_relation hm hn hfirst hsecond
  have hpair : (j, l) =
      (EisensteinCubeUnitIndex.zeta,
        EisensteinCubeUnitIndex.zeta) := by
    by_contra hbad
    obtain ⟨p, hp, hlocal⟩ :=
      fourScalar_bad_unit_indices_local j l hbad
    have hrelMod := cast_fourScalar_relation p hrel
    have hzero := hlocal (x : ZMod p) (y : ZMod p)
      (u : ZMod p) (v : ZMod p) hrelMod
    exact false_of_first_cubeCoords_zero_mod
      p hp hmn hm hn hfirst hzero
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- In a `k = ±8` branch, local checks modulo `3`, `5`, and `7` eliminate
eight of the nine pairs of cube-unit classes.  Only `(ζ₃²,1)` is
compatible with primitive odd parameters. -/
theorem eightScalar_unit_indices_eq
    {m n x y u v : ℤ} {j l : EisensteinCubeUnitIndex}
    (hmn : IsCoprime m n) (hm : Odd m) (hn : Odd n)
    (hmod : (m : ZMod 4) = (n : ZMod 4))
    (hfirst : ((m + n) / 2, n) = eisensteinCubeUnitCoords j x y)
    (hsecond : ((m + n) / 2, (n - m) / 4) =
      eisensteinCubeUnitCoords l u v) :
    j = EisensteinCubeUnitIndex.zetaSq ∧
      l = EisensteinCubeUnitIndex.one := by
  have hrel :=
    eightScalar_cubeCoords_relation hm hn hmod hfirst hsecond
  have hpair : (j, l) =
      (EisensteinCubeUnitIndex.zetaSq,
        EisensteinCubeUnitIndex.one) := by
    by_contra hbad
    obtain ⟨p, hp, hlocal⟩ :=
      eightScalar_bad_unit_indices_local j l hbad
    have hrelMod := cast_eightScalar_relation p hrel
    have hzero := hlocal (x : ZMod p) (y : ZMod p)
      (u : ZMod p) (v : ZMod p) hrelMod
    exact false_of_first_cubeCoords_zero_mod
      p hp hmn hm hn hfirst hzero
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

private theorem fourScalar_survivor_eta_zero_mod_seven :
    ∀ x y u v : ZMod 7,
      fourScalarSecondCoords
          (eisensteinCubeUnitCoords EisensteinCubeUnitIndex.zeta x y) =
        eisensteinCubeUnitCoords EisensteinCubeUnitIndex.zeta u v →
      (eisensteinCubeUnitCoords
        EisensteinCubeUnitIndex.zeta x y).1 = 0 := by
  decide

private theorem eightScalar_survivor_eta_zero_mod_seven :
    ∀ x y u v : ZMod 7,
      eightScalarSecondDoubledCoords
          (eisensteinCubeUnitCoords EisensteinCubeUnitIndex.zetaSq x y) =
        doubleSecondCoord
          (eisensteinCubeUnitCoords EisensteinCubeUnitIndex.one u v) →
      (eisensteinCubeUnitCoords
        EisensteinCubeUnitIndex.zetaSq x y).1 =
          (eisensteinCubeUnitCoords
            EisensteinCubeUnitIndex.zetaSq x y).2 := by
  decide

/-- The surviving `(ζ₃,ζ₃)` cubic system forces its first cube's
`ζ₃` coordinate to be divisible by the distinguished rational prime
`7`. -/
theorem seven_dvd_eisensteinCubeEta_of_fourScalar_survivor
    {x y u v : ℤ}
    (heta : eisensteinCubeEta u v = 2 * eisensteinCubeEta x y)
    (hreal : eisensteinCubeReal u v =
      eisensteinCubeReal x y + 2 * eisensteinCubeEta x y) :
    (7 : ℤ) ∣ eisensteinCubeEta x y := by
  have hrel :
      fourScalarSecondCoords
          (eisensteinCubeUnitCoords EisensteinCubeUnitIndex.zeta x y) =
        eisensteinCubeUnitCoords EisensteinCubeUnitIndex.zeta u v := by
    change
      (2 * (-eisensteinCubeEta x y),
        (eisensteinCubeReal x y - eisensteinCubeEta x y) -
          (-eisensteinCubeEta x y)) =
      (-eisensteinCubeEta u v,
        eisensteinCubeReal u v - eisensteinCubeEta u v)
    ext
    all_goals omega
  have hrelMod := cast_fourScalar_relation 7 hrel
  have hzero := fourScalar_survivor_eta_zero_mod_seven
    (x : ZMod 7) (y : ZMod 7) (u : ZMod 7) (v : ZMod 7) hrelMod
  have hetaZero : ((eisensteinCubeEta x y : ℤ) : ZMod 7) = 0 := by
    simpa [eisensteinCubeUnitCoords, eisensteinCubeEta] using hzero
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (eisensteinCubeEta x y) 7).mp hetaZero

/-- The surviving `(ζ₃²,1)` cubic system likewise forces the first
cube's `ζ₃` coordinate to be divisible by `7`. -/
theorem seven_dvd_eisensteinCubeEta_of_eightScalar_survivor
    {x y u v : ℤ}
    (hreal : eisensteinCubeReal u v =
      eisensteinCubeEta x y - eisensteinCubeReal x y)
    (heta : 2 * eisensteinCubeEta u v = -eisensteinCubeEta x y) :
    (7 : ℤ) ∣ eisensteinCubeEta x y := by
  have hrel :
      eightScalarSecondDoubledCoords
          (eisensteinCubeUnitCoords EisensteinCubeUnitIndex.zetaSq x y) =
        doubleSecondCoord
          (eisensteinCubeUnitCoords EisensteinCubeUnitIndex.one u v) := by
    change
      (eisensteinCubeEta x y - eisensteinCubeReal x y,
        -eisensteinCubeReal x y -
          (eisensteinCubeEta x y - eisensteinCubeReal x y)) =
      (eisensteinCubeReal u v, 2 * eisensteinCubeEta u v)
    ext
    all_goals omega
  have hrelMod := cast_eightScalar_relation 7 hrel
  have hzero := eightScalar_survivor_eta_zero_mod_seven
    (x : ZMod 7) (y : ZMod 7) (u : ZMod 7) (v : ZMod 7) hrelMod
  have hetaZero : ((eisensteinCubeEta x y : ℤ) : ZMod 7) = 0 := by
    simp only [eisensteinCubeUnitCoords] at hzero
    simp only [eisensteinCubeEta]
    push_cast
    linear_combination hzero
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (eisensteinCubeEta x y) 7).mp hetaZero

private theorem splitHalfFirstFactor_cubeUnitCoords
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {m n : ℤ}
    (hclass : EisensteinCubeUnitClass hζ
      (splitHalfFirstFactor hζ m n)) :
    ∃ (j : EisensteinCubeUnitIndex) (x y : ℤ),
      ((m + n) / 2, n) = eisensteinCubeUnitCoords j x y := by
  obtain ⟨j, x, y, hring⟩ :=
    eisensteinCubeCoordinateClass_of_unitClass hζ hclass
  have hcoords := splitEisensteinCoords_injective hζ (by
    simpa only [splitHalfFirstFactor] using hring)
  exact ⟨j, x, y, Prod.ext hcoords.1 hcoords.2⟩

private theorem splitHalfSecondFactor_cubeUnitCoords
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {m n : ℤ}
    (hclass : EisensteinCubeUnitClass hζ
      (splitHalfSecondFactor hζ m n)) :
    ∃ (j : EisensteinCubeUnitIndex) (x y : ℤ),
      (m + n, (n - m) / 2) = eisensteinCubeUnitCoords j x y := by
  obtain ⟨j, x, y, hring⟩ :=
    eisensteinCubeCoordinateClass_of_unitClass hζ hclass
  have hcoords := splitEisensteinCoords_injective hζ (by
    simpa only [splitHalfSecondFactor] using hring)
  exact ⟨j, x, y, Prod.ext hcoords.1 hcoords.2⟩

private theorem splitQuarterSecondFactor_cubeUnitCoords
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {m n : ℤ}
    (hclass : EisensteinCubeUnitClass hζ
      (splitQuarterSecondFactor hζ m n)) :
    ∃ (j : EisensteinCubeUnitIndex) (x y : ℤ),
      ((m + n) / 2, (n - m) / 4) =
        eisensteinCubeUnitCoords j x y := by
  obtain ⟨j, x, y, hring⟩ :=
    eisensteinCubeCoordinateClass_of_unitClass hζ hclass
  have hcoords := splitEisensteinCoords_injective hζ (by
    simpa only [splitQuarterSecondFactor] using hring)
  exact ⟨j, x, y, Prod.ext hcoords.1 hcoords.2⟩

/-- The two cubic systems left after exact two-adic normalization and all
finite cube-unit-class exclusions.  The `±4` branch retains only the
`(ζ₃,ζ₃)` pair, and the `±8` branch only `(ζ₃²,1)`. -/
def SurvivingEisensteinCubeSystems (m n k : ℤ) : Prop :=
  ((k = -4 ∨ k = 4) ∧
    ∃ x y u v : ℤ,
      (m + n) / 2 = -eisensteinCubeEta x y ∧
      n = eisensteinCubeReal x y - eisensteinCubeEta x y ∧
      eisensteinCubeEta u v = 2 * eisensteinCubeEta x y ∧
      eisensteinCubeReal u v =
        eisensteinCubeReal x y + 2 * eisensteinCubeEta x y ∧
      (7 : ℤ) ∣ m + n) ∨
  ((k = -8 ∨ k = 8) ∧
    ∃ x y u v : ℤ,
      (m + n) / 2 =
        eisensteinCubeEta x y - eisensteinCubeReal x y ∧
      n = -eisensteinCubeReal x y ∧
      eisensteinCubeReal u v =
        eisensteinCubeEta x y - eisensteinCubeReal x y ∧
      2 * eisensteinCubeEta u v = -eisensteinCubeEta x y ∧
      (7 : ℤ) ∣ m - n)

/-! ## The cube-allocated finite boundary -/

/-- The finite `X₁(18)` Eisenstein boundary after the powers of `2` have
been removed and unique factorization has allocated both normalized factors
to associated cubes.  The remaining work is the finite six-unit analysis,
including the distinguished prime above `7`. -/
def CubeAllocatedEisensteinIntegerFiniteSplitCyclicCubicObstruction : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
      [IsCyclotomicExtension {3} ℚ K]
      {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
      (m n a b k : ℤ),
    0 < n →
    0 < b →
    IsCoprime m n →
    IsCoprime a b →
    a ≠ 0 →
    a ≠ b →
    Odd m →
    Odd n →
    m ^ 2 - n ^ 2 = k * (a * b * (a - b)) →
    m ^ 2 - 6 * m * n - 3 * n ^ 2 =
      k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) →
    -2 * m ^ 2 - 6 * m * n =
      k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3) →
    hζ.toInteger * splitFirstEisensteinFactor hζ m n *
        splitSecondEisensteinFactor hζ m n =
      (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3 →
    ((k = -8 ∧ (m : ZMod 4) = (n : ZMod 4)) ∨
      (k = -4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 8 ∧ (m : ZMod 4) = (n : ZMod 4))) →
    firstParameterForm m n * piParameterForm m n =
      k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 →
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) →
    (((k = -4 ∨ k = 4) ∧
        ∃ x y : 𝓞 K,
          Associated (x ^ 3) (splitHalfFirstFactor hζ m n) ∧
          Associated (y ^ 3) (splitHalfSecondFactor hζ m n)) ∨
      ((k = -8 ∨ k = 8) ∧
        ∃ x y : 𝓞 K,
          Associated (x ^ 3) (splitHalfFirstFactor hζ m n) ∧
          Associated (y ^ 3) (splitQuarterSecondFactor hζ m n))) →
    False

/-- The finite `X₁(18)` boundary after the six Eisenstein units have been
reduced, by absorbing signs into cube roots, to the three classes represented
by `1`, `ζ₃`, and `ζ₃²`. -/
def ThreeUnitClassEisensteinIntegerFiniteSplitCyclicCubicObstruction : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
      [IsCyclotomicExtension {3} ℚ K]
      {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
      (m n a b k : ℤ),
    0 < n →
    0 < b →
    IsCoprime m n →
    IsCoprime a b →
    a ≠ 0 →
    a ≠ b →
    Odd m →
    Odd n →
    m ^ 2 - n ^ 2 = k * (a * b * (a - b)) →
    m ^ 2 - 6 * m * n - 3 * n ^ 2 =
      k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) →
    -2 * m ^ 2 - 6 * m * n =
      k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3) →
    hζ.toInteger * splitFirstEisensteinFactor hζ m n *
        splitSecondEisensteinFactor hζ m n =
      (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3 →
    ((k = -8 ∧ (m : ZMod 4) = (n : ZMod 4)) ∨
      (k = -4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 8 ∧ (m : ZMod 4) = (n : ZMod 4))) →
    firstParameterForm m n * piParameterForm m n =
      k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 →
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) →
    (((k = -4 ∨ k = 4) ∧
        EisensteinCubeUnitClass hζ (splitHalfFirstFactor hζ m n) ∧
        EisensteinCubeUnitClass hζ (splitHalfSecondFactor hζ m n)) ∨
      ((k = -8 ∨ k = 8) ∧
        EisensteinCubeUnitClass hζ (splitHalfFirstFactor hζ m n) ∧
        EisensteinCubeUnitClass hζ
          (splitQuarterSecondFactor hζ m n))) →
    False

/-- The final explicit integer boundary after all two-adic allocation and
finite cube-unit-class checks.  A proof now needs to exclude exactly the two
systems in `SurvivingEisensteinCubeSystems`, with the distinguished-prime-
above-`7` information retained. -/
def SurvivingEisensteinCubeSystemFiniteSplitCyclicCubicObstruction : Prop :=
  ∀ (m n a b k : ℤ),
    0 < n →
    0 < b →
    IsCoprime m n →
    IsCoprime a b →
    a ≠ 0 →
    a ≠ b →
    Odd m →
    Odd n →
    m ^ 2 - n ^ 2 = k * (a * b * (a - b)) →
    m ^ 2 - 6 * m * n - 3 * n ^ 2 =
      k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) →
    -2 * m ^ 2 - 6 * m * n =
      k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3) →
    ((k = -8 ∧ (m : ZMod 4) = (n : ZMod 4)) ∨
      (k = -4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 8 ∧ (m : ZMod 4) = (n : ZMod 4))) →
    firstParameterForm m n * piParameterForm m n =
      k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 →
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) →
    SurvivingEisensteinCubeSystems m n k →
    False

/-- Classifying the six units into three sign-free classes turns the
three-unit-class boundary into the cube-allocated boundary. -/
theorem cubeAllocatedEisensteinIntegerObstruction_of_threeUnitClass
    (hobs :
      ThreeUnitClassEisensteinIntegerFiniteSplitCyclicCubicObstruction) :
    CubeAllocatedEisensteinIntegerFiniteSplitCyclicCubicObstruction := by
  intro K _ _ _ ζ hζ m n a b k hn hb hmn hab ha habne hm hnodd
    hleading htrace hpair hfactor hmodFour hnorm hseven hallocated
  have hunitAllocated :
      (((k = -4 ∨ k = 4) ∧
          EisensteinCubeUnitClass hζ (splitHalfFirstFactor hζ m n) ∧
          EisensteinCubeUnitClass hζ (splitHalfSecondFactor hζ m n)) ∨
        ((k = -8 ∨ k = 8) ∧
          EisensteinCubeUnitClass hζ (splitHalfFirstFactor hζ m n) ∧
          EisensteinCubeUnitClass hζ
            (splitQuarterSecondFactor hζ m n))) := by
    rcases hallocated with
      ⟨hk, x, y, hx, hy⟩ | ⟨hk, x, y, hx, hy⟩
    · exact Or.inl ⟨hk,
        eq_cube_or_zeta_mul_cube_or_zeta_sq_mul_cube_of_associated hζ hx,
        eq_cube_or_zeta_mul_cube_or_zeta_sq_mul_cube_of_associated hζ hy⟩
    · exact Or.inr ⟨hk,
        eq_cube_or_zeta_mul_cube_or_zeta_sq_mul_cube_of_associated hζ hx,
        eq_cube_or_zeta_mul_cube_or_zeta_sq_mul_cube_of_associated hζ hy⟩
  exact hobs K hζ m n a b k hn hb hmn hab ha habne hm hnodd hleading
    htrace hpair hfactor hmodFour hnorm hseven hunitAllocated

/-- The finite local unit-index checks reduce the three-unit-class boundary
to the two explicit surviving integer systems. -/
theorem threeUnitClassEisensteinIntegerObstruction_of_survivingSystems
    (hobs :
      SurvivingEisensteinCubeSystemFiniteSplitCyclicCubicObstruction) :
    ThreeUnitClassEisensteinIntegerFiniteSplitCyclicCubicObstruction := by
  intro K _ _ _ ζ hζ m n a b k hn hb hmn hab ha habne hm hnodd
    hleading htrace hpair _hfactor hmodFour hnorm hseven hunitAllocated
  have hmodFour' := hmodFour
  have hsurviving : SurvivingEisensteinCubeSystems m n k := by
    rcases hunitAllocated with
      ⟨hk, hfirstClass, hsecondClass⟩ |
        ⟨hk, hfirstClass, hsecondClass⟩
    · obtain ⟨j, x, y, hfirstCoords⟩ :=
        splitHalfFirstFactor_cubeUnitCoords hζ hfirstClass
      obtain ⟨l, u, v, hsecondCoords⟩ :=
        splitHalfSecondFactor_cubeUnitCoords hζ hsecondClass
      obtain ⟨hj, hl⟩ :=
        fourScalar_unit_indices_eq hmn hm hnodd
          hfirstCoords hsecondCoords
      subst j
      subst l
      have hfirstReal :
          (m + n) / 2 = -eisensteinCubeEta x y := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeEta] using
          congrArg Prod.fst hfirstCoords
      have hfirstEta :
          n = eisensteinCubeReal x y - eisensteinCubeEta x y := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal,
          eisensteinCubeEta] using congrArg Prod.snd hfirstCoords
      have hsecondReal :
          m + n = -eisensteinCubeEta u v := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeEta] using
          congrArg Prod.fst hsecondCoords
      have hsecondEta :
          (n - m) / 2 =
            eisensteinCubeReal u v - eisensteinCubeEta u v := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal,
          eisensteinCubeEta] using congrArg Prod.snd hsecondCoords
      obtain ⟨r, hr⟩ := hm
      obtain ⟨s, hs⟩ := hnodd
      have hsum : 2 * ((m + n) / 2) = m + n := by omega
      have hdiff : 2 * ((n - m) / 2) = n - m := by omega
      have hsecondCubeEta :
          eisensteinCubeEta u v = 2 * eisensteinCubeEta x y := by
        omega
      have hsecondCubeReal :
          eisensteinCubeReal u v =
            eisensteinCubeReal x y + 2 * eisensteinCubeEta x y := by
        omega
      have hsevenEta :=
        seven_dvd_eisensteinCubeEta_of_fourScalar_survivor
          hsecondCubeEta hsecondCubeReal
      obtain ⟨q, hq⟩ := hsevenEta
      have hsevenSum : (7 : ℤ) ∣ m + n := by
        refine ⟨-2 * q, ?_⟩
        omega
      exact Or.inl ⟨hk, x, y, u, v, hfirstReal, hfirstEta,
        hsecondCubeEta, hsecondCubeReal, hsevenSum⟩
    · have hmod : (m : ZMod 4) = (n : ZMod 4) := by
        rcases hmodFour with hnegEight | hnegFour | hfour | height
        · exact hnegEight.2
        · exfalso
          rcases hk with hk | hk <;> omega
        · exfalso
          rcases hk with hk | hk <;> omega
        · exact height.2
      obtain ⟨j, x, y, hfirstCoords⟩ :=
        splitHalfFirstFactor_cubeUnitCoords hζ hfirstClass
      obtain ⟨l, u, v, hsecondCoords⟩ :=
        splitQuarterSecondFactor_cubeUnitCoords hζ hsecondClass
      obtain ⟨hj, hl⟩ :=
        eightScalar_unit_indices_eq hmn hm hnodd hmod
          hfirstCoords hsecondCoords
      subst j
      subst l
      have hfirstReal :
          (m + n) / 2 =
            eisensteinCubeEta x y - eisensteinCubeReal x y := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal,
          eisensteinCubeEta] using congrArg Prod.fst hfirstCoords
      have hfirstEta : n = -eisensteinCubeReal x y := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal] using
          congrArg Prod.snd hfirstCoords
      have hsecondReal :
          (m + n) / 2 = eisensteinCubeReal u v := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeReal] using
          congrArg Prod.fst hsecondCoords
      have hsecondEta :
          (n - m) / 4 = eisensteinCubeEta u v := by
        simpa [eisensteinCubeUnitCoords, eisensteinCubeEta] using
          congrArg Prod.snd hsecondCoords
      have hfour : (4 : ℤ) ∣ n - m :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub m n 4).mp hmod
      obtain ⟨r, hr⟩ := hm
      obtain ⟨s, hs⟩ := hnodd
      obtain ⟨t, ht⟩ := hfour
      have hsum : 2 * ((m + n) / 2) = m + n := by omega
      have hdiff : 4 * ((n - m) / 4) = n - m := by omega
      have hsecondCubeReal :
          eisensteinCubeReal u v =
            eisensteinCubeEta x y - eisensteinCubeReal x y := by
        omega
      have hsecondCubeEta :
          2 * eisensteinCubeEta u v = -eisensteinCubeEta x y := by
        omega
      have hsevenEta :=
        seven_dvd_eisensteinCubeEta_of_eightScalar_survivor
          hsecondCubeReal hsecondCubeEta
      obtain ⟨q, hq⟩ := hsevenEta
      have hsevenDifference : (7 : ℤ) ∣ m - n := by
        refine ⟨2 * q, ?_⟩
        omega
      exact Or.inr ⟨hk, x, y, u, v, hfirstReal, hfirstEta,
        hsecondCubeReal, hsecondCubeEta, hsevenDifference⟩
  exact hobs m n a b k hn hb hmn hab ha habne hm hnodd hleading htrace
    hpair hmodFour' hnorm hseven hsurviving

/-- Removing the exact powers of `2` and allocating coprime factors to
cubes turns the cube-allocated boundary into the earlier support-only-over-
`2` boundary. -/
theorem twoPrimeSupportedEisensteinIntegerObstruction_of_cubeAllocated
    (hobs :
      CubeAllocatedEisensteinIntegerFiniteSplitCyclicCubicObstruction) :
    TwoPrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction := by
  intro K _ _ _ ζ hζ m n a b k hn hb hmn hsupport hab ha habne hm
    hnodd hleading htrace hpair hfactor hmodFour hnorm hseven
  have hmodFour' := hmodFour
  have hfactor' :
      hζ.toInteger * splitFirstEisensteinFactor hζ m n *
          splitSecondEisensteinFactor hζ m n =
        (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3 := by
    simpa only [splitFirstEisensteinFactor,
      splitSecondEisensteinFactor] using hfactor
  have hallocated :
      (((k = -4 ∨ k = 4) ∧
          ∃ x y : 𝓞 K,
            Associated (x ^ 3) (splitHalfFirstFactor hζ m n) ∧
            Associated (y ^ 3) (splitHalfSecondFactor hζ m n)) ∨
        ((k = -8 ∨ k = 8) ∧
          ∃ x y : 𝓞 K,
            Associated (x ^ 3) (splitHalfFirstFactor hζ m n) ∧
            Associated (y ^ 3) (splitQuarterSecondFactor hζ m n))) := by
    rcases hmodFour with hnegEight | hnegFour | hfour | height
    · refine Or.inr ⟨Or.inl hnegEight.1, ?_⟩
      exact exists_associated_cubes_of_eight_scalar
        hζ m n a b k hm hnodd hnegEight.2 hsupport hfactor'
          (Or.inl hnegEight.1)
    · refine Or.inl ⟨Or.inl hnegFour.1, ?_⟩
      exact exists_associated_cubes_of_four_scalar
        hζ m n a b k hm hnodd hsupport hfactor' (Or.inl hnegFour.1)
    · refine Or.inl ⟨Or.inr hfour.1, ?_⟩
      exact exists_associated_cubes_of_four_scalar
        hζ m n a b k hm hnodd hsupport hfactor' (Or.inr hfour.1)
    · refine Or.inr ⟨Or.inr height.1, ?_⟩
      exact exists_associated_cubes_of_eight_scalar
        hζ m n a b k hm hnodd height.2 hsupport hfactor'
          (Or.inr height.1)
  exact hobs K hζ m n a b k hn hb hmn hab ha habne hm hnodd hleading
    htrace hpair hfactor' hmodFour' hnorm hseven hallocated

/-- The cube-allocated Eisenstein boundary has a checked exact-order-
eighteen consumer. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_cubeAllocatedEisensteinIntegerObstruction
    (hobs :
      CubeAllocatedEisensteinIntegerFiniteSplitCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_twoPrimeSupportedEisensteinIntegerObstruction
    (twoPrimeSupportedEisensteinIntegerObstruction_of_cubeAllocated hobs) E Q

/-- The three-unit-class Eisenstein boundary has a checked exact-order-
eighteen consumer. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_threeUnitClassEisensteinIntegerObstruction
    (hobs :
      ThreeUnitClassEisensteinIntegerFiniteSplitCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_cubeAllocatedEisensteinIntegerObstruction
    (cubeAllocatedEisensteinIntegerObstruction_of_threeUnitClass hobs) E Q

/-- Excluding the two explicit surviving cubic systems excludes exact
rational order eighteen. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_survivingEisensteinCubeSystemObstruction
    (hobs :
      SurvivingEisensteinCubeSystemFiniteSplitCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_threeUnitClassEisensteinIntegerObstruction
    (threeUnitClassEisensteinIntegerObstruction_of_survivingSystems hobs)
      E Q

end MazurTorsion.XOneEighteenDescent
