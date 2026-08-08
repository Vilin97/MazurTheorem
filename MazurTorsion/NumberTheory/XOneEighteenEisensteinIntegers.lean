/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenDescent
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# Eisenstein-integer factorization for `X₁(18)`

The split cyclic-cubic descent for the order-eighteen curve produces an
identity in integral coordinate pairs for `ℤ[ζ₃]`.  This file realizes those
pairs in the ring of integers of any third cyclotomic number field and lifts
the coordinate identity to an actual ring equality

`ζ₃ ((m+n) + 2nζ₃) (2(m+n) + (n-m)ζ₃) = k (a+bζ₃)³`.

The resulting finite obstruction records this equality together with the
checked modulo-four split between `k = ±4` and `k = ±8`.  Its conversion to
the earlier refined obstruction chooses the canonical field
`CyclotomicField 3 ℚ`, so it has a compiled exact-order-eighteen consumer.

Mathlib proves that the ring of integers in every such field is a principal
ideal ring.  The common-prime support of the two displayed linear factors is
proved below: a common prime lies over `2` or is the ramified prime above `3`.
What remains is the unique-factorization allocation in the product, including
the scalar prime above `2`, the distinguished prime above `7`, and the ensuing
unit cases.
-/

open NumberField Polynomial

namespace MazurTorsion.XOneEighteenDescent

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- Interpret the integral coordinate pair `(a,b)` as the algebraic integer
`a + bζ₃`. -/
def eisensteinIntegerOfPair (z : ℤ × ℤ) : 𝓞 K :=
  z.1 + z.2 * hζ.toInteger

/-- The coordinate interpretation respects Eisenstein multiplication. -/
theorem eisensteinIntegerOfPair_mul (z w : ℤ × ℤ) :
    eisensteinIntegerOfPair hζ (eisensteinMul z w) =
      eisensteinIntegerOfPair hζ z * eisensteinIntegerOfPair hζ w := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  simp only [eisensteinIntegerOfPair, eisensteinMul]
  push_cast
  linear_combination -b * d * hroot

/-- The first linear factor in the split cyclic-cubic identity. -/
def splitFirstEisensteinFactor (m n : ℤ) : 𝓞 K :=
  ((m + n : ℤ) : 𝓞 K) + (2 * n) * hζ.toInteger

/-- The second linear factor in the split cyclic-cubic identity.  It is
the Eisenstein conjugate of the factor whose norm is
`piParameterForm m n`. -/
def splitSecondEisensteinFactor (m n : ℤ) : 𝓞 K :=
  ((2 * (m + n) : ℤ) : 𝓞 K) + (n - m) * hζ.toInteger

/-- The split-coefficient coordinate identity, realized in the ring of
integers of a field containing a primitive third root of unity. -/
theorem split_parameter_eisenstein_integer_factorization
    (m n a b k : ℤ)
    (hleading : m ^ 2 - n ^ 2 = k * (a * b * (a - b)))
    (htrace :
      m ^ 2 - 6 * m * n - 3 * n ^ 2 =
        k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3)) :
    hζ.toInteger *
        (((m + n : ℤ) : 𝓞 K) + (2 * n) * hζ.toInteger) *
        (((2 * (m + n) : ℤ) : 𝓞 K) + (n - m) * hζ.toInteger) =
      (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3 := by
  have hpair := split_parameter_eisenstein_product_eq_scalar_cube
    m n a b k hleading htrace
  have hlift := congrArg (eisensteinIntegerOfPair hζ) hpair
  have hleft :
      eisensteinIntegerOfPair hζ
          (eisensteinMul (0, 1)
            (eisensteinMul (m + n, 2 * n)
              (eisensteinConj (3 * m + n, m - n)))) =
        eisensteinIntegerOfPair hζ (0, 1) *
          (eisensteinIntegerOfPair hζ (m + n, 2 * n) *
            eisensteinIntegerOfPair hζ
              (eisensteinConj (3 * m + n, m - n))) := by
    rw [eisensteinIntegerOfPair_mul, eisensteinIntegerOfPair_mul]
  have hright :
      eisensteinIntegerOfPair hζ
          (eisensteinMul (k, 0)
            (eisensteinMul (eisensteinMul (a, b) (a, b)) (a, b))) =
        eisensteinIntegerOfPair hζ (k, 0) *
          ((eisensteinIntegerOfPair hζ (a, b) *
              eisensteinIntegerOfPair hζ (a, b)) *
            eisensteinIntegerOfPair hζ (a, b)) := by
    rw [eisensteinIntegerOfPair_mul, eisensteinIntegerOfPair_mul,
      eisensteinIntegerOfPair_mul]
  rw [hleft, hright] at hlift
  simp only [eisensteinIntegerOfPair, eisensteinConj, Int.cast_add,
    Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_ofNat,
    Int.cast_zero, pow_three] at hlift ⊢
  ring_nf at hlift ⊢
  exact hlift

/-! ## Common-prime support of the two linear factors -/

/-- Any common divisor of the two split linear factors divides the
determinant `2(1+2ζ₃)`.  The proof uses the primitive parameter condition
to combine the two determinant identities. -/
theorem common_dvd_splitEisensteinFactors_dvd_two_mul_threePrime
    (m n : ℤ) (hmn : IsCoprime m n) (d : 𝓞 K)
    (hfirst : d ∣ splitFirstEisensteinFactor hζ m n)
    (hsecond : d ∣ splitSecondEisensteinFactor hζ m n) :
    d ∣ (2 : 𝓞 K) * (1 + 2 * hζ.toInteger) := by
  let η : 𝓞 K := hζ.toInteger
  have hroot : η ^ 2 + η + 1 = 0 := by
    dsimp [η]
    have hz := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
      (by norm_num)
    rw [Polynomial.cyclotomic_three] at hz
    simpa [Polynomial.IsRoot] using hz
  have hfirst' :
      d ∣ ((m : 𝓞 K) + (n : 𝓞 K) * (1 + 2 * η)) := by
    convert hfirst using 1
    simp only [splitFirstEisensteinFactor, η, Int.cast_add]
    ring
  have hsecond' :
      d ∣ ((m : 𝓞 K) * (2 - η) + (n : 𝓞 K) * (2 + η)) := by
    convert hsecond using 1
    simp only [splitSecondEisensteinFactor, η, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat]
    ring
  have hm : d ∣ (m : 𝓞 K) * (-(2 : 𝓞 K) * (1 + 2 * η)) := by
    have hcomb := dvd_sub (hfirst'.mul_left (2 + η))
      (hsecond'.mul_left (1 + 2 * η))
    convert hcomb using 1
    linear_combination -2 * (m : 𝓞 K) * hroot
  have hn : d ∣ (n : 𝓞 K) * (-(2 : 𝓞 K) * (1 + 2 * η)) := by
    have hcomb := dvd_sub hsecond' (hfirst'.mul_left (2 - η))
    convert hcomb using 1
    linear_combination -2 * (n : 𝓞 K) * hroot
  have hmn' : IsCoprime (m : 𝓞 K) (n : 𝓞 K) := by
    simpa using hmn.map (algebraMap ℤ (𝓞 K))
  obtain ⟨u, v, huv⟩ := hmn'
  have hdet : d ∣ (-(2 : 𝓞 K) * (1 + 2 * η)) := by
    have hone := congrArg
      (fun x : 𝓞 K => x * (-(2 : 𝓞 K) * (1 + 2 * η))) huv.symm
    rw [one_mul] at hone
    rw [hone, add_mul]
    simpa only [mul_assoc] using dvd_add (hm.mul_left u) (hn.mul_left v)
  convert hdet.neg_right using 1
  simp [η]

/-- The determinant factor `1+2ζ₃` is associated to the standard
ramified factor `ζ₃-1`. -/
theorem splitEisensteinThreePrime_associated :
    Associated (1 + 2 * hζ.toInteger) (hζ.toInteger - 1) := by
  let ηu : (𝓞 K)ˣ :=
    (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
  apply Associated.symm
  refine ⟨-ηu, ?_⟩
  change (hζ.toInteger - 1) * (-hζ.toInteger) =
    1 + 2 * hζ.toInteger
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  linear_combination -hroot

/-- The non-rational determinant factor is the prime above `3`. -/
theorem splitEisensteinThreePrime_prime
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    Prime (1 + 2 * hζ.toInteger) := by
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = 3 :=
    hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hne : hζ.toInteger - 1 ≠ 0 := by
    intro hzero
    rw [hzero, Algebra.norm_zero] at hnorm
    norm_num at hnorm
  have hprime : Prime (hζ.toInteger - 1) := by
    apply Ideal.prime_of_irreducible_absNorm_span hne
    rw [Ideal.absNorm_span_singleton, hnorm]
    exact Nat.prime_three
  exact (splitEisensteinThreePrime_associated hζ).symm.prime hprime

/-- A prime common to the two linear factors lies over `2` or is
associated to the unique ramified prime `ζ₃-1` above `3`. -/
theorem common_prime_splitEisensteinFactors_support
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hmn : IsCoprime m n) (p : 𝓞 K) (hp : Prime p)
    (hfirst : p ∣ splitFirstEisensteinFactor hζ m n)
    (hsecond : p ∣ splitSecondEisensteinFactor hζ m n) :
    p ∣ (2 : 𝓞 K) ∨ Associated p (hζ.toInteger - 1) := by
  have hsupport :=
    common_dvd_splitEisensteinFactors_dvd_two_mul_threePrime
      hζ m n hmn p hfirst hsecond
  rcases hp.dvd_mul.mp hsupport with htwo | hthree
  · exact Or.inl htwo
  · exact Or.inr <| hp.associated_of_dvd
      (splitEisensteinThreePrime_prime hζ) hthree |>.trans
        (splitEisensteinThreePrime_associated hζ)

/-- The finite arithmetic boundary in an actual third cyclotomic ring of
integers.  Its hypotheses retain both the Eisenstein factorization and the
reviewed modulo-four separation of the four possible scalar quotients.

This proposition is designed for the remaining ideal-support and unit-case
analysis; it does not assert that those cases have already been eliminated. -/
def EisensteinIntegerFiniteSplitCyclicCubicObstruction : Prop :=
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
    hζ.toInteger *
        (((m + n : ℤ) : 𝓞 K) + (2 * n) * hζ.toInteger) *
        (((2 * (m + n) : ℤ) : 𝓞 K) + (n - m) * hζ.toInteger) =
      (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3 →
    ((k = -8 ∧ (m : ZMod 4) = (n : ZMod 4)) ∨
      (k = -4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 8 ∧ (m : ZMod 4) = (n : ZMod 4))) →
    firstParameterForm m n * piParameterForm m n =
      k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 →
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) →
    False

/-- The finite Eisenstein boundary after proving the common-prime support
of its two linear factors.  Compared with
`EisensteinIntegerFiniteSplitCyclicCubicObstruction`, a prospective proof
may assume that every common prime lies over `2` or is the ramified prime
above `3`; the theorem below derives this certificate from the primitive
parameters. -/
def PrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
      [IsCyclotomicExtension {3} ℚ K]
      {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
      (m n a b k : ℤ),
    0 < n →
    0 < b →
    IsCoprime m n →
    (∀ p : 𝓞 K,
      Prime p →
      p ∣ splitFirstEisensteinFactor hζ m n →
      p ∣ splitSecondEisensteinFactor hζ m n →
      p ∣ (2 : 𝓞 K) ∨ Associated p (hζ.toInteger - 1)) →
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
    hζ.toInteger *
        (((m + n : ℤ) : 𝓞 K) + (2 * n) * hζ.toInteger) *
        (((2 * (m + n) : ℤ) : 𝓞 K) + (n - m) * hζ.toInteger) =
      (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3 →
    ((k = -8 ∧ (m : ZMod 4) = (n : ZMod 4)) ∨
      (k = -4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 4 ∧ (m : ZMod 4) ≠ (n : ZMod 4)) ∨
      (k = 8 ∧ (m : ZMod 4) = (n : ZMod 4))) →
    firstParameterForm m n * piParameterForm m n =
      k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 →
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) →
    False

/-- The common-prime-supported boundary implies the preceding
Eisenstein-integer boundary. -/
theorem eisensteinIntegerObstruction_of_primeSupported
    (hobs :
      PrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction) :
    EisensteinIntegerFiniteSplitCyclicCubicObstruction := by
  intro K _ _ _ ζ hζ m n a b k hn hb hmn hab ha habne hm hnodd
    hleading htrace hpair hfactor hmodFour hnorm hseven
  exact hobs K hζ m n a b k hn hb hmn
    (fun p hp hfirst hsecond =>
      common_prime_splitEisensteinFactors_support
        hζ m n hmn p hp hfirst hsecond)
    hab ha habne hm hnodd hleading htrace hpair hfactor hmodFour hnorm
    hseven

/-- The ring-of-integers obstruction implies the coordinate-level refined
finite obstruction by specializing to the canonical third cyclotomic field. -/
theorem refinedFiniteSplitCyclicCubicObstruction_of_eisensteinInteger
    (hobs : EisensteinIntegerFiniteSplitCyclicCubicObstruction) :
    RefinedFiniteSplitCyclicCubicObstruction := by
  intro m n a b k hn hb hmn hab ha habne hm hnodd hleading htrace hpair
    _hcoordinate hmodFour hnorm hseven
  let K := CyclotomicField 3 ℚ
  letI : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have : NumberField K :=
    IsCyclotomicExtension.numberField {3} ℚ K
  have hfactor := split_parameter_eisenstein_integer_factorization
    hζ m n a b k hleading htrace
  exact hobs K hζ m n a b k hn hb hmn hab ha habne hm hnodd hleading
    htrace hpair hfactor hmodFour hnorm hseven

/-- A proof of the finite Eisenstein-integer obstruction excludes exact
rational order eighteen through the checked descent and Tate-normal-form
consumer. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_eisensteinIntegerObstruction
    (hobs : EisensteinIntegerFiniteSplitCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_refinedFiniteSplitCyclicCubicObstruction
    (refinedFiniteSplitCyclicCubicObstruction_of_eisensteinInteger hobs) E Q

/-- The common-prime-supported Eisenstein boundary excludes exact rational
order eighteen.  This is the downstream endpoint for the support theorem,
and leaves only the explicitly displayed primes over `2` and `3` before the
remaining unit-case analysis. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_primeSupportedEisensteinIntegerObstruction
    (hobs :
      PrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_eisensteinIntegerObstruction
    (eisensteinIntegerObstruction_of_primeSupported hobs) E Q

end MazurTorsion.XOneEighteenDescent
