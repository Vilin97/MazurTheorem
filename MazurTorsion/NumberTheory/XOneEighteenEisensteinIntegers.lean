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
ideal ring.  A common prime of the two displayed linear factors first lies
over `2` or at the ramified prime above `3`.  The ramified case is then
excluded: primitivity bounds each factor to depth one, while the
scalar-times-cube identity would force total depth divisible by three.  What
remains is the unique-factorization allocation at the primes over `2`, the
distinguished prime above `7`, and the ensuing unit cases.
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

/-! ## Excluding the ramified common prime -/

private theorem splitEisensteinCoords_zero [CharZero K]
    {a b : ℤ}
    (h : (a : 𝓞 K) + b * hζ.toInteger = 0) :
    a = 0 ∧ b = 0 := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hnormK : ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K) = 0 := by
    calc
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K) =
          ((a : 𝓞 K) + b * hζ.toInteger) *
            ((a - b : ℤ) - b * hζ.toInteger) := by
            push_cast
            linear_combination (b : 𝓞 K) ^ 2 * hroot
      _ = 0 := by rw [h]; simp
  have hnormZ : a ^ 2 - a * b + b ^ 2 = 0 := by
    exact_mod_cast hnormK
  have hb : b = 0 := by
    nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  subst b
  norm_num at hnormZ
  exact ⟨hnormZ, rfl⟩

/-- Equality of Eisenstein integers in the integral basis `(1, ζ₃)` is
coordinatewise. -/
theorem splitEisensteinCoords_injective [CharZero K]
    {a b c d : ℤ}
    (h : (a : 𝓞 K) + b * hζ.toInteger =
      (c : 𝓞 K) + d * hζ.toInteger) :
    a = c ∧ b = d := by
  have hzero : ((a - c : ℤ) : 𝓞 K) +
      ((b - d : ℤ) : 𝓞 K) * hζ.toInteger = 0 := by
    push_cast
    linear_combination h
  obtain ⟨hac, hbd⟩ :=
    splitEisensteinCoords_zero (a := a - c) (b := b - d) hζ hzero
  exact ⟨sub_eq_zero.mp hac, sub_eq_zero.mp hbd⟩

/-- Every integer of a third cyclotomic field has Eisenstein coordinates. -/
theorem exists_splitEisensteinCoords
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (z : 𝓞 K) :
    ∃ a b : ℤ, z = a + b * hζ.toInteger := by
  let pb := hζ.integralPowerBasis
  have hdim : pb.dim = 2 := by
    dsimp only [pb]
    rw [hζ.integralPowerBasis_dim]
    decide
  obtain ⟨f, hfdeg, hz⟩ := pb.exists_eq_aeval z
  have hfdeg' : f.natDegree < 2 := by simpa [hdim] using hfdeg
  let a : ℤ := f.coeff 0
  let b : ℤ := f.coeff 1
  have hf : f = Polynomial.C a + Polynomial.C b * Polynomial.X := by
    have hsum := f.as_sum_range' 2 hfdeg'
    norm_num [Finset.sum_range_succ] at hsum
    calc
      f = Polynomial.C (f.coeff 0) +
          Polynomial.monomial 1 (f.coeff 1) := hsum
      _ = Polynomial.C a + Polynomial.C b * Polynomial.X := by
        rw [Polynomial.C_mul_X_eq_monomial]
  refine ⟨a, b, ?_⟩
  calc
    z = Polynomial.aeval pb.gen f := hz
    _ = a + b * hζ.toInteger := by
      rw [hf]
      simp only [map_add, map_mul, Polynomial.aeval_C,
        Polynomial.aeval_X]
      rw [show pb.gen = hζ.toInteger by
        exact hζ.integralPowerBasis_gen]
      simp

/-- The square of the standard ramified factor is `-3ζ₃`. -/
theorem splitEisensteinThreePrime_sq :
    (hζ.toInteger - 1) ^ 2 =
      (3 : 𝓞 K) * (-hζ.toInteger) := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  linear_combination hroot

/-- Thus the square of `ζ₃ - 1` is associated to the rational integer
`3`. -/
theorem splitEisensteinThreePrime_sq_associated :
    Associated ((hζ.toInteger - 1) ^ 2) (3 : 𝓞 K) := by
  rw [splitEisensteinThreePrime_sq hζ]
  exact associated_mul_unit_left _ _
    ((hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).neg)

/-- Divisibility by a rational integer in the Eisenstein ring implies
coordinatewise integer divisibility. -/
theorem int_dvd_splitEisensteinCoords
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (q a b : ℤ)
    (hdiv : (q : 𝓞 K) ∣ (a : 𝓞 K) + b * hζ.toInteger) :
    q ∣ a ∧ q ∣ b := by
  obtain ⟨z, hz⟩ := hdiv
  obtain ⟨c, d, hcd⟩ := exists_splitEisensteinCoords hζ z
  have hcoords :
      ((a : ℤ) : 𝓞 K) + b * hζ.toInteger =
        ((q * c : ℤ) : 𝓞 K) + (q * d) * hζ.toInteger := by
    rw [hz, hcd]
    push_cast
    ring
  have hcoords' :
      ((a : ℤ) : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger =
        ((q * c : ℤ) : 𝓞 K) +
          ((q * d : ℤ) : 𝓞 K) * hζ.toInteger := by
    simpa only [Int.cast_mul] using hcoords
  obtain ⟨ha, hb⟩ := splitEisensteinCoords_injective
    (a := a) (b := b) (c := q * c) (d := q * d) hζ hcoords'
  exact ⟨⟨c, ha⟩, ⟨d, hb⟩⟩

/-- Primitivity of `(m,n)` bounds the ramified-prime depth of the first
split factor by one. -/
theorem splitFirstEisensteinFactor_threePrime_sq_not_dvd
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hmn : IsCoprime m n) :
    ¬ (hζ.toInteger - 1) ^ 2 ∣
      splitFirstEisensteinFactor hζ m n := by
  intro hsq
  have hthree : (3 : 𝓞 K) ∣ splitFirstEisensteinFactor hζ m n :=
    (splitEisensteinThreePrime_sq_associated hζ).dvd_iff_dvd_left.mp hsq
  have hcoords :
      (3 : ℤ) ∣ m + n ∧ (3 : ℤ) ∣ 2 * n := by
    apply int_dvd_splitEisensteinCoords hζ 3 (m + n) (2 * n)
    simpa only [splitFirstEisensteinFactor, Int.cast_mul,
      Int.cast_ofNat] using hthree
  obtain ⟨u, hu⟩ := hcoords.1
  obtain ⟨v, hv⟩ := hcoords.2
  have hn : (3 : ℤ) ∣ n := by
    refine ⟨v / 2, ?_⟩
    omega
  obtain ⟨w, hw⟩ := hn
  have hm : (3 : ℤ) ∣ m := by
    refine ⟨u - w, ?_⟩
    omega
  have hunit : IsUnit (3 : ℤ) := hmn.isUnit_of_dvd' hm ⟨w, hw⟩
  exact (by norm_num [Int.isUnit_iff] at hunit)

/-- Primitivity of `(m,n)` bounds the ramified-prime depth of the second
split factor by one. -/
theorem splitSecondEisensteinFactor_threePrime_sq_not_dvd
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n : ℤ) (hmn : IsCoprime m n) :
    ¬ (hζ.toInteger - 1) ^ 2 ∣
      splitSecondEisensteinFactor hζ m n := by
  intro hsq
  have hthree : (3 : 𝓞 K) ∣ splitSecondEisensteinFactor hζ m n :=
    (splitEisensteinThreePrime_sq_associated hζ).dvd_iff_dvd_left.mp hsq
  have hcoords :
      (3 : ℤ) ∣ 2 * (m + n) ∧ (3 : ℤ) ∣ n - m := by
    apply int_dvd_splitEisensteinCoords
      hζ 3 (2 * (m + n)) (n - m)
    convert hthree using 1
    · norm_num
    · simp only [splitSecondEisensteinFactor]
      push_cast
      ring
  obtain ⟨u, hu⟩ := hcoords.1
  obtain ⟨v, hv⟩ := hcoords.2
  have hsum : (3 : ℤ) ∣ m + n := by
    refine ⟨u / 2, ?_⟩
    omega
  obtain ⟨w, hw⟩ := hsum
  have hn : (3 : ℤ) ∣ n := by
    refine ⟨(w + v) / 2, ?_⟩
    omega
  obtain ⟨t, ht⟩ := hn
  have hm : (3 : ℤ) ∣ m := by
    refine ⟨w - t, ?_⟩
    omega
  have hunit : IsUnit (3 : ℤ) := hmn.isUnit_of_dvd' hm ⟨t, ht⟩
  exact (by norm_num [Int.isUnit_iff] at hunit)

private theorem three_dvd_of_splitEisensteinThreePrime_dvd_intCast
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (k : ℤ) (hdiv : hζ.toInteger - 1 ∣ (k : 𝓞 K)) :
    (3 : ℤ) ∣ k := by
  obtain ⟨z, hz⟩ := hdiv
  obtain ⟨c, d, hcd⟩ := exists_splitEisensteinCoords hζ z
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcoords :
      ((k : ℤ) : 𝓞 K) + (0 : 𝓞 K) * hζ.toInteger =
        ((-c - d : ℤ) : 𝓞 K) +
          (c - 2 * d : ℤ) * hζ.toInteger := by
    rw [zero_mul, add_zero, hz, hcd]
    push_cast
    linear_combination d * hroot
  obtain ⟨hk, heta⟩ := splitEisensteinCoords_injective
    (a := k) (b := 0) (c := -c - d) (d := c - 2 * d) hζ
    (by simpa using hcoords)
  refine ⟨-d, ?_⟩
  omega

private theorem prime_cube_not_dvd_mul_of_exact_depth_one
    {R : Type*} [CommRing R] [IsDomain R]
    {p x y : R} (hp : Prime p)
    (hpx : p ∣ x) (hpy : p ∣ y)
    (hpx2 : ¬ p ^ 2 ∣ x) (hpy2 : ¬ p ^ 2 ∣ y) :
    ¬ p ^ 3 ∣ x * y := by
  intro hp3
  obtain ⟨u, hu⟩ := hpx
  obtain ⟨v, hv⟩ := hpy
  obtain ⟨w, hw⟩ := hp3
  have huv : u * v = p * w := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero)
    calc
      p ^ 2 * (u * v) = x * y := by rw [hu, hv]; ring
      _ = p ^ 3 * w := hw
      _ = p ^ 2 * (p * w) := by ring
  rcases hp.dvd_mul.mp ⟨w, huv⟩ with hpu | hpv
  · obtain ⟨t, ht⟩ := hpu
    apply hpx2
    refine ⟨t, ?_⟩
    rw [hu, ht]
    ring
  · obtain ⟨t, ht⟩ := hpv
    apply hpy2
    refine ⟨t, ?_⟩
    rw [hv, ht]
    ring

/-- The ramified prime `ζ₃ - 1` cannot divide both split factors in the
scalar-times-cube identity.  If it did, both factors would have exact depth
one, whereas the right side has depth divisible by three because the four
possible scalars are prime to `3`. -/
theorem splitEisensteinThreePrime_not_common
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (m n a b k : ℤ) (hmn : IsCoprime m n)
    (hfactor :
      hζ.toInteger * splitFirstEisensteinFactor hζ m n *
          splitSecondEisensteinFactor hζ m n =
        (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3)
    (hk : k = -8 ∨ k = -4 ∨ k = 4 ∨ k = 8) :
    ¬ ((hζ.toInteger - 1) ∣ splitFirstEisensteinFactor hζ m n ∧
      (hζ.toInteger - 1) ∣ splitSecondEisensteinFactor hζ m n) := by
  rintro ⟨hfirst, hsecond⟩
  let p : 𝓞 K := hζ.toInteger - 1
  let z : 𝓞 K := ((a : ℤ) : 𝓞 K) + b * hζ.toInteger
  have hp : Prime p :=
    (splitEisensteinThreePrime_associated hζ).prime
      (splitEisensteinThreePrime_prime hζ)
  have hnotk : ¬ p ∣ (k : 𝓞 K) := by
    intro hpk
    have hthree : (3 : ℤ) ∣ k :=
      three_dvd_of_splitEisensteinThreePrime_dvd_intCast hζ k hpk
    rcases hk with rfl | rfl | rfl | rfl <;> norm_num at hthree
  have hpLeft : p ∣
      hζ.toInteger * splitFirstEisensteinFactor hζ m n *
        splitSecondEisensteinFactor hζ m n :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hfirst hζ.toInteger)
      (splitSecondEisensteinFactor hζ m n)
  have hpRight : p ∣ (k : 𝓞 K) * z ^ 3 := by
    rw [← hfactor]
    exact hpLeft
  have hpz3 : p ∣ z ^ 3 := (hp.dvd_mul.mp hpRight).resolve_left hnotk
  have hpz : p ∣ z := hp.dvd_of_dvd_pow hpz3
  have hp3Right : p ^ 3 ∣ (k : 𝓞 K) * z ^ 3 :=
    dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpz 3) (k : 𝓞 K)
  have hp3Left : p ^ 3 ∣
      hζ.toInteger *
        (splitFirstEisensteinFactor hζ m n *
          splitSecondEisensteinFactor hζ m n) := by
    rw [← mul_assoc, hfactor]
    exact hp3Right
  have hp3Product : p ^ 3 ∣
      splitFirstEisensteinFactor hζ m n *
        splitSecondEisensteinFactor hζ m n :=
    (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).dvd_mul_left.mp hp3Left
  exact prime_cube_not_dvd_mul_of_exact_depth_one hp hfirst hsecond
    (splitFirstEisensteinFactor_threePrime_sq_not_dvd hζ m n hmn)
    (splitSecondEisensteinFactor_threePrime_sq_not_dvd hζ m n hmn)
    hp3Product

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

/-- The finite Eisenstein boundary after the ramified prime above `3` has
also been excluded from the common support.  A prospective proof now needs
to allocate only primes dividing the rational scalar `2`; the remaining
scalar and unit cases are still explicit in the hypotheses. -/
def TwoPrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction : Prop :=
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
      p ∣ (2 : 𝓞 K)) →
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

/-- Excluding the ramified common prime turns a common-support-over-`2`
obstruction into the preceding support-over-`2`-or-`3` obstruction. -/
theorem primeSupportedEisensteinIntegerObstruction_of_twoPrimeSupported
    (hobs :
      TwoPrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction) :
    PrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction := by
  intro K _ _ _ ζ hζ m n a b k hn hb hmn hsupport hab ha habne hm
    hnodd hleading htrace hpair hfactor hmodFour hnorm hseven
  have hmodFour' := hmodFour
  have hk : k = -8 ∨ k = -4 ∨ k = 4 ∨ k = 8 := by
    rcases hmodFour with hnegEight | hnegFour | hfour | height
    · exact Or.inl hnegEight.1
    · exact Or.inr (Or.inl hnegFour.1)
    · exact Or.inr (Or.inr (Or.inl hfour.1))
    · exact Or.inr (Or.inr (Or.inr height.1))
  have hfactor' :
      hζ.toInteger * splitFirstEisensteinFactor hζ m n *
          splitSecondEisensteinFactor hζ m n =
        (k : 𝓞 K) * (((a : ℤ) : 𝓞 K) + b * hζ.toInteger) ^ 3 := by
    simpa only [splitFirstEisensteinFactor,
      splitSecondEisensteinFactor] using hfactor
  have hthreeExcluded :=
    splitEisensteinThreePrime_not_common
      hζ m n a b k hmn hfactor' hk
  have hsupportTwo : ∀ p : 𝓞 K,
      Prime p →
      p ∣ splitFirstEisensteinFactor hζ m n →
      p ∣ splitSecondEisensteinFactor hζ m n →
      p ∣ (2 : 𝓞 K) := by
    intro p hp hfirst hsecond
    rcases hsupport p hp hfirst hsecond with htwo | hthree
    · exact htwo
    · exact False.elim <| hthreeExcluded ⟨
        hthree.dvd_iff_dvd_left.mp hfirst,
        hthree.dvd_iff_dvd_left.mp hsecond⟩
  exact hobs K hζ m n a b k hn hb hmn hsupportTwo hab ha habne hm
    hnodd hleading htrace hpair hfactor hmodFour' hnorm hseven

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

/-- The support-only-over-`2` Eisenstein boundary has a checked
exact-order-eighteen consumer. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_twoPrimeSupportedEisensteinIntegerObstruction
    (hobs :
      TwoPrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_primeSupportedEisensteinIntegerObstruction
    (primeSupportedEisensteinIntegerObstruction_of_twoPrimeSupported hobs) E Q

end MazurTorsion.XOneEighteenDescent
