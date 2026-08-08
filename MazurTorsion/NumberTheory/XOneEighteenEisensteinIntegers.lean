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
ideal ring.  What remains here is the arithmetic use of unique factorization:
the support of the three factors, the exceptional primes above `2` and `7`,
and the ensuing unit cases are not proved in this file.
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

end MazurTorsion.XOneEighteenDescent
