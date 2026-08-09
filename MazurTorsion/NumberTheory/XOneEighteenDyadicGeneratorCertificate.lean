/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenDyadicCubicCertificate

/-!
# Dyadic reductions of the four `X₁(18)` norm-kernel generators

At the dyadic factor with `s ≡ 74`, the normalized degree-nine generator
reduces to `7 + 10τ + τ²` modulo `16`.  This file evaluates the four integral
generator polynomials at that element and checks that their fifteen nonempty
products are precisely the nonsquare triples certified in
`XOneEighteenDyadicCubicCertificate`.

The separate integral-reduction bridge must prove that the global algebraic
integers reduce to these triples.  No completion or integrality assertion is
made here.
-/

namespace MazurTorsion.XOneEighteenDyadicGeneratorCertificate

open MazurTorsion.XOneEighteenDyadicCubicCertificate

/-- The multiplicative identity in the cubic coefficient model. -/
def one : CubicResidue := ![1, 0, 0]

/-- Powers for the cubic multiplication, rather than the pointwise
multiplication inherited by coefficient vectors. -/
def cubicPow (x : CubicResidue) : ℕ → CubicResidue
  | 0 => one
  | n + 1 => mul (cubicPow x n) x

/-- Reduction modulo `16` of the normalized generator at `s ≡ 74`. -/
def normalizedGenerator : CubicResidue := ![7, 10, 1]

/-- Reduction of the first integral norm-kernel generator polynomial. -/
def firstGenerator : CubicResidue :=
  -cubicPow normalizedGenerator 8 + 3 * cubicPow normalizedGenerator 7 -
    8 * cubicPow normalizedGenerator 5 + 6 * cubicPow normalizedGenerator 4 +
    8 * cubicPow normalizedGenerator 3 - 7 * cubicPow normalizedGenerator 2 -
    3 * normalizedGenerator + 3 * one

/-- Reduction of the second integral norm-kernel generator polynomial. -/
def secondGenerator : CubicResidue :=
  -cubicPow normalizedGenerator 6 + 3 * cubicPow normalizedGenerator 5 -
    cubicPow normalizedGenerator 4 - 4 * cubicPow normalizedGenerator 3 +
    3 * cubicPow normalizedGenerator 2 + 3 * normalizedGenerator - one

/-- Reduction of the third integral norm-kernel generator polynomial. -/
def thirdGenerator : CubicResidue :=
  -mul
    (cubicPow normalizedGenerator 3 - cubicPow normalizedGenerator 2 + one)
    (cubicPow normalizedGenerator 5 - 3 * cubicPow normalizedGenerator 4 +
      cubicPow normalizedGenerator 3 + 4 * cubicPow normalizedGenerator 2 -
      3 * normalizedGenerator - 4 * one)

/-- Reduction of the fourth integral norm-kernel generator polynomial. -/
def fourthGenerator : CubicResidue :=
  -mul
    (cubicPow normalizedGenerator 3 - 2 * cubicPow normalizedGenerator 2 +
      normalizedGenerator + one)
    (cubicPow normalizedGenerator 3 - cubicPow normalizedGenerator 2 -
      2 * normalizedGenerator - one)

/-- The four reductions, in the order used by binary masks. -/
def generator : Fin 4 → CubicResidue :=
  ![firstGenerator, secondGenerator, thirdGenerator, fourthGenerator]

/-- Exact reductions of the four generator polynomials. -/
theorem generator_eq :
    generator = ![![15, 1, 5], ![12, 11, 11], ![14, 6, 2], ![2, 0, 2]] := by
  decide +kernel

/-- Product of the four generators selected by the low four bits of a mask. -/
def maskedProduct (mask : Fin 16) : CubicResidue :=
  mul (if mask.val.testBit 0 then generator 0 else one) <|
    mul (if mask.val.testBit 1 then generator 1 else one) <|
      mul (if mask.val.testBit 2 then generator 2 else one)
        (if mask.val.testBit 3 then generator 3 else one)

/-- The canonical nonzero four-bit mask corresponding to `i+1`. -/
def nonzeroMask (i : Fin 15) : Fin 16 :=
  ⟨i.val + 1, by omega⟩

/-- The fifteen nonempty products agree with the certified candidate table. -/
theorem maskedProduct_nonzeroMask (i : Fin 15) :
    maskedProduct (nonzeroMask i) = candidate i := by
  decide +kernel +revert

/-- Every nonempty product of the four projected generators is a nonsquare
modulo `16`. -/
theorem maskedProduct_nonsquare (i : Fin 15) :
    ¬ XOneEighteenDyadicCubicCertificate.IsSquare
      (maskedProduct (nonzeroMask i)) := by
  rw [maskedProduct_nonzeroMask]
  exact candidate_nonsquare i

end MazurTorsion.XOneEighteenDyadicGeneratorCertificate
