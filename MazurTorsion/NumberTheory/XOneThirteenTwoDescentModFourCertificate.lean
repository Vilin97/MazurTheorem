/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentModTwoCertificate
import Mathlib.Data.Fin.VecNotation

/-!
# The mod-four local-image certificate for `X₁(13)`

This file verifies the bounded `O / 4 O` calculation used to separate the
two visible local Kummer generators at `2`.  In the integral power basis
`1, a, ..., a⁵`, the order modulo `4` is represented by

`(ZMod 4)[a] / (a⁶ - 2a⁵ + 3a⁴ - 4a³ + 4a² - 2a + 1)`.

The multiplication formula below reduces raw products through degree ten.
The square of an arbitrary coefficient vector depends only on the parity of
each of its six coefficients.  This is proved algebraically by writing the
vector as its binary lift plus twice another vector.  Consequently the
square test examines only 64 normalized roots, rather than all 4096 elements
of the quotient.

For the four exponents `(e,b,c,d)`, the tested element is

`lambda^e * 5^b * qB^c * qC^d`,

where `qB = 1 - 2a²` and `qC = 2 - a²`.  Exactly `0000` and `0100`
are squares.  Thus a square forces `c = d = 0`.

The descent framework is Michael Stoll, *Implementing 2-descent for
Jacobians of hyperelliptic curves*, Acta Arith. 98 (2001), Section 5,
DOI `10.4064/aa98-3-4`.  All finite identities here were independently
recomputed and are checked by Lean; no third-party code is retained.
-/

namespace MazurTorsion.XOneThirteenTwoDescentModFourCertificate

open Polynomial

abbrev F2 := ZMod 2
abbrev F4 := ZMod 4

private instance : NeZero (2 : ℕ) := ⟨by decide⟩
private instance : NeZero (4 : ℕ) := ⟨by decide⟩
private instance : Fintype F2 := ZMod.fintype 2
private instance : Fintype F4 := ZMod.fintype 4

/-- Binary coefficient vectors used for normalized square roots. -/
abbrev V2 := Fin 6 → F2

/-- Coefficient vectors in `O / 4 O`. -/
abbrev V4 := Fin 6 → F4

/-- The defining polynomial for the chosen integral generator modulo `4`. -/
noncomputable def g : F4[X] :=
  X ^ 6 - 2 * X ^ 5 + 3 * X ^ 4 - 4 * X ^ 3 +
    4 * X ^ 2 - 2 * X + 1

/-- The coefficient of degree `n` in an ordinary product before reduction. -/
def convolutionCoefficient (x y : V4) (n : ℕ) : F4 :=
  ∑ i : Fin 6, ∑ j : Fin 6,
    if i.val + j.val = n then x i * y j else 0

/-- Multiplication in the six-dimensional quotient modulo `g`.

The reductions of `a⁶`, ..., `a¹⁰` have coefficient vectors

`[3,2,0,0,1,2]`, `[2,3,2,0,2,1]`, `[3,0,3,2,1,0]`,
`[0,3,0,3,2,1]`, and `[3,2,3,0,0,0]`, respectively.
-/
def quotientMul (x y : V4) : V4 :=
  let c := convolutionCoefficient x y
  ![c 0 + 3 * c 6 + 2 * c 7 + 3 * c 8 + 3 * c 10,
    c 1 + 2 * c 6 + 3 * c 7 + 3 * c 9 + 2 * c 10,
    c 2 + 2 * c 7 + 3 * c 8 + 3 * c 10,
    c 3 + 2 * c 8 + 3 * c 9,
    c 4 + c 6 + 2 * c 7 + c 8 + 2 * c 9,
    c 5 + 2 * c 6 + c 7 + c 9]

/-- The multiplicative identity in quotient coordinates. -/
def one : V4 := ![1, 0, 0, 0, 0, 0]

/-- The coefficientwise double of a vector. -/
def double (x : V4) : V4 := fun i ↦ 2 * x i

/-- Reduction of a mod-four coefficient to its parity. -/
def parity (x : F4) : F2 :=
  ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) x

/-- The canonical representative `0` or `1` in `ZMod 4` of a binary value. -/
def bitLift (x : F2) : F4 := (x.val : F4)

/-- Coefficientwise parity reduction. -/
def parityVector (x : V4) : V2 := fun i ↦ parity (x i)

/-- Coefficientwise canonical lift of a binary vector. -/
def normalizedRoot (x : V2) : V4 := fun i ↦ bitLift (x i)

/-- There are exactly 64 binary-normalized root candidates. -/
theorem card_normalizedRoots : Fintype.card V2 = 64 := by
  decide

/-- The remaining half after removing the canonical parity representative. -/
def halfDifference (x : F4) : F4 := (x.val / 2 : ℕ)

/-- The coefficientwise half-difference. -/
def halfDifferenceVector (x : V4) : V4 := fun i ↦ halfDifference (x i)

theorem coefficient_parity_decomposition (x : F4) :
    x = bitLift (parity x) + 2 * halfDifference x := by
  decide +revert

/-- Every vector is its normalized binary lift plus twice another vector. -/
theorem parity_decomposition (x : V4) :
    x = normalizedRoot (parityVector x) + double (halfDifferenceVector x) := by
  funext i
  exact coefficient_parity_decomposition (x i)

theorem convolutionCoefficient_add_left (x y z : V4) (n : ℕ) :
    convolutionCoefficient (x + y) z n =
      convolutionCoefficient x z n + convolutionCoefficient y z n := by
  simp only [convolutionCoefficient, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i.val + j.val = n <;> simp [h]

theorem convolutionCoefficient_add_right (x y z : V4) (n : ℕ) :
    convolutionCoefficient x (y + z) n =
      convolutionCoefficient x y n + convolutionCoefficient x z n := by
  simp only [convolutionCoefficient, Pi.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i.val + j.val = n <;> simp [h]

theorem convolutionCoefficient_comm (x y : V4) (n : ℕ) :
    convolutionCoefficient x y n = convolutionCoefficient y x n := by
  simp only [convolutionCoefficient]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm, mul_comm]

theorem convolutionCoefficient_double_left (x y : V4) (n : ℕ) :
    convolutionCoefficient (double x) y n =
      2 * convolutionCoefficient x y n := by
  simp [convolutionCoefficient, double, mul_assoc, Finset.mul_sum]

theorem convolutionCoefficient_double_right (x y : V4) (n : ℕ) :
    convolutionCoefficient x (double y) n =
      2 * convolutionCoefficient x y n := by
  rw [convolutionCoefficient_comm, convolutionCoefficient_double_left,
    convolutionCoefficient_comm]

theorem convolutionCoefficient_add_double_self (r s : V4) (n : ℕ) :
    convolutionCoefficient (r + double s) (r + double s) n =
      convolutionCoefficient r r n := by
  rw [convolutionCoefficient_add_left, convolutionCoefficient_add_right,
    convolutionCoefficient_add_right, convolutionCoefficient_double_right,
    convolutionCoefficient_double_left, convolutionCoefficient_double_left,
    convolutionCoefficient_double_right, convolutionCoefficient_comm s r]
  ring_nf
  have hfour : (4 : F4) = 0 := by decide
  simp [hfour]

/-- Adding twice any vector does not change a square in this characteristic
four quotient.  This is the algebraic reason only 64 roots need testing. -/
theorem quotientMul_add_double_self (r s : V4) :
    quotientMul (r + double s) (r + double s) = quotientMul r r := by
  funext i
  fin_cases i <;>
    simp [quotientMul, convolutionCoefficient_add_double_self]

/-- Every mod-four vector has the same square as its normalized binary
parity lift. -/
theorem quotientMul_self_eq_normalizedRoot (x : V4) :
    quotientMul x x =
      quotientMul (normalizedRoot (parityVector x))
        (normalizedRoot (parityVector x)) := by
  conv_lhs => rw [parity_decomposition x]
  exact quotientMul_add_double_self _ _

/-- The usual square predicate in the 4096-element quotient. -/
def IsSquare (x : V4) : Prop := ∃ r : V4, quotientMul r r = x

/-- The square predicate reduces exactly to the 64 binary-normalized roots. -/
theorem isSquare_iff_exists_normalizedRoot (x : V4) :
    IsSquare x ↔
      ∃ r : V2, quotientMul (normalizedRoot r) (normalizedRoot r) = x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨parityVector r, ?_⟩
    rw [← quotientMul_self_eq_normalizedRoot r]
    exact hr
  · rintro ⟨r, hr⟩
    exact ⟨normalizedRoot r, hr⟩

/-- `lambda = 15 - 7a + a² - 2a³ - a⁴ + 5a⁵`. -/
def lambda : V4 := ![15, -7, 1, -2, -1, 5]

/-- The rational scalar `5`. -/
def five : V4 := ![5, 0, 0, 0, 0, 0]

/-- The first visible local Kummer generator `qB = 1 - 2a²`. -/
def qB : V4 := ![1, 0, -2, 0, 0, 0]

/-- The second visible local Kummer generator `qC = 2 - a²`. -/
def qC : V4 := ![2, 0, -1, 0, 0, 0]

theorem lambda_reduced_coefficients : lambda = ![3, 1, 1, 2, 3, 1] := by
  decide

theorem five_reduced_coefficients : five = one := by
  decide

theorem qB_reduced_coefficients : qB = ![1, 0, 2, 0, 0, 0] := by
  decide

theorem qC_reduced_coefficients : qC = ![2, 0, 3, 0, 0, 0] := by
  decide

/-- Exponentiation by a bit. -/
def bitPow (x : V4) (e : F2) : V4 := if e = 0 then one else x

/-- The four bits indexing the bounded local-image calculation, in the order
`e`, `b`, `c`, `d`. -/
abbrev Exponents := Fin 4 → F2

/-- There are exactly sixteen exponent patterns in the certificate. -/
theorem card_exponents : Fintype.card Exponents = 16 := by
  decide

def exponentE (s : Exponents) : F2 := s 0
def exponentB (s : Exponents) : F2 := s 1
def exponentC (s : Exponents) : F2 := s 2
def exponentD (s : Exponents) : F2 := s 3

/-- The product `lambda^e * 5^b * qB^c * qC^d`, with fixed left
association in the explicit quotient multiplication. -/
def certificateProduct (s : Exponents) : V4 :=
  quotientMul
    (quotientMul
      (quotientMul (bitPow lambda (exponentE s)) (bitPow five (exponentB s)))
      (bitPow qB (exponentC s)))
    (bitPow qC (exponentD s))

/-- The all-zero bit pattern. -/
def zeroPattern : Exponents := ![0, 0, 0, 0]

/-- The bit pattern selecting only the rational scalar `5`. -/
def fivePattern : Exponents := ![0, 1, 0, 0]

/-- Among the sixteen products, exactly bit patterns `0000` and `0100`
are squares.  The decision procedure examines the sixteen products against
the 64 normalized roots supplied by `isSquare_iff_exists_normalizedRoot`. -/
theorem certificateProduct_isSquare_iff (s : Exponents) :
    IsSquare (certificateProduct s) ↔ s = zeroPattern ∨ s = fivePattern := by
  rw [isSquare_iff_exists_normalizedRoot]
  decide +revert

/-- Independence of the two visible local Kummer generators: if the tested
product is a square, then the exponents of `qB` and `qC` both vanish. -/
theorem qB_qC_exponents_eq_zero_of_certificateProduct_isSquare
    (s : Exponents) (hs : IsSquare (certificateProduct s)) :
    exponentC s = 0 ∧ exponentD s = 0 := by
  rcases (certificateProduct_isSquare_iff s).1 hs with h | h
  · rw [h]
    decide
  · rw [h]
    decide

end MazurTorsion.XOneThirteenTwoDescentModFourCertificate
