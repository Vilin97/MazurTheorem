/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2Lookup
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4Lookup
public import MazurTorsion.Kubert.OrderSevenCoefficientSimp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ShiftPart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ShiftPart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3ShiftPart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4ShiftPart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4MainPart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquarePart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart1Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart1Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A3Part0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4SquarePart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0MainPart1Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart1Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquarePart0Simp
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3DenseData

/-!
# Recurrence 3 dense certificate for the order-seven resultant

This module checks the four remaining scalar residuals as exact dense integer
convolutions.  Intermediate products are separately certified against fixed
coefficient tables so that every kernel reduction stays within Lean's default
resource limits.  The terminal recurrence module is the named downstream
consumer.
-/

@[expose] public section

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate
namespace IntegerDenseCertificate

/-- Add two little-endian dense coefficient lists. -/
def add : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: add xs ys

/-- Scale a little-endian dense coefficient list. -/
def scale (a : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: xs => (a * x) :: scale a xs

/-- Convolve two little-endian dense coefficient lists. -/
def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, ys => add (scale x ys) (0 :: mul xs ys)

/-- Negate a little-endian dense coefficient list. -/
def neg (xs : List ℤ) : List ℤ := scale (-1) xs

/-- Subtract two little-endian dense coefficient lists. -/
def sub (xs ys : List ℤ) : List ℤ := add xs (neg ys)

/-- Compare dense lists in bounded chunks. -/
def chunkedEq (chunk : ℕ) : ℕ → List ℤ → List ℤ → Bool
  | 0, xs, ys => xs.isEmpty && ys.isEmpty
  | fuel + 1, xs, ys =>
      (xs.take chunk == ys.take chunk) &&
        chunkedEq chunk fuel (xs.drop chunk) (ys.drop chunk)

/-- A successful bounded chunk comparison proves ordinary list equality. -/
theorem eq_of_chunkedEq {chunk fuel : ℕ} {xs ys : List ℤ}
    (h : chunkedEq chunk fuel xs ys = true) : xs = ys := by
  induction fuel generalizing xs ys with
  | zero =>
      cases xs <;> cases ys <;> simp_all [chunkedEq]
  | succ fuel ih =>
      simp only [chunkedEq, Bool.and_eq_true, beq_iff_eq] at h
      rw [← List.take_append_drop chunk xs, ← List.take_append_drop chunk ys,
        h.1, ih h.2]

def a0 : List ℤ := Data.a0
def a1 : List ℤ := Data.a1
def a2 : List ℤ := Data.a2
def a3 : List ℤ := Data.a3
def a4 : List ℤ := Data.a4
def a5 : List ℤ := Data.a5

def b0 : List ℤ := Data.b0
def b1 : List ℤ := Data.b1
def b2 : List ℤ := Data.b2
def b3 : List ℤ := Data.b3
def b4 : List ℤ := Data.b4

def c0 : List ℤ := Data.c0
def c1 : List ℤ := Data.c1
def c2 : List ℤ := Data.c2
def c3 : List ℤ := Data.c3

def discriminant : List ℤ := Data.discriminant
def b4Square : List ℤ := Data.b4Square
def a5Square : List ℤ := Data.a5Square
def discriminantSquare : List ℤ := Data.discriminantSquare
def discriminantPower4 : List ℤ := Data.discriminantPower4
def discriminantPower8 : List ℤ := Data.discriminantPower8
def discriminantPower16 : List ℤ := Data.discriminantPower16
def discriminantPower20 : List ℤ := Data.discriminantPower20
def discriminantPower22 : List ℤ := Data.discriminantPower22
def quotientLinear : List ℤ := Data.quotientLinear
def quotientConstant : List ℤ := Data.quotientConstant
def exceptionalProductNumerator : List ℤ := Data.exceptionalProduct

/-- The leading quartic coefficient square agrees with its fixed table. -/
theorem b4Square_checked : mul b4 b4 = b4Square :=
  eq_of_chunkedEq (chunk := 32) (fuel := 12) (by decide +kernel)

/-- The leading quintic coefficient square agrees with its fixed table. -/
theorem a5Square_checked : mul a5 a5 = a5Square :=
  eq_of_chunkedEq (chunk := 32) (fuel := 9) (by decide +kernel)

/-- The first discriminant squaring step agrees with its fixed table. -/
theorem discriminantSquare_checked :
    mul discriminant discriminant = discriminantSquare :=
  eq_of_chunkedEq (chunk := 32) (fuel := 1) (by decide +kernel)

/-- The fourth discriminant power agrees with its fixed table. -/
theorem discriminantPower4_checked :
    mul discriminantSquare discriminantSquare = discriminantPower4 :=
  eq_of_chunkedEq (chunk := 32) (fuel := 1) (by decide +kernel)

/-- The eighth discriminant power agrees with its fixed table. -/
theorem discriminantPower8_checked :
    mul discriminantPower4 discriminantPower4 = discriminantPower8 :=
  eq_of_chunkedEq (chunk := 32) (fuel := 1) (by decide +kernel)

/-- The sixteenth discriminant power agrees with its fixed table. -/
theorem discriminantPower16_checked :
    mul discriminantPower8 discriminantPower8 = discriminantPower16 :=
  eq_of_chunkedEq (chunk := 32) (fuel := 2) (by decide +kernel)

/-- The twentieth discriminant power agrees with its fixed table. -/
theorem discriminantPower20_checked :
    mul discriminantPower16 discriminantPower4 = discriminantPower20 :=
  eq_of_chunkedEq (chunk := 32) (fuel := 2) (by decide +kernel)

/-- The twenty-second discriminant power agrees with its fixed table. -/
theorem discriminantPower22_checked :
    mul discriminantPower20 discriminantSquare = discriminantPower22 :=
  eq_of_chunkedEq (chunk := 32) (fuel := 3) (by decide +kernel)

/-- The linear pseudo-quotient coefficient agrees with its fixed table. -/
theorem quotientLinear_checked : mul b4 a5 = quotientLinear :=
  eq_of_chunkedEq (chunk := 32) (fuel := 10) (by decide +kernel)

/-- The constant pseudo-quotient coefficient agrees with its fixed table. -/
theorem quotientConstant_checked :
    sub (mul b4 a4) (mul b3 a5) = quotientConstant :=
  eq_of_chunkedEq (chunk := 32) (fuel := 10) (by decide +kernel)

/-- The cleared exceptional product agrees with its fixed table. -/
theorem exceptionalProductNumerator_checked :
    mul a5Square discriminantPower22 = exceptionalProductNumerator :=
  eq_of_chunkedEq (chunk := 32) (fuel := 11) (by decide +kernel)

def scalar0ScaledLeft : List ℤ :=
  scale 85566736552441 (mul b4Square a0)

def scalar0ScaledRight : List ℤ :=
  add (scale 85566736552441 (mul b0 quotientConstant))
    (mul exceptionalProductNumerator c0)

def scalar1ScaledLeft : List ℤ :=
  scale 85566736552441 (mul b4Square a1)

def scalar1ScaledRight : List ℤ :=
  add
    (add (scale 85566736552441 (mul b0 quotientLinear))
      (scale 85566736552441 (mul b1 quotientConstant)))
    (mul exceptionalProductNumerator c1)

def scalar2ScaledLeft : List ℤ :=
  scale 85566736552441 (mul b4Square a2)

def scalar2ScaledRight : List ℤ :=
  add
    (add (scale 85566736552441 (mul b1 quotientLinear))
      (scale 85566736552441 (mul b2 quotientConstant)))
    (mul exceptionalProductNumerator c2)

def scalar3ScaledLeft : List ℤ :=
  scale 85566736552441 (mul b4Square a3)

def scalar3ScaledRight : List ℤ :=
  add
    (add (scale 85566736552441 (mul b2 quotientLinear))
      (scale 85566736552441 (mul b3 quotientConstant)))
    (mul exceptionalProductNumerator c3)

/-- The cleared constant scalar residual vanishes. -/
theorem scalar0_scaled_checked : scalar0ScaledLeft = scalar0ScaledRight :=
  eq_of_chunkedEq (chunk := 32) (fuel := 16) (by decide +kernel)

/-- The cleared linear scalar residual vanishes. -/
theorem scalar1_scaled_checked : scalar1ScaledLeft = scalar1ScaledRight :=
  eq_of_chunkedEq (chunk := 32) (fuel := 16) (by decide +kernel)

/-- The cleared quadratic scalar residual vanishes. -/
theorem scalar2_scaled_checked : scalar2ScaledLeft = scalar2ScaledRight :=
  eq_of_chunkedEq (chunk := 32) (fuel := 16) (by decide +kernel)

/-- The cleared cubic scalar residual vanishes. -/
theorem scalar3_scaled_checked : scalar3ScaledLeft = scalar3ScaledRight :=
  eq_of_chunkedEq (chunk := 32) (fuel := 16) (by decide +kernel)

end IntegerDenseCertificate
end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
