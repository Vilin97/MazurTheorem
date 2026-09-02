/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial

/-!
# Cached coefficients of dense polynomial sums

This probe isolates the cheap consumer needed by the large order-twenty-five
assembly certificate.  Once each summand has supplied a checked coefficient
or row equality, the lemmas below combine those cached equalities without
unfolding any multiplication used to construct the summands.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialSumCoefficientProbe

open OrderTwentyFiveDensePolynomial

/-- A scalar coefficient of a dense bivariate polynomial, with zero outside
the represented rectangle. -/
def coefficient (p : Two) (outer inner : ℕ) : ℤ :=
  (p.getD outer []).getD inner 0

/-- Right-associated addition of dense bivariate polynomials. -/
def sum : List Two → Two
  | [] => []
  | p :: ps => Two.add p (sum ps)

/-- Right-associated addition of dense univariate rows. -/
def rowSum : List One → One
  | [] => []
  | p :: ps => One.add p (rowSum ps)

private theorem oneAdd_nil (p : One) : One.add p [] = p := by
  cases p <;> rfl

private theorem getD_addWith : ∀ p q n,
    (addWith One.add p q).getD n [] =
      One.add (p.getD n []) (q.getD n []) := by
  intro p
  induction p with
  | nil =>
      intro q n
      simp [addWith, One.add]
  | cons a p ih =>
      intro q n
      cases q with
      | nil => simp [addWith, oneAdd_nil]
      | cons b q =>
          cases n with
          | zero => rfl
          | succ n => simpa [addWith] using ih q n

private theorem getD_addWithInt : ∀ (p q : One) (n : ℕ),
    (addWith (· + ·) p q).getD n 0 =
      p.getD n 0 + q.getD n 0 := by
  intro p
  induction p with
  | nil =>
      intro q n
      simp [addWith]
  | cons a p ih =>
      intro q n
      cases q with
      | nil => simp [addWith]
      | cons b q =>
          cases n with
          | zero => rfl
          | succ n => simpa [addWith] using ih q n

/-- Taking one outer row commutes with dense addition. -/
theorem row_add (p q : Two) (outer : ℕ) :
    (Two.add p q).getD outer [] =
      One.add (p.getD outer []) (q.getD outer []) := by
  exact getD_addWith p q outer

/-- Taking a scalar coefficient commutes with dense addition. -/
theorem coefficient_add (p q : Two) (outer inner : ℕ) :
    coefficient (Two.add p q) outer inner =
      coefficient p outer inner + coefficient q outer inner := by
  rw [coefficient, coefficient, coefficient, row_add]
  exact getD_addWithInt (p.getD outer []) (q.getD outer []) inner

/-- Taking one outer row commutes with a right-associated dense sum. -/
theorem row_sum (ps : List Two) (outer : ℕ) :
    (sum ps).getD outer [] =
      rowSum (ps.map fun p => p.getD outer []) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [sum, row_add, List.map_cons, rowSum, ih]

/-- Taking a scalar coefficient commutes with a right-associated dense sum. -/
theorem coefficient_sum (ps : List Two) (outer inner : ℕ) :
    coefficient (sum ps) outer inner =
      (ps.map fun p => coefficient p outer inner).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [sum, coefficient_add, List.map_cons, List.sum_cons, ih]

/-- Eleven cached scalar coefficient equalities can be combined without
recomputing any of the eleven summands. -/
theorem coefficient_sum_eleven_of_cached
    (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Two)
    (outer inner : ℕ) (z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : ℤ)
    (h1 : coefficient t1 outer inner = z1)
    (h2 : coefficient t2 outer inner = z2)
    (h3 : coefficient t3 outer inner = z3)
    (h4 : coefficient t4 outer inner = z4)
    (h5 : coefficient t5 outer inner = z5)
    (h6 : coefficient t6 outer inner = z6)
    (h7 : coefficient t7 outer inner = z7)
    (h8 : coefficient t8 outer inner = z8)
    (h9 : coefficient t9 outer inner = z9)
    (h10 : coefficient t10 outer inner = z10)
    (h11 : coefficient t11 outer inner = z11) :
    coefficient (sum [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11])
        outer inner =
      z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8 + z9 + z10 + z11 := by
  rw [coefficient_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  ring

/-- Eleven cached row equalities can likewise be combined without inspecting
the construction of the summands. -/
theorem row_sum_eleven_of_cached
    (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Two) (outer : ℕ)
    (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : One)
    (h1 : t1.getD outer [] = r1)
    (h2 : t2.getD outer [] = r2)
    (h3 : t3.getD outer [] = r3)
    (h4 : t4.getD outer [] = r4)
    (h5 : t5.getD outer [] = r5)
    (h6 : t6.getD outer [] = r6)
    (h7 : t7.getD outer [] = r7)
    (h8 : t8.getD outer [] = r8)
    (h9 : t9.getD outer [] = r9)
    (h10 : t10.getD outer [] = r10)
    (h11 : t11.getD outer [] = r11) :
    (sum [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]).getD outer [] =
      rowSum [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11] := by
  rw [row_sum]
  simp only [List.map_cons, List.map_nil]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- The hard assembly coefficient `(42, 4)` reduces immediately once the
eleven signed term coefficients have been checked separately. -/
theorem row42_coefficient4_of_cached
    (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Two)
    (h1 : coefficient t1 42 4 = -363277523642)
    (h2 : coefficient t2 42 4 = 409684617855)
    (h3 : coefficient t3 42 4 = -81569893061)
    (h4 : coefficient t4 42 4 = 3696857819817)
    (h5 : coefficient t5 42 4 = 16148904296)
    (h6 : coefficient t6 42 4 = 318)
    (h7 : coefficient t7 42 4 = -11080631045208)
    (h8 : coefficient t8 42 4 = 11199197480)
    (h9 : coefficient t9 42 4 = -3)
    (h10 : coefficient t10 42 4 = 0)
    (h11 : coefficient t11 42 4 = 202428774795) :
    coefficient (sum [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]) 42 4 =
      -7189159147353 := by
  rw [coefficient_sum_eleven_of_cached t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11
    42 4
    (-363277523642) 409684617855 (-81569893061) 3696857819817 16148904296
    318 (-11080631045208) 11199197480 (-3) 0 202428774795
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  norm_num

end MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialSumCoefficientProbe
