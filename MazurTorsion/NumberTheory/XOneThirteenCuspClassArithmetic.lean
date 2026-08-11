/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit

/-!
# Arithmetic of the six projective cusp classes on `X₁(13)`

This file isolates the small abelian-group calculation behind the classical
order-`19` cusp subgroup.  Here `D` denotes `[∞⁻-∞⁺]`, while
`A`, `Abar`, `B`, and `C` denote the four affine cusp classes based at
`∞⁺`.  Three principal divisors and the divisors of `X` and `X+1`
give the five relations packaged below.

No divisor-class group is manufactured here.  A projective divisor
implementation must instantiate this certificate using actual principal
divisor identities.  Once instantiated, the rest is pure checked group
arithmetic: every cusp is a displayed multiple of `D`, and `19 • D = 0`.
-/

namespace MazurTorsion.XOneThirteenCuspClassArithmetic

/-- The five projective principal-divisor relations needed for the cusp
subgroup computation. -/
structure Certificate
    (G : Type*) [AddCommGroup G]
    (D A Abar B C : G) : Prop where
  w : A + B = 3 • D
  wSubX : 3 • A + C = 3 • D
  wSubQuadratic : A + 4 • C = 3 • D
  x : A + Abar = D
  xAddOne : B + C = D

variable {G : Type*} [AddCommGroup G]
variable {D A Abar B C : G}

namespace Certificate

variable (R : Certificate G D A Abar B C)

include R

/-- Eliminating `B` from the divisors of `w` and `X+1`. -/
theorem A_sub_C : A - C = 2 • D := by
  calc
    A - C = (A + B) - (B + C) := by abel
    _ = 3 • D - D := by rw [R.w, R.xAddOne]
    _ = 2 • D := by abel

/-- First integral relation between the affine cusp generator and the two
infinity branches. -/
theorem four_A_eq_five_D : 4 • A = 5 • D := by
  calc
    4 • A = (3 • A + C) + (A - C) := by abel
    _ = 3 • D + 2 • D := by rw [R.wSubX, R.A_sub_C]
    _ = 5 • D := by abel

/-- Second integral relation, obtained from the quadratic shift. -/
theorem five_A_eq_eleven_D : 5 • A = 11 • D := by
  calc
    5 • A = (A + 4 • C) + 4 • (A - C) := by abel
    _ = 3 • D + 4 • (2 • D) := by
      rw [R.wSubQuadratic, R.A_sub_C]
    _ = 11 • D := by abel

/-- The infinity difference is killed by nineteen. -/
theorem nineteen_nsmul_D : 19 • D = 0 := by
  calc
    19 • D = 4 • (11 • D) - 5 • (5 • D) := by abel
    _ = 4 • (5 • A) - 5 • (4 • A) := by
      rw [← R.five_A_eq_eleven_D, ← R.four_A_eq_five_D]
    _ = 0 := by abel

/-- The cusp `(0,1)` represents `6D`. -/
theorem A_eq : A = 6 • D := by
  calc
    A = 5 • A - 4 • A := by abel
    _ = 11 • D - 5 • D := by
      rw [R.five_A_eq_eleven_D, R.four_A_eq_five_D]
    _ = 6 • D := by abel

/-- The cusp `(-1,-1)` represents `4D`. -/
theorem C_eq : C = 4 • D := by
  calc
    C = A - (A - C) := by abel
    _ = A - 2 • D := by rw [R.A_sub_C]
    _ = 6 • D - 2 • D := by rw [R.A_eq]
    _ = 4 • D := by abel

/-- The cusp `(-1,1)` represents `16D`. -/
theorem B_eq : B = 16 • D := by
  calc
    B = D - C := by rw [← R.xAddOne]; abel
    _ = D - 4 • D := by rw [R.C_eq]
    _ = 16 • D - 19 • D := by abel
    _ = 16 • D := by rw [R.nineteen_nsmul_D, sub_zero]

/-- The conjugate cusp `(0,-1)` represents `14D`. -/
theorem Abar_eq : Abar = 14 • D := by
  calc
    Abar = D - A := by rw [← R.x]; abel
    _ = D - 6 • D := by rw [R.A_eq]
    _ = 14 • D - 19 • D := by abel
    _ = 14 • D := by rw [R.nineteen_nsmul_D, sub_zero]

/-- All projective cusp-class consequences in one downstream-facing
statement. -/
theorem cusp_class_table :
    19 • D = 0 ∧ A = 6 • D ∧ Abar = 14 • D ∧
      B = 16 • D ∧ C = 4 • D :=
  ⟨R.nineteen_nsmul_D, R.A_eq, R.Abar_eq, R.B_eq, R.C_eq⟩

/-- Distinct infinity branches make the displayed order exactly nineteen. -/
theorem addOrderOf_D (hD : D ≠ 0) : addOrderOf D = 19 :=
  XOneThirteenDescent.exact_order_nineteen_of_divisor_certificate
    D R.nineteen_nsmul_D hD

end Certificate

end MazurTorsion.XOneThirteenCuspClassArithmetic
