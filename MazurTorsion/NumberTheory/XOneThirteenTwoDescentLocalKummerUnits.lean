/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentLocalKummerPoints

/-!
# Unit certificates for the two dyadic Kummer representatives

The fake two-descent target uses units of the dyadic étale algebra.  This
leaf supplies explicit Bézout inverses for the two representatives

`qB = 1 - 2a²` and `qC = 2 - a²`.

The products are `313` and `193`, the nonzero curve values already checked
at `x = 1/2` and `x = 2`.  Mapping the identities to the base-changed sextic
algebra and dividing by those scalar units packages both representatives as
actual units.  Every identity retained here is verified by polynomial
arithmetic in Lean.
-/

namespace MazurTorsion.XOneThirteenTwoDescentLocalKummerUnits

open XOneThirteenTwoDescentMagmaBridge
open XOneThirteenTwoDescentLocalElements
open XOneThirteenTwoDescentLocalKummerPoints

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Integer-coefficient Bézout cofactor for `qC`. -/
def localQCBezout : MagmaOrder :=
  integralA ^ 10 + 4 * integralA ^ 8 + 9 * integralA ^ 6 +
    20 * integralA ^ 4 + 46 * integralA ^ 2 + 96

/-- Integer-coefficient Bézout cofactor for `qB`. -/
def localQBBezout : MagmaOrder :=
  32 * integralA ^ 10 + 80 * integralA ^ 8 +
    72 * integralA ^ 6 + 100 * integralA ^ 4 +
    242 * integralA ^ 2 + 249

/-- Exact resultant identity at `x = 2`. -/
theorem localQC_mul_bezout : localQC * localQCBezout = 193 := by
  have h := integralA_spec
  simp only [localQC, localQCBezout]
  linear_combination
    -(integralA ^ 6 + 2 * integralA ^ 5 +
      3 * integralA ^ 4 + 4 * integralA ^ 3 +
      4 * integralA ^ 2 + 2 * integralA + 1) * h

/-- Exact resultant identity at `x = 1/2`, with denominators cleared. -/
theorem localQB_mul_bezout : localQB * localQBBezout = 313 := by
  have h := integralA_spec
  simp only [localQB, localQBBezout]
  linear_combination
    (-64 * (integralA ^ 6 + 2 * integralA ^ 5 +
      3 * integralA ^ 4 + 4 * integralA ^ 3 +
      4 * integralA ^ 2 + 2 * integralA + 1)) * h

/-- The image of `qC` times its integral cofactor is the scalar `193`. -/
theorem padicQC_mul_bezout :
    magmaOrderToPadic localQC * magmaOrderToPadic localQCBezout = 193 := by
  rw [← map_mul, localQC_mul_bezout, map_ofNat]

/-- The image of `qB` times its integral cofactor is the scalar `313`. -/
theorem padicQB_mul_bezout :
    magmaOrderToPadic localQB * magmaOrderToPadic localQBBezout = 313 := by
  rw [← map_mul, localQB_mul_bezout, map_ofNat]

/-- An explicit inverse for the dyadic image of `qC`. -/
def padicQCInverse : MagmaPadicAlgebra :=
  algebraMap ℚ_[2] MagmaPadicAlgebra (193 : ℚ_[2])⁻¹ *
    magmaOrderToPadic localQCBezout

/-- An explicit inverse for the dyadic image of `qB`. -/
def padicQBInverse : MagmaPadicAlgebra :=
  algebraMap ℚ_[2] MagmaPadicAlgebra (313 : ℚ_[2])⁻¹ *
    magmaOrderToPadic localQBBezout

theorem padicQC_mul_inverse :
    magmaOrderToPadic localQC * padicQCInverse = 1 := by
  calc
    magmaOrderToPadic localQC * padicQCInverse =
        algebraMap ℚ_[2] MagmaPadicAlgebra (193 : ℚ_[2])⁻¹ *
          (magmaOrderToPadic localQC *
            magmaOrderToPadic localQCBezout) := by
      simp only [padicQCInverse]
      ring
    _ = algebraMap ℚ_[2] MagmaPadicAlgebra (193 : ℚ_[2])⁻¹ *
          193 := by rw [padicQC_mul_bezout]
    _ = 1 := by
      rw [← map_ofNat (algebraMap ℚ_[2] MagmaPadicAlgebra) 193,
        ← map_mul]
      norm_num

theorem padicQB_mul_inverse :
    magmaOrderToPadic localQB * padicQBInverse = 1 := by
  calc
    magmaOrderToPadic localQB * padicQBInverse =
        algebraMap ℚ_[2] MagmaPadicAlgebra (313 : ℚ_[2])⁻¹ *
          (magmaOrderToPadic localQB *
            magmaOrderToPadic localQBBezout) := by
      simp only [padicQBInverse]
      ring
    _ = algebraMap ℚ_[2] MagmaPadicAlgebra (313 : ℚ_[2])⁻¹ *
          313 := by rw [padicQB_mul_bezout]
    _ = 1 := by
      rw [← map_ofNat (algebraMap ℚ_[2] MagmaPadicAlgebra) 313,
        ← map_mul]
      norm_num

/-- The local Kummer representative `qC`, as an actual unit of the dyadic
sextic algebra. -/
def padicQCUnit : MagmaPadicAlgebraˣ :=
  Units.mkOfMulEqOne (magmaOrderToPadic localQC) padicQCInverse
    padicQC_mul_inverse

/-- The local Kummer representative `qB`, as an actual unit of the dyadic
sextic algebra. -/
def padicQBUnit : MagmaPadicAlgebraˣ :=
  Units.mkOfMulEqOne (magmaOrderToPadic localQB) padicQBInverse
    padicQB_mul_inverse

@[simp]
theorem padicQCUnit_coe :
    (padicQCUnit : MagmaPadicAlgebra) = magmaOrderToPadic localQC :=
  rfl

@[simp]
theorem padicQBUnit_coe :
    (padicQBUnit : MagmaPadicAlgebra) = magmaOrderToPadic localQB :=
  rfl

/-- Both fixed local Kummer representatives are genuine units. -/
theorem local_kummer_representatives_are_units :
    IsUnit (magmaOrderToPadic localQB) ∧
      IsUnit (magmaOrderToPadic localQC) :=
  ⟨padicQBUnit.isUnit, padicQCUnit.isUnit⟩

end

end MazurTorsion.XOneThirteenTwoDescentLocalKummerUnits
