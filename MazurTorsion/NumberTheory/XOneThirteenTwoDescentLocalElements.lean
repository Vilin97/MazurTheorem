/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentLocalIntersection
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentPrimeSupport

/-!
# Explicit local elements for the `X₁(13)` two-descent

This leaf connects the local elements used in the independent two-descent
calculation to the genuine monogenic order `ℤ[a]/(g)` and to its reduction
modulo two.  In particular it checks the denominator-cleared identity

`lambda * pi² = 2`

and verifies that `lambda`, `5`, `qB = 1 - 2a²`, and `qC = 2 - a²`
have exactly the coefficient vectors used by the finite local-intersection
certificate.

Only polynomial arithmetic in the explicit order is used here.  The
existence of the corresponding local Kummer classes over `ℚ₂` is a
separate statement.
-/

namespace MazurTorsion.XOneThirteenTwoDescentLocalElements

open XOneThirteenTwoDescentMagmaBridge
open XOneThirteenTwoDescentModTwoCertificate
open XOneThirteenTwoDescentLocalIntersection

noncomputable section

private theorem modTwo_two_eq_zero : (2 : MagmaModTwo) = 0 := by
  rw [← map_ofNat (AdjoinRoot.of magmaSexticModTwo) 2]
  rw [show (2 : ZMod 2) = 0 by decide, map_zero]

/-- The element denoted `pi` in the local calculation. -/
def localPi : MagmaOrder :=
  integralA ^ 3 + integralA ^ 2 + 1

/-- The integral representative of the rational scalar ambiguity
`lambda = 2 / pi²`. -/
def localLambda : MagmaOrder :=
  15 - 7 * integralA + integralA ^ 2 - 2 * integralA ^ 3 -
    integralA ^ 4 + 5 * integralA ^ 5

/-- The first displayed local Kummer generator, arising from `x = 1/2`. -/
def localQB : MagmaOrder := 1 - 2 * integralA ^ 2

/-- The second displayed local Kummer generator, arising from `x = 2`. -/
def localQC : MagmaOrder := 2 - integralA ^ 2

/-- Exact polynomial certificate for `lambda = 2 / pi²`. -/
theorem localLambda_mul_localPi_sq :
    localLambda * localPi ^ 2 = 2 := by
  have h := integralA_spec
  simp only [localLambda, localPi]
  linear_combination
    (5 * integralA ^ 5 + 19 * integralA ^ 4 +
      24 * integralA ^ 3 + 17 * integralA ^ 2 +
      19 * integralA + 13) * h

/-- The actual order element `lambda` reduces to the vector retained in the
finite certificate. -/
theorem localLambda_modTwo_coordinates :
    magmaOrderToModTwo localLambda =
      modTwoCoordinateValue 1 1 1 0 1 1 := by
  simp only [localLambda, map_sub, map_add, map_mul, map_pow, map_ofNat,
    map_one, magmaOrderToModTwo_integralA, modTwoCoordinateValue]
  simp only [map_zero, zero_mul, add_zero]
  linear_combination
    (7 - 4 * modTwoA - modTwoA ^ 3 - modTwoA ^ 4 +
      2 * modTwoA ^ 5) * modTwo_two_eq_zero

/-- The rational scalar `5` reduces to the identity vector. -/
theorem rationalFive_modTwo_coordinates :
    magmaOrderToModTwo (5 : MagmaOrder) =
      modTwoCoordinateValue 1 0 0 0 0 0 := by
  simp only [map_ofNat, modTwoCoordinateValue, map_zero, map_one, zero_mul,
    add_zero]
  linear_combination 2 * modTwo_two_eq_zero

/-- The actual order element `qB` reduces to `1`. -/
theorem localQB_modTwo_coordinates :
    magmaOrderToModTwo localQB =
      modTwoCoordinateValue 1 0 0 0 0 0 := by
  simp only [localQB, map_sub, map_mul, map_pow, map_ofNat, map_one,
    magmaOrderToModTwo_integralA, modTwoCoordinateValue, map_zero, zero_mul,
    add_zero]
  linear_combination (-modTwoA ^ 2) * modTwo_two_eq_zero

/-- The actual order element `qC` reduces to `a²`. -/
theorem localQC_modTwo_coordinates :
    magmaOrderToModTwo localQC =
      modTwoCoordinateValue 0 0 1 0 0 0 := by
  simp only [localQC, map_sub, map_pow, map_ofNat, map_one,
    magmaOrderToModTwo_integralA, modTwoCoordinateValue, map_zero, zero_mul,
    zero_add, one_mul, add_zero]
  linear_combination (1 - modTwoA ^ 2) * modTwo_two_eq_zero

/-- The four exact reductions, bundled as the arithmetic input to the finite
local-intersection certificate. -/
theorem actual_local_reduction_coordinates :
    magmaOrderToModTwo localLambda =
        modTwoCoordinateValue 1 1 1 0 1 1 ∧
      magmaOrderToModTwo (5 : MagmaOrder) =
        modTwoCoordinateValue 1 0 0 0 0 0 ∧
      magmaOrderToModTwo localQB =
        modTwoCoordinateValue 1 0 0 0 0 0 ∧
      magmaOrderToModTwo localQC =
        modTwoCoordinateValue 0 0 1 0 0 0 :=
  ⟨localLambda_modTwo_coordinates, rationalFive_modTwo_coordinates,
    localQB_modTwo_coordinates, localQC_modTwo_coordinates⟩

/-- After the exact reductions above, the finite certificate says that a
locally representable surviving global class must be the identity class. -/
theorem global_class_eq_zero_of_reduced_local_certificate
    (z : XOneThirteenTwoDescentSquareclasses.GlobalSquareclassCertificate)
    (e d : ZMod 2)
    (hsquare : XOneThirteenTwoDescentModTwoCertificate.IsSquare
      (globalLocalReducedProduct z e d)) :
    z = (0, 0) :=
  global_eq_zero_of_globalLocalReducedProduct_isSquare z e d hsquare

end

end MazurTorsion.XOneThirteenTwoDescentLocalElements
