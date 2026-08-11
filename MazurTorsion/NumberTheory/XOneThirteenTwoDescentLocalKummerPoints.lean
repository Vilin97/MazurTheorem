/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentLocalElements
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentLocalPointInputs

/-!
# Two concrete dyadic Kummer points for `X₁(13)`

The checked Hensel inputs at `x = 1/2` and `x = 2` give actual points on the
genus-two curve over `ℚ₂`.  This leaf base-changes the explicit integral
sextic order to `ℚ₂` and verifies the associated `x - theta` expressions.
Under the alternate primitive element, `theta = a²`, so

* twice the representative at `x = 1/2` is `qB = 1 - 2a²`;
* the representative at `x = 2` is `qC = 2 - a²`.

These are exact algebra equalities.  Passing from point representatives to a
homomorphism on the Jacobian, and proving that these points span its local
image, remain separate descent statements.
-/

namespace MazurTorsion.XOneThirteenTwoDescentLocalKummerPoints

open Polynomial
open XOneThirteenTwoDescentMagmaBridge
open XOneThirteenTwoDescentLocalElements
open XOneThirteenTwoDescentLocalPointInputs

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The integral Magma sextic after coefficient extension to `ℚ₂`. -/
def magmaPadicSextic : ℚ_[2][X] :=
  magmaSextic.map (Int.castRingHom ℚ_[2])

/-- The explicit dyadic sextic algebra used for local Kummer values. -/
abbrev MagmaPadicAlgebra := AdjoinRoot magmaPadicSextic

/-- The distinguished dyadic primitive element. -/
def padicA : MagmaPadicAlgebra :=
  AdjoinRoot.root magmaPadicSextic

/-- Base change of the integral order to the dyadic sextic algebra. -/
def magmaOrderToPadic : MagmaOrder →+* MagmaPadicAlgebra :=
  AdjoinRoot.map (Int.castRingHom ℚ_[2]) magmaSextic magmaPadicSextic (by
    simp only [magmaPadicSextic]
    exact dvd_rfl)

@[simp]
theorem magmaOrderToPadic_integralA :
    magmaOrderToPadic integralA = padicA := by
  change
    AdjoinRoot.map (Int.castRingHom ℚ_[2]) magmaSextic magmaPadicSextic _
      (AdjoinRoot.root magmaSextic) = AdjoinRoot.root magmaPadicSextic
  exact AdjoinRoot.map_root _ _ _ _

/-- The fixed curve polynomial, now evaluated over `ℚ₂`. -/
def padicCurveRhs (x : ℚ_[2]) : ℚ_[2] :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

/-- A concrete affine point on the dyadic curve. -/
structure PadicAffinePoint where
  x : ℚ_[2]
  y : ℚ_[2]
  equation : y ^ 2 = padicCurveRhs x

/-- There is an actual dyadic point above `x = 2`. -/
theorem exists_padicAffinePoint_at_two :
    ∃ P : PadicAffinePoint, P.x = 2 := by
  obtain ⟨y, hy⟩ := exists_padic_sq_eq_oneHundredNinetyThree
  refine ⟨⟨2, y, ?_⟩, rfl⟩
  rw [hy]
  norm_num [padicCurveRhs]

/-- There is an actual dyadic point above `x = 1/2`. -/
theorem exists_padicAffinePoint_at_oneHalf :
    ∃ P : PadicAffinePoint, P.x = 1 / 2 := by
  obtain ⟨y, hy⟩ :=
    exists_padic_sq_eq_threeHundredThirteen_div_sixtyFour
  refine ⟨⟨1 / 2, y, ?_⟩, rfl⟩
  rw [hy]
  norm_num [padicCurveRhs]

/-- The standard point representative `x - theta`, with `theta = a²`. -/
def pointKummerRepresentative (x : ℚ_[2]) : MagmaPadicAlgebra :=
  algebraMap ℚ_[2] MagmaPadicAlgebra x - padicA ^ 2

/-- At `x = 2`, the actual Kummer representative is the image of `qC`. -/
theorem pointKummerRepresentative_two :
    pointKummerRepresentative 2 = magmaOrderToPadic localQC := by
  simp only [pointKummerRepresentative, localQC, map_sub, map_pow,
    map_ofNat, magmaOrderToPadic_integralA]

/-- At `x = 1/2`, clearing the rational scalar `2` gives the image of
`qB`. -/
theorem two_mul_pointKummerRepresentative_oneHalf :
    2 * pointKummerRepresentative (1 / 2) =
      magmaOrderToPadic localQB := by
  simp only [pointKummerRepresentative, localQB, map_sub, map_mul, map_pow,
    map_ofNat, map_one, magmaOrderToPadic_integralA]
  have hhalf : (2 : MagmaPadicAlgebra) *
      algebraMap ℚ_[2] MagmaPadicAlgebra (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ_[2] MagmaPadicAlgebra) 2,
      ← map_mul]
    norm_num
  linear_combination hhalf

/-- The two Hensel points and their exact Kummer representatives, packaged
as the concrete local-image input. -/
theorem two_local_points_with_kummer_representatives :
    (∃ P : PadicAffinePoint,
      P.x = 1 / 2 ∧
        2 * pointKummerRepresentative P.x =
          magmaOrderToPadic localQB) ∧
      (∃ P : PadicAffinePoint,
        P.x = 2 ∧ pointKummerRepresentative P.x =
          magmaOrderToPadic localQC) := by
  constructor
  · obtain ⟨P, hP⟩ := exists_padicAffinePoint_at_oneHalf
    refine ⟨P, hP, ?_⟩
    rw [hP, two_mul_pointKummerRepresentative_oneHalf]
  · obtain ⟨P, hP⟩ := exists_padicAffinePoint_at_two
    refine ⟨P, hP, ?_⟩
    rw [hP, pointKummerRepresentative_two]

end

end MazurTorsion.XOneThirteenTwoDescentLocalKummerPoints
