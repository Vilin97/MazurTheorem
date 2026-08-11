/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentMagmaBridge
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentSquareRootParity

/-!
# The genuine mod-four algebra behind the `X₁(13)` local certificate

The finite certificate in `XOneThirteenTwoDescentModFourCertificate` uses
six coefficient vectors and an explicit multiplication formula.  This leaf
identifies that formula with multiplication in the actual reduction

`(ZMod 4)[a] / (a⁶ - 2a⁵ + 3a⁴ - 4a³ + 4a² - 2a + 1)`

of the monogenic descent order.  Thus later local arguments can reduce an
honest integral square equality to the 64-case parity certificate.
-/

namespace MazurTorsion.XOneThirteenTwoDescentModFourBridge

open Polynomial
open XOneThirteenTwoDescentMagmaBridge
open XOneThirteenTwoDescentModFourCertificate

noncomputable section

private instance : NeZero (4 : ℕ) := ⟨by decide⟩

/-- The defining integral polynomial reduced coefficientwise modulo four. -/
def magmaSexticModFour : F4[X] :=
  magmaSextic.map (Int.castRingHom F4)

theorem magmaSexticModFour_eq_g : magmaSexticModFour = g := by
  simp [magmaSexticModFour, magmaSextic, g]

theorem magmaSexticModFour_monic : magmaSexticModFour.Monic :=
  magmaSextic_monic.map (Int.castRingHom F4)

/-- The genuine quotient algebra obtained by reducing the descent order
modulo four. -/
abbrev MagmaModFour := AdjoinRoot magmaSexticModFour

/-- Its distinguished residue-class primitive element. -/
def modFourA : MagmaModFour := AdjoinRoot.root magmaSexticModFour

/-- Genuine coefficient reduction from the integral order. -/
def magmaOrderToModFour : MagmaOrder →+* MagmaModFour :=
  AdjoinRoot.map (Int.castRingHom F4) magmaSextic magmaSexticModFour (by
    simp only [magmaSexticModFour]
    exact dvd_rfl)

@[simp]
theorem magmaOrderToModFour_integralA :
    magmaOrderToModFour integralA = modFourA := by
  exact AdjoinRoot.map_root _ _ _ _

/-- Interpret a six-term coefficient vector in the genuine quotient. -/
def coordinateValue (v : V4) : MagmaModFour :=
  algebraMap F4 MagmaModFour (v 0) +
    algebraMap F4 MagmaModFour (v 1) * modFourA +
    algebraMap F4 MagmaModFour (v 2) * modFourA ^ 2 +
    algebraMap F4 MagmaModFour (v 3) * modFourA ^ 3 +
    algebraMap F4 MagmaModFour (v 4) * modFourA ^ 4 +
    algebraMap F4 MagmaModFour (v 5) * modFourA ^ 5

private theorem modFourA_spec :
    modFourA ^ 6 - 2 * modFourA ^ 5 + 3 * modFourA ^ 4 -
        4 * modFourA ^ 3 + 4 * modFourA ^ 2 - 2 * modFourA + 1 = 0 := by
  have h := congrArg magmaOrderToModFour integralA_spec
  simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
    map_zero, magmaOrderToModFour_integralA] using h

private theorem modFour_four_eq_zero : (4 : MagmaModFour) = 0 := by
  change algebraMap F4 MagmaModFour (4 : F4) = 0
  rw [show (4 : F4) = 0 by decide, map_zero]

private theorem modFourA_pow_six :
    modFourA ^ 6 = 3 + 2 * modFourA + modFourA ^ 4 + 2 * modFourA ^ 5 := by
  have h := modFourA_spec
  have hfour := modFour_four_eq_zero
  simp only [hfour, zero_mul, sub_zero, add_zero] at h
  linear_combination h - (1 + modFourA ^ 4) * hfour

private theorem modFourA_pow_seven :
    modFourA ^ 7 = 2 + 3 * modFourA + 2 * modFourA ^ 2 +
      2 * modFourA ^ 4 + modFourA ^ 5 := by
  calc
    modFourA ^ 7 = modFourA * modFourA ^ 6 := by ring
    _ = modFourA *
        (3 + 2 * modFourA + modFourA ^ 4 + 2 * modFourA ^ 5) := by
      rw [modFourA_pow_six]
    _ = _ := by
      ring_nf
      rw [modFourA_pow_six]
      linear_combination
        (1 + modFourA + modFourA ^ 5) * modFour_four_eq_zero

private theorem modFourA_pow_eight :
    modFourA ^ 8 = 3 + 3 * modFourA ^ 2 + 2 * modFourA ^ 3 +
      modFourA ^ 4 := by
  calc
    modFourA ^ 8 = modFourA * modFourA ^ 7 := by ring
    _ = modFourA *
        (2 + 3 * modFourA + 2 * modFourA ^ 2 +
          2 * modFourA ^ 4 + modFourA ^ 5) := by
      rw [modFourA_pow_seven]
    _ = _ := by
      ring_nf
      rw [modFourA_pow_six]
      linear_combination
        (modFourA + modFourA ^ 5) * modFour_four_eq_zero

private theorem modFourA_pow_nine :
    modFourA ^ 9 = 3 * modFourA + 3 * modFourA ^ 3 +
      2 * modFourA ^ 4 + modFourA ^ 5 := by
  calc
    modFourA ^ 9 = modFourA * modFourA ^ 8 := by ring
    _ = modFourA *
        (3 + 3 * modFourA ^ 2 + 2 * modFourA ^ 3 +
          modFourA ^ 4) := by
      rw [modFourA_pow_eight]
    _ = _ := by ring

private theorem modFourA_pow_ten :
    modFourA ^ 10 = 3 + 2 * modFourA + 3 * modFourA ^ 2 := by
  calc
    modFourA ^ 10 = modFourA * modFourA ^ 9 := by ring
    _ = modFourA *
        (3 * modFourA + 3 * modFourA ^ 3 +
          2 * modFourA ^ 4 + modFourA ^ 5) := by
      rw [modFourA_pow_nine]
    _ = _ := by
      ring_nf
      rw [modFourA_pow_six]
      linear_combination
        (modFourA ^ 4 + modFourA ^ 5) * modFour_four_eq_zero

/-- The displayed vector multiplication is exactly multiplication in the
genuine quotient algebra. -/
theorem coordinateValue_quotientMul (x y : V4) :
    coordinateValue (quotientMul x y) =
      coordinateValue x * coordinateValue y := by
  simp [coordinateValue, quotientMul, convolutionCoefficient,
    Fin.sum_univ_succ, map_add, map_mul, map_ofNat]
  ring_nf
  rw [modFourA_pow_ten, modFourA_pow_nine, modFourA_pow_eight,
    modFourA_pow_seven, modFourA_pow_six]
  ring

end

end MazurTorsion.XOneThirteenTwoDescentModFourBridge
