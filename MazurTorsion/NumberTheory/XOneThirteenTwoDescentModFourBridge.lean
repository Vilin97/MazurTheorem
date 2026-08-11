/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentMagmaBridge
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentLocalElements
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

open Module Polynomial
open XOneThirteenTwoDescentMagmaBridge
open XOneThirteenTwoDescentModFourCertificate
open XOneThirteenTwoDescentLocalElements

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
  algebraMap F4 MagmaModFour (v 0) * modFourA ^ 0 +
    algebraMap F4 MagmaModFour (v 1) * modFourA +
    algebraMap F4 MagmaModFour (v 2) * modFourA ^ 2 +
    algebraMap F4 MagmaModFour (v 3) * modFourA ^ 3 +
    algebraMap F4 MagmaModFour (v 4) * modFourA ^ 4 +
    algebraMap F4 MagmaModFour (v 5) * modFourA ^ 5

/-- The canonical power basis of the genuine mod-four quotient. -/
def modFourPowerBasis : PowerBasis F4 MagmaModFour :=
  AdjoinRoot.powerBasis' magmaSexticModFour_monic

@[simp]
theorem modFourPowerBasis_dim : modFourPowerBasis.dim = 6 := by
  change magmaSexticModFour.natDegree = 6
  rw [magmaSexticModFour_eq_g]
  simp only [g]
  compute_degree!

private def modFourIndexEquiv : Fin modFourPowerBasis.dim ≃ Fin 6 :=
  finCongr modFourPowerBasis_dim

/-- The canonical power basis, reindexed by the fixed six coordinate slots. -/
def modFourFixedBasis : Basis (Fin 6) F4 MagmaModFour :=
  modFourPowerBasis.basis.reindex modFourIndexEquiv

theorem modFourFixedBasis_apply (i : Fin 6) :
    modFourFixedBasis i = modFourA ^ (i : ℕ) := by
  rw [modFourFixedBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- Power-basis coordinates of an element of the genuine quotient. -/
def coordinateEquiv : MagmaModFour ≃ₗ[F4] V4 :=
  modFourFixedBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite F4 F4 (Fin 6)

theorem coordinateValue_eq_coordinateEquiv_symm (v : V4) :
    coordinateValue v = coordinateEquiv.symm v := by
  rw [show coordinateValue v =
      v 0 • modFourFixedBasis 0 +
        v 1 • modFourFixedBasis 1 +
        v 2 • modFourFixedBasis 2 +
        v 3 • modFourFixedBasis 3 +
        v 4 • modFourFixedBasis 4 +
        v 5 • modFourFixedBasis 5 by
    simp [coordinateValue, Algebra.smul_def, modFourFixedBasis_apply]]
  apply modFourFixedBasis.repr.injective
  ext i
  fin_cases i <;>
    simp [coordinateEquiv, Finsupp.linearEquivFunOnFinite]

/-- Every element of the genuine quotient has a unique displayed
six-coordinate vector. -/
theorem exists_unique_coordinateValue (z : MagmaModFour) :
    ∃! v : V4, coordinateValue v = z := by
  refine ⟨coordinateEquiv z, ?_, ?_⟩
  · simpa only [coordinateValue_eq_coordinateEquiv_symm] using
      coordinateEquiv.symm_apply_apply z
  · intro v hv
    rw [coordinateValue_eq_coordinateEquiv_symm] at hv
    have h := congrArg coordinateEquiv hv
    simpa using h

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

/-! ## The actual four local factors -/

theorem localLambda_modFour_coordinates :
    magmaOrderToModFour localLambda = coordinateValue lambda := by
  simp [localLambda, coordinateValue, lambda,
    magmaOrderToModFour_integralA, map_sub, map_add, map_mul, map_pow,
    map_ofNat, map_one]
  ring

@[simp]
theorem coordinateValue_one : coordinateValue one = 1 := by
  simp [coordinateValue, one]

theorem rationalFive_modFour_coordinates :
    magmaOrderToModFour (5 : MagmaOrder) = coordinateValue five := by
  rw [map_ofNat]
  simpa [coordinateValue, five] using
    (map_ofNat (AdjoinRoot.of magmaSexticModFour) 5).symm

theorem localQB_modFour_coordinates :
    magmaOrderToModFour localQB = coordinateValue qB := by
  simp [localQB, coordinateValue, qB,
    magmaOrderToModFour_integralA, map_sub, map_mul, map_pow,
    map_ofNat, map_one]
  ring

theorem localQC_modFour_coordinates :
    magmaOrderToModFour localQC = coordinateValue qC := by
  simp [localQC, coordinateValue, qC,
    magmaOrderToModFour_integralA, map_sub, map_pow, map_ofNat, map_one]
  ring

/-- Exponentiation by a binary exponent in the actual integral order. -/
def orderBitPow (x : MagmaOrder) (e : F2) : MagmaOrder :=
  if e = 0 then 1 else x

/-- The actual integral product whose six-coordinate reduction is the
sixteen-case finite certificate. -/
def actualCertificateProduct (s : Exponents) : MagmaOrder :=
  ((orderBitPow localLambda (exponentE s) *
      orderBitPow 5 (exponentB s)) *
    orderBitPow localQB (exponentC s)) *
  orderBitPow localQC (exponentD s)

private theorem map_orderBitPow (x : MagmaOrder) (e : F2) :
    magmaOrderToModFour (orderBitPow x e) =
      if e = 0 then 1 else magmaOrderToModFour x := by
  by_cases he : e = 0 <;> simp [orderBitPow, he]

/-- Exact transport of every actual integral product to the retained
mod-four vector. -/
theorem actualCertificateProduct_modFour (s : Exponents) :
    magmaOrderToModFour (actualCertificateProduct s) =
      coordinateValue (certificateProduct s) := by
  simp only [actualCertificateProduct, map_mul, map_orderBitPow,
    certificateProduct, bitPow]
  rw [localLambda_modFour_coordinates,
    rationalFive_modFour_coordinates,
    localQB_modFour_coordinates,
    localQC_modFour_coordinates,
    coordinateValue_quotientMul,
    coordinateValue_quotientMul,
    coordinateValue_quotientMul]
  by_cases he : exponentE s = 0 <;>
    by_cases hb : exponentB s = 0 <;>
    by_cases hc : exponentC s = 0 <;>
    by_cases hd : exponentD s = 0 <;>
    simp [he, hb, hc, hd]

/-- An actual square in the integral descent order among the sixteen tested
products has no `qB` or `qC` contribution.  This is the first direct consumer
of the finite mod-four certificate in the genuine quotient algebra. -/
theorem qB_qC_exponents_eq_zero_of_actualCertificateProduct_isSquare
    (s : Exponents)
    (hsquare : ∃ w : MagmaOrder, w ^ 2 = actualCertificateProduct s) :
    exponentC s = 0 ∧ exponentD s = 0 := by
  obtain ⟨w, hw⟩ := hsquare
  obtain ⟨v, hv, _⟩ :=
    exists_unique_coordinateValue (magmaOrderToModFour w)
  have hmapped := congrArg magmaOrderToModFour hw
  rw [map_pow, actualCertificateProduct_modFour] at hmapped
  have hvSquare :
      coordinateValue (quotientMul v v) =
        coordinateValue (certificateProduct s) := by
    rw [coordinateValue_quotientMul, hv]
    simpa only [pow_two] using hmapped
  have hvector : quotientMul v v = certificateProduct s := by
    rw [coordinateValue_eq_coordinateEquiv_symm,
      coordinateValue_eq_coordinateEquiv_symm] at hvSquare
    exact coordinateEquiv.symm.injective hvSquare
  apply qB_qC_exponents_eq_zero_of_certificateProduct_isSquare s
  exact ⟨v, hvector⟩

end

end MazurTorsion.XOneThirteenTwoDescentModFourBridge
