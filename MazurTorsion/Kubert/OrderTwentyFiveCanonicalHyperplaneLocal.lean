/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalHyperplaneScheme
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Local Artin factors of the order-25 canonical hyperplane sections

The four nonreduced affine intersection schemes split into fat points at the
displayed rational cusps.  Chinese remaindering gives the exact algebra
decompositions

* `K[Y]/(Y²(Y+1)) ≃ K[Y]/(Y²) × K[Y]/(Y+1)`;
* `K[Y]/(Y³)` at cusp 4 for `w = 0`;
* `K[Y]/(Y³(Y-1)) ≃ K[Y]/(Y³) × K[Y]/(Y-1)`;
* `K[Y]/(Y²(Y-1)) ≃ K[Y]/(Y²) × K[Y]/(Y-1)`.

The factors are named by their canonical cusp and coordinate section.  Their
dimensions over every field are respectively the local lengths

`ord(w) = (0,1,0,2,3)` and `ord(z) = (3,0,1,0,2)`.

This is stronger than root-multiplicity bookkeeping: the local thickened
points are actual affine schemes and the product decompositions are algebra
equivalences.  The named downstream consumer
`orderTwentyFiveCanonical_hyperplaneLocalFactorLengths` packages all six
local lengths.  Identifying these factors with quotients of the local rings
of a glued smooth projective carrier remains the next boundary.
-/

noncomputable section

open Polynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.Kubert

universe u

private def adjoinRootMulRingEquiv
    {K : Type*} [CommRing K] (p q : Polynomial K)
    (h : IsCoprime p q) :
    AdjoinRoot (p * q) ≃+* AdjoinRoot p × AdjoinRoot q := by
  let I : Ideal (Polynomial K) := Ideal.span {p}
  let J : Ideal (Polynomial K) := Ideal.span {q}
  have hIJ : IsCoprime I J :=
    (Ideal.isCoprime_span_singleton_iff p q).2 h
  let e₁ : AdjoinRoot (p * q) ≃+* (Polynomial K ⧸ I * J) :=
    Ideal.quotEquivOfEq
      (Ideal.span_singleton_mul_span_singleton p q).symm
  let e₂ : (Polynomial K ⧸ I * J) ≃+*
      (AdjoinRoot p × AdjoinRoot q) :=
    Ideal.quotientMulEquivQuotientProd I J hIJ
  exact e₁.trans e₂

/-! ## Cusp-labelled local factors -/

/-- The length-two factor of `w = 0` at canonical cusp 3. -/
abbrev OrderTwentyFiveCanonicalCuspThreeWFatRing
    (K : Type u) [CommRing K] :=
  AdjoinRoot (X ^ 2 : Polynomial K)

/-- The reduced length-one factor of `w = 0` at canonical cusp 1. -/
abbrev OrderTwentyFiveCanonicalCuspOneWFatRing
    (K : Type u) [CommRing K] :=
  AdjoinRoot (X + C 1 : Polynomial K)

/-- The length-three factor of `w = 0` at canonical cusp 4. -/
abbrev OrderTwentyFiveCanonicalCuspFourWFatRing
    (K : Type u) [CommRing K] :=
  AdjoinRoot (X ^ 3 : Polynomial K)

/-- The length-three factor of `z = 0` at canonical cusp 0. -/
abbrev OrderTwentyFiveCanonicalCuspZeroZFatRing
    (K : Type u) [CommRing K] :=
  AdjoinRoot (X ^ 3 : Polynomial K)

/-- The reduced length-one overlap factor of `z = 0` at canonical cusp 2. -/
abbrev OrderTwentyFiveCanonicalCuspTwoZFatRing
    (K : Type u) [CommRing K] :=
  AdjoinRoot (X - C 1 : Polynomial K)

/-- The length-two factor of `z = 0` at canonical cusp 4. -/
abbrev OrderTwentyFiveCanonicalCuspFourZFatRing
    (K : Type u) [CommRing K] :=
  AdjoinRoot (X ^ 2 : Polynomial K)

/-- The length-two `w`-section factor at cusp 3 as an affine scheme. -/
abbrev orderTwentyFiveCanonicalCuspThreeWFatScheme
    (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalCuspThreeWFatRing K))

/-- The reduced `w`-section factor at cusp 1 as an affine scheme. -/
abbrev orderTwentyFiveCanonicalCuspOneWFatScheme
    (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalCuspOneWFatRing K))

/-- The length-three `w`-section factor at cusp 4 as an affine scheme. -/
abbrev orderTwentyFiveCanonicalCuspFourWFatScheme
    (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalCuspFourWFatRing K))

/-- The length-three `z`-section factor at cusp 0 as an affine scheme. -/
abbrev orderTwentyFiveCanonicalCuspZeroZFatScheme
    (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalCuspZeroZFatRing K))

/-- The reduced overlap factor of `z = 0` at cusp 2 as an affine scheme. -/
abbrev orderTwentyFiveCanonicalCuspTwoZFatScheme
    (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalCuspTwoZFatRing K))

/-- The length-two `z`-section factor at cusp 4 as an affine scheme. -/
abbrev orderTwentyFiveCanonicalCuspFourZFatScheme
    (K : Type u) [CommRing K] : Scheme :=
  Spec (.of (OrderTwentyFiveCanonicalCuspFourZFatRing K))

/-! ## Chinese-remainder decompositions -/

/-- The `z = 1`, `w = 0` chart splits into its cusp-3 and cusp-1
thickenings. -/
def orderTwentyFiveCanonicalWZIntersectionRingEquiv
    {K : Type*} [Field K] :
    OrderTwentyFiveCanonicalWZIntersectionRing K ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspThreeWFatRing K ×
        OrderTwentyFiveCanonicalCuspOneWFatRing K := by
  have h := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (R := K) (a := 0) (b := -1) (by norm_num)
  let e : OrderTwentyFiveCanonicalWZIntersectionRing K ≃+*
      OrderTwentyFiveCanonicalCuspThreeWFatRing K ×
        OrderTwentyFiveCanonicalCuspOneWFatRing K := by
    change AdjoinRoot ((X ^ 2 : Polynomial K) * (X + C 1)) ≃+*
      AdjoinRoot (X ^ 2 : Polynomial K) × AdjoinRoot (X + C 1)
    exact adjoinRootMulRingEquiv (X ^ 2 : Polynomial K) (X + C 1) (by
      simpa using h.pow_left (m := 2))
  exact AlgEquiv.ofRingEquiv (f := e) (by intro r; rfl)

/-- The `x = 1`, `w = 0` chart is exactly the cusp-4 length-three
thickening. -/
def orderTwentyFiveCanonicalWXIntersectionRingEquiv
    {K : Type*} [Field K] :
    OrderTwentyFiveCanonicalWXIntersectionRing K ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspFourWFatRing K := by
  change AdjoinRoot (X ^ 3 : Polynomial K) ≃ₐ[K]
    AdjoinRoot (X ^ 3 : Polynomial K)
  exact AlgEquiv.refl

/-- The `w = 1`, `z = 0` chart splits into its cusp-0 and cusp-2
thickenings. -/
def orderTwentyFiveCanonicalZWIntersectionRingEquiv
    {K : Type*} [Field K] :
    OrderTwentyFiveCanonicalZWIntersectionRing K ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspZeroZFatRing K ×
        OrderTwentyFiveCanonicalCuspTwoZFatRing K := by
  have h := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (R := K) (a := 0) (b := 1) (by norm_num)
  let e : OrderTwentyFiveCanonicalZWIntersectionRing K ≃+*
      OrderTwentyFiveCanonicalCuspZeroZFatRing K ×
        OrderTwentyFiveCanonicalCuspTwoZFatRing K := by
    change AdjoinRoot ((X ^ 3 : Polynomial K) * (X - C 1)) ≃+*
      AdjoinRoot (X ^ 3 : Polynomial K) × AdjoinRoot (X - C 1)
    exact adjoinRootMulRingEquiv (X ^ 3 : Polynomial K) (X - C 1) (by
      simpa using h.pow_left (m := 3))
  exact AlgEquiv.ofRingEquiv (f := e) (by intro r; rfl)

/-- The `x = 1`, `z = 0` chart splits into its cusp-4 and cusp-2
thickenings.  The cusp-2 factor is literally the same algebra as in the
`w = 1` chart. -/
def orderTwentyFiveCanonicalZXIntersectionRingEquiv
    {K : Type*} [Field K] :
    OrderTwentyFiveCanonicalZXIntersectionRing K ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspFourZFatRing K ×
        OrderTwentyFiveCanonicalCuspTwoZFatRing K := by
  have h := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (R := K) (a := 0) (b := 1) (by norm_num)
  let e : OrderTwentyFiveCanonicalZXIntersectionRing K ≃+*
      OrderTwentyFiveCanonicalCuspFourZFatRing K ×
        OrderTwentyFiveCanonicalCuspTwoZFatRing K := by
    change AdjoinRoot ((X ^ 2 : Polynomial K) * (X - C 1)) ≃+*
      AdjoinRoot (X ^ 2 : Polynomial K) × AdjoinRoot (X - C 1)
    exact adjoinRootMulRingEquiv (X ^ 2 : Polynomial K) (X - C 1) (by
      simpa using h.pow_left (m := 2))
  exact AlgEquiv.ofRingEquiv (f := e) (by intro r; rfl)

/-! ## Cusp labels and local lengths -/

/-- The centers of the factors above are exactly the displayed canonical
cusp representatives in the normalized charts. -/
theorem orderTwentyFiveCanonical_hyperplaneLocalFactorCenters :
    (![0, 0, 1, 0] : Fin 4 → ℚ) =
        orderTwentyFiveCanonicalCuspVector 3 ∧
      (![0, -1, 1, 0] : Fin 4 → ℚ) =
        orderTwentyFiveCanonicalCuspVector 1 ∧
      (![1, 0, 0, 0] : Fin 4 → ℚ) =
        orderTwentyFiveCanonicalCuspVector 4 ∧
      (![0, 0, 0, 1] : Fin 4 → ℚ) =
        orderTwentyFiveCanonicalCuspVector 0 ∧
      (![1, 1, 0, 1] : Fin 4 → ℚ) =
        orderTwentyFiveCanonicalCuspVector 2 := by
  constructor
  · ext i
    fin_cases i <;>
      norm_num [orderTwentyFiveCanonicalCuspVector,
        orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
        orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four]
  constructor
  · ext i
    fin_cases i <;>
      norm_num [orderTwentyFiveCanonicalCuspVector,
        orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
        orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four]
  constructor
  · ext i
    fin_cases i <;>
      norm_num [orderTwentyFiveCanonicalCuspVector,
        orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
        orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four]
  constructor
  · ext i
    fin_cases i <;>
      norm_num [orderTwentyFiveCanonicalCuspVector,
        orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
        orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four]
  · ext i
    fin_cases i <;>
      norm_num [orderTwentyFiveCanonicalCuspVector,
        orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
        orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four]

private theorem adjoinRoot_X_pow_finrank
    {K : Type*} [Field K] (n : ℕ) :
    Module.finrank K (AdjoinRoot (X ^ n : Polynomial K)) = n := by
  have hmonic : (X ^ n : Polynomial K).Monic := Polynomial.monic_X.pow n
  rw [(AdjoinRoot.powerBasis hmonic.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim hmonic.ne_zero,
    Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]

private theorem adjoinRoot_X_sub_C_finrank
    {K : Type*} [Field K] (a : K) :
    Module.finrank K (AdjoinRoot (X - C a)) = 1 := by
  have hmonic := Polynomial.monic_X_sub_C a
  rw [(AdjoinRoot.powerBasis hmonic.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim hmonic.ne_zero,
    Polynomial.natDegree_X_sub_C]

private theorem adjoinRoot_X_add_C_finrank
    {K : Type*} [Field K] (a : K) :
    Module.finrank K (AdjoinRoot (X + C a)) = 1 := by
  have hmonic := Polynomial.monic_X_add_C a
  rw [(AdjoinRoot.powerBasis hmonic.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim hmonic.ne_zero,
    Polynomial.natDegree_X_add_C]

/-- Named downstream package for the six nonzero local intersection lengths.
Together with the factor centers, these are the scheme-theoretic versions of
`ord(w) = (0,1,0,2,3)` and `ord(z) = (3,0,1,0,2)`. -/
theorem orderTwentyFiveCanonical_hyperplaneLocalFactorLengths
    {K : Type*} [Field K] :
    Module.finrank K (OrderTwentyFiveCanonicalCuspOneWFatRing K) = 1 ∧
      Module.finrank K (OrderTwentyFiveCanonicalCuspThreeWFatRing K) = 2 ∧
      Module.finrank K (OrderTwentyFiveCanonicalCuspFourWFatRing K) = 3 ∧
      Module.finrank K (OrderTwentyFiveCanonicalCuspZeroZFatRing K) = 3 ∧
      Module.finrank K (OrderTwentyFiveCanonicalCuspTwoZFatRing K) = 1 ∧
      Module.finrank K (OrderTwentyFiveCanonicalCuspFourZFatRing K) = 2 := by
  exact ⟨adjoinRoot_X_add_C_finrank 1, adjoinRoot_X_pow_finrank 2,
    adjoinRoot_X_pow_finrank 3, adjoinRoot_X_pow_finrank 3,
    adjoinRoot_X_sub_C_finrank 1, adjoinRoot_X_pow_finrank 2⟩

end MazurTorsion.Kubert
