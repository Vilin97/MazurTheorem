/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirteenModel
import Mathlib.Data.Fintype.Sets
import Mathlib.FieldTheory.Separable

/-!
# Finite-field certificates for the `X₁(13)` sextic

This file records elementary certificates for the reduction modulo `3` of

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

The reduced sextic is separable: explicit Bézout coefficients for it and its
derivative are checked in the kernel.  Its affine solutions over `ZMod 3` are
exactly

`(0, 1), (0, -1), (-1, 1), (-1, -1)`.

For the usual weighted-projective compactification of a monic even-degree
hyperelliptic equation, the normalized infinity chart has equation `η² = 1`.
We define and enumerate those normalized directions, obtaining two of them.
The resulting sum type is only an explicit finite-field point *certificate*;
this file does not assert an equivalence with a projective-curve API.

In particular, none of these calculations proves a classification over
`ℚ`, a theorem about the Jacobian, or injectivity of reduction on rational
points.
-/

namespace MazurTorsion.XOneThirteenFiniteField

open Polynomial

abbrev F3 := ZMod 3

/-- The order-thirteen hyperelliptic sextic reduced modulo `3`. -/
noncomputable def sextic : Polynomial F3 :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- A computable presentation of the sextic's value function. -/
def sexticValue (x : F3) : F3 :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

/-- Evaluation of the reduced sextic agrees with the displayed formula. -/
lemma eval_sextic (x : F3) :
    Polynomial.eval x sextic = sexticValue x := by
  simp [sextic, sexticValue]

private lemma three_eq_zero : (3 : F3) = 0 := by decide

private lemma four_eq_one : (4 : F3) = 1 := by decide

private lemma five_eq_two : (5 : F3) = 2 := by decide

private lemma six_eq_zero : (6 : F3) = 0 := by decide

private lemma polynomial_four_eq_one : (4 : Polynomial F3) = 1 := by
  change C (4 : F3) = C 1
  rw [four_eq_one]

private lemma polynomial_three_eq_zero : (3 : Polynomial F3) = 0 := by
  rw [← C_ofNat (R := F3) 3, three_eq_zero, C_0]

private lemma polynomial_six_eq_zero : (6 : Polynomial F3) = 0 := by
  rw [← C_ofNat (R := F3) 6, six_eq_zero, C_0]

private lemma C_two_mul_two :
    C (2 : F3) * (2 : Polynomial F3) = 1 := by
  rw [← C_ofNat (R := F3) 2, ← C_mul]
  have h : (2 : F3) * 2 = 1 := by decide
  rw [h, C_1]

/-- The formal derivative of the reduced sextic. -/
lemma derivative_sextic :
    sextic.derivative = X ^ 4 + X ^ 3 + 1 := by
  simp [sextic, derivative_add, derivative_mul, derivative_pow]
  simp [three_eq_zero, four_eq_one, five_eq_two, six_eq_zero,
    polynomial_four_eq_one, polynomial_six_eq_zero]
  ring_nf
  calc
    C 2 * X ^ 4 * 2 =
        (C 2 * (2 : Polynomial F3)) * X ^ 4 := by ring
    _ = X ^ 4 := by rw [C_two_mul_two, one_mul]

/-- Left Bézout coefficient for the sextic and its derivative. -/
noncomputable def bezoutLeft : Polynomial F3 :=
  X ^ 3 + 1

/-- Right Bézout coefficient for the sextic and its derivative. -/
noncomputable def bezoutRight : Polynomial F3 :=
  -(X ^ 5 + X ^ 4 + X)

/-- Explicit gcd certificate for the sextic and its derivative. -/
lemma sextic_derivative_bezout :
    bezoutLeft * sextic + bezoutRight * sextic.derivative = 1 := by
  rw [derivative_sextic]
  simp only [bezoutLeft, bezoutRight, sextic]
  ring_nf
  simp [polynomial_three_eq_zero, polynomial_six_eq_zero]

/-- The reduced sextic is coprime to its derivative. -/
theorem sextic_isCoprime_derivative :
    IsCoprime sextic sextic.derivative :=
  ⟨bezoutLeft, bezoutRight, sextic_derivative_bezout⟩

/-- The reduction modulo `3` is separable. -/
theorem sextic_separable : sextic.Separable :=
  sextic_isCoprime_derivative

/-- In particular, the reduced sextic is squarefree. -/
theorem sextic_squarefree : Squarefree sextic :=
  sextic_separable.squarefree

/-- The sextic and its derivative have no common root over `F3`. -/
theorem sextic_or_derivative_ne_zero (x : F3) :
    Polynomial.eval x sextic ≠ 0 ∨
      Polynomial.eval x sextic.derivative ≠ 0 := by
  by_contra h
  simp only [not_or, not_ne_iff] at h
  have heval :=
    congrArg (Polynomial.eval x) sextic_derivative_bezout
  simp [h.1, h.2] at heval

/-- An affine solution of the reduced hyperelliptic equation. -/
def AffineSolution :=
  {p : F3 × F3 // p.2 ^ 2 = sexticValue p.1}

instance : Fintype AffineSolution := by
  unfold AffineSolution
  infer_instance

/-- Complete enumeration of affine solutions over `F3`. -/
theorem affine_solution_iff :
    ∀ x y : F3,
      y ^ 2 = sexticValue x ↔
        (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = -1 ∧ (y = 1 ∨ y = -1)) := by
  decide

/-- Polynomial-evaluation form of the complete affine enumeration. -/
theorem affine_solution_polynomial_iff (x y : F3) :
    y ^ 2 = Polynomial.eval x sextic ↔
      (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      (x = -1 ∧ (y = 1 ∨ y = -1)) := by
  rw [eval_sextic]
  exact affine_solution_iff x y

/-- There are exactly four affine solutions over `F3`. -/
theorem card_affineSolution :
    Fintype.card AffineSolution = 4 := by
  decide

/-- The two affine abscissas occurring modulo `3`.  They are precisely the
reductions of the rational affine cusp abscissas from the sextic model. -/
def IsAffineCuspX (x : F3) : Prop :=
  x = 0 ∨ x = -1

instance (x : F3) : Decidable (IsAffineCuspX x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = -1))

/-- Computable form of `affine_solution_is_cusp`. -/
theorem affine_solution_is_cusp_value :
    ∀ x y : F3,
      y ^ 2 = sexticValue x →
        IsAffineCuspX x := by
  decide

/-- Every affine `F3`-solution has a cusp abscissa. -/
theorem affine_solution_is_cusp :
    ∀ x y : F3,
      y ^ 2 = Polynomial.eval x sextic →
        IsAffineCuspX x := by
  intro x y h
  rw [eval_sextic] at h
  exact affine_solution_is_cusp_value x y h

/-- The affine equation has two ordinates over each cusp abscissa. -/
theorem cusp_abscissa_solution_iff :
    ∀ x : F3,
      IsAffineCuspX x →
        ∀ y : F3,
          y ^ 2 = sexticValue x ↔
            y = 1 ∨ y = -1 := by
  decide

/-- The derivative has the following computable value function. -/
lemma eval_derivative_sextic (x : F3) :
    Polynomial.eval x sextic.derivative =
      x ^ 4 + x ^ 3 + 1 := by
  rw [derivative_sextic]
  simp

/-- Explicit affine Jacobian certificate: at a solution, the two partial
derivatives `-f'(x)` and `2y` cannot both vanish. -/
theorem affine_jacobian_nonsingular :
    ∀ x y : F3,
      y ^ 2 = sexticValue x →
        x ^ 4 + x ^ 3 + 1 ≠ 0 ∨ 2 * y ≠ 0 := by
  decide

/-- Polynomial-evaluation form of the affine Jacobian certificate. -/
theorem affine_jacobian_nonsingular_polynomial
    (x y : F3)
    (hxy : y ^ 2 = Polynomial.eval x sextic) :
    Polynomial.eval x sextic.derivative ≠ 0 ∨ 2 * y ≠ 0 := by
  rw [eval_sextic] at hxy
  rw [eval_derivative_sextic]
  exact affine_jacobian_nonsingular x y hxy

/-- The reduced sextic is monic. -/
theorem sextic_monic : sextic.Monic := by
  simp only [sextic]
  monicity <;> norm_num

/-- A normalized direction in the infinity chart of the monic even-degree
model.  In weighted-projective coordinates these are the solutions with
`X = 1` and `Z = 0`. -/
def InfinityDirection :=
  {η : F3 // η ^ 2 = 1}

instance : Fintype InfinityDirection := by
  unfold InfinityDirection
  infer_instance

/-- The normalized equation `η² = 1` is exactly the leading-coefficient
equation for this monic sextic. -/
theorem infinity_equation_iff_leadingCoeff (η : F3) :
    η ^ 2 = 1 ↔ η ^ 2 = sextic.leadingCoeff := by
  rw [sextic_monic.leadingCoeff]

/-- Every normalized infinity direction satisfies the actual
leading-coefficient equation of the sextic. -/
theorem infinity_direction_satisfies_leadingCoeff
    (η : InfinityDirection) :
    η.1 ^ 2 = sextic.leadingCoeff :=
  (infinity_equation_iff_leadingCoeff η.1).mp η.property

/-- The normalized infinity directions are exactly `η = ±1`. -/
theorem infinity_direction_iff :
    ∀ η : F3,
      η ^ 2 = 1 ↔ η = 1 ∨ η = -1 := by
  decide

/-- There are exactly two normalized points in the infinity chart. -/
theorem card_infinityDirection :
    Fintype.card InfinityDirection = 2 := by
  decide

/-- The `Y`-partial derivative is nonzero at either infinity direction, so
the two normalized infinity-chart points are distinct smooth directions. -/
theorem infinity_direction_jacobian_nonsingular
    (η : InfinityDirection) :
    2 * η.1 ≠ 0 := by
  have heta :
      η.1 = 1 ∨ η.1 = -1 :=
    (infinity_direction_iff η.1).mp η.property
  rcases heta with heta | heta <;> rw [heta] <;> decide

/-- The elementary six-element certificate obtained by adjoining the two
normalized infinity directions to the four affine solutions.

No equivalence with a projective-curve implementation is claimed here. -/
def PointCertificate :=
  AffineSolution ⊕ InfinityDirection

instance : Fintype PointCertificate := by
  unfold PointCertificate
  infer_instance

/-- The affine enumeration plus the normalized infinity chart has six
elements. -/
theorem card_pointCertificate :
    Fintype.card PointCertificate = 6 := by
  change Fintype.card (AffineSolution ⊕ InfinityDirection) = 6
  rw [Fintype.card_sum]
  rw [card_affineSolution, card_infinityDirection]

end MazurTorsion.XOneThirteenFiniteField
