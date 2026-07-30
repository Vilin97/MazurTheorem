/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderEighteenModel
import Mathlib.Data.Fintype.Sets
import Mathlib.FieldTheory.Separable

/-!
# Finite-field and symmetry certificates for the `X₁(18)` sextic

The genus-two reduction for order eighteen produces

`Y² = X⁶ - 4X⁵ + 10X⁴ - 10X³ + 5X² - 2X + 1`.

This file records two independent elementary boundaries.

First, modulo `5`, the sextic is separable and has exactly four affine
solutions, all above `X = 0` or `X = 1`.  Its monic even-degree infinity
chart has two smooth normalized directions.  Their sum is packaged only
as a six-element finite-field point certificate; no projective-curve API
equivalence or reduction theorem is asserted.

Second, over `ℚ`, the Möbius transformation

`X ↦ 1/(1-X)`

has order three on the abscissa.  Its lift

`(X,Y) ↦ (1/(1-X), -Y/(1-X)³)`

preserves the sextic and also has order three away from `X = 0,1`.  Two
checked invariant functions satisfy a conic equation.  These identities
expose the elementary order-three symmetry used in classical treatments;
they do not construct an endomorphism of the Jacobian or prove its rank.
-/

namespace MazurTorsion.XOneEighteenFiniteField

open Polynomial

/-! ## Rational order-three symmetry -/

/-- The order-three Möbius transformation on the abscissa. -/
def orderThreeX (x : ℚ) : ℚ :=
  1 / (1 - x)

/-- The order-three lift to the ordinate.  The minus sign selects the
order-three lift rather than the lift whose cube is the hyperelliptic
involution. -/
def orderThreeY (x y : ℚ) : ℚ :=
  -y / (1 - x) ^ 3

/-- The sextic is covariant under the Möbius transformation. -/
theorem orderThree_sextic_covariance
    (x : ℚ) (hx1 : x ≠ 1) :
    (1 - x) ^ 6 *
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial
          (orderThreeX x) =
      MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  simp only [orderThreeX,
    MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial]
  field_simp [hden]
  ring

/-- The second Möbius iterate in a denominator-safe form. -/
theorem orderThreeX_sq
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    orderThreeX (orderThreeX x) = (x - 1) / x := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  simp only [orderThreeX]
  field_simp [hden, hx0]
  ring

/-- The Möbius transformation has exact third iterate equal to the
identity on its noncuspidal affine domain. -/
theorem orderThreeX_cube
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    orderThreeX (orderThreeX (orderThreeX x)) = x := by
  rw [orderThreeX_sq x hx0 hx1]
  simp only [orderThreeX]
  field_simp [hx0]
  ring

/-- The lifted transformation preserves the hyperelliptic equation. -/
theorem orderThree_preserves_curve
    (x y : ℚ) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    orderThreeY x y ^ 2 =
      MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial
        (orderThreeX x) := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  simp only [orderThreeY, orderThreeX,
    MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial] at hcurve ⊢
  field_simp [hden]
  field_simp [hden] at hcurve
  linear_combination hcurve

/-- The selected lift has third iterate equal to the identity on the
noncuspidal affine domain. -/
theorem orderThreeY_cube
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    orderThreeY (orderThreeX (orderThreeX x))
        (orderThreeY (orderThreeX x) (orderThreeY x y)) = y := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  simp only [orderThreeY, orderThreeX]
  field_simp [hden, hx0]
  ring

/-- A rational invariant of the order-three action on the abscissa. -/
def invariantX (x : ℚ) : ℚ :=
  (x ^ 3 - 3 * x + 1) / (x * (x - 1))

/-- A rational invariant involving the ordinate. -/
def invariantY (x y : ℚ) : ℚ :=
  y / (x * (x - 1))

/-- The abscissa invariant is the trace of the three-element Möbius orbit. -/
theorem invariantX_eq_orbit_sum
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    invariantX x =
      x + orderThreeX x + orderThreeX (orderThreeX x) := by
  rw [orderThreeX_sq x hx0 hx1]
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [invariantX, orderThreeX]
  field_simp [hden, hx0, hxsub]
  ring

/-- The product of the three abscissas in a Möbius orbit is `-1`. -/
theorem orderThree_orbit_product
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    x * orderThreeX x * orderThreeX (orderThreeX x) = -1 := by
  rw [orderThreeX_sq x hx0 hx1]
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  simp only [orderThreeX]
  field_simp [hden, hx0]
  ring

/-- The first displayed function is invariant under the Möbius action. -/
theorem invariantX_orderThree
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    invariantX (orderThreeX x) = invariantX x := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [invariantX, orderThreeX]
  field_simp [hden, hx0, hxsub]
  ring

/-- The ordinate invariant is fixed by the chosen order-three lift. -/
theorem invariantY_orderThree
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    invariantY (orderThreeX x) (orderThreeY x y) =
      invariantY x y := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [invariantY, orderThreeX, orderThreeY]
  field_simp [hden, hx0, hxsub]
  ring

/-- On the sextic, the two invariant functions lie on a rational conic.
This is only a function-field identity, not a theorem about the Jacobian. -/
theorem invariant_conic_equation
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    invariantY x y ^ 2 =
      invariantX x ^ 2 - 4 * invariantX x + 12 := by
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [invariantX, invariantY,
    MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial] at hcurve ⊢
  field_simp [hx0, hxsub]
  linear_combination hcurve

/-! ## Reduction modulo five -/

abbrev F5 := ZMod 5

/-- The order-eighteen sextic reduced modulo `5`, in reduced-coefficient
form. -/
noncomputable def sextic : Polynomial F5 :=
  X ^ 6 + X ^ 5 + 3 * X + 1

/-- A computable presentation of the reduced sextic's value function. -/
def sexticValue (x : F5) : F5 :=
  x ^ 6 + x ^ 5 + 3 * x + 1

/-- Evaluation of the polynomial agrees with its computable value
function. -/
lemma eval_sextic (x : F5) :
    Polynomial.eval x sextic = sexticValue x := by
  simp [sextic, sexticValue]

/-- The reduced value function agrees with the original integral sextic
formula modulo `5`. -/
lemma sexticValue_eq_model_formula (x : F5) :
    sexticValue x =
      x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 +
        5 * x ^ 2 - 2 * x + 1 := by
  fin_cases x <;> decide

private lemma five_eq_zero : (5 : F5) = 0 := by decide

private lemma six_eq_one : (6 : F5) = 1 := by decide

private lemma polynomial_five_eq_zero : (5 : Polynomial F5) = 0 := by
  rw [← C_ofNat (R := F5) 5, five_eq_zero, C_0]

private lemma polynomial_eleven_eq_one :
    (11 : Polynomial F5) = 1 := by
  rw [← C_ofNat (R := F5) 11]
  have h : (11 : F5) = 1 := by decide
  rw [h, C_1]

private lemma polynomial_fifteen_eq_zero :
    (15 : Polynomial F5) = 0 := by
  rw [← C_ofNat (R := F5) 15]
  have h : (15 : F5) = 0 := by decide
  rw [h, C_0]

/-- The formal derivative of the reduced sextic. -/
lemma derivative_sextic :
    sextic.derivative = X ^ 5 + 3 := by
  simp [sextic, derivative_add, derivative_mul, derivative_pow]
  simp [five_eq_zero, six_eq_one]

/-- Left Bézout coefficient for the sextic and its derivative. -/
noncomputable def bezoutLeft : Polynomial F5 :=
  2

/-- Right Bézout coefficient for the sextic and its derivative. -/
noncomputable def bezoutRight : Polynomial F5 :=
  3 * X + 3

/-- Explicit gcd certificate for the sextic and its derivative. -/
lemma sextic_derivative_bezout :
    bezoutLeft * sextic + bezoutRight * sextic.derivative = 1 := by
  rw [derivative_sextic]
  simp only [bezoutLeft, bezoutRight, sextic]
  ring_nf
  simp [polynomial_five_eq_zero, polynomial_eleven_eq_one,
    polynomial_fifteen_eq_zero]

/-- The reduced sextic is coprime to its derivative. -/
theorem sextic_isCoprime_derivative :
    IsCoprime sextic sextic.derivative :=
  ⟨bezoutLeft, bezoutRight, sextic_derivative_bezout⟩

/-- The reduction modulo `5` is separable. -/
theorem sextic_separable : sextic.Separable :=
  sextic_isCoprime_derivative

/-- In particular, the reduced sextic is squarefree. -/
theorem sextic_squarefree : Squarefree sextic :=
  sextic_separable.squarefree

/-- The sextic and its derivative have no common root over `F5`. -/
theorem sextic_or_derivative_ne_zero (x : F5) :
    Polynomial.eval x sextic ≠ 0 ∨
      Polynomial.eval x sextic.derivative ≠ 0 := by
  by_contra h
  simp only [not_or, not_ne_iff] at h
  have heval : (0 : F5) = 1 := by
    calc
      0 = Polynomial.eval x
          (bezoutLeft * sextic + bezoutRight * sextic.derivative) := by
            simp [h.1, h.2]
      _ = Polynomial.eval x 1 :=
        congrArg (Polynomial.eval x) sextic_derivative_bezout
      _ = 1 := by simp
  have hne : (0 : F5) ≠ 1 := by decide
  exact hne heval

/-- An affine solution of the reduced hyperelliptic equation. -/
def AffineSolution :=
  {p : F5 × F5 // p.2 ^ 2 = sexticValue p.1}

instance : Fintype AffineSolution := by
  unfold AffineSolution
  infer_instance

/-- Complete enumeration of affine solutions over `F5`. -/
theorem affine_solution_iff :
    ∀ x y : F5,
      y ^ 2 = sexticValue x ↔
        (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = 1 ∧ (y = 1 ∨ y = -1)) := by
  decide

/-- Polynomial-evaluation form of the complete affine enumeration. -/
theorem affine_solution_polynomial_iff (x y : F5) :
    y ^ 2 = Polynomial.eval x sextic ↔
      (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      (x = 1 ∧ (y = 1 ∨ y = -1)) := by
  rw [eval_sextic]
  exact affine_solution_iff x y

/-- There are exactly four affine solutions over `F5`. -/
theorem card_affineSolution :
    Fintype.card AffineSolution = 4 := by
  decide

/-- The two affine abscissas occurring modulo `5`. -/
def IsAffineCuspX (x : F5) : Prop :=
  x = 0 ∨ x = 1

instance (x : F5) : Decidable (IsAffineCuspX x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = 1))

/-- Every affine `F5`-solution has a cusp abscissa. -/
theorem affine_solution_is_cusp_value :
    ∀ x y : F5,
      y ^ 2 = sexticValue x →
        IsAffineCuspX x := by
  decide

/-- Polynomial-evaluation form of the cusp-abscissa enumeration. -/
theorem affine_solution_is_cusp
    (x y : F5)
    (hxy : y ^ 2 = Polynomial.eval x sextic) :
    IsAffineCuspX x := by
  rw [eval_sextic] at hxy
  exact affine_solution_is_cusp_value x y hxy

/-- The affine equation has two ordinates over each cusp abscissa. -/
theorem cusp_abscissa_solution_iff :
    ∀ x : F5,
      IsAffineCuspX x →
        ∀ y : F5,
          y ^ 2 = sexticValue x ↔
            y = 1 ∨ y = -1 := by
  decide

/-- The derivative has the following computable value function. -/
lemma eval_derivative_sextic (x : F5) :
    Polynomial.eval x sextic.derivative = x ^ 5 + 3 := by
  rw [derivative_sextic]
  simp

/-- Explicit affine Jacobian certificate. -/
theorem affine_jacobian_nonsingular :
    ∀ x y : F5,
      y ^ 2 = sexticValue x →
        x ^ 5 + 3 ≠ 0 ∨ 2 * y ≠ 0 := by
  decide

/-- Polynomial-evaluation form of the affine Jacobian certificate. -/
theorem affine_jacobian_nonsingular_polynomial
    (x y : F5)
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
model. -/
def InfinityDirection :=
  {η : F5 // η ^ 2 = 1}

instance : Fintype InfinityDirection := by
  unfold InfinityDirection
  infer_instance

/-- The normalized equation is exactly the leading-coefficient equation
for this monic sextic. -/
theorem infinity_equation_iff_leadingCoeff (η : F5) :
    η ^ 2 = 1 ↔ η ^ 2 = sextic.leadingCoeff := by
  rw [sextic_monic.leadingCoeff]

/-- Every normalized infinity direction satisfies the actual
leading-coefficient equation. -/
theorem infinity_direction_satisfies_leadingCoeff
    (η : InfinityDirection) :
    η.1 ^ 2 = sextic.leadingCoeff :=
  (infinity_equation_iff_leadingCoeff η.1).mp η.property

/-- The normalized infinity directions are exactly `η = ±1`. -/
theorem infinity_direction_iff :
    ∀ η : F5,
      η ^ 2 = 1 ↔ η = 1 ∨ η = -1 := by
  decide

/-- There are exactly two normalized points in the infinity chart. -/
theorem card_infinityDirection :
    Fintype.card InfinityDirection = 2 := by
  decide

/-- The `Y`-partial derivative is nonzero at either infinity direction. -/
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

end MazurTorsion.XOneEighteenFiniteField
