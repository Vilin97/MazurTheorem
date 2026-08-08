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

This file records elementary certificates for the reductions modulo `3` and
`5` of

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

Both reduced sextics are separable: explicit Bézout coefficients for them and
their derivatives are checked in the kernel.  The affine solutions over
`ZMod 3` are exactly

`(0, 1), (0, -1), (-1, 1), (-1, -1)`.

For the usual weighted-projective compactification of a monic even-degree
hyperelliptic equation, the normalized infinity chart has equation `η² = 1`.
We define and enumerate those normalized directions, obtaining two of them.
The resulting sum type is only an explicit finite-field point *certificate*;
this file does not assert an equivalence with a projective-curve API.  We also
enumerate the same equation in transparent quadratic-algebra presentations
of `𝔽₉` and `𝔽₂₅`.  The nonsquare and inverse certificates for those
presentations are checked by `decide`, as are the point counts.

In particular, none of these calculations proves a classification over
`ℚ`, a theorem about the Jacobian, or injectivity of reduction on rational
points.
-/

namespace MazurTorsion.XOneThirteenFiniteField

open Polynomial

/-- The three-element residue field used for the order-thirteen point count. -/
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

/-! ## The second good prime -/

/-- The five-element residue field used for the second point count. -/
abbrev F5 := ZMod 5

/-- The order-thirteen hyperelliptic sextic reduced modulo `5`. -/
noncomputable def sexticF5 : Polynomial F5 :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- A computable presentation of the sextic's value function modulo `5`. -/
def sexticValueF5 (x : F5) : F5 :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

private lemma five_eq_zero_F5 : (5 : F5) = 0 := by decide

private lemma six_eq_one_F5 : (6 : F5) = 1 := by decide

private lemma polynomial_five_eq_zero_F5 :
    (5 : Polynomial F5) = 0 := by
  rw [← C_ofNat (R := F5) 5, five_eq_zero_F5, C_0]

private lemma polynomial_six_eq_one_F5 :
    (6 : Polynomial F5) = 1 := by
  rw [← C_ofNat (R := F5) 6, six_eq_one_F5, C_1]

private lemma polynomial_ten_eq_zero_F5 :
    (10 : Polynomial F5) = 0 := by
  have hten : (10 : F5) = 0 := by decide
  rw [← C_ofNat (R := F5) 10, hten, C_0]

private lemma C_five_eq_zero_F5 : C (5 : F5) = 0 := by
  rw [five_eq_zero_F5, C_0]

private lemma C_six_eq_one_F5 : C (6 : F5) = 1 := by
  rw [six_eq_one_F5, C_1]

private lemma C_three_mul_two_F5 :
    C (3 : F5) * (2 : Polynomial F5) = 1 := by
  rw [← C_ofNat (R := F5) 2, ← C_mul]
  have h : (3 : F5) * 2 = 1 := by decide
  rw [h, C_1]

/-- Evaluation of the reduced sextic modulo `5` agrees with the displayed
formula. -/
lemma eval_sexticF5 (x : F5) :
    Polynomial.eval x sexticF5 = sexticValueF5 x := by
  simp [sexticF5, sexticValueF5]

/-- The formal derivative of the sextic modulo `5`. -/
lemma derivative_sexticF5 :
    sexticF5.derivative = X ^ 5 + 4 * X ^ 3 + X ^ 2 + 2 * X + 4 := by
  simp [sexticF5, derivative_add, derivative_mul, derivative_pow]
  ring_nf
  rw [C_six_eq_one_F5, C_five_eq_zero_F5,
    polynomial_six_eq_one_F5]
  ring_nf
  calc
    X * C 2 + X ^ 2 * C 3 * 2 + X ^ 3 * C 4 + X ^ 5 =
        X ^ 5 + C 2 * X + (C 3 * (2 : Polynomial F5)) * X ^ 2 +
          C 4 * X ^ 3 := by ring
    _ = X ^ 5 + C 2 * X + X ^ 2 + C 4 * X ^ 3 := by
      rw [C_three_mul_two_F5]
      ring
    _ = X * 2 + X ^ 2 + X ^ 3 * 4 + X ^ 5 := by
      rw [← C_ofNat (R := F5) 2, ← C_ofNat (R := F5) 4]
      ring

/-- Left Bézout coefficient for the sextic modulo `5` and its derivative. -/
noncomputable def bezoutLeftF5 : Polynomial F5 :=
  -X ^ 3 + X ^ 2 - 2 * X + 2

/-- Right Bézout coefficient for the sextic modulo `5` and its derivative. -/
noncomputable def bezoutRightF5 : Polynomial F5 :=
  X ^ 4 + X ^ 3 + 2 * X ^ 2 - 2 * X + 1

/-- Explicit gcd certificate for the sextic modulo `5` and its derivative. -/
lemma sexticF5_derivative_bezout :
    bezoutLeftF5 * sexticF5 + bezoutRightF5 * sexticF5.derivative = 1 := by
  rw [derivative_sexticF5]
  simp only [bezoutLeftF5, bezoutRightF5, sexticF5]
  ring_nf
  simp [polynomial_five_eq_zero_F5, polynomial_six_eq_one_F5,
    polynomial_ten_eq_zero_F5]

/-- The reduction modulo `5` is separable. -/
theorem sexticF5_separable : sexticF5.Separable :=
  ⟨bezoutLeftF5, bezoutRightF5, sexticF5_derivative_bezout⟩

/-- An affine solution of the reduced equation over `𝔽₅`. -/
def AffineSolutionF5 :=
  {p : F5 × F5 // p.2 ^ 2 = sexticValueF5 p.1}

instance : Fintype AffineSolutionF5 := by
  unfold AffineSolutionF5
  infer_instance

/-- There are four affine solutions over `𝔽₅`. -/
theorem card_affineSolutionF5 :
    Fintype.card AffineSolutionF5 = 4 := by
  decide

/-- The normalized infinity directions over `𝔽₅`. -/
def InfinityDirectionF5 :=
  {η : F5 // η ^ 2 = 1}

instance : Fintype InfinityDirectionF5 := by
  unfold InfinityDirectionF5
  infer_instance

/-- There are two normalized infinity directions over `𝔽₅`. -/
theorem card_infinityDirectionF5 :
    Fintype.card InfinityDirectionF5 = 2 := by
  decide

/-- The six-element point certificate over `𝔽₅`. -/
def PointCertificateF5 :=
  AffineSolutionF5 ⊕ InfinityDirectionF5

instance : Fintype PointCertificateF5 := by
  unfold PointCertificateF5
  infer_instance

/-- The affine enumeration and infinity chart have six elements over `𝔽₅`. -/
theorem card_pointCertificateF5 :
    Fintype.card PointCertificateF5 = 6 := by
  change Fintype.card (AffineSolutionF5 ⊕ InfinityDirectionF5) = 6
  rw [Fintype.card_sum, card_affineSolutionF5, card_infinityDirectionF5]

/-! ## Quadratic extension certificates -/

/-- A transparent pair presentation of a quadratic algebra over `ZMod n`.
Multiplication below imposes `ω² = d`. -/
abbrev QuadraticPair (n : ℕ) := ZMod n × ZMod n

/-- Zero in the pair presentation. -/
def quadraticPairZero {n : ℕ} : QuadraticPair n :=
  (0, 0)

/-- One in the pair presentation. -/
def quadraticPairOne {n : ℕ} : QuadraticPair n :=
  (1, 0)

/-- Addition in the pair presentation. -/
def quadraticPairAdd {n : ℕ}
    (u v : QuadraticPair n) : QuadraticPair n :=
  (u.1 + v.1, u.2 + v.2)

/-- Multiplication in the pair presentation with `ω² = d`. -/
def quadraticPairMul {n : ℕ} (d : ZMod n)
    (u v : QuadraticPair n) : QuadraticPair n :=
  (u.1 * v.1 + d * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- Natural-number scalar multiplication in the pair presentation. -/
def quadraticPairNatScale {n : ℕ} (a : ℕ)
    (u : QuadraticPair n) : QuadraticPair n :=
  ((a : ZMod n) * u.1, (a : ZMod n) * u.2)

/-- Powers computed with the transparent quadratic multiplication. -/
def quadraticPairPow {n : ℕ} (d : ZMod n)
    (u : QuadraticPair n) : ℕ → QuadraticPair n
  | 0 => quadraticPairOne
  | k + 1 => quadraticPairMul d (quadraticPairPow d u k) u

/-- The sextic value in the pair presentation. -/
def quadraticPairSexticValue {n : ℕ} (d : ZMod n)
    (x : QuadraticPair n) : QuadraticPair n :=
  quadraticPairAdd (quadraticPairPow d x 6)
    (quadraticPairAdd
      (quadraticPairNatScale 2 (quadraticPairPow d x 5))
      (quadraticPairAdd (quadraticPairPow d x 4)
        (quadraticPairAdd
          (quadraticPairNatScale 2 (quadraticPairPow d x 3))
          (quadraticPairAdd
            (quadraticPairNatScale 6 (quadraticPairPow d x 2))
            (quadraticPairAdd (quadraticPairNatScale 4 x)
              quadraticPairOne)))))

/-- A quadratic-pair affine solution. -/
def QuadraticAffineSolution (n : ℕ) (d : ZMod n) :=
  {p : QuadraticPair n × QuadraticPair n //
    quadraticPairMul d p.2 p.2 = quadraticPairSexticValue d p.1}

/-- A normalized quadratic-pair infinity direction. -/
def QuadraticInfinityDirection (n : ℕ) (d : ZMod n) :=
  {η : QuadraticPair n //
    quadraticPairMul d η η = quadraticPairOne}

/-- The pair presentation of `𝔽₉`, using `ω² = 2`. -/
abbrev F9Pair := QuadraticPair 3

/-- Two is not a square in `𝔽₃`. -/
theorem two_not_square_F3 :
    ∀ a : F3, a ^ 2 ≠ 2 := by
  decide

/-- Every nonzero element in the nine-element pair presentation has a
multiplicative inverse.  Together with `two_not_square_F3`, this is a finite
certificate that the displayed quadratic algebra is the field `𝔽₉`. -/
theorem F9Pair_nonzero_has_mul_inverse :
    ∀ u : F9Pair, u ≠ quadraticPairZero →
      ∃ v : F9Pair,
        quadraticPairMul (2 : F3) u v = quadraticPairOne := by
  decide

instance : Fintype (QuadraticAffineSolution 3 (2 : F3)) := by
  unfold QuadraticAffineSolution QuadraticPair
  infer_instance

instance : Fintype (QuadraticInfinityDirection 3 (2 : F3)) := by
  unfold QuadraticInfinityDirection QuadraticPair
  infer_instance

/-- There are six affine solutions over the checked `𝔽₉` presentation. -/
theorem card_affineSolutionF9 :
    Fintype.card (QuadraticAffineSolution 3 (2 : F3)) = 6 := by
  decide

/-- There are two normalized infinity directions over the checked `𝔽₉`
presentation. -/
theorem card_infinityDirectionF9 :
    Fintype.card (QuadraticInfinityDirection 3 (2 : F3)) = 2 := by
  decide

/-- The point certificate over `𝔽₉`. -/
def PointCertificateF9 :=
  QuadraticAffineSolution 3 (2 : F3) ⊕
    QuadraticInfinityDirection 3 (2 : F3)

instance : Fintype PointCertificateF9 := by
  unfold PointCertificateF9
  infer_instance

/-- The quadratic-extension point certificate has eight elements over
`𝔽₉`. -/
theorem card_pointCertificateF9 :
    Fintype.card PointCertificateF9 = 8 := by
  change Fintype.card
    (QuadraticAffineSolution 3 (2 : F3) ⊕
      QuadraticInfinityDirection 3 (2 : F3)) = 8
  rw [Fintype.card_sum, card_affineSolutionF9, card_infinityDirectionF9]

/-- The pair presentation of `𝔽₂₅`, using `ω² = 2`. -/
abbrev F25Pair := QuadraticPair 5

/-- Two is not a square in `𝔽₅`. -/
theorem two_not_square_F5 :
    ∀ a : F5, a ^ 2 ≠ 2 := by
  decide

/-- Every nonzero element in the twenty-five-element pair presentation has
a multiplicative inverse. -/
theorem F25Pair_nonzero_has_mul_inverse :
    ∀ u : F25Pair, u ≠ quadraticPairZero →
      ∃ v : F25Pair,
        quadraticPairMul (2 : F5) u v = quadraticPairOne := by
  decide

instance : Fintype (QuadraticAffineSolution 5 (2 : F5)) := by
  unfold QuadraticAffineSolution QuadraticPair
  infer_instance

instance : Fintype (QuadraticInfinityDirection 5 (2 : F5)) := by
  unfold QuadraticInfinityDirection QuadraticPair
  infer_instance

/-- There are ten affine solutions over the checked `𝔽₂₅` presentation. -/
theorem card_affineSolutionF25 :
    Fintype.card (QuadraticAffineSolution 5 (2 : F5)) = 10 := by
  decide

/-- There are two normalized infinity directions over the checked
`𝔽₂₅` presentation. -/
theorem card_infinityDirectionF25 :
    Fintype.card (QuadraticInfinityDirection 5 (2 : F5)) = 2 := by
  decide

/-- The point certificate over `𝔽₂₅`. -/
def PointCertificateF25 :=
  QuadraticAffineSolution 5 (2 : F5) ⊕
    QuadraticInfinityDirection 5 (2 : F5)

instance : Fintype PointCertificateF25 := by
  unfold PointCertificateF25
  infer_instance

/-- The quadratic-extension point certificate has twelve elements over
`𝔽₂₅`. -/
theorem card_pointCertificateF25 :
    Fintype.card PointCertificateF25 = 12 := by
  change Fintype.card
    (QuadraticAffineSolution 5 (2 : F5) ⊕
      QuadraticInfinityDirection 5 (2 : F5)) = 12
  rw [Fintype.card_sum, card_affineSolutionF25,
    card_infinityDirectionF25]

/-- The two checked pairs of point counts.  For a smooth projective genus-two
curve these are the inputs `(#C(𝔽_q), #C(𝔽_{q²}))` to the standard
Jacobian-order formula.  This theorem only packages the finite enumerations;
it does not supply that geometric identification. -/
theorem twoPrime_pointCertificate_counts :
    (Fintype.card PointCertificate = 6 ∧
      Fintype.card PointCertificateF9 = 8) ∧
    (Fintype.card PointCertificateF5 = 6 ∧
      Fintype.card PointCertificateF25 = 12) := by
  exact ⟨⟨card_pointCertificate, card_pointCertificateF9⟩,
    ⟨card_pointCertificateF5, card_pointCertificateF25⟩⟩

/-! ## Degree-two divisor labels -/

/-- Labels for the six rational cusp points in either good reduction. -/
inductive RationalCuspLabel
  | zeroPos
  | zeroNeg
  | negOnePos
  | negOneNeg
  | infinityPos
  | infinityNeg
  deriving DecidableEq

instance : Fintype RationalCuspLabel where
  elems := {.zeroPos, .zeroNeg, .negOnePos, .negOneNeg,
    .infinityPos, .infinityNeg}
  complete x := by cases x <;> simp

/-- The ordering used to give unordered pairs a unique representative. -/
def rationalCuspLabelIndex : RationalCuspLabel → Fin 6
  | .zeroPos => 0
  | .zeroNeg => 1
  | .negOnePos => 2
  | .negOneNeg => 3
  | .infinityPos => 4
  | .infinityNeg => 5

/-- The hyperelliptic involution on rational cusp labels. -/
def rationalCuspConjugate : RationalCuspLabel → RationalCuspLabel
  | .zeroPos => .zeroNeg
  | .zeroNeg => .zeroPos
  | .negOnePos => .negOneNeg
  | .negOneNeg => .negOnePos
  | .infinityPos => .infinityNeg
  | .infinityNeg => .infinityPos

/-- The cusp label interpreted in the point certificate over `𝔽₃`. -/
def rationalCuspLabelPointF3 : RationalCuspLabel → PointCertificate
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .negOnePos => .inl ⟨(-1, 1), by decide⟩
  | .negOneNeg => .inl ⟨(-1, -1), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- A computational inverse label for the `𝔽₃` point certificate. -/
def pointCertificateCuspLabelF3 : PointCertificate → RationalCuspLabel
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.2 = 1 then .negOnePos else .negOneNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The inverse label recovers every rational cusp label over `𝔽₃`. -/
theorem pointCertificateCuspLabelF3_leftInverse :
    Function.LeftInverse pointCertificateCuspLabelF3
      rationalCuspLabelPointF3 := by
  intro c
  cases c <;> decide

/-- The six cusp labels enumerate the complete point certificate over `𝔽₃`. -/
theorem rationalCuspLabelPointF3_bijective :
    Function.Bijective rationalCuspLabelPointF3 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointCertificateCuspLabelF3_leftInverse.injective
  · rw [card_pointCertificate]
    decide

/-- The cusp label interpreted in the point certificate over `𝔽₅`. -/
def rationalCuspLabelPointF5 : RationalCuspLabel → PointCertificateF5
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .negOnePos => .inl ⟨(-1, 1), by decide⟩
  | .negOneNeg => .inl ⟨(-1, -1), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- A computational inverse label for the `𝔽₅` point certificate. -/
def pointCertificateCuspLabelF5 : PointCertificateF5 → RationalCuspLabel
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.2 = 1 then .negOnePos else .negOneNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The inverse label recovers every rational cusp label over `𝔽₅`. -/
theorem pointCertificateCuspLabelF5_leftInverse :
    Function.LeftInverse pointCertificateCuspLabelF5
      rationalCuspLabelPointF5 := by
  intro c
  cases c <;> decide

/-- The six cusp labels enumerate the complete point certificate over `𝔽₅`. -/
theorem rationalCuspLabelPointF5_bijective :
    Function.Bijective rationalCuspLabelPointF5 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointCertificateCuspLabelF5_leftInverse.injective
  · rw [card_pointCertificateF5]
    decide

/-- An unordered pair of rational cusp labels, represented in increasing
index order. -/
def UnorderedRationalCuspPair :=
  {p : RationalCuspLabel × RationalCuspLabel //
    (rationalCuspLabelIndex p.1 : ℕ) ≤
      (rationalCuspLabelIndex p.2 : ℕ)}

instance : Fintype UnorderedRationalCuspPair := by
  unfold UnorderedRationalCuspPair
  infer_instance

/-- Six points have twenty-one unordered pairs with repetition. -/
theorem card_unorderedRationalCuspPair :
    Fintype.card UnorderedRationalCuspPair = 21 := by
  decide

/-- A rational cusp pair is a member of the hyperelliptic pencil when its
second label is the conjugate of its first. -/
def IsRationalHyperellipticPair
    (p : UnorderedRationalCuspPair) : Prop :=
  p.1.2 = rationalCuspConjugate p.1.1

instance (p : UnorderedRationalCuspPair) :
    Decidable (IsRationalHyperellipticPair p) := by
  unfold IsRationalHyperellipticPair
  infer_instance

/-- Exactly three rational unordered pairs are hyperelliptic fibers. -/
theorem card_rationalHyperellipticPair :
    Fintype.card {p : UnorderedRationalCuspPair //
      IsRationalHyperellipticPair p} = 3 := by
  decide

/-- Conjugation in the pair presentation. -/
def quadraticPairConjugate {n : ℕ}
    (u : QuadraticPair n) : QuadraticPair n :=
  (u.1, -u.2)

/-- Cubing in the checked nine-element presentation is pair conjugation. -/
theorem quadraticPairPow_three_eq_conjugate_F9 :
    ∀ u : F9Pair,
      quadraticPairPow (2 : F3) u 3 = quadraticPairConjugate u := by
  decide

/-- Fifth powering in the checked twenty-five-element presentation is pair
conjugation. -/
theorem quadraticPairPow_five_eq_conjugate_F25 :
    ∀ u : F25Pair,
      quadraticPairPow (2 : F5) u 5 = quadraticPairConjugate u := by
  decide

/-- A quadratic affine solution whose two coordinates do not both lie in
the base field. -/
def IsNonBaseQuadraticAffineSolution {n : ℕ} {d : ZMod n}
    (P : QuadraticAffineSolution n d) : Prop :=
  P.1.1.2 ≠ 0 ∨ P.1.2.2 ≠ 0

instance {n : ℕ} {d : ZMod n}
    (P : QuadraticAffineSolution n d) :
    Decidable (IsNonBaseQuadraticAffineSolution P) := by
  unfold IsNonBaseQuadraticAffineSolution
  infer_instance

/-- There are two non-base affine solutions over `𝔽₉`. -/
theorem card_nonBaseAffineSolutionF9 :
    Fintype.card {P : QuadraticAffineSolution 3 (2 : F3) //
      IsNonBaseQuadraticAffineSolution P} = 2 := by
  decide

/-- The non-base `𝔽₉` solutions form the fiber above the base-field
abscissa `1`, and their ordinates are genuinely quadratic. -/
theorem nonBaseAffineSolutionF9_abscissa :
    ∀ P : QuadraticAffineSolution 3 (2 : F3),
      IsNonBaseQuadraticAffineSolution P →
        P.1.1 = ((1, 0) : F9Pair) ∧ P.1.2.2 ≠ 0 := by
  decide

/-- At the non-base `𝔽₉` abscissa, the two ordinates are equal or
quadratic conjugates. -/
theorem nonBaseAffineSolutionF9_ordinates :
    ∀ P Q : QuadraticAffineSolution 3 (2 : F3),
      IsNonBaseQuadraticAffineSolution P →
      IsNonBaseQuadraticAffineSolution Q →
      P.1.1 = Q.1.1 →
        Q.1.2 = P.1.2 ∨ Q.1.2 = quadraticPairConjugate P.1.2 := by
  decide

/-- There are six non-base affine solutions over `𝔽₂₅`. -/
theorem card_nonBaseAffineSolutionF25 :
    Fintype.card {P : QuadraticAffineSolution 5 (2 : F5) //
      IsNonBaseQuadraticAffineSolution P} = 6 := by
  decide

/-- The non-base `𝔽₂₅` solutions lie above the three base-field
abscissas `1`, `2`, and `3`, with genuinely quadratic ordinates. -/
theorem nonBaseAffineSolutionF25_abscissa :
    ∀ P : QuadraticAffineSolution 5 (2 : F5),
      IsNonBaseQuadraticAffineSolution P →
        P.1.1.2 = 0 ∧
        (P.1.1.1 = 1 ∨ P.1.1.1 = 2 ∨ P.1.1.1 = 3) ∧
        P.1.2.2 ≠ 0 := by
  decide

/-- Above any of the three non-base `𝔽₂₅` abscissas, the two ordinates
are equal or quadratic conjugates. -/
theorem nonBaseAffineSolutionF25_ordinates :
    ∀ P Q : QuadraticAffineSolution 5 (2 : F5),
      IsNonBaseQuadraticAffineSolution P →
      IsNonBaseQuadraticAffineSolution Q →
      P.1.1 = Q.1.1 →
        Q.1.2 = P.1.2 ∨ Q.1.2 = quadraticPairConjugate P.1.2 := by
  decide

/-- The one quadratic closed fiber over `𝔽₃`, labeled by its base-field
abscissa. -/
def QuadraticClosedFiberF3 :=
  {x : F3 // x = 1}

instance : Fintype QuadraticClosedFiberF3 := by
  unfold QuadraticClosedFiberF3
  infer_instance

/-- There is one non-rational quadratic closed fiber over `𝔽₃`. -/
theorem card_quadraticClosedFiberF3 :
    Fintype.card QuadraticClosedFiberF3 = 1 := by
  decide

/-- The three quadratic closed fibers over `𝔽₅`, labeled by their
base-field abscissas. -/
def QuadraticClosedFiberF5 :=
  {x : F5 // x = 1 ∨ x = 2 ∨ x = 3}

instance : Fintype QuadraticClosedFiberF5 := by
  unfold QuadraticClosedFiberF5
  infer_instance

/-- There are three non-rational quadratic closed fibers over `𝔽₅`. -/
theorem card_quadraticClosedFiberF5 :
    Fintype.card QuadraticClosedFiberF5 = 3 := by
  decide

/-- Degree-two effective-divisor labels over `𝔽₃`: either an unordered
pair of rational points or the unique quadratic Frobenius orbit. -/
def DegreeTwoDivisorCertificateF3 :=
  UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF3

instance : Fintype DegreeTwoDivisorCertificateF3 := by
  unfold DegreeTwoDivisorCertificateF3
  infer_instance

/-- The degree-two certificate over `𝔽₃` has twenty-two elements. -/
theorem card_degreeTwoDivisorCertificateF3 :
    Fintype.card DegreeTwoDivisorCertificateF3 = 22 := by
  change Fintype.card
    (UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF3) = 22
  rw [Fintype.card_sum, card_unorderedRationalCuspPair,
    card_quadraticClosedFiberF3]

/-- Degree-two effective-divisor labels over `𝔽₅`. -/
def DegreeTwoDivisorCertificateF5 :=
  UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF5

instance : Fintype DegreeTwoDivisorCertificateF5 := by
  unfold DegreeTwoDivisorCertificateF5
  infer_instance

/-- The degree-two certificate over `𝔽₅` has twenty-four elements. -/
theorem card_degreeTwoDivisorCertificateF5 :
    Fintype.card DegreeTwoDivisorCertificateF5 = 24 := by
  change Fintype.card
    (UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF5) = 24
  rw [Fintype.card_sum, card_unorderedRationalCuspPair,
    card_quadraticClosedFiberF5]

/-- The hyperelliptic-pencil labels among the degree-two certificates over
`𝔽₃`.  The quadratic closed fiber is one of those pencil members. -/
def IsCanonicalDegreeTwoF3 : DegreeTwoDivisorCertificateF3 → Prop
  | .inl p => IsRationalHyperellipticPair p
  | .inr _ => True

instance (D : DegreeTwoDivisorCertificateF3) :
    Decidable (IsCanonicalDegreeTwoF3 D) := by
  cases D with
  | inl p =>
      change Decidable (IsRationalHyperellipticPair p)
      exact inferInstance
  | inr _ => exact isTrue trivial

/-- The hyperelliptic pencil has four labels over `𝔽₃`. -/
theorem card_canonicalDegreeTwoF3 :
    Fintype.card {D : DegreeTwoDivisorCertificateF3 //
      IsCanonicalDegreeTwoF3 D} = 4 := by
  decide

/-- The hyperelliptic-pencil labels over `𝔽₅`. -/
def IsCanonicalDegreeTwoF5 : DegreeTwoDivisorCertificateF5 → Prop
  | .inl p => IsRationalHyperellipticPair p
  | .inr _ => True

instance (D : DegreeTwoDivisorCertificateF5) :
    Decidable (IsCanonicalDegreeTwoF5 D) := by
  cases D with
  | inl p =>
      change Decidable (IsRationalHyperellipticPair p)
      exact inferInstance
  | inr _ => exact isTrue trivial

/-- The hyperelliptic pencil has six labels over `𝔽₅`. -/
theorem card_canonicalDegreeTwoF5 :
    Fintype.card {D : DegreeTwoDivisorCertificateF5 //
      IsCanonicalDegreeTwoF5 D} = 6 := by
  decide

/-- The combinatorial reduced degree-two class certificate over `𝔽₃`:
retain every noncanonical divisor label and collapse the complete
hyperelliptic pencil to one distinguished label.

This is not defined to be a Picard group or a Jacobian. -/
def ReducedDegreeTwoClassCertificateF3 :=
  {D : DegreeTwoDivisorCertificateF3 // ¬ IsCanonicalDegreeTwoF3 D} ⊕ Unit

instance : Fintype ReducedDegreeTwoClassCertificateF3 := by
  unfold ReducedDegreeTwoClassCertificateF3
  infer_instance

/-- The reduced degree-two class certificate over `𝔽₃` has nineteen
elements. -/
theorem card_reducedDegreeTwoClassCertificateF3 :
    Fintype.card ReducedDegreeTwoClassCertificateF3 = 19 := by
  decide

/-- The analogous combinatorial reduced degree-two class certificate over
`𝔽₅`.  No Picard or Jacobian identification is asserted. -/
def ReducedDegreeTwoClassCertificateF5 :=
  {D : DegreeTwoDivisorCertificateF5 // ¬ IsCanonicalDegreeTwoF5 D} ⊕ Unit

instance : Fintype ReducedDegreeTwoClassCertificateF5 := by
  unfold ReducedDegreeTwoClassCertificateF5
  infer_instance

/-- The reduced degree-two class certificate over `𝔽₅` has nineteen
elements. -/
theorem card_reducedDegreeTwoClassCertificateF5 :
    Fintype.card ReducedDegreeTwoClassCertificateF5 = 19 := by
  decide

end MazurTorsion.XOneThirteenFiniteField
