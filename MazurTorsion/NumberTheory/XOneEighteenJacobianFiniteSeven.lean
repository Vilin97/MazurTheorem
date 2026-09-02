/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenJacobianFinite

/-!
# The second finite Jacobian certificate for `X₁(18)`

This file supplies the independent good-reduction count at seven.  The
order-eighteen sextic has ten points over `𝔽₇` and forty over `𝔽₄₉`.
Its seventy Frobenius-stable effective divisors of degree two contain the
eight-member hyperelliptic pencil, so the reduced degree-two certificate has
sixty-three elements:

`#J(𝔽₇) = (#C(𝔽₇)² + #C(𝔽₄₉))/2 - 7 = 63`.

Together with the twenty-one-element certificate at five, this gives the
two coprime-residue-characteristic targets needed by a future rational
Jacobian reduction argument.  As in the companion file, no geometric Picard
identification is asserted here.
-/

namespace MazurTorsion.XOneEighteenFiniteField

open Polynomial

/-! ## The squarefree reduction over `𝔽₇` -/

/-- The seven-element residue field. -/
abbrev F7 := ZMod 7

/-- The order-eighteen sextic reduced modulo seven. -/
noncomputable def sexticF7 : Polynomial F7 :=
  X ^ 6 + 3 * X ^ 5 + 3 * X ^ 4 + 4 * X ^ 3 +
    5 * X ^ 2 + 5 * X + 1

/-- A computable value function for the reduced sextic. -/
def sexticValueF7 (x : F7) : F7 :=
  x ^ 6 + 3 * x ^ 5 + 3 * x ^ 4 + 4 * x ^ 3 +
    5 * x ^ 2 + 5 * x + 1

/-- Polynomial evaluation agrees with the computable value function. -/
lemma eval_sexticF7 (x : F7) :
    Polynomial.eval x sexticF7 = sexticValueF7 x := by
  simp [sexticF7, sexticValueF7]

/-- The displayed reduced formula agrees with the integral order-eighteen
model modulo seven. -/
lemma sexticValueF7_eq_model_formula (x : F7) :
    sexticValueF7 x =
      x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 +
        5 * x ^ 2 - 2 * x + 1 := by
  fin_cases x <;> decide

private lemma C_two_mul_five_F7 :
    C (2 : F7) * (5 : Polynomial F7) = 3 := by
  change C (2 : F7) * C (5 : F7) = C (3 : F7)
  rw [← C_mul]
  congr 1

private lemma C_three_mul_four_F7 :
    C (3 : F7) * (4 : Polynomial F7) = 5 := by
  change C (3 : F7) * C (4 : F7) = C (5 : F7)
  rw [← C_mul]
  congr 1

private lemma C_four_mul_three_F7 :
    C (4 : F7) * (3 : Polynomial F7) = 5 := by
  change C (4 : F7) * C (3 : F7) = C (5 : F7)
  rw [← C_mul]
  congr 1

private lemma C_five_mul_three_F7 :
    C (5 : F7) * (3 : Polynomial F7) = 1 := by
  change C (5 : F7) * C (3 : F7) = C (1 : F7)
  rw [← C_mul]
  congr 1

/-- The derivative of the reduced sextic. -/
lemma derivative_sexticF7 :
    sexticF7.derivative =
      6 * X ^ 5 + X ^ 4 + 5 * X ^ 3 + 5 * X ^ 2 + 3 * X + 5 := by
  simp [sexticF7, derivative_add, derivative_mul, derivative_pow]
  ring_nf
  rw [mul_assoc X (C (2 : F7)) (5 : Polynomial F7),
    C_two_mul_five_F7]
  rw [mul_assoc (X ^ 2) (C (3 : F7)) (4 : Polynomial F7),
    C_three_mul_four_F7]
  rw [mul_assoc (X ^ 3) (C (4 : F7)) (3 : Polynomial F7),
    C_four_mul_three_F7]
  rw [mul_assoc (X ^ 4) (C (5 : F7)) (3 : Polynomial F7),
    C_five_mul_three_F7]
  rw [← C_ofNat (R := F7) 6]
  ring

/-- Left coefficient in an explicit Bézout certificate. -/
noncomputable def bezoutLeftF7 : Polynomial F7 :=
  X ^ 4 + X ^ 3 + 6 * X ^ 2 + 2 * X + 6

/-- Right coefficient in an explicit Bézout certificate. -/
noncomputable def bezoutRightF7 : Polynomial F7 :=
  X ^ 5 + 5 * X ^ 4 + X ^ 3 + 2 * X ^ 2 + 4 * X + 6

private lemma polynomial_seven_eq_zero_F7 :
    (7 : Polynomial F7) = 0 := by
  rw [← C_ofNat]
  have h : (7 : F7) = 0 := by decide
  rw [h, C_0]

private lemma polynomial_twentyEight_eq_zero_F7 :
    (28 : Polynomial F7) = 0 := by
  rw [← C_ofNat]
  have h : (28 : F7) = 0 := by decide
  rw [h, C_0]

private lemma polynomial_thirtyFive_eq_zero_F7 :
    (35 : Polynomial F7) = 0 := by
  rw [← C_ofNat]
  have h : (35 : F7) = 0 := by decide
  rw [h, C_0]

private lemma polynomial_thirtySix_eq_one_F7 :
    (36 : Polynomial F7) = 1 := by
  rw [← C_ofNat]
  have h : (36 : F7) = 1 := by decide
  rw [h, C_1]

private lemma polynomial_seventy_eq_zero_F7 :
    (70 : Polynomial F7) = 0 := by
  rw [← C_ofNat]
  have h : (70 : F7) = 0 := by decide
  rw [h, C_0]

private lemma polynomial_ninetyEight_eq_zero_F7 :
    (98 : Polynomial F7) = 0 := by
  rw [← C_ofNat]
  have h : (98 : F7) = 0 := by decide
  rw [h, C_0]

private lemma polynomial_oneTwentySix_eq_zero_F7 :
    (126 : Polynomial F7) = 0 := by
  rw [← C_ofNat]
  have h : (126 : F7) = 0 := by decide
  rw [h, C_0]

private lemma polynomial_oneThirtyThree_eq_zero_F7 :
    (133 : Polynomial F7) = 0 := by
  rw [← C_ofNat]
  have h : (133 : F7) = 0 := by decide
  rw [h, C_0]

/-- Exact Bézout identity for the reduction and its derivative. -/
lemma sexticF7_derivative_bezout :
    bezoutLeftF7 * sexticF7 +
        bezoutRightF7 * sexticF7.derivative = 1 := by
  rw [derivative_sexticF7]
  simp only [bezoutLeftF7, bezoutRightF7, sexticF7]
  ring_nf
  simp [polynomial_seven_eq_zero_F7,
    polynomial_twentyEight_eq_zero_F7,
    polynomial_thirtyFive_eq_zero_F7,
    polynomial_thirtySix_eq_one_F7,
    polynomial_seventy_eq_zero_F7,
    polynomial_ninetyEight_eq_zero_F7,
    polynomial_oneTwentySix_eq_zero_F7,
    polynomial_oneThirtyThree_eq_zero_F7]

/-- The reduction modulo seven is separable. -/
theorem sexticF7_separable : sexticF7.Separable :=
  ⟨bezoutLeftF7, bezoutRightF7, sexticF7_derivative_bezout⟩

/-- An affine solution over `𝔽₇`. -/
def AffineSolutionF7 :=
  {p : F7 × F7 // p.2 ^ 2 = sexticValueF7 p.1}

instance : Fintype AffineSolutionF7 := by
  unfold AffineSolutionF7
  infer_instance

/-- There are eight affine solutions over `𝔽₇`. -/
theorem card_affineSolutionF7 :
    Fintype.card AffineSolutionF7 = 8 := by
  decide

/-- A normalized infinity direction over `𝔽₇`. -/
def InfinityDirectionF7 :=
  {η : F7 // η ^ 2 = 1}

instance : Fintype InfinityDirectionF7 := by
  unfold InfinityDirectionF7
  infer_instance

/-- There are two normalized infinity directions over `𝔽₇`. -/
theorem card_infinityDirectionF7 :
    Fintype.card InfinityDirectionF7 = 2 := by
  decide

/-- The complete base-field point certificate at seven. -/
def PointCertificateF7 :=
  AffineSolutionF7 ⊕ InfinityDirectionF7

instance : Fintype PointCertificateF7 := by
  unfold PointCertificateF7
  infer_instance

/-- The curve has ten points in the checked `𝔽₇` certificate. -/
theorem card_pointCertificateF7 :
    Fintype.card PointCertificateF7 = 10 := by
  change Fintype.card (AffineSolutionF7 ⊕ InfinityDirectionF7) = 10
  rw [Fintype.card_sum, card_affineSolutionF7,
    card_infinityDirectionF7]

/-! ## Enumeration over `𝔽₄₉` -/

/-- The pair presentation of `𝔽₄₉`, with `ω² = 3`. -/
abbrev F49Pair := QuadraticPair 7

/-- Three is not a square in `𝔽₇`. -/
theorem three_not_square_F7 :
    ∀ a : F7, a ^ 2 ≠ 3 := by
  decide

/-- Every nonzero pair has a multiplicative inverse. -/
theorem F49Pair_nonzero_has_mul_inverse :
    ∀ u : F49Pair, u ≠ quadraticPairZero →
      ∃ v : F49Pair,
        quadraticPairMul (3 : F7) u v = quadraticPairOne := by
  decide

/-- The reduced order-eighteen sextic evaluated in the `𝔽₄₉` pair
presentation. -/
def quadraticPairSexticValueF7
    (x : F49Pair) : F49Pair :=
  quadraticPairAdd (quadraticPairPow (3 : F7) x 6)
    (quadraticPairAdd
      (quadraticPairNatScale 3 (quadraticPairPow (3 : F7) x 5))
      (quadraticPairAdd
        (quadraticPairNatScale 3 (quadraticPairPow (3 : F7) x 4))
        (quadraticPairAdd
          (quadraticPairNatScale 4 (quadraticPairPow (3 : F7) x 3))
          (quadraticPairAdd
            (quadraticPairNatScale 5 (quadraticPairPow (3 : F7) x 2))
            (quadraticPairAdd (quadraticPairNatScale 5 x)
              quadraticPairOne)))))

/-- An affine solution in the `𝔽₄₉` pair presentation. -/
def QuadraticAffineSolutionF7 :=
  {p : F49Pair × F49Pair //
    quadraticPairMul (3 : F7) p.2 p.2 =
      quadraticPairSexticValueF7 p.1}

/-- A normalized infinity direction in the `𝔽₄₉` presentation. -/
def QuadraticInfinityDirectionF7 :=
  {η : F49Pair //
    quadraticPairMul (3 : F7) η η = quadraticPairOne}

instance : Fintype QuadraticAffineSolutionF7 := by
  unfold QuadraticAffineSolutionF7 QuadraticPair
  infer_instance

instance : Fintype QuadraticInfinityDirectionF7 := by
  unfold QuadraticInfinityDirectionF7 QuadraticPair
  infer_instance

/-- There are thirty-eight affine solutions over `𝔽₄₉`. -/
theorem card_affineSolutionF49 :
    Fintype.card QuadraticAffineSolutionF7 = 38 := by
  decide +kernel

/-- There are two normalized infinity directions over `𝔽₄₉`. -/
theorem card_infinityDirectionF49 :
    Fintype.card QuadraticInfinityDirectionF7 = 2 := by
  decide

/-- The complete point certificate over `𝔽₄₉`. -/
def PointCertificateF49 :=
  QuadraticAffineSolutionF7 ⊕ QuadraticInfinityDirectionF7

instance : Fintype PointCertificateF49 := by
  unfold PointCertificateF49
  infer_instance

/-- The curve has forty points in the checked `𝔽₄₉` presentation. -/
theorem card_pointCertificateF49 :
    Fintype.card PointCertificateF49 = 40 := by
  change Fintype.card
    (QuadraticAffineSolutionF7 ⊕ QuadraticInfinityDirectionF7) = 40
  rw [Fintype.card_sum, card_affineSolutionF49,
    card_infinityDirectionF49]

/-- Seventh powering is Frobenius conjugation in the checked pair field. -/
theorem quadraticPairPow_seven_eq_conjugate_F49 :
    ∀ u : F49Pair,
      quadraticPairPow (3 : F7) u 7 = quadraticPairConjugate u := by
  decide

/-- A quadratic affine solution not defined over `𝔽₇`. -/
def IsNonBaseQuadraticAffineSolutionF7
    (P : QuadraticAffineSolutionF7) : Prop :=
  P.1.1.2 ≠ 0 ∨ P.1.2.2 ≠ 0

instance (P : QuadraticAffineSolutionF7) :
    Decidable (IsNonBaseQuadraticAffineSolutionF7 P) := by
  unfold IsNonBaseQuadraticAffineSolutionF7
  infer_instance

/-- Exactly thirty affine points are genuinely quadratic. -/
theorem card_nonBaseAffineSolutionF49 :
    Fintype.card {P : QuadraticAffineSolutionF7 //
      IsNonBaseQuadraticAffineSolutionF7 P} = 30 := by
  decide +kernel

/-! ## The fifteen quadratic Frobenius orbits -/

/-- One representative coordinate pair for each non-base Frobenius orbit. -/
def quadraticClosedPointRepresentativeListF7 :
    List (F49Pair × F49Pair) :=
  [(((0, 1) : F49Pair), ((3, 5) : F49Pair)),
    (((0, 1) : F49Pair), ((4, 2) : F49Pair)),
    (((1, 2) : F49Pair), ((3, 2) : F49Pair)),
    (((1, 2) : F49Pair), ((4, 5) : F49Pair)),
    (((2, 0) : F49Pair), ((0, 2) : F49Pair)),
    (((2, 2) : F49Pair), ((3, 1) : F49Pair)),
    (((2, 2) : F49Pair), ((4, 6) : F49Pair)),
    (((2, 3) : F49Pair), ((0, 3) : F49Pair)),
    (((2, 3) : F49Pair), ((0, 4) : F49Pair)),
    (((3, 2) : F49Pair), ((2, 6) : F49Pair)),
    (((3, 2) : F49Pair), ((5, 1) : F49Pair)),
    (((3, 3) : F49Pair), ((1, 5) : F49Pair)),
    (((3, 3) : F49Pair), ((6, 2) : F49Pair)),
    (((4, 0) : F49Pair), ((0, 2) : F49Pair)),
    (((6, 0) : F49Pair), ((0, 2) : F49Pair))]

/-- Membership in the selected list of non-base orbit representatives. -/
def IsQuadraticClosedPointRepresentativeF7
    (P : QuadraticAffineSolutionF7) : Prop :=
  P.1 ∈ quadraticClosedPointRepresentativeListF7

instance (P : QuadraticAffineSolutionF7) :
    Decidable (IsQuadraticClosedPointRepresentativeF7 P) := by
  unfold IsQuadraticClosedPointRepresentativeF7
  infer_instance

/-- The selected set of quadratic closed-point representatives. -/
def QuadraticClosedPointRepresentativeF7 :=
  {P : QuadraticAffineSolutionF7 //
    IsQuadraticClosedPointRepresentativeF7 P}

instance : Fintype QuadraticClosedPointRepresentativeF7 := by
  unfold QuadraticClosedPointRepresentativeF7
  infer_instance

/-- There are fifteen quadratic Frobenius orbits. -/
theorem card_quadraticClosedPointRepresentativeF7 :
    Fintype.card QuadraticClosedPointRepresentativeF7 = 15 := by
  decide +kernel

/-- Every genuinely quadratic point is represented by the displayed list
up to Frobenius conjugation. -/
theorem quadraticClosedPointRepresentativeF7_complete :
    ∀ P : QuadraticAffineSolutionF7,
      IsNonBaseQuadraticAffineSolutionF7 P →
        ∃ Q : QuadraticClosedPointRepresentativeF7,
          P.1 = Q.1.1 ∨
            P.1 = (quadraticPairConjugate Q.1.1.1,
              quadraticPairConjugate Q.1.1.2) := by
  decide +kernel

/-- A selected quadratic orbit is in the hyperelliptic pencil when its
abscissa is fixed by Frobenius. -/
def IsQuadraticHyperellipticOrbitF7
    (Q : QuadraticClosedPointRepresentativeF7) : Prop :=
  Q.1.1.1.2 = 0

instance (Q : QuadraticClosedPointRepresentativeF7) :
    Decidable (IsQuadraticHyperellipticOrbitF7 Q) := by
  unfold IsQuadraticHyperellipticOrbitF7
  infer_instance

/-- Three quadratic orbits are hyperelliptic fibers. -/
theorem card_quadraticHyperellipticOrbitF7 :
    Fintype.card {Q : QuadraticClosedPointRepresentativeF7 //
      IsQuadraticHyperellipticOrbitF7 Q} = 3 := by
  decide +kernel

/-! ## Rational pairs and the sixty-three reduced labels -/

/-- Labels for the ten base-field points. -/
inductive RationalPointLabelF7
  | zeroPos | zeroNeg
  | onePos | oneNeg
  | threePos | threeNeg
  | fivePos | fiveNeg
  | infinityPos | infinityNeg
  deriving DecidableEq

instance : Fintype RationalPointLabelF7 where
  elems := {.zeroPos, .zeroNeg, .onePos, .oneNeg,
    .threePos, .threeNeg, .fivePos, .fiveNeg,
    .infinityPos, .infinityNeg}
  complete x := by cases x <;> simp

/-- An index selecting one order of each rational pair. -/
def rationalPointLabelIndexF7 : RationalPointLabelF7 → Fin 10
  | .zeroPos => 0
  | .zeroNeg => 1
  | .onePos => 2
  | .oneNeg => 3
  | .threePos => 4
  | .threeNeg => 5
  | .fivePos => 6
  | .fiveNeg => 7
  | .infinityPos => 8
  | .infinityNeg => 9

/-- The hyperelliptic involution on the ten rational labels. -/
def rationalPointConjugateF7 : RationalPointLabelF7 → RationalPointLabelF7
  | .zeroPos => .zeroNeg
  | .zeroNeg => .zeroPos
  | .onePos => .oneNeg
  | .oneNeg => .onePos
  | .threePos => .threeNeg
  | .threeNeg => .threePos
  | .fivePos => .fiveNeg
  | .fiveNeg => .fivePos
  | .infinityPos => .infinityNeg
  | .infinityNeg => .infinityPos

/-- A rational label interpreted in the base-field point certificate. -/
def rationalPointLabelPointF7 : RationalPointLabelF7 → PointCertificateF7
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .onePos => .inl ⟨(1, 1), by decide⟩
  | .oneNeg => .inl ⟨(1, -1), by decide⟩
  | .threePos => .inl ⟨(3, 1), by decide⟩
  | .threeNeg => .inl ⟨(3, -1), by decide⟩
  | .fivePos => .inl ⟨(5, 3), by decide⟩
  | .fiveNeg => .inl ⟨(5, -3), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- A computational inverse to the ten rational point labels. -/
def pointCertificateLabelF7 : PointCertificateF7 → RationalPointLabelF7
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.1 = 1 then
        if p.1.2 = 1 then .onePos else .oneNeg
      else if p.1.1 = 3 then
        if p.1.2 = 1 then .threePos else .threeNeg
      else if p.1.2 = 3 then .fivePos else .fiveNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The computational inverse recovers each rational point label. -/
theorem pointCertificateLabelF7_leftInverse :
    Function.LeftInverse pointCertificateLabelF7
      rationalPointLabelPointF7 := by
  intro c
  cases c <;> decide

/-- The ten rational labels enumerate the complete point certificate. -/
theorem rationalPointLabelPointF7_bijective :
    Function.Bijective rationalPointLabelPointF7 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointCertificateLabelF7_leftInverse.injective
  · rw [card_pointCertificateF7]
    decide

/-- An unordered pair of rational points. -/
def UnorderedRationalPointPairF7 :=
  {p : RationalPointLabelF7 × RationalPointLabelF7 //
    (rationalPointLabelIndexF7 p.1 : ℕ) ≤
      (rationalPointLabelIndexF7 p.2 : ℕ)}

instance : Fintype UnorderedRationalPointPairF7 := by
  unfold UnorderedRationalPointPairF7
  infer_instance

/-- Ten points have fifty-five unordered pairs with repetition. -/
theorem card_unorderedRationalPointPairF7 :
    Fintype.card UnorderedRationalPointPairF7 = 55 := by
  decide

/-- A rational pair belonging to the hyperelliptic pencil. -/
def IsRationalHyperellipticPairF7
    (p : UnorderedRationalPointPairF7) : Prop :=
  p.1.2 = rationalPointConjugateF7 p.1.1

instance (p : UnorderedRationalPointPairF7) :
    Decidable (IsRationalHyperellipticPairF7 p) := by
  unfold IsRationalHyperellipticPairF7
  infer_instance

/-- Five rational pairs are hyperelliptic fibers. -/
theorem card_rationalHyperellipticPairF7 :
    Fintype.card {p : UnorderedRationalPointPairF7 //
      IsRationalHyperellipticPairF7 p} = 5 := by
  decide

/-- The seventy Frobenius-stable effective degree-two labels over `𝔽₇`. -/
def DegreeTwoDivisorCertificateF7 :=
  UnorderedRationalPointPairF7 ⊕ QuadraticClosedPointRepresentativeF7

instance : Fintype DegreeTwoDivisorCertificateF7 := by
  unfold DegreeTwoDivisorCertificateF7
  infer_instance

/-- There are seventy effective degree-two labels. -/
theorem card_degreeTwoDivisorCertificateF7 :
    Fintype.card DegreeTwoDivisorCertificateF7 = 70 := by
  change Fintype.card
    (UnorderedRationalPointPairF7 ⊕
      QuadraticClosedPointRepresentativeF7) = 70
  rw [Fintype.card_sum, card_unorderedRationalPointPairF7,
    card_quadraticClosedPointRepresentativeF7]

/-- Membership in the eight-member hyperelliptic pencil. -/
def IsCanonicalDegreeTwoF7 : DegreeTwoDivisorCertificateF7 → Prop
  | .inl p => IsRationalHyperellipticPairF7 p
  | .inr Q => IsQuadraticHyperellipticOrbitF7 Q

instance (D : DegreeTwoDivisorCertificateF7) :
    Decidable (IsCanonicalDegreeTwoF7 D) := by
  cases D with
  | inl p =>
      change Decidable (IsRationalHyperellipticPairF7 p)
      exact inferInstance
  | inr Q =>
      change Decidable (IsQuadraticHyperellipticOrbitF7 Q)
      exact inferInstance

/-- The hyperelliptic pencil has eight labels over `𝔽₇`. -/
theorem card_canonicalDegreeTwoF7 :
    Fintype.card {D : DegreeTwoDivisorCertificateF7 //
      IsCanonicalDegreeTwoF7 D} = 8 := by
  decide +kernel

/-- Retain every noncanonical degree-two label and collapse the
hyperelliptic pencil to one distinguished label. -/
def ReducedDegreeTwoClassCertificateF7 :=
  {D : DegreeTwoDivisorCertificateF7 // ¬ IsCanonicalDegreeTwoF7 D} ⊕ Unit

instance : Fintype ReducedDegreeTwoClassCertificateF7 := by
  unfold ReducedDegreeTwoClassCertificateF7
  infer_instance

/-- The reduced degree-two certificate has sixty-three elements. -/
theorem card_reducedDegreeTwoClassCertificateF7 :
    Fintype.card ReducedDegreeTwoClassCertificateF7 = 63 := by
  decide +kernel

/-- The two point counts give the expected finite Jacobian order. -/
theorem jacobianOrderFormulaInputF7 :
    (Fintype.card PointCertificateF7 ^ 2 +
        Fintype.card PointCertificateF49) / 2 - 7 = 63 := by
  rw [card_pointCertificateF7, card_pointCertificateF49]
  norm_num

/-- Named consumer for a future geometric finite-Picard equivalence. -/
theorem finitePicard_card_eq_sixtyThree_of_reducedDegreeTwoEquiv
    {J7 : Type*} [Fintype J7]
    (e : J7 ≃ ReducedDegreeTwoClassCertificateF7) :
    Fintype.card J7 = 63 := by
  rw [Fintype.card_congr e,
    card_reducedDegreeTwoClassCertificateF7]

/-! ## The exact two-reduction arithmetic boundary -/

/-- The two good-reduction bounds force the cardinality of a finite rational
Jacobian to divide twenty-one.  The extra factors are precisely the possible
primary kernels in residue characteristics five and seven. -/
theorem rationalJacobian_card_dvd_twentyOne_of_two_reduction_bounds
    {JQ : Type*} [Fintype JQ] (a b : ℕ)
    (h5 : Fintype.card JQ ∣
      Fintype.card ReducedDegreeTwoClassCertificateF5 * 5 ^ a)
    (h7 : Fintype.card JQ ∣
      Fintype.card ReducedDegreeTwoClassCertificateF7 * 7 ^ b) :
    Fintype.card JQ ∣ 21 := by
  rw [card_reducedDegreeTwoClassCertificateF5] at h5
  rw [card_reducedDegreeTwoClassCertificateF7] at h7
  have hdivGcd :
      Fintype.card JQ ∣ Nat.gcd (21 * 5 ^ a) (63 * 7 ^ b) :=
    Nat.dvd_gcd h5 h7
  have hcoprimeFiveThree : Nat.Coprime (5 ^ a) 3 :=
    (show Nat.Coprime 5 3 by decide).pow_left a
  have hcoprimeFiveSeven : Nat.Coprime (5 ^ a) (7 ^ b) :=
    (show Nat.Coprime 5 7 by decide).pow a b
  have hcoprime : Nat.Coprime (5 ^ a) (3 * 7 ^ b) :=
    hcoprimeFiveThree.mul_right hcoprimeFiveSeven
  have hgcd : Nat.gcd (21 * 5 ^ a) (63 * 7 ^ b) = 21 := by
    rw [show 63 * 7 ^ b = 21 * (3 * 7 ^ b) by ring]
    rw [Nat.gcd_mul_left, hcoprime.gcd_eq_one, mul_one]
  rwa [hgcd] at hdivGcd

/-- If the rational Jacobian also contains a subgroup of order twenty-one,
the two reduction bounds determine its exact cardinality. -/
theorem rationalJacobian_card_eq_twentyOne_of_two_reduction_bounds
    {JQ : Type*} [Fintype JQ] (a b : ℕ)
    (h5 : Fintype.card JQ ∣
      Fintype.card ReducedDegreeTwoClassCertificateF5 * 5 ^ a)
    (h7 : Fintype.card JQ ∣
      Fintype.card ReducedDegreeTwoClassCertificateF7 * 7 ^ b)
    (h21 : 21 ∣ Fintype.card JQ) :
    Fintype.card JQ = 21 :=
  Nat.dvd_antisymm
    (rationalJacobian_card_dvd_twentyOne_of_two_reduction_bounds
      a b h5 h7) h21

private theorem natCard_dvd_card_ker_mul_card_target
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) :
    Nat.card A ∣ Nat.card f.ker * Nat.card B := by
  rw [← f.ker.card_mul_index, AddSubgroup.index_ker]
  exact Nat.mul_dvd_mul_left (Nat.card f.ker)
    f.range.card_addSubgroup_dvd_card

/-- Direct consumer for future geometric reduction maps.  Additive
reduction homomorphisms with primary kernels, together with genuine
equivalences from the two finite Picard groups to the checked certificates,
force the rational Jacobian to have order twenty-one once an order-twenty-one
subgroup has been constructed. -/
theorem rationalJacobian_card_eq_twentyOne_of_reduction_homs
    {JQ J5 J7 : Type*}
    [AddCommGroup JQ] [AddCommGroup J5] [AddCommGroup J7]
    [Fintype JQ]
    (e5 : J5 ≃ ReducedDegreeTwoClassCertificateF5)
    (e7 : J7 ≃ ReducedDegreeTwoClassCertificateF7)
    (red5 : JQ →+ J5) (red7 : JQ →+ J7)
    (a b : ℕ)
    (hker5 : Nat.card red5.ker = 5 ^ a)
    (hker7 : Nat.card red7.ker = 7 ^ b)
    (h21 : 21 ∣ Fintype.card JQ) :
    Fintype.card JQ = 21 := by
  have hJ5 : Nat.card J5 = 21 := by
    calc
      Nat.card J5 = Nat.card ReducedDegreeTwoClassCertificateF5 :=
        Nat.card_congr e5
      _ = Fintype.card ReducedDegreeTwoClassCertificateF5 :=
        Nat.card_eq_fintype_card
      _ = 21 := card_reducedDegreeTwoClassCertificateF5
  have hJ7 : Nat.card J7 = 63 := by
    calc
      Nat.card J7 = Nat.card ReducedDegreeTwoClassCertificateF7 :=
        Nat.card_congr e7
      _ = Fintype.card ReducedDegreeTwoClassCertificateF7 :=
        Nat.card_eq_fintype_card
      _ = 63 := card_reducedDegreeTwoClassCertificateF7
  have h5raw := natCard_dvd_card_ker_mul_card_target red5
  rw [hker5, hJ5] at h5raw
  have h5 : Fintype.card JQ ∣
      Fintype.card ReducedDegreeTwoClassCertificateF5 * 5 ^ a := by
    rw [card_reducedDegreeTwoClassCertificateF5]
    simpa only [Nat.card_eq_fintype_card, mul_comm] using h5raw
  have h7raw := natCard_dvd_card_ker_mul_card_target red7
  rw [hker7, hJ7] at h7raw
  have h7 : Fintype.card JQ ∣
      Fintype.card ReducedDegreeTwoClassCertificateF7 * 7 ^ b := by
    rw [card_reducedDegreeTwoClassCertificateF7]
    simpa only [Nat.card_eq_fintype_card, mul_comm] using h7raw
  exact rationalJacobian_card_eq_twentyOne_of_two_reduction_bounds
    a b h5 h7 h21

end MazurTorsion.XOneEighteenFiniteField
