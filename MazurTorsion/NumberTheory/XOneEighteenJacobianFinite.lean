/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenFiniteField

/-!
# The finite Jacobian certificate for `X₁(18)` at five

The checked reduction of the order-eighteen sextic has six points over
`𝔽₅`.  This file enumerates the same curve over the transparent quadratic
field presentation `𝔽₂₅ = 𝔽₅[ω]/(ω²-2)` and obtains sixteen points.

The twenty-six Frobenius-stable effective divisors of degree two consist of
twenty-one unordered pairs of rational points and five quadratic orbits.
Collapsing the six members of the hyperelliptic pencil leaves twenty-one
reduced degree-two labels, in agreement with

`#J(𝔽₅) = (#C(𝔽₅)² + #C(𝔽₂₅))/2 - 5 = 21`.

The resulting type is deliberately a finite combinatorial certificate, not
a definition of the Picard group.  The final theorem below is the named
consumer expected from a future geometric equivalence with the finite
degree-zero Picard group.
-/

namespace MazurTorsion.XOneEighteenFiniteField

/-! ## A transparent presentation of `𝔽₂₅` -/

/-- A pair presentation of a quadratic algebra over `ZMod n`. -/
abbrev QuadraticPair (n : ℕ) := ZMod n × ZMod n

/-- Zero in the quadratic-pair presentation. -/
def quadraticPairZero {n : ℕ} : QuadraticPair n :=
  (0, 0)

/-- One in the quadratic-pair presentation. -/
def quadraticPairOne {n : ℕ} : QuadraticPair n :=
  (1, 0)

/-- Addition in the quadratic-pair presentation. -/
def quadraticPairAdd {n : ℕ}
    (u v : QuadraticPair n) : QuadraticPair n :=
  (u.1 + v.1, u.2 + v.2)

/-- Multiplication with the relation `ω² = d`. -/
def quadraticPairMul {n : ℕ} (d : ZMod n)
    (u v : QuadraticPair n) : QuadraticPair n :=
  (u.1 * v.1 + d * u.2 * v.2,
    u.1 * v.2 + u.2 * v.1)

/-- Natural-number scalar multiplication in the pair presentation. -/
def quadraticPairNatScale {n : ℕ} (a : ℕ)
    (u : QuadraticPair n) : QuadraticPair n :=
  ((a : ZMod n) * u.1, (a : ZMod n) * u.2)

/-- Powers in the quadratic-pair presentation. -/
def quadraticPairPow {n : ℕ} (d : ZMod n)
    (u : QuadraticPair n) : ℕ → QuadraticPair n
  | 0 => quadraticPairOne
  | k + 1 => quadraticPairMul d (quadraticPairPow d u k) u

/-- The reduced order-eighteen sextic evaluated in the quadratic-pair
presentation. -/
def quadraticPairSexticValue {n : ℕ} (d : ZMod n)
    (x : QuadraticPair n) : QuadraticPair n :=
  quadraticPairAdd (quadraticPairPow d x 6)
    (quadraticPairAdd (quadraticPairPow d x 5)
      (quadraticPairAdd (quadraticPairNatScale 3 x)
        quadraticPairOne))

/-- An affine solution in the quadratic-pair presentation. -/
def QuadraticAffineSolution (n : ℕ) (d : ZMod n) :=
  {p : QuadraticPair n × QuadraticPair n //
    quadraticPairMul d p.2 p.2 = quadraticPairSexticValue d p.1}

/-- A normalized infinity direction in the quadratic-pair presentation. -/
def QuadraticInfinityDirection (n : ℕ) (d : ZMod n) :=
  {η : QuadraticPair n //
    quadraticPairMul d η η = quadraticPairOne}

/-- The pair presentation of `𝔽₂₅`, with `ω² = 2`. -/
abbrev F25Pair := QuadraticPair 5

/-- Two is not a square in `𝔽₅`. -/
theorem two_not_square_F5 :
    ∀ a : F5, a ^ 2 ≠ 2 := by
  decide

/-- Every nonzero pair has a multiplicative inverse.  Together with the
nonsquare certificate this verifies that the displayed algebra is the
twenty-five-element field. -/
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

/-- There are fourteen affine solutions over the checked `𝔽₂₅`
presentation. -/
theorem card_affineSolutionF25 :
    Fintype.card (QuadraticAffineSolution 5 (2 : F5)) = 14 := by
  decide

/-- There are two normalized infinity directions over `𝔽₂₅`. -/
theorem card_infinityDirectionF25 :
    Fintype.card (QuadraticInfinityDirection 5 (2 : F5)) = 2 := by
  decide

/-- The complete point certificate over `𝔽₂₅`. -/
def PointCertificateF25 :=
  QuadraticAffineSolution 5 (2 : F5) ⊕
    QuadraticInfinityDirection 5 (2 : F5)

instance : Fintype PointCertificateF25 := by
  unfold PointCertificateF25
  infer_instance

/-- The order-eighteen curve has sixteen points in the checked `𝔽₂₅`
presentation. -/
theorem card_pointCertificateF25 :
    Fintype.card PointCertificateF25 = 16 := by
  change Fintype.card
    (QuadraticAffineSolution 5 (2 : F5) ⊕
      QuadraticInfinityDirection 5 (2 : F5)) = 16
  rw [Fintype.card_sum, card_affineSolutionF25,
    card_infinityDirectionF25]

/-- Conjugation in the quadratic-pair presentation. -/
def quadraticPairConjugate {n : ℕ}
    (u : QuadraticPair n) : QuadraticPair n :=
  (u.1, -u.2)

/-- Fifth powering in the checked field presentation is Frobenius
conjugation. -/
theorem quadraticPairPow_five_eq_conjugate_F25 :
    ∀ u : F25Pair,
      quadraticPairPow (2 : F5) u 5 = quadraticPairConjugate u := by
  decide

/-- A quadratic affine solution not defined over the base field. -/
def IsNonBaseQuadraticAffineSolution
    (P : QuadraticAffineSolution 5 (2 : F5)) : Prop :=
  P.1.1.2 ≠ 0 ∨ P.1.2.2 ≠ 0

instance (P : QuadraticAffineSolution 5 (2 : F5)) :
    Decidable (IsNonBaseQuadraticAffineSolution P) := by
  unfold IsNonBaseQuadraticAffineSolution
  infer_instance

/-- Exactly ten affine points are genuinely quadratic. -/
theorem card_nonBaseAffineSolutionF25 :
    Fintype.card {P : QuadraticAffineSolution 5 (2 : F5) //
      IsNonBaseQuadraticAffineSolution P} = 10 := by
  decide

/-! ## The five quadratic Frobenius orbits -/

/-- A canonical representative of each non-base Frobenius orbit.  The first
three representatives are the quadratic hyperelliptic fibers above
`x = 2,3,4`; the last two have genuinely quadratic abscissas. -/
def IsQuadraticClosedPointRepresentative
    (P : QuadraticAffineSolution 5 (2 : F5)) : Prop :=
  P.1 = (((2, 0) : F25Pair), ((0, 2) : F25Pair)) ∨
  P.1 = (((3, 0) : F25Pair), ((0, 1) : F25Pair)) ∨
  P.1 = (((4, 0) : F25Pair), ((0, 2) : F25Pair)) ∨
  P.1 = (((3, 2) : F25Pair), ((1, 2) : F25Pair)) ∨
  P.1 = (((3, 2) : F25Pair), ((4, 3) : F25Pair))

instance (P : QuadraticAffineSolution 5 (2 : F5)) :
    Decidable (IsQuadraticClosedPointRepresentative P) := by
  unfold IsQuadraticClosedPointRepresentative
  infer_instance

/-- The five selected orbit representatives. -/
def QuadraticClosedPointRepresentative :=
  {P : QuadraticAffineSolution 5 (2 : F5) //
    IsQuadraticClosedPointRepresentative P}

instance : Fintype QuadraticClosedPointRepresentative := by
  unfold QuadraticClosedPointRepresentative
  infer_instance

/-- There are five quadratic closed-point representatives. -/
theorem card_quadraticClosedPointRepresentative :
    Fintype.card QuadraticClosedPointRepresentative = 5 := by
  decide

/-- Every non-base affine point is one of the selected representatives or
its Frobenius conjugate. -/
theorem quadraticClosedPointRepresentative_complete :
    ∀ P : QuadraticAffineSolution 5 (2 : F5),
      IsNonBaseQuadraticAffineSolution P →
        ∃ Q : QuadraticClosedPointRepresentative,
          P.1 = Q.1.1 ∨
            P.1 = (quadraticPairConjugate Q.1.1.1,
              quadraticPairConjugate Q.1.1.2) := by
  decide

/-- A selected quadratic orbit belongs to the hyperelliptic pencil exactly
when its abscissa is fixed by Frobenius. -/
def IsQuadraticHyperellipticOrbit
    (Q : QuadraticClosedPointRepresentative) : Prop :=
  Q.1.1.1.2 = 0

instance (Q : QuadraticClosedPointRepresentative) :
    Decidable (IsQuadraticHyperellipticOrbit Q) := by
  unfold IsQuadraticHyperellipticOrbit
  infer_instance

/-- Three of the five quadratic orbits are hyperelliptic fibers. -/
theorem card_quadraticHyperellipticOrbit :
    Fintype.card {Q : QuadraticClosedPointRepresentative //
      IsQuadraticHyperellipticOrbit Q} = 3 := by
  decide

/-! ## Rational pairs and reduced degree-two labels -/

/-- Labels for the six points in the base-field certificate. -/
inductive RationalPointLabel
  | zeroPos
  | zeroNeg
  | onePos
  | oneNeg
  | infinityPos
  | infinityNeg
  deriving DecidableEq

instance : Fintype RationalPointLabel where
  elems := {.zeroPos, .zeroNeg, .onePos, .oneNeg,
    .infinityPos, .infinityNeg}
  complete x := by cases x <;> simp

/-- An index used to choose one ordering of a rational point pair. -/
def rationalPointLabelIndex : RationalPointLabel → Fin 6
  | .zeroPos => 0
  | .zeroNeg => 1
  | .onePos => 2
  | .oneNeg => 3
  | .infinityPos => 4
  | .infinityNeg => 5

/-- The hyperelliptic involution on rational point labels. -/
def rationalPointConjugate : RationalPointLabel → RationalPointLabel
  | .zeroPos => .zeroNeg
  | .zeroNeg => .zeroPos
  | .onePos => .oneNeg
  | .oneNeg => .onePos
  | .infinityPos => .infinityNeg
  | .infinityNeg => .infinityPos

/-- A rational label interpreted in the existing six-point certificate. -/
def rationalPointLabelPointF5 : RationalPointLabel → PointCertificate
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .onePos => .inl ⟨(1, 1), by decide⟩
  | .oneNeg => .inl ⟨(1, -1), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- A computational inverse to the rational point labeling. -/
def pointCertificateLabelF5 : PointCertificate → RationalPointLabel
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.2 = 1 then .onePos else .oneNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The computational inverse recovers every rational label. -/
theorem pointCertificateLabelF5_leftInverse :
    Function.LeftInverse pointCertificateLabelF5
      rationalPointLabelPointF5 := by
  intro c
  cases c <;> decide

/-- The six labels enumerate the complete base-field point certificate. -/
theorem rationalPointLabelPointF5_bijective :
    Function.Bijective rationalPointLabelPointF5 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointCertificateLabelF5_leftInverse.injective
  · rw [card_pointCertificate]
    decide

/-- An unordered pair of rational points, represented in increasing label
order. -/
def UnorderedRationalPointPair :=
  {p : RationalPointLabel × RationalPointLabel //
    (rationalPointLabelIndex p.1 : ℕ) ≤
      (rationalPointLabelIndex p.2 : ℕ)}

instance : Fintype UnorderedRationalPointPair := by
  unfold UnorderedRationalPointPair
  infer_instance

/-- Six rational points have twenty-one unordered pairs with repetition. -/
theorem card_unorderedRationalPointPair :
    Fintype.card UnorderedRationalPointPair = 21 := by
  decide

/-- A rational pair is a member of the hyperelliptic pencil. -/
def IsRationalHyperellipticPair
    (p : UnorderedRationalPointPair) : Prop :=
  p.1.2 = rationalPointConjugate p.1.1

instance (p : UnorderedRationalPointPair) :
    Decidable (IsRationalHyperellipticPair p) := by
  unfold IsRationalHyperellipticPair
  infer_instance

/-- Exactly three unordered rational pairs are hyperelliptic fibers. -/
theorem card_rationalHyperellipticPair :
    Fintype.card {p : UnorderedRationalPointPair //
      IsRationalHyperellipticPair p} = 3 := by
  decide

/-- Degree-two effective-divisor labels: either an unordered pair of
base-field points or one of the five quadratic Frobenius orbits. -/
def DegreeTwoDivisorCertificateF5 :=
  UnorderedRationalPointPair ⊕ QuadraticClosedPointRepresentative

instance : Fintype DegreeTwoDivisorCertificateF5 := by
  unfold DegreeTwoDivisorCertificateF5
  infer_instance

/-- There are twenty-six Frobenius-stable effective degree-two labels. -/
theorem card_degreeTwoDivisorCertificateF5 :
    Fintype.card DegreeTwoDivisorCertificateF5 = 26 := by
  change Fintype.card
    (UnorderedRationalPointPair ⊕
      QuadraticClosedPointRepresentative) = 26
  rw [Fintype.card_sum, card_unorderedRationalPointPair,
    card_quadraticClosedPointRepresentative]

/-- The six labels belonging to the complete hyperelliptic pencil. -/
def IsCanonicalDegreeTwoF5 : DegreeTwoDivisorCertificateF5 → Prop
  | .inl p => IsRationalHyperellipticPair p
  | .inr Q => IsQuadraticHyperellipticOrbit Q

instance (D : DegreeTwoDivisorCertificateF5) :
    Decidable (IsCanonicalDegreeTwoF5 D) := by
  cases D with
  | inl p =>
      change Decidable (IsRationalHyperellipticPair p)
      exact inferInstance
  | inr Q =>
      change Decidable (IsQuadraticHyperellipticOrbit Q)
      exact inferInstance

/-- The hyperelliptic pencil has six labels over `𝔽₅`. -/
theorem card_canonicalDegreeTwoF5 :
    Fintype.card {D : DegreeTwoDivisorCertificateF5 //
      IsCanonicalDegreeTwoF5 D} = 6 := by
  decide

/-- Retain every noncanonical degree-two label and collapse the complete
hyperelliptic pencil to one distinguished label.

This is a combinatorial certificate, not a definition of the Jacobian. -/
def ReducedDegreeTwoClassCertificateF5 :=
  {D : DegreeTwoDivisorCertificateF5 // ¬ IsCanonicalDegreeTwoF5 D} ⊕ Unit

instance : Fintype ReducedDegreeTwoClassCertificateF5 := by
  unfold ReducedDegreeTwoClassCertificateF5
  infer_instance

/-- The reduced degree-two class certificate has twenty-one elements. -/
theorem card_reducedDegreeTwoClassCertificateF5 :
    Fintype.card ReducedDegreeTwoClassCertificateF5 = 21 := by
  decide

/-- The checked point counts give the expected genus-two Jacobian order
twenty-one through the standard numerical formula. -/
theorem jacobianOrderFormulaInputF5 :
    (Fintype.card PointCertificate ^ 2 +
        Fintype.card PointCertificateF25) / 2 - 5 = 21 := by
  rw [card_pointCertificate, card_pointCertificateF25]
  norm_num

/-- Named downstream consumer: once a geometric finite Picard group is
identified with the reduced certificate, its cardinality is exactly
twenty-one. -/
theorem finitePicard_card_eq_twentyOne_of_reducedDegreeTwoEquiv
    {J5 : Type*} [Fintype J5]
    (e : J5 ≃ ReducedDegreeTwoClassCertificateF5) :
    Fintype.card J5 = 21 := by
  rw [Fintype.card_congr e,
    card_reducedDegreeTwoClassCertificateF5]

end MazurTorsion.XOneEighteenFiniteField
