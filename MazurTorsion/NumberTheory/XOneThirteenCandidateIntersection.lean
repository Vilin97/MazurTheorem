/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenFiniteField
import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit

/-!
# A finite two-prime candidate certificate for `X₁(13)`

This file gives a small, fully enumerated certificate for the finite step
which occurs after a rational Jacobian has been identified with a cyclic
group of order `19` and its coordinates have been aligned at the good primes
`3` and `5`.

The six reduced curve points are labelled by their rational cusp names and
assigned the cyclic coordinates

`1, -1, 7, -7, 8, -8 : ZMod 19`.

Unordered pairs of those labels give twenty-one degree-two labels.  Removing
the three hyperelliptic pairs and adjoining the collapsed canonical pencil
gives nineteen candidate class labels.  The displayed coordinate is checked
to be a bijection with `ZMod 19`.  Direct finite enumeration then proves that
exactly six of the nineteen candidates can be represented by a curve point
at both primes.

This is deliberately a fixed certificate, not a generic Mumford
representation and not an assertion that the certificate type is a
geometric Jacobian.  The final theorem is phrased as a consumer: once genuine
reduction maps supply the two coordinate equalities, it returns the explicit
cuspidal coordinate.
-/

namespace MazurTorsion.XOneThirteenCandidateIntersection

open Polynomial
open MazurTorsion.XOneThirteenFiniteField

/-! ## The second reduced curve -/

/-- The five-element residue field used for the second point certificate. -/
abbrev F5 := ZMod 5

/-- The order-thirteen sextic evaluated modulo `5`. -/
def sexticValueF5 (x : F5) : F5 :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

/-- An affine solution of the reduced equation over `𝔽₅`. -/
def AffineSolutionF5 :=
  {p : F5 × F5 // p.2 ^ 2 = sexticValueF5 p.1}

instance : Fintype AffineSolutionF5 := by
  unfold AffineSolutionF5
  infer_instance

/-- Complete affine enumeration over `𝔽₅`. -/
theorem affine_solution_F5_iff :
    ∀ x y : F5,
      y ^ 2 = sexticValueF5 x ↔
        (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = -1 ∧ (y = 1 ∨ y = -1)) := by
  decide

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

/-- The complete six-element point certificate over `𝔽₅`. -/
def PointCertificateF5 :=
  AffineSolutionF5 ⊕ InfinityDirectionF5

instance : Fintype PointCertificateF5 := by
  unfold PointCertificateF5
  infer_instance

/-- The affine enumeration and infinity chart give six points over `𝔽₅`. -/
theorem card_pointCertificateF5 :
    Fintype.card PointCertificateF5 = 6 := by
  change Fintype.card (AffineSolutionF5 ⊕ InfinityDirectionF5) = 6
  rw [Fintype.card_sum, card_affineSolutionF5,
    card_infinityDirectionF5]

/-! ## Six compatible cusp labels -/

/-- Labels for the six rational cusps in either good reduction. -/
inductive CuspLabel
  | zeroPos
  | zeroNeg
  | negOnePos
  | negOneNeg
  | infinityPos
  | infinityNeg
  deriving DecidableEq

instance : Fintype CuspLabel where
  elems := {.zeroPos, .zeroNeg, .negOnePos, .negOneNeg,
    .infinityPos, .infinityNeg}
  complete x := by cases x <;> simp

/-- An index used to select a unique representative of an unordered pair. -/
def cuspLabelIndex : CuspLabel → Fin 6
  | .zeroPos => 0
  | .zeroNeg => 1
  | .negOnePos => 2
  | .negOneNeg => 3
  | .infinityPos => 4
  | .infinityNeg => 5

/-- Hyperelliptic conjugation on the six labels. -/
def cuspConjugate : CuspLabel → CuspLabel
  | .zeroPos => .zeroNeg
  | .zeroNeg => .zeroPos
  | .negOnePos => .negOneNeg
  | .negOneNeg => .negOnePos
  | .infinityPos => .infinityNeg
  | .infinityNeg => .infinityPos

/-- The aligned cyclic coordinate of each rational cusp. -/
def cuspCoordinate : CuspLabel → ZMod 19
  | .zeroPos => 1
  | .zeroNeg => -1
  | .negOnePos => 7
  | .negOneNeg => -7
  | .infinityPos => 8
  | .infinityNeg => -8

/-- Conjugate cusp labels have opposite cyclic coordinates. -/
theorem cuspCoordinate_conjugate :
    ∀ c : CuspLabel,
      cuspCoordinate (cuspConjugate c) = -cuspCoordinate c := by
  intro c
  cases c <;> decide

/-- Interpret a cusp label in the checked point certificate over `𝔽₃`. -/
def cuspPointF3 : CuspLabel → PointCertificate
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .negOnePos => .inl ⟨(-1, 1), by decide⟩
  | .negOneNeg => .inl ⟨(-1, -1), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- Interpret a cusp label in the checked point certificate over `𝔽₅`. -/
def cuspPointF5 : CuspLabel → PointCertificateF5
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .negOnePos => .inl ⟨(-1, 1), by decide⟩
  | .negOneNeg => .inl ⟨(-1, -1), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- A computational inverse label for the point certificate at `3`. -/
def pointLabelF3 : PointCertificate → CuspLabel
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.2 = 1 then .negOnePos else .negOneNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The inverse label recovers each cusp label at `3`. -/
theorem pointLabelF3_leftInverse :
    Function.LeftInverse pointLabelF3 cuspPointF3 := by
  intro c
  cases c <;> decide

/-- The labels enumerate the complete point certificate at `3`. -/
theorem cuspPointF3_bijective :
    Function.Bijective cuspPointF3 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointLabelF3_leftInverse.injective
  · rw [card_pointCertificate]
    decide

/-- A computational inverse label for the point certificate at `5`. -/
def pointLabelF5 : PointCertificateF5 → CuspLabel
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.2 = 1 then .negOnePos else .negOneNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The inverse label recovers each cusp label at `5`. -/
theorem pointLabelF5_leftInverse :
    Function.LeftInverse pointLabelF5 cuspPointF5 := by
  intro c
  cases c <;> decide

/-- The labels enumerate the complete point certificate at `5`. -/
theorem cuspPointF5_bijective :
    Function.Bijective cuspPointF5 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointLabelF5_leftInverse.injective
  · rw [card_pointCertificateF5]
    decide

/-- Cyclic coordinate of a checked curve point at `3`. -/
def pointCoordinateF3
    (P : PointCertificate) : ZMod 19 :=
  cuspCoordinate (pointLabelF3 P)

/-- Cyclic coordinate of a checked curve point at `5`. -/
def pointCoordinateF5
    (P : PointCertificateF5) : ZMod 19 :=
  cuspCoordinate (pointLabelF5 P)

/-! ## The nineteen fixed candidate classes -/

/-- An unordered pair of cusp labels, represented in increasing order. -/
def UnorderedCuspPair :=
  {p : CuspLabel × CuspLabel //
    (cuspLabelIndex p.1 : ℕ) ≤ (cuspLabelIndex p.2 : ℕ)}

instance : Fintype UnorderedCuspPair := by
  unfold UnorderedCuspPair
  infer_instance

/-- The twenty-one unordered degree-two labels on six points. -/
theorem card_unorderedCuspPair :
    Fintype.card UnorderedCuspPair = 21 := by
  decide

/-- A pair belonging to the hyperelliptic pencil. -/
def IsHyperellipticPair (p : UnorderedCuspPair) : Prop :=
  p.1.2 = cuspConjugate p.1.1

instance (p : UnorderedCuspPair) : Decidable (IsHyperellipticPair p) :=
  inferInstanceAs (Decidable (p.1.2 = cuspConjugate p.1.1))

/-- Exactly three unordered cusp pairs are hyperelliptic fibers. -/
theorem card_hyperellipticPair :
    Fintype.card {p : UnorderedCuspPair // IsHyperellipticPair p} = 3 := by
  decide

/-- The fixed candidate class set: eighteen noncanonical cusp pairs and the
collapsed hyperelliptic pencil. -/
def CandidateDivisorClass :=
  {p : UnorderedCuspPair // ¬IsHyperellipticPair p} ⊕ Unit

instance : Fintype CandidateDivisorClass := by
  unfold CandidateDivisorClass
  infer_instance

/-- There are exactly nineteen fixed candidate classes. -/
theorem card_candidateDivisorClass :
    Fintype.card CandidateDivisorClass = 19 := by
  decide

/-- Cyclic coordinate of a fixed candidate class. -/
def candidateCoordinate : CandidateDivisorClass → ZMod 19
  | .inl p => cuspCoordinate p.1.1.1 + cuspCoordinate p.1.1.2
  | .inr _ => 0

/-- The explicit coordinate enumerates every residue modulo `19` exactly
once. -/
theorem candidateCoordinate_bijective :
    Function.Bijective candidateCoordinate := by
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact (by decide :
      ∀ z : ZMod 19,
        ∃ D : CandidateDivisorClass, candidateCoordinate D = z)
  · rw [card_candidateDivisorClass, ZMod.card]

/-- A candidate has a representative among the reduced curve points at
`3`. -/
def SurvivesAtThree (D : CandidateDivisorClass) : Prop :=
  ∃ P : PointCertificate,
    candidateCoordinate D = pointCoordinateF3 P

/-- A candidate has a representative among the reduced curve points at
`5`. -/
def SurvivesAtFive (D : CandidateDivisorClass) : Prop :=
  ∃ P : PointCertificateF5,
    candidateCoordinate D = pointCoordinateF5 P

/-- A candidate has one of the six aligned rational-cusp coordinates. -/
def IsCuspidalCandidate (D : CandidateDivisorClass) : Prop :=
  ∃ c : CuspLabel, candidateCoordinate D = cuspCoordinate c

/- The three finite predicates are decidable by their explicit finite
presentations. -/
instance (D : CandidateDivisorClass) :
    Decidable (SurvivesAtThree D) := by
  unfold SurvivesAtThree
  infer_instance

instance (D : CandidateDivisorClass) :
    Decidable (SurvivesAtFive D) := by
  unfold SurvivesAtFive
  infer_instance

instance (D : CandidateDivisorClass) :
    Decidable (IsCuspidalCandidate D) := by
  unfold IsCuspidalCandidate
  infer_instance

/-- Expanded form of the six allowed cyclic coordinates. -/
theorem isCuspidalCandidate_iff_coordinate
    (D : CandidateDivisorClass) :
    IsCuspidalCandidate D ↔
      candidateCoordinate D = 1 ∨
      candidateCoordinate D = -1 ∨
      candidateCoordinate D = 7 ∨
      candidateCoordinate D = -7 ∨
      candidateCoordinate D = 8 ∨
      candidateCoordinate D = -8 := by
  unfold IsCuspidalCandidate
  constructor
  · rintro ⟨c, hc⟩
    cases c <;> simp_all [cuspCoordinate]
  · intro h
    rcases h with h | h | h | h | h | h
    · exact ⟨.zeroPos, h⟩
    · exact ⟨.zeroNeg, h⟩
    · exact ⟨.negOnePos, h⟩
    · exact ⟨.negOneNeg, h⟩
    · exact ⟨.infinityPos, h⟩
    · exact ⟨.infinityNeg, h⟩

/-- The fixed curve/class intersection certificate: a class survives as a
curve point at both aligned good reductions exactly when it is one of the
six cuspidal candidates. -/
theorem survives_two_reductions_iff_cuspidal
    (D : CandidateDivisorClass) :
    SurvivesAtThree D ∧ SurvivesAtFive D ↔ IsCuspidalCandidate D := by
  simp only [SurvivesAtThree, SurvivesAtFive, IsCuspidalCandidate,
    pointCoordinateF3, pointCoordinateF5]
  constructor
  · rintro ⟨⟨P, hP⟩, -⟩
    exact ⟨pointLabelF3 P, hP⟩
  · rintro ⟨c, hc⟩
    refine ⟨⟨cuspPointF3 c, ?_⟩, ⟨cuspPointF5 c, ?_⟩⟩
    · rw [hc]
      rw [pointLabelF3_leftInverse c]
    · rw [hc]
      rw [pointLabelF5_leftInverse c]

/-- Exactly six of the nineteen candidate classes survive both curve
reductions. -/
theorem card_two_reduction_curve_intersection :
    Fintype.card {D : CandidateDivisorClass //
      SurvivesAtThree D ∧ SurvivesAtFive D} = 6 := by
  classical
  have hiff : ∀ D : CandidateDivisorClass,
      (SurvivesAtThree D ∧ SurvivesAtFive D) ↔
        IsCuspidalCandidate D :=
    survives_two_reductions_iff_cuspidal
  simp_rw [hiff]
  decide

/-- Downstream-facing consumer for genuine aligned reductions.  Once a
candidate class is identified with the coordinates of actual reduced curve
points at `3` and `5`, its coordinate is one of the six rational-cusp
coordinates. -/
theorem cusp_coordinate_of_aligned_reduction_witnesses
    (D : CandidateDivisorClass)
    (P3 : PointCertificate) (P5 : PointCertificateF5)
    (h3 : candidateCoordinate D = pointCoordinateF3 P3)
    (h5 : candidateCoordinate D = pointCoordinateF5 P5) :
    ∃ c : CuspLabel, candidateCoordinate D = cuspCoordinate c :=
  (survives_two_reductions_iff_cuspidal D).mp
    ⟨⟨P3, h3⟩, ⟨P5, h5⟩⟩

/-- Coordinate-level form of the downstream consumer. -/
theorem candidate_coordinate_of_aligned_reduction_witnesses
    (D : CandidateDivisorClass)
    (P3 : PointCertificate) (P5 : PointCertificateF5)
    (h3 : candidateCoordinate D = pointCoordinateF3 P3)
    (h5 : candidateCoordinate D = pointCoordinateF5 P5) :
    candidateCoordinate D = 1 ∨
      candidateCoordinate D = -1 ∨
      candidateCoordinate D = 7 ∨
      candidateCoordinate D = -7 ∨
      candidateCoordinate D = 8 ∨
      candidateCoordinate D = -8 :=
  (isCuspidalCandidate_iff_coordinate D).mp
    (cusp_coordinate_of_aligned_reduction_witnesses D P3 P5 h3 h5)

end MazurTorsion.XOneThirteenCandidateIntersection
