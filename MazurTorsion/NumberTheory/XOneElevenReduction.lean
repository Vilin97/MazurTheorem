/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime
import MazurTorsion.Kubert.OrderElevenModel

/-!
# Conditional rational-point classification on `X₁(11)`

The selected model is

`v² + v = u³ - u²`.

It has good reduction at three, and its reduced point group has exactly
five elements.  Reduction is injective on a finite rational point group.
Consequently, under the explicit hypothesis

`[Finite curve.toAffine.Point]`,

the five visible rational points exhaust the group: the point at infinity
and the four affine points with `u = 0` or `u = 1` and `v = 0` or `v = -1`.

This file deliberately does not manufacture the finiteness hypothesis.
Proving Mordell--Weil rank zero (or otherwise proving
`Finite curve.toAffine.Point`) is the remaining unconditional boundary.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneEleven

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

instance : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

/-- The integral model used for reduction at three. -/
def integralCurve : WeierstrassCurve ℤ :=
  ⟨0, -1, 1, 0, 0⟩

lemma map_integralCurve :
    (integralCurve.map (algebraMap ℤ ℚ)).toAffine =
      curve.toAffine := by
  ext <;> simp [integralCurve, curve]

lemma discriminant_integralCurve :
    integralCurve.Δ = -11 := by
  norm_num [integralCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The height-one prime `(p)` of `ℤ`. -/
def intPrime (p : ℕ) [Fact p.Prime] :
    HeightOneSpectrum ℤ :=
  .ofPrime (p := Ideal.span {(p : ℤ)})
    (Ideal.prime_span_singleton_iff.mpr
      (Nat.prime_iff_prime_int.mp Fact.out))

@[simp] lemma intPrime_asIdeal (p : ℕ) [Fact p.Prime] :
    (intPrime p).asIdeal = Ideal.span {(p : ℤ)} :=
  rfl

instance (p : ℕ) [Fact p.Prime] :
    DecidableEq (ℤ ⧸ (intPrime p).asIdeal) :=
  (Int.quotientSpanNatEquivZMod p).toEquiv.decidableEq

lemma isElliptic_redCurve {p : ℕ} [Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ integralCurve.Δ) :
    (redCurve (intPrime p) integralCurve).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (integralCurve.map
      (algebraMap ℤ
        (ℤ ⧸ (intPrime p).asIdeal))).Δ ≠ 0
  rwa [Ne, WeierstrassCurve.map_Δ,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    intPrime_asIdeal, Ideal.mem_span_singleton]

instance :
    (redCurve (intPrime 3) integralCurve).IsElliptic :=
  isElliptic_redCurve
    (by norm_num [discriminant_integralCurve])

/-- The integral model has good reduction at three. -/
theorem good_reduction_at_three :
    (redCurve (intPrime 3) integralCurve).IsElliptic :=
  inferInstance

/-- The concrete reduction over `ZMod 3`. -/
def curveModThree : WeierstrassCurve (ZMod 3) :=
  ⟨0, -1, 1, 0, 0⟩

instance : curveModThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

noncomputable def residueThreeAlgEquiv :
    (ℤ ⧸ (intPrime 3).asIdeal) ≃ₐ[ℤ] ZMod 3 :=
  AlgEquiv.ofRingEquiv
    (f := Int.quotientSpanNatEquivZMod 3) fun x ↦ by
      simp only [algebraMap_int_eq, eq_intCast,
        map_intCast]

lemma baseChange_modThree :
    ((integralCurve.toAffine ⁄ (ZMod 3)) :
      WeierstrassCurve _).toAffine =
        curveModThree.toAffine := by
  ext <;> decide +kernel

/-- Identification of the abstract residue-field point group with the
computable `ZMod 3` point group. -/
noncomputable def reducedPointEquiv :
    (redCurve (intPrime 3) integralCurve).Point ≃+
      curveModThree.toAffine.Point :=
  (Point.mapEquiv (W' := integralCurve.toAffine)
      residueThreeAlgEquiv).trans
    (Point.congr baseChange_modThree)

noncomputable instance :
    Finite (redCurve (intPrime 3) integralCurve).Point :=
  .of_equiv curveModThree.toAffine.Point
    reducedPointEquiv.symm.toEquiv

/-- The reduction modulo three has exactly five points. -/
theorem card_reducedCurve :
    Nat.card
      (redCurve (intPrime 3) integralCurve).Point = 5 := by
  calc
    Nat.card
        (redCurve (intPrime 3) integralCurve).Point =
        Fintype.card curveModThree.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 5 := by decide

lemma three_mem_prime :
    (3 : ℤ) ∈ (intPrime 3).asIdeal :=
  Ideal.mem_span_singleton_self 3

lemma three_not_mem_prime_pow_two :
    (3 : ℤ) ∉ (intPrime 3).asIdeal ^ (3 - 1) := by
  rw [intPrime_asIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  norm_num

/-- Reduction at three is injective whenever the rational point group is
finite.  Finiteness is an explicit input, not a conclusion of this file. -/
theorem reduction_injective
    [Finite curve.toAffine.Point] :
    Function.Injective
      (redHom (intPrime 3) map_integralCurve) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero
    (intPrime 3) map_integralCurve
    (by norm_num) three_mem_prime
    three_not_mem_prime_pow_two
    (isOfFinAddOrder_of_finite (P - Q))
  change
    redHom (intPrime 3) map_integralCurve (P - Q) = 0
  rw [map_sub, hPQ, sub_self]

/-- Under the explicit finiteness hypothesis, the rational point group
has at most five elements. -/
theorem point_card_le_five
    [Finite curve.toAffine.Point] :
    Nat.card curve.toAffine.Point ≤ 5 := by
  calc
    Nat.card curve.toAffine.Point ≤
        Nat.card
          (redCurve (intPrime 3) integralCurve).Point :=
      Nat.card_le_card_of_injective
        (redHom (intPrime 3) map_integralCurve)
        reduction_injective
    _ = 5 := card_reducedCurve

private lemma nonsingular_zero_zero :
    curve.toAffine.Nonsingular 0 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff,
    curve]

private lemma nonsingular_zero_neg_one :
    curve.toAffine.Nonsingular 0 (-1) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff,
    curve]

private lemma nonsingular_one_zero :
    curve.toAffine.Nonsingular 1 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff,
    curve]

private lemma nonsingular_one_neg_one :
    curve.toAffine.Nonsingular 1 (-1) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff,
    curve]

/-- The rational point `(0,0)`. -/
def P00 : curve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

/-- The rational point `(0,-1)`. -/
def P0n1 : curve.toAffine.Point :=
  .some 0 (-1) nonsingular_zero_neg_one

/-- The rational point `(1,0)`. -/
def P10 : curve.toAffine.Point :=
  .some 1 0 nonsingular_one_zero

/-- The rational point `(1,-1)`. -/
def P1n1 : curve.toAffine.Point :=
  .some 1 (-1) nonsingular_one_neg_one

/-- The point at infinity and the four visible affine rational points. -/
def fiveVisiblePoints : Fin 5 → curve.toAffine.Point
  | 0 => 0
  | 1 => P00
  | 2 => P0n1
  | 3 => P10
  | 4 => P1n1

theorem fiveVisiblePoints_injective :
    Function.Injective fiveVisiblePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [fiveVisiblePoints, P00, P0n1, P10, P1n1]
      at hij ⊢

/-- Under the explicit finiteness hypothesis, the five visible points
exhaust the rational point group. -/
theorem fiveVisiblePoints_bijective
    [Finite curve.toAffine.Point] :
    Function.Bijective fiveVisiblePoints := by
  exact
    fiveVisiblePoints_injective.bijective_of_nat_card_le
      (by simpa using point_card_le_five)

/-- Under the explicit finiteness hypothesis, the rational point group
has exactly five elements. -/
theorem point_card_eq_five
    [Finite curve.toAffine.Point] :
    Nat.card curve.toAffine.Point = 5 := by
  apply le_antisymm point_card_le_five
  have hle :=
    Nat.card_le_card_of_injective
      fiveVisiblePoints fiveVisiblePoints_injective
  simpa using hle

/-- Under the explicit finiteness hypothesis, every affine rational point
has abscissa zero or one. -/
theorem point_abscissa_eq_zero_or_one
    [Finite curve.toAffine.Point]
    {U V : ℚ}
    (hP : curve.toAffine.Nonsingular U V) :
    U = 0 ∨ U = 1 := by
  let P : curve.toAffine.Point := .some U V hP
  obtain ⟨i, hi⟩ :=
    fiveVisiblePoints_bijective.2 P
  fin_cases i
  · have hzero : P ≠ 0 :=
      Point.some_ne_zero hP
    exact
      (hzero (by
        simpa only [fiveVisiblePoints] using hi.symm)).elim
  · left
    have hcoords : (0 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [fiveVisiblePoints, P00, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm
  · left
    have hcoords :
        (0 : ℚ) = U ∧ (-1 : ℚ) = V := by
      simpa only [fiveVisiblePoints, P0n1, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm
  · right
    have hcoords : (1 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [fiveVisiblePoints, P10, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm
  · right
    have hcoords :
        (1 : ℚ) = U ∧ (-1 : ℚ) = V := by
      simpa only [fiveVisiblePoints, P1n1, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm

/-- Proposition-level restatement that makes the sole remaining boundary
explicit: finiteness of the rational point group implies the complete
five-point classification. -/
theorem finite_implies_five_point_classification
    (hfinite : Finite curve.toAffine.Point) :
    Nat.card curve.toAffine.Point = 5 ∧
      ∀ {U V : ℚ},
        curve.toAffine.Nonsingular U V →
          U = 0 ∨ U = 1 := by
  letI := hfinite
  exact
    ⟨point_card_eq_five,
      fun hP ↦ point_abscissa_eq_zero_or_one hP⟩

end MazurTorsion.XOneEleven
