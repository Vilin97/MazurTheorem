/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalOrbit

/-!
# The noncuspidal open chart on the order-twenty-five canonical carrier

The five explicit cyclic functions on the canonical complete intersection
have denominators

`w`, `x - y`, `y + z - w`, `x`, and `z`.

This file proves that every nonzero rational point where one of these five
linear forms vanishes is one of the five displayed cusps.  The proof first
classifies the hyperplane `w = 0`; the checked order-five deck transformation
then transports that classification cyclically to the other four
hyperplanes.

Consequently a noncuspidal rational point automatically lies in the common
domain of all five cyclic functions.  A separate rational-root argument
excludes the value `1` for the first cyclic function.  The named downstream
consumer `orderTwentyFiveCanonical_lehmerRoots_of_noncuspidal` therefore
produces two roots of one Lehmer quintic without any additional denominator
or exceptional-value hypotheses.

This is still a statement about rational points on the explicit canonical
carrier.  Identifying that carrier with the marked modular quotient remains
a separate boundary.
-/

namespace MazurTorsion.Kubert

/-- A rational canonical representative lies on one of the five displayed
cusp rays. -/
def OrderTwentyFiveCanonicalCoordinates.IsCusp
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) : Prop :=
  ∃ i : Fin 5,
    OrderTwentyFiveCanonicalRepresentsCusp i p.x p.y p.z p.w

/-- A nonzero rational point on the canonical complete intersection which
does not lie on any of the five displayed cusp rays. -/
def OrderTwentyFiveCanonicalCoordinates.IsNoncuspidal
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) : Prop :=
  OrderTwentyFiveCanonicalCoordinatesNonzero p.x p.y p.z p.w ∧
    p.OnCurve ∧ ¬p.IsCusp

/-- The deck transformation carries each displayed cusp ray to another
displayed cusp ray. -/
theorem OrderTwentyFiveCanonicalCoordinates.IsCusp.deckTransform
    {p : OrderTwentyFiveCanonicalCoordinates ℚ} (h : p.IsCusp) :
    (orderTwentyFiveCanonicalDeckTransform p).IsCusp := by
  rcases h with ⟨i, a, ha, hx, hy, hz, hw⟩
  fin_cases i
  · refine ⟨1, -a, neg_ne_zero.mpr ha, ?_⟩
    norm_num [orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero] at hx hy hz hw
    change p.z = (-a) * 0 ∧ p.w - p.y = (-a) * (-1) ∧
      -p.w = (-a) * 1 ∧ p.x - p.y = (-a) * 0
    simp [hx, hy, hz, hw]
  · refine ⟨2, a, ha, ?_⟩
    norm_num [orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero] at hx hy hz hw
    change p.z = a * 1 ∧ p.w - p.y = a * 1 ∧
      -p.w = a * 0 ∧ p.x - p.y = a * 1
    simp [hx, hy, hz, hw]
  · refine ⟨3, -a, neg_ne_zero.mpr ha, ?_⟩
    norm_num [orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero] at hx hy hz hw
    change p.z = (-a) * 0 ∧ p.w - p.y = (-a) * 0 ∧
      -p.w = (-a) * 1 ∧ p.x - p.y = (-a) * 0
    simp [hx, hy, hz, hw]
  · refine ⟨4, a, ha, ?_⟩
    norm_num [orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero] at hx hy hz hw
    change p.z = a * 1 ∧ p.w - p.y = a * 0 ∧
      -p.w = a * 0 ∧ p.x - p.y = a * 0
    simp [hx, hy, hz, hw]
  · refine ⟨0, a, ha, ?_⟩
    norm_num [orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero] at hx hy hz hw
    change p.z = a * 0 ∧ p.w - p.y = a * 0 ∧
      -p.w = a * 0 ∧ p.x - p.y = a * 1
    simp [hx, hy, hz, hw]

/-- The invertible deck transformation preserves nonzeroness of a coordinate
representative. -/
theorem orderTwentyFiveCanonicalCoordinatesNonzero_deckTransform
    {p : OrderTwentyFiveCanonicalCoordinates ℚ}
    (h : OrderTwentyFiveCanonicalCoordinatesNonzero p.x p.y p.z p.w) :
    OrderTwentyFiveCanonicalCoordinatesNonzero
      (orderTwentyFiveCanonicalDeckTransform p).x
      (orderTwentyFiveCanonicalDeckTransform p).y
      (orderTwentyFiveCanonicalDeckTransform p).z
      (orderTwentyFiveCanonicalDeckTransform p).w := by
  by_contra hzero
  simp only [OrderTwentyFiveCanonicalCoordinatesNonzero,
    orderTwentyFiveCanonicalDeckTransform, not_or, not_not] at hzero
  rcases hzero with ⟨hz, hwy, hw, hxy⟩
  have hw0 : p.w = 0 := by linear_combination -hw
  have hy0 : p.y = 0 := by linear_combination hw0 - hwy
  have hx0 : p.x = 0 := by linear_combination hxy + hy0
  exact h.elim (fun hx ↦ hx hx0)
    (fun hy ↦ hy.elim (fun hy ↦ hy hy0)
      (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw0)))

/-- Noncuspidality is preserved by the order-five deck transformation. -/
theorem OrderTwentyFiveCanonicalCoordinates.IsNoncuspidal.deckTransform
    {p : OrderTwentyFiveCanonicalCoordinates ℚ} (h : p.IsNoncuspidal) :
    (orderTwentyFiveCanonicalDeckTransform p).IsNoncuspidal := by
  refine ⟨
    orderTwentyFiveCanonicalCoordinatesNonzero_deckTransform h.1,
    h.2.1.deckTransform, ?_⟩
  intro hcusp
  have hcusp' :=
    hcusp.deckTransform.deckTransform.deckTransform.deckTransform
  rw [orderTwentyFiveCanonicalDeckTransform_five] at hcusp'
  exact h.2.2 hcusp'

/-- A nonzero rational point of the canonical carrier on `w = 0` is one of
the displayed cusp rays. -/
theorem orderTwentyFiveCanonical_w_eq_zero_isCusp
    (p : OrderTwentyFiveCanonicalCoordinates ℚ)
    (hnonzero : OrderTwentyFiveCanonicalCoordinatesNonzero p.x p.y p.z p.w)
    (hcurve : p.OnCurve) (hw : p.w = 0) :
    p.IsCusp := by
  have hcubic : p.x * p.y * p.z = 0 := by
    have hcubic' := hcurve.2
    simp [orderTwentyFiveCanonicalCubic, hw] at hcubic'
    simpa using hcubic'
  rcases mul_eq_zero.mp hcubic with hxy | hz
  · rcases mul_eq_zero.mp hxy with hx | hy
    · have hyprod : p.y * (p.y + p.z) = 0 := by
        have hquadric := hcurve.1
        simp only [orderTwentyFiveCanonicalQuadric] at hquadric
        simp only [hx, hw, zero_mul, sub_zero] at hquadric
        linear_combination hquadric
      rcases mul_eq_zero.mp hyprod with hy | hyz
      · have hz0 : p.z ≠ 0 := by
          intro hz
          exact hnonzero.elim (fun hx' ↦ hx' hx)
            (fun hy' ↦ hy'.elim (fun hy' ↦ hy' hy)
              (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw)))
        refine ⟨3, p.z, hz0, ?_⟩
        change p.x = p.z * 0 ∧ p.y = p.z * 0 ∧
          p.z = p.z * 1 ∧ p.w = p.z * 0
        simp [hx, hy, hw]
      · have hyneg : p.y = -p.z := by linear_combination hyz
        have hz0 : p.z ≠ 0 := by
          intro hz
          have hy0 : p.y = 0 := by
            calc
              p.y = -p.z := hyneg
              _ = 0 := by rw [hz, neg_zero]
          exact hnonzero.elim (fun hx' ↦ hx' hx)
            (fun hy' ↦ hy'.elim (fun hy' ↦ hy' hy0)
              (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw)))
        refine ⟨1, p.z, hz0, ?_⟩
        change p.x = p.z * 0 ∧ p.y = p.z * (-1) ∧
          p.z = p.z * 1 ∧ p.w = p.z * 0
        simp [hx, hyneg, hw]
    · have hxz : p.x * p.z = 0 := by
        have hquadric := hcurve.1
        simp only [orderTwentyFiveCanonicalQuadric] at hquadric
        simp only [hy, hw, zero_mul] at hquadric
        linear_combination -hquadric
      rcases mul_eq_zero.mp hxz with hx | hz
      · have hz0 : p.z ≠ 0 := by
          intro hz
          exact hnonzero.elim (fun hx' ↦ hx' hx)
            (fun hy' ↦ hy'.elim (fun hy' ↦ hy' hy)
              (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw)))
        refine ⟨3, p.z, hz0, ?_⟩
        change p.x = p.z * 0 ∧ p.y = p.z * 0 ∧
          p.z = p.z * 1 ∧ p.w = p.z * 0
        simp [hx, hy, hw]
      · have hx0 : p.x ≠ 0 := by
          intro hx
          exact hnonzero.elim (fun hx' ↦ hx' hx)
            (fun hy' ↦ hy'.elim (fun hy' ↦ hy' hy)
              (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw)))
        refine ⟨4, p.x, hx0, ?_⟩
        change p.x = p.x * 1 ∧ p.y = p.x * 0 ∧
          p.z = p.x * 0 ∧ p.w = p.x * 0
        simp [hy, hz, hw]
  · have hy : p.y = 0 := by
      have hquadric := hcurve.1
      simp only [orderTwentyFiveCanonicalQuadric] at hquadric
      simp only [hz, hw, mul_zero, sub_zero, add_zero] at hquadric
      exact sq_eq_zero_iff.mp hquadric
    have hx0 : p.x ≠ 0 := by
      intro hx
      exact hnonzero.elim (fun hx' ↦ hx' hx)
        (fun hy' ↦ hy'.elim (fun hy' ↦ hy' hy)
          (fun hz' ↦ hz'.elim (fun hz' ↦ hz' hz) (fun hw' ↦ hw' hw)))
    refine ⟨4, p.x, hx0, ?_⟩
    change p.x = p.x * 1 ∧ p.y = p.x * 0 ∧
      p.z = p.x * 0 ∧ p.w = p.x * 0
    simp [hy, hz, hw]

/-- A noncuspidal rational point cannot lie on `w = 0`. -/
theorem orderTwentyFiveCanonical_w_ne_zero_of_noncuspidal
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) (h : p.IsNoncuspidal) :
    p.w ≠ 0 := by
  intro hw
  exact h.2.2 (orderTwentyFiveCanonical_w_eq_zero_isCusp p h.1 h.2.1 hw)

/-- Every denominator in the five-term cyclic orbit is nonzero at a
noncuspidal rational point. -/
theorem orderTwentyFiveCanonical_cyclicDenominators_ne_zero_of_noncuspidal
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) (h : p.IsNoncuspidal) :
    p.w ≠ 0 ∧ p.x - p.y ≠ 0 ∧ p.y + p.z - p.w ≠ 0 ∧
      p.x ≠ 0 ∧ p.z ≠ 0 := by
  have h0 := orderTwentyFiveCanonical_w_ne_zero_of_noncuspidal p h
  have hT := h.deckTransform
  have h1 := orderTwentyFiveCanonical_w_ne_zero_of_noncuspidal
    (orderTwentyFiveCanonicalDeckTransform p) hT
  have hT2 := hT.deckTransform
  have h2 := orderTwentyFiveCanonical_w_ne_zero_of_noncuspidal
    (orderTwentyFiveCanonicalDeckTransform
      (orderTwentyFiveCanonicalDeckTransform p)) hT2
  have hT3 := hT2.deckTransform
  have h3 := orderTwentyFiveCanonical_w_ne_zero_of_noncuspidal
    (orderTwentyFiveCanonicalDeckTransform
      (orderTwentyFiveCanonicalDeckTransform
        (orderTwentyFiveCanonicalDeckTransform p))) hT3
  have hT4 := hT3.deckTransform
  have h4 := orderTwentyFiveCanonical_w_ne_zero_of_noncuspidal
    (orderTwentyFiveCanonicalDeckTransform
      (orderTwentyFiveCanonicalDeckTransform
        (orderTwentyFiveCanonicalDeckTransform
          (orderTwentyFiveCanonicalDeckTransform p)))) hT4
  refine ⟨h0, ?_, ?_, ?_, ?_⟩
  · simpa only [orderTwentyFiveCanonicalDeckTransform] using h1
  · intro hlinear
    apply h2
    simp only [orderTwentyFiveCanonicalDeckTransform]
    linear_combination hlinear
  · intro hx
    apply h3
    simp only [orderTwentyFiveCanonicalDeckTransform]
    linear_combination -hx
  · intro hz
    apply h4
    simp only [orderTwentyFiveCanonicalDeckTransform]
    linear_combination -hz

private noncomputable def orderTwentyFiveCanonicalUnitOnePolynomial :
    Polynomial ℤ :=
  Polynomial.X ^ 2 - Polynomial.X - Polynomial.C 1

private theorem orderTwentyFiveCanonicalUnitOnePolynomial_monic :
    orderTwentyFiveCanonicalUnitOnePolynomial.Monic := by
  unfold orderTwentyFiveCanonicalUnitOnePolynomial
  monicity!

private theorem orderTwentyFiveCanonicalUnitOnePolynomial_no_root_mod_two :
    ∀ t : ZMod 2, t ^ 2 - t - 1 ≠ 0 := by
  decide

/-- The quadratic forced by a hypothetical value `r₀ = 1` has no rational
root. -/
theorem orderTwentyFiveCanonicalUnitOnePolynomial_ne_zero (t : ℚ) :
    t ^ 2 - t - 1 ≠ 0 := by
  intro ht
  have hroot :
      Polynomial.aeval t orderTwentyFiveCanonicalUnitOnePolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderTwentyFiveCanonicalUnitOnePolynomial]
    linear_combination ht
  obtain ⟨z, hzt, -⟩ :=
    exists_integer_of_is_root_of_monic
      orderTwentyFiveCanonicalUnitOnePolynomial_monic hroot
  have hzrat : (z : ℚ) ^ 2 - (z : ℚ) - 1 = 0 := by
    have hzcast : (z : ℚ) = t := by
      simpa using hzt.symm
    rw [hzcast]
    exact ht
  have hzint : z ^ 2 - z - 1 = 0 := by
    exact_mod_cast hzrat
  apply orderTwentyFiveCanonicalUnitOnePolynomial_no_root_mod_two (z : ZMod 2)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 2)) hzint

/-- The first cyclic unit is never `1` at a noncuspidal rational point. -/
theorem orderTwentyFiveCanonicalRootZero_ne_one_of_noncuspidal
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) (h : p.IsNoncuspidal) :
    orderTwentyFiveCanonicalRootZero p ≠ 1 := by
  have hw := orderTwentyFiveCanonical_w_ne_zero_of_noncuspidal p h
  intro hroot
  have hzw : -p.z = p.w := by
    have hdiv : -p.z / p.w = (1 : ℚ) := by
      simpa only [orderTwentyFiveCanonicalRootZero] using hroot
    simpa using (div_eq_iff hw).mp hdiv
  have hz : p.z = -p.w := by linear_combination -hzw
  have hquadric := h.2.1.1
  simp only [orderTwentyFiveCanonicalQuadric] at hquadric
  have hgolden : p.y ^ 2 - p.y * p.w - p.w ^ 2 = 0 := by
    rw [hz] at hquadric
    linear_combination hquadric
  apply orderTwentyFiveCanonicalUnitOnePolynomial_ne_zero (p.y / p.w)
  field_simp [hw]
  linear_combination hgolden

/-- The Lehmer parameter recovered from the explicit five-term canonical
orbit. -/
def orderTwentyFiveCanonicalOrbitParameter
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) : ℚ :=
  orderTwentyFiveOrbitParameter
    (orderTwentyFiveCanonicalRootZero p)
    (orderTwentyFiveCanonicalRootOne p)
    (orderTwentyFiveCanonicalRootTwo p)
    (orderTwentyFiveCanonicalRootThree p)
    (orderTwentyFiveCanonicalRootFour p)

/-- A noncuspidal rational point on the canonical carrier supplies two roots
of one explicitly recovered Lehmer quintic, with no separate chart
hypotheses. -/
theorem orderTwentyFiveCanonical_lehmerRoots_of_noncuspidal
    (p : OrderTwentyFiveCanonicalCoordinates ℚ) (h : p.IsNoncuspidal) :
    orderTwentyFiveLehmerPolynomial
        (orderTwentyFiveCanonicalOrbitParameter p)
        (orderTwentyFiveCanonicalRootZero p) = 0 ∧
      orderTwentyFiveLehmerPolynomial
        (orderTwentyFiveCanonicalOrbitParameter p)
        (orderTwentyFiveCanonicalRootTwo p) = 0 := by
  obtain ⟨hw, hxy, hlinear, hx, hz⟩ :=
    orderTwentyFiveCanonical_cyclicDenominators_ne_zero_of_noncuspidal p h
  simpa only [orderTwentyFiveCanonicalOrbitParameter] using
    orderTwentyFiveCanonical_lehmerRoots p h.2.1
      hw hxy hlinear hx hz
      (orderTwentyFiveCanonicalRootZero_ne_one_of_noncuspidal p h)

end MazurTorsion.Kubert
