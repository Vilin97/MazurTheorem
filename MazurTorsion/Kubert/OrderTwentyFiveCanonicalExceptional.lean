/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalCurve

/-!
# The exceptional projection locus on the order-twenty-five canonical carrier

The inverse from the singular plane sextic to the canonical complete
intersection uses the denominator

`D = xz + w(z-x)`.

This file classifies the rational canonical points for which `D = 0`.  There
are exactly four projective possibilities, represented by canonical cusp
indices `0`, `1`, `3`, and `4`.  Thus every possible noncuspidal rational
point lies in the explicit inverse chart from
`OrderTwentyFiveCanonicalCurve`.

The only arithmetic exclusion needed in the affine `w ≠ 0` case is that
`t³ + t² - 1` has no rational root.  The proof uses its monicity and a direct
root check modulo two.  The elimination identity producing that cubic is
checked by `ring`.

`orderTwentyFiveCanonical_exceptionalProjection_isCusp` is the named
downstream consumer for the rational-point classification.
-/

namespace MazurTorsion.Kubert

/-- A coordinate representative is nonzero precisely when at least one of
its four coordinates is nonzero. -/
def OrderTwentyFiveCanonicalCoordinatesNonzero
    (x y z w : ℚ) : Prop :=
  x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0

/-- A rational coordinate quadruple represents one of the five fixed
canonical cusp points when it is a nonzero scalar multiple of that cusp's
chosen vector. -/
def OrderTwentyFiveCanonicalRepresentsCusp
    (i : Fin 5) (x y z w : ℚ) : Prop :=
  ∃ a : ℚ, a ≠ 0 ∧
    x = a * orderTwentyFiveCanonicalCuspX i ∧
    y = a * orderTwentyFiveCanonicalCuspY i ∧
    z = a * orderTwentyFiveCanonicalCuspZ i ∧
    w = a * orderTwentyFiveCanonicalCuspW i

/-- The auxiliary conic expression obtained after removing the nonzero
factor `w` from the inverse-chart numerator. -/
def orderTwentyFiveCanonicalExceptionalAuxiliary
    {R : Type*} [CommRing R] (x z w : R) : R :=
  x ^ 2 - x * z + z ^ 2 - w * z

/-- The rational-root obstruction on the affine exceptional chart. -/
def orderTwentyFiveCanonicalExceptionalCubic
    {R : Type*} [CommRing R] (x w : R) : R :=
  x ^ 3 + w * x ^ 2 - w ^ 3

/-- Eliminate `z` between `D = 0` and the auxiliary conic without division. -/
theorem orderTwentyFiveCanonical_exceptional_elimination_identity
    {R : Type*} [CommRing R] (x z w : R) :
    (x + w) ^ 2 * orderTwentyFiveCanonicalExceptionalAuxiliary x z w =
      x * orderTwentyFiveCanonicalExceptionalCubic x w +
        (-w ^ 2 - w * x - x ^ 2 + z * (w + x)) *
          orderTwentyFiveCanonicalProjectionDenominator x z w := by
  simp only [orderTwentyFiveCanonicalExceptionalAuxiliary,
    orderTwentyFiveCanonicalExceptionalCubic,
    orderTwentyFiveCanonicalProjectionDenominator]
  ring

private noncomputable def
    orderTwentyFiveCanonicalExceptionalCubicPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 3 + Polynomial.X ^ 2 - Polynomial.C 1

private lemma orderTwentyFiveCanonicalExceptionalCubicPolynomial_monic :
    orderTwentyFiveCanonicalExceptionalCubicPolynomial.Monic := by
  unfold orderTwentyFiveCanonicalExceptionalCubicPolynomial
  monicity!

private lemma orderTwentyFiveCanonicalExceptionalCubic_no_root_mod_two :
    ∀ t : ZMod 2, t ^ 3 + t ^ 2 - 1 ≠ 0 := by
  decide

/-- The normalized exceptional cubic has no rational root. -/
theorem orderTwentyFiveCanonicalExceptionalCubic_ne_zero (t : ℚ) :
    t ^ 3 + t ^ 2 - 1 ≠ 0 := by
  intro ht
  have hroot :
      Polynomial.aeval t
        orderTwentyFiveCanonicalExceptionalCubicPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderTwentyFiveCanonicalExceptionalCubicPolynomial]
    linear_combination ht
  obtain ⟨z, hzt, -⟩ :=
    exists_integer_of_is_root_of_monic
      orderTwentyFiveCanonicalExceptionalCubicPolynomial_monic hroot
  have hzrat : (z : ℚ) ^ 3 + (z : ℚ) ^ 2 - 1 = 0 := by
    have hzcast : (z : ℚ) = t := by
      simpa using hzt.symm
    rw [hzcast]
    exact ht
  have hzint : z ^ 3 + z ^ 2 - 1 = 0 := by
    exact_mod_cast hzrat
  apply orderTwentyFiveCanonicalExceptionalCubic_no_root_mod_two (z : ZMod 2)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 2)) hzint

/-- The inverse-chart denominator vanishes at four displayed cusps and equals
`-1` at cusp index `2`. -/
theorem orderTwentyFiveCanonicalCusp_projectionDenominator (i : Fin 5) :
    orderTwentyFiveCanonicalProjectionDenominator
        (orderTwentyFiveCanonicalCuspX i)
        (orderTwentyFiveCanonicalCuspZ i)
        (orderTwentyFiveCanonicalCuspW i) =
      if i = 2 then -1 else 0 := by
  fin_cases i <;>
    norm_num [orderTwentyFiveCanonicalProjectionDenominator,
      orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspZ,
      orderTwentyFiveCanonicalCuspW, Matrix.cons_val_zero] <;>
    decide

/-- Exactly cusp index `2` belongs to the nonexceptional inverse chart. -/
theorem orderTwentyFiveCanonicalCusp_projectionDenominator_eq_zero_iff
    (i : Fin 5) :
    orderTwentyFiveCanonicalProjectionDenominator
        (orderTwentyFiveCanonicalCuspX i)
        (orderTwentyFiveCanonicalCuspZ i)
        (orderTwentyFiveCanonicalCuspW i) = 0 ↔
      i ≠ 2 := by
  rw [orderTwentyFiveCanonicalCusp_projectionDenominator]
  by_cases hi : i = 2 <;> simp [hi]

/-- A nonzero rational canonical representative with exceptional projection
denominator is one of the four cusp rays not meeting the inverse chart. -/
theorem orderTwentyFiveCanonical_exceptionalProjection_isCusp
    (x y z w : ℚ)
    (hnonzero : OrderTwentyFiveCanonicalCoordinatesNonzero x y z w)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w)
    (hD : orderTwentyFiveCanonicalProjectionDenominator x z w = 0) :
    ∃ i : Fin 5, i ≠ 2 ∧
      OrderTwentyFiveCanonicalRepresentsCusp i x y z w := by
  have hB : orderTwentyFiveCanonicalProjectionNumerator x z w = 0 := by
    have hcubic := hcurve.2
    rw [orderTwentyFiveCanonicalCubic_eq_projectionLinear, hD] at hcubic
    simpa using hcubic
  by_cases hw : w = 0
  · have hxz : x * z = 0 := by
      simpa [orderTwentyFiveCanonicalProjectionDenominator, hw] using hD
    rcases mul_eq_zero.mp hxz with hx | hz
    · have hyprod : y * (y + z) = 0 := by
        have hquadric := hcurve.1
        simp only [orderTwentyFiveCanonicalQuadric, hx, hw,
          zero_mul, sub_zero] at hquadric
        linear_combination hquadric
      rcases mul_eq_zero.mp hyprod with hy | hyz
      · have hz0 : z ≠ 0 := by
          intro hz
          exact hnonzero.elim (fun h => h hx)
            (fun h => h.elim (fun h => h hy)
              (fun h => h.elim (fun h => h hz) (fun h => h hw)))
        refine ⟨3, by decide, z, hz0, ?_⟩
        change x = z * 0 ∧ y = z * 0 ∧ z = z * 1 ∧ w = z * 0
        simp [hx, hy, hw]
      · have hyneg : y = -z := by linear_combination hyz
        have hz0 : z ≠ 0 := by
          intro hz
          have hy0 : y = 0 := by rw [hyneg, hz, neg_zero]
          exact hnonzero.elim (fun h => h hx)
            (fun h => h.elim (fun h => h hy0)
              (fun h => h.elim (fun h => h hz) (fun h => h hw)))
        refine ⟨1, by decide, z, hz0, ?_⟩
        change x = z * 0 ∧ y = z * (-1) ∧ z = z * 1 ∧ w = z * 0
        simp [hx, hyneg, hw]
    · have hy : y = 0 := by
        have hquadric := hcurve.1
        simp only [orderTwentyFiveCanonicalQuadric, hz, hw,
          mul_zero, sub_zero, add_zero] at hquadric
        exact sq_eq_zero_iff.mp hquadric
      have hx0 : x ≠ 0 := by
        intro hx
        exact hnonzero.elim (fun h => h hx)
          (fun h => h.elim (fun h => h hy)
            (fun h => h.elim (fun h => h hz) (fun h => h hw)))
      refine ⟨4, by decide, x, hx0, ?_⟩
      change x = x * 1 ∧ y = x * 0 ∧ z = x * 0 ∧ w = x * 0
      simp [hy, hz, hw]
  · have haux :
        orderTwentyFiveCanonicalExceptionalAuxiliary x z w = 0 := by
      have hmul :
          w * orderTwentyFiveCanonicalExceptionalAuxiliary x z w = 0 := by
        simpa [orderTwentyFiveCanonicalProjectionNumerator,
          orderTwentyFiveCanonicalExceptionalAuxiliary] using hB
      exact (mul_eq_zero.mp hmul).resolve_left hw
    have hproduct :
        x * orderTwentyFiveCanonicalExceptionalCubic x w = 0 := by
      have hid :=
        orderTwentyFiveCanonical_exceptional_elimination_identity x z w
      rw [haux, hD] at hid
      simpa using hid.symm
    have hx : x = 0 := by
      rcases mul_eq_zero.mp hproduct with hx | hcubic
      · exact hx
      · exfalso
        apply orderTwentyFiveCanonicalExceptionalCubic_ne_zero (x / w)
        simp only [orderTwentyFiveCanonicalExceptionalCubic] at hcubic
        field_simp [hw]
        linear_combination hcubic
    have hz : z = 0 := by
      have hD' := hD
      simp only [orderTwentyFiveCanonicalProjectionDenominator, hx,
        zero_mul, sub_zero, zero_add] at hD'
      exact (mul_eq_zero.mp hD').resolve_left hw
    have hy : y = 0 := by
      have hquadric := hcurve.1
      simp only [orderTwentyFiveCanonicalQuadric, hx, hz,
        mul_zero, zero_mul, sub_zero, add_zero] at hquadric
      exact sq_eq_zero_iff.mp hquadric
    refine ⟨0, by decide, w, hw, ?_⟩
    change x = w * 0 ∧ y = w * 0 ∧ z = w * 0 ∧ w = w * 1
    simp [hx, hy, hz]

end MazurTorsion.Kubert
