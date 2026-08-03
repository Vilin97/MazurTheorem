/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderElevenModelInverse
import MazurTorsion.NumberTheory.XOneElevenDescent

/-!
# The `X₁(11)` five-coset endpoint from the uniform prime theorem

The preferred post-formal-immersion route to the retained five-coset release
obligation is short once exact rational order eleven has been excluded
uniformly.  The reverse modular bridge shows that every affine rational point
on `X₁(11)` has abscissa `0` or `1`.  The equation then leaves exactly the four
visible affine points; together with infinity, these are the five checked
multiples of `(0,0)`.

This file packages that argument as a real consumer of a uniform order-eleven
exclusion.  It does not assume such an exclusion and does not claim the open
Challenge unconditionally.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEleven

/-- Under a uniform exclusion of exact rational order eleven, every rational
point on the selected `X₁(11)` model is one of the five visible multiples of
`P00`. -/
theorem point_eq_fiveRepresentative_of_no_order_eleven
    (hno : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
      (P : E.toAffine.Point), addOrderOf P ≠ 11)
    (P : curve.toAffine.Point) :
    ∃ i : Fin 5, P = fiveRepresentative i := by
  rcases P with _ | ⟨u, v, hP⟩
  · refine ⟨0, ?_⟩
    change (0 : curve.toAffine.Point) = 0
    rfl
  · have hu : u = 0 ∨ u = 1 :=
      MazurTorsion.Kubert.model_abscissa_eq_zero_or_one_of_no_order_eleven
        hno hP
    have heq := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    norm_num [curve] at heq
    rcases hu with rfl | rfl
    · have hv : v = 0 ∨ v = -1 := by
        have hfactor : v * (v + 1) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp hfactor with hv | hv
        · exact Or.inl hv
        · exact Or.inr (by linarith)
      rcases hv with rfl | rfl
      · refine ⟨1, ?_⟩
        change
          WeierstrassCurve.Affine.Point.some 0 0 hP =
            (1 : ℕ) • P00
        rw [one_nsmul, P00]
      · refine ⟨4, ?_⟩
        change
          WeierstrassCurve.Affine.Point.some 0 (-1) hP =
            (4 : ℕ) • P00
        rw [four_P00, P0n1]
    · have hv : v = 0 ∨ v = -1 := by
        have hfactor : v * (v + 1) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp hfactor with hv | hv
        · exact Or.inl hv
        · exact Or.inr (by linarith)
      rcases hv with rfl | rfl
      · refine ⟨3, ?_⟩
        change
          WeierstrassCurve.Affine.Point.some 1 0 hP =
            (3 : ℕ) • P00
        rw [triple_P00, P10]
      · refine ⟨2, ?_⟩
        change
          WeierstrassCurve.Affine.Point.some 1 (-1) hP =
            (2 : ℕ) • P00
        rw [double_P00, P1n1]

/-- The retained five-coset proposition follows directly from the uniform
order-eleven exclusion: choose the visible representative itself and take the
quotient point `Q = 0`. -/
theorem fiveCosetBound_of_no_order_eleven
    (hno : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
      (P : E.toAffine.Point), addOrderOf P ≠ 11) :
    FiveCosetBound := by
  intro P
  obtain ⟨i, hi⟩ :=
    point_eq_fiveRepresentative_of_no_order_eleven hno P
  exact ⟨i, 0, by simpa using hi⟩

/-- Downstream cardinality/classification consumer of the preferred uniform
prime route to the five-coset endpoint. -/
theorem five_point_classification_of_no_order_eleven
    (hno : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
      (P : E.toAffine.Point), addOrderOf P ≠ 11) :
    Nat.card curve.toAffine.Point = 5 ∧
      ∀ {U V : ℚ},
        curve.toAffine.Nonsingular U V → U = 0 ∨ U = 1 :=
  five_point_classification_of_cosetBound
    (fiveCosetBound_of_no_order_eleven hno)

end MazurTorsion.XOneEleven
