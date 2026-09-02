/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFiveIsogenyDoubling
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Five-division normalization for order twenty-five

If `P` has exact order twenty-five, then `5P` has exact order five.  Tate
normalization at `5P` therefore places the curve in the diagonal order-five
family.  The same group equivalence transports `P` to a rational point of
exact order twenty-five whose fivefold multiple is the marked origin.

This is the input needed by an explicit degree-five quotient or division
calculation.  In particular, no Fricke involution is asserted to preserve a
rational generator: the transported point and its fivefold multiple live on
the same rational elliptic curve throughout.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Exact order twenty-five normalizes at `5P` into the order-five Tate
family, retaining the discriminant and `c₄` scales and the transported
five-division relation. -/
theorem orderTwentyFive_orderFive_family_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h25 : addOrderOf P = 25) :
    ∃ (c u : ℚ) (_ : c ≠ 0) (_ : c ^ 2 - 11 * c - 1 ≠ 0)
      (_ : u ≠ 0)
      (h00 : (orderFiveCurve c).toAffine.Nonsingular 0 0)
      (e : E.toAffine.Point ≃+ (orderFiveCurve c).toAffine.Point),
      e ((5 : ℕ) • P) =
          WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * E.Δ = (orderFiveCurve c).Δ ∧
        u ^ 4 * E.c₄ = (orderFiveCurve c).c₄ ∧
        addOrderOf (e P) = 25 ∧
        (5 : ℕ) • e P =
          WeierstrassCurve.Affine.Point.some 0 0 h00 := by
  have hnot : ∀ n : ℕ, ¬ (25 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (h25 ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hQ2 :
      (5 : ℕ) • P + (5 : ℕ) • P ≠ 0 := by
    intro hzero
    apply hnot 10 (by norm_num)
    simpa only [← two_nsmul, ← mul_nsmul] using hzero
  have hQ3 :
      (5 : ℕ) • P + (5 : ℕ) • P + (5 : ℕ) • P ≠ 0 := by
    intro hzero
    apply hnot 15 (by norm_num)
    calc
      (15 : ℕ) • P = (3 : ℕ) • ((5 : ℕ) • P) := by
        rw [← mul_nsmul]
      _ = (5 : ℕ) • P + (5 : ℕ) • P + (5 : ℕ) • P := by
        abel
      _ = 0 := hzero
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, hc₄, -⟩ :=
    exists_tateNormalCurve_scaled E ((5 : ℕ) • P) hQ2 hQ3
  have horder5 :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    rw [addOrderOf_nsmul' P (by norm_num), h25]
    norm_num
  have hbc : b = c :=
    tateNormalCurve_parameters_eq_of_order_five b c hb h00 horder5
  subst b
  let eFive : E.toAffine.Point ≃+ (orderFiveCurve c).toAffine.Point := e
  have h00Five : (orderFiveCurve c).toAffine.Nonsingular 0 0 := h00
  have heQFive :
      eFive ((5 : ℕ) • P) =
        WeierstrassCurve.Affine.Point.some 0 0 h00Five := by
    exact heQ
  have hdiscFive : u ^ 12 * E.Δ = (orderFiveCurve c).Δ := by
    exact hdisc
  have hc₄Five : u ^ 4 * E.c₄ = (orderFiveCurve c).c₄ := by
    exact hc₄
  have hc : c ≠ 0 := hb
  have hfactor : c ^ 2 - 11 * c - 1 ≠ 0 := by
    intro hzero
    have hDeltaZero : (orderFiveCurve c).Δ = 0 := by
      rw [orderFiveCurve_discriminant, hzero, mul_zero]
    have hDeltaNe : (orderFiveCurve c).Δ ≠ 0 := by
      rw [← hdiscFive]
      exact mul_ne_zero (pow_ne_zero 12 hu) E.isUnit_Δ.ne_zero
    exact hDeltaNe hDeltaZero
  have horder25 : addOrderOf (eFive P) = 25 := by
    rw [AddEquiv.addOrderOf_eq]
    exact h25
  refine ⟨c, u, hc, hfactor, hu, h00Five, eFive, heQFive,
    hdiscFive, hc₄Five,
    horder25, ?_⟩
  rw [← map_nsmul]
  exact heQFive

/-- The transported order-twenty-five point avoids the two kernel poles.
Its explicit Vélu coordinates define a nonsingular rational point of exact
order five on the degree-five quotient. -/
theorem orderTwentyFive_orderFiveVelu_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h25 : addOrderOf P = 25) :
    ∃ (c u x y : ℚ)
      (h00 : (orderFiveCurve c).toAffine.Nonsingular 0 0)
      (hxy : (orderFiveCurve c).toAffine.Nonsingular x y)
      (hc : c ≠ 0) (hfactor : c ^ 2 - 11 * c - 1 ≠ 0)
      (_hu : u ≠ 0),
        x ≠ 0 ∧ x ≠ c ∧
        addOrderOf
          (WeierstrassCurve.Affine.Point.some x y hxy :
            (orderFiveCurve c).toAffine.Point) = 25 ∧
        (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some x y hxy :
              (orderFiveCurve c).toAffine.Point) =
          WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        (orderFiveVeluTarget c).toAffine.Nonsingular
          (orderFiveVeluX c x) (orderFiveVeluY c x y) ∧
        (letI : (orderFiveCurve c).IsElliptic :=
            orderFiveCurve_isElliptic c hc hfactor;
          addOrderOf
              (orderFivePointMap c
                (WeierstrassCurve.Affine.Point.some x y hxy)) = 5) ∧
        u ^ 12 * E.Δ = (orderFiveCurve c).Δ ∧
        u ^ 4 * E.c₄ = (orderFiveCurve c).c₄ := by
  obtain ⟨c, u, hc, hfactor, hu, h00, e, -, hdisc, hc₄,
      horder25, hfive⟩ :=
    orderTwentyFive_orderFive_family_package E P h25
  cases hEP : e P with
  | zero =>
      rw [hEP] at horder25
      have h1 : addOrderOf
          (WeierstrassCurve.Affine.Point.zero :
            (orderFiveCurve c).toAffine.Point) = 1 :=
        addOrderOf_zero
      rw [h1] at horder25
      exact absurd horder25 (by norm_num)
  | @some x y hxy =>
      rw [hEP] at horder25 hfive
      have hkernel : ¬ (x = 0 ∨ x = c) := by
        intro hx
        have hzero :=
          five_nsmul_eq_zero_of_orderFive_kernel_abscissa hc hxy hx
        have horiginZero :
            (WeierstrassCurve.Affine.Point.some 0 0 h00 :
              (orderFiveCurve c).toAffine.Point) = 0 := by
          rw [← hfive]
          exact hzero
        exact WeierstrassCurve.Affine.Point.some_ne_zero h00 horiginZero
      have hx0 : x ≠ 0 := fun hx ↦ hkernel (Or.inl hx)
      have hxc : x ≠ c := fun hx ↦ hkernel (Or.inr hx)
      letI : (orderFiveCurve c).IsElliptic :=
        orderFiveCurve_isElliptic c hc hfactor
      have htarget :
          (orderFiveVeluTarget c).toAffine.Nonsingular
            (orderFiveVeluX c x) (orderFiveVeluY c x y) :=
        (orderFiveVeluTarget c).toAffine.equation_iff_nonsingular.mp
          (orderFiveVelu_equation hxy hx0 hxc)
      have hfiveCanonical :
          (5 : ℕ) •
              (WeierstrassCurve.Affine.Point.some x y hxy :
                (orderFiveCurve c).toAffine.Point) =
            orderFiveOrigin c := by
        simpa only [orderFiveOrigin] using hfive
      have himageOrder :
          addOrderOf
              (orderFivePointMap c
                (WeierstrassCurve.Affine.Point.some x y hxy)) = 5 :=
        addOrderOf_orderFivePointMap_of_orderTwentyFive
          horder25 hfiveCanonical
      exact ⟨c, u, x, y, h00, hxy, hc, hfactor, hu, hx0, hxc,
        horder25, hfive, htarget, himageOrder, hdisc, hc₄⟩

end MazurTorsion.Kubert
