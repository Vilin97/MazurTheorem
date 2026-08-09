/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.TateNormalForm

/-!
# Transporting an order-twenty-five marked-point exclusion

This leaf module separates Tate normalization from any particular
Diophantine argument on the normalized parameters.  An exclusion of every
nonsingular Tate-normal marked point of exact order twenty-five transports
to arbitrary rational elliptic curves.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- If exact order twenty-five is impossible for every nonsingular marked
point on a Tate normal curve, then it is impossible for every rational point
on an elliptic Weierstrass curve. -/
theorem rationalPoint_addOrderOf_ne_twentyFive_of_marked_exclusion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hMarkedExclusion :
      ∀ (b c : ℚ) (hb : b ≠ 0)
        (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0),
        addOrderOf
          (WeierstrassCurve.Affine.Point.some 0 0 h00 :
            (tateNormalCurve b c).toAffine.Point) ≠ 25) :
    addOrderOf P ≠ 25 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  intro hP
  have hP2 : P + P ≠ 0 := by
    intro h
    have hdvd : addOrderOf P ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hP] at hdvd
    norm_num at hdvd
  have hP3 : P + P + P ≠ 0 := by
    intro h
    have hdvd : addOrderOf P ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [show (3 : ℕ) • P = P + P + P by abel]
        exact h)
    rw [hP] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, -, -, hb, h00, e, heP, -, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) P hP2 hP3
  have hMarkedOrder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25 := by
    rw [← heP, AddEquiv.addOrderOf_eq]
    exact hP
  exact hMarkedExclusion b c hb h00 hMarkedOrder

end MazurTorsion.Kubert
