/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyOneReduction
import MazurTorsion.Kubert.OrderTwentyOneExceptionalJ
import MazurTorsion.NumberTheory.XZeroTwentyOneTransfer

/-!
# Excluding the exceptional hauptmodul values at order twenty-one

The hauptmodul certificate sends an exact order-21 point to a rational
pair on the `X₀(3)`–`X₀(7)` fibre product with a cleared `j`-link.  When
the `t₃`-value is one of the four noncuspidal values

`-18, -81/2, -1152, -81/128`,

the `j`-link forces one of the four exceptional `j`-equations on the
order-seven Tate family carrying the point, which the mod-five
certificates exclude.  Together with the plane-to-Weierstrass transfer
(the remaining leaf), this closes exact rational order twenty-one.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- An exact order-21 point cannot coexist with a `j`-link at any of the
four noncuspidal `t₃`-values of `X₀(21)`. -/
theorem no_orderTwentyOne_exceptional_t₃
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21)
    {t₃ : ℚ}
    (hlink : (t₃ + 27) * (t₃ + 3) ^ 3 * E.Δ = E.c₄ ^ 3 * t₃)
    (hval : t₃ = -18 ∨ t₃ = -81 / 2 ∨ t₃ = -1152 ∨
      t₃ = -81 / 128) : False := by
  obtain ⟨d, u, hd0, hd1, hu, h00₇, e₇, -, hdisc₇, hc₄₇⟩ :=
    orderTwentyOne_tate_package E P h21
  have hscale :
      ∀ p q : ℚ, q * E.c₄ ^ 3 = p * E.Δ →
        q * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 =
          p * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
    intro p q hpq
    calc
      q * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 =
          q * (u ^ 4 * E.c₄) ^ 3 := by rw [hc₄₇]
      _ = u ^ 12 * (q * E.c₄ ^ 3) := by ring
      _ = u ^ 12 * (p * E.Δ) := by rw [hpq]
      _ = p * (u ^ 12 * E.Δ) := by ring
      _ = p * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
        rw [hdisc₇]
  rcases hval with rfl | rfl | rfl | rfl
  · exact no_seven_family_j_first d
      (hscale 3375 2 (by linear_combination (1 / 9 : ℚ) * hlink))
  · exact no_seven_family_j_second d
      (hscale (-140625) 8 (by linear_combination (16 / 81 : ℚ) * hlink))
  · exact no_seven_family_j_third d
      (hscale (-189613868625) 128
        (by linear_combination (1 / 9 : ℚ) * hlink))
  · exact no_seven_family_j_fourth d
      (hscale (-1159088625) 2097152
        (by linear_combination (268435456 / 81 : ℚ) * hlink))

/-- No elliptic curve over `ℚ` has a rational point of exact order
twenty-one. -/
theorem no_rational_point_of_order_twentyOne
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21) : False := by
  obtain ⟨t₃, t₇, ht₃0, ht₇0, hpair, h3link, -⟩ :=
    exists_hauptmodulPair_of_order_twentyOne E P h21
  have hcases :=
    MazurTorsion.XZeroTwentyOne.hauptmodulPair_t₃_cases
      ht₃0 ht₇0 hpair
  apply no_orderTwentyOne_exceptional_t₃ E P h21 h3link
  tauto

/-- Interface form of the order-21 exclusion on the base-changed model. -/
theorem rationalPoint_addOrderOf_ne_twentyOne
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 21 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  intro hQ
  exact no_rational_point_of_order_twentyOne (E⁄ℚ) Q hQ

end MazurTorsion.Kubert
