/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate

/-!
# Recovering the second order-twenty-five orbit relation

Four of Lécacheux's cyclic equations and the norm-one equation imply the
remaining cyclic equation.  The norm-one equation itself supplies the
nonvanishing needed for cancellation.  This small identity lets the raw
certificate bridge avoid a fifth large generated calculation.
-/

namespace MazurTorsion.Kubert

/-- The first, third, fourth, and fifth cyclic orbit relations, together with
the norm-one relation, imply the second cyclic relation. -/
theorem orderTwentyFiveOrbitRelationOne_eq_zero_of_other_relations
    (a b c d e : ℚ)
    (h₀ : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h₂ : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h₃ : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h₄ : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h₅ : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveOrbitRelationOne a b c d e = 0 := by
  have h₀' : a * (b - d) = a - c :=
    (sub_eq_zero.mp (by
      simpa only [orderTwentyFiveOrbitRelationZero] using h₀)).symm
  have h₂' : c - e = c * (d - a) :=
    sub_eq_zero.mp (by
      simpa only [orderTwentyFiveOrbitRelationTwo] using h₂)
  have h₃' : d - a = d * (e - b) :=
    sub_eq_zero.mp (by
      simpa only [orderTwentyFiveOrbitRelationThree] using h₃)
  have h₄' : e - b = e * (a - c) :=
    sub_eq_zero.mp (by
      simpa only [orderTwentyFiveOrbitRelationFour] using h₄)
  have h₅' : a * b * c * d * e = 1 :=
    sub_eq_zero.mp (by
      simpa only [orderTwentyFiveOrbitRelationFive] using h₅)
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0] at h₅'
    norm_num at h₅'
  have hmul : a * orderTwentyFiveOrbitRelationOne a b c d e = 0 := by
    simp only [orderTwentyFiveOrbitRelationOne]
    calc
      a * (b - d - b * (c - e)) =
          a * (b - d) - a * b * (c - e) := by ring
      _ = (a - c) - a * b * (c * (d - a)) := by rw [h₀', h₂']
      _ = (a - c) - a * b * c * (d * (e - b)) := by rw [h₃']; ring
      _ = (a - c) - a * b * c * d * (e * (a - c)) := by rw [h₄']; ring
      _ = (a - c) * (1 - a * b * c * d * e) := by ring
      _ = 0 := by rw [h₅']; ring
  exact (mul_eq_zero.mp hmul).resolve_left ha

end MazurTorsion.Kubert
