/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerThreeAdic

/-!
# The exact 3-adic root multiset of Lehmer's order-twenty-five quintic

The root alternatives from the lower Newton polygon do not by themselves fix
how many roots have each valuation.  This file combines them with the product
and cubic elementary symmetric sum supplied by Vieta's formulas.  The two
symmetric constraints eliminate the spurious count patterns and show that the
five valuations are exactly \(3a, a, -a, -a, -2a\).

We state the result as an identity between monic polynomials in an integer
variable.  This records the multiset without choosing a permutation of the
five roots.  The final marked-point theorem is the named downstream consumer.
-/

namespace MazurTorsion.Kubert

private theorem val_add_eq_left_of_lt_exact
    (q r : ℚ) (hq : q ≠ 0)
    (hval : padicValRat 3 q < padicValRat 3 r) :
    q + r ≠ 0 ∧ padicValRat 3 (q + r) = padicValRat 3 q := by
  by_cases hr : r = 0
  · simp [hr, hq]
  · have hsum : q + r ≠ 0 := by
      intro hzero
      have hneg : r = -q := eq_neg_of_add_eq_zero_right hzero
      rw [hneg, padicValRat.neg] at hval
      exact (lt_irrefl _ hval)
    exact ⟨hsum, padicValRat.add_eq_of_lt hsum hq hr hval⟩

private theorem val_foldl_add_eq_of_head_lt
    (q : ℚ) (l : List ℚ) (hq : q ≠ 0)
    (hl : ∀ r ∈ l, padicValRat 3 q < padicValRat 3 r) :
    let s := l.foldl (· + ·) q
    s ≠ 0 ∧ padicValRat 3 s = padicValRat 3 q := by
  induction l generalizing q with
  | nil => simpa using hq
  | cons r l ih =>
      have hr := hl r (by simp)
      obtain ⟨hqr, hvqr⟩ := val_add_eq_left_of_lt_exact q r hq hr
      have htail : ∀ s ∈ l,
          padicValRat 3 (q + r) < padicValRat 3 s := by
        intro s hs
        rw [hvqr]
        exact hl s (by simp [hs])
      obtain ⟨hs, hvs⟩ := ih (q + r) hqr htail
      exact ⟨hs, hvs.trans hvqr⟩

private theorem le_val_list_sum_of_nonpos
    (b : ℤ) (hb : b ≤ 0) (l : List ℚ)
    (hl : ∀ q ∈ l, b ≤ padicValRat 3 q) :
    b ≤ padicValRat 3 l.sum := by
  induction l with
  | nil => simpa using hb
  | cons q l ih =>
      by_cases hsum : q + l.sum = 0
      · simp [hsum, hb]
      · exact le_trans (le_min (hl q (by simp))
          (ih (fun r hr => hl r (by simp [hr]))))
          (padicValRat.min_le_padicValRat_add hsum)

private theorem three_values_sum_four
    (a x y z : ℤ) (ha : 0 < a)
    (hx : x = 3 * a ∨ x = a ∨ x = -a ∨ x = -2 * a)
    (hy : y = 3 * a ∨ y = a ∨ y = -a ∨ y = -2 * a)
    (hz : z = 3 * a ∨ z = a ∨ z = -a ∨ z = -2 * a)
    (hsum : x + y + z = 4 * a) :
    (x = -2 * a ∧ y = 3 * a ∧ z = 3 * a) ∨
      (x = 3 * a ∧ y = -2 * a ∧ z = 3 * a) ∨
      (x = 3 * a ∧ y = 3 * a ∧ z = -2 * a) := by
  rcases hx with hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy <;>
    rcases hz with hz | hz | hz | hz <;>
    omega

private theorem triple_values_low
    (a x y z : ℤ) (ha : 0 < a)
    (hx : x = 3 * a ∨ x = a ∨ x = -a ∨ x = -2 * a)
    (hy : y = 3 * a ∨ y = a ∨ y = -a ∨ y = -2 * a)
    (hz : z = 3 * a ∨ z = a ∨ z = -a ∨ z = -2 * a)
    (hxy : ¬(x = -2 * a ∧ y = -2 * a))
    (hxz : ¬(x = -2 * a ∧ z = -2 * a))
    (hyz : ¬(y = -2 * a ∧ z = -2 * a))
    (hlow : x + y + z ≤ -4 * a) :
    (x = -2 * a ∧ y = -a ∧ z = -a) ∨
      (x = -a ∧ y = -2 * a ∧ z = -a) ∨
      (x = -a ∧ y = -a ∧ z = -2 * a) := by
  rcases hx with hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy <;>
    rcases hz with hz | hz | hz | hz <;>
    omega

private theorem two_values_sum_four
    (a x y : ℤ) (ha : 0 < a)
    (hx : x = 3 * a ∨ x = a ∨ x = -a ∨ x = -2 * a)
    (hy : y = 3 * a ∨ y = a ∨ y = -a ∨ y = -2 * a)
    (hsum : x + y = 4 * a) :
    (x = 3 * a ∧ y = a) ∨ (x = a ∧ y = 3 * a) := by
  rcases hx with hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy <;>
    omega

private theorem exact_pattern_of_low_triple
    (a p q r s t : ℤ) (ha : 0 < a)
    (hp : p = 3 * a ∨ p = a ∨ p = -a ∨ p = -2 * a)
    (hq : q = 3 * a ∨ q = a ∨ q = -a ∨ q = -2 * a)
    (hr : r = 3 * a ∨ r = a ∨ r = -a ∨ r = -2 * a)
    (hs : s = 3 * a ∨ s = a ∨ s = -a ∨ s = -2 * a)
    (ht : t = 3 * a ∨ t = a ∨ t = -a ∨ t = -2 * a)
    (hpq : ¬(p = -2 * a ∧ q = -2 * a))
    (hpr : ¬(p = -2 * a ∧ r = -2 * a))
    (hqr : ¬(q = -2 * a ∧ r = -2 * a))
    (hsum : p + q + r + s + t = 0)
    (hlow : p + q + r ≤ -4 * a) :
    ∀ T : ℤ,
      (T - p) * (T - q) * (T - r) * (T - s) * (T - t) =
        (T - 3 * a) * (T - a) * (T + a) ^ 2 * (T + 2 * a) := by
  rcases triple_values_low a p q r ha hp hq hr hpq hpr hqr hlow with
      ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
  all_goals
    subst p
    subst q
    subst r
    have hst : s + t = 4 * a := by omega
    rcases two_values_sum_four a s t ha hs ht hst with
        ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      subst s <;> subst t <;> intro T <;> ring

private def noUniqueLowTriple (a p q r s t : ℤ) : Prop :=
  ¬(p + q + r < -4 * a ∧
    p + q + r < p + q + s ∧ p + q + r < p + q + t ∧
    p + q + r < p + r + s ∧ p + q + r < p + r + t ∧
    p + q + r < p + s + t ∧ p + q + r < q + r + s ∧
    p + q + r < q + r + t ∧ p + q + r < q + s + t ∧
    p + q + r < r + s + t)

private theorem no_two_neg_two'
    (a p q r s t : ℤ) (ha : 0 < a)
    (hr : r = 3 * a ∨ r = a ∨ r = -a ∨ r = -2 * a)
    (hs : s = 3 * a ∨ s = a ∨ s = -a ∨ s = -2 * a)
    (ht : t = 3 * a ∨ t = a ∨ t = -a ∨ t = -2 * a)
    (hsum : p + q + r + s + t = 0)
    (hur : noUniqueLowTriple a p q r s t)
    (hus : noUniqueLowTriple a p q s r t)
    (hut : noUniqueLowTriple a p q t r s) :
    ¬(p = -2 * a ∧ q = -2 * a) := by
  simp only [noUniqueLowTriple] at hur hus hut
  rintro ⟨hp, hq⟩
  have hrest : r + s + t = 4 * a := by omega
  rcases three_values_sum_four a r s t ha hr hs ht hrest with
      ⟨hr, hs, ht⟩ | ⟨hr, hs, ht⟩ | ⟨hr, hs, ht⟩ <;>
    omega

private theorem all_pairs_not_neg_two
    (a z0 z1 z2 z3 z4 : ℤ) (ha : 0 < a)
    (hz0 : z0 = 3 * a ∨ z0 = a ∨ z0 = -a ∨ z0 = -2 * a)
    (hz1 : z1 = 3 * a ∨ z1 = a ∨ z1 = -a ∨ z1 = -2 * a)
    (hz2 : z2 = 3 * a ∨ z2 = a ∨ z2 = -a ∨ z2 = -2 * a)
    (hz3 : z3 = 3 * a ∨ z3 = a ∨ z3 = -a ∨ z3 = -2 * a)
    (hz4 : z4 = 3 * a ∨ z4 = a ∨ z4 = -a ∨ z4 = -2 * a)
    (hsum : z0 + z1 + z2 + z3 + z4 = 0)
    (h012 : noUniqueLowTriple a z0 z1 z2 z3 z4)
    (h013 : noUniqueLowTriple a z0 z1 z3 z2 z4)
    (h014 : noUniqueLowTriple a z0 z1 z4 z2 z3)
    (h023 : noUniqueLowTriple a z0 z2 z3 z1 z4)
    (h024 : noUniqueLowTriple a z0 z2 z4 z1 z3)
    (h034 : noUniqueLowTriple a z0 z3 z4 z1 z2)
    (h123 : noUniqueLowTriple a z1 z2 z3 z0 z4)
    (h124 : noUniqueLowTriple a z1 z2 z4 z0 z3)
    (h134 : noUniqueLowTriple a z1 z3 z4 z0 z2)
    (h234 : noUniqueLowTriple a z2 z3 z4 z0 z1) :
    ¬(z0 = -2 * a ∧ z1 = -2 * a) ∧
      ¬(z0 = -2 * a ∧ z2 = -2 * a) ∧
      ¬(z0 = -2 * a ∧ z3 = -2 * a) ∧
      ¬(z0 = -2 * a ∧ z4 = -2 * a) ∧
      ¬(z1 = -2 * a ∧ z2 = -2 * a) ∧
      ¬(z1 = -2 * a ∧ z3 = -2 * a) ∧
      ¬(z1 = -2 * a ∧ z4 = -2 * a) ∧
      ¬(z2 = -2 * a ∧ z3 = -2 * a) ∧
      ¬(z2 = -2 * a ∧ z4 = -2 * a) ∧
      ¬(z3 = -2 * a ∧ z4 = -2 * a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact no_two_neg_two' a z0 z1 z2 z3 z4 ha hz2 hz3 hz4 hsum
      h012 h013 h014
  · exact no_two_neg_two' a z0 z2 z1 z3 z4 ha hz1 hz3 hz4 (by omega)
      (by simp only [noUniqueLowTriple] at h012 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h023 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h024 ⊢; omega)
  · exact no_two_neg_two' a z0 z3 z1 z2 z4 ha hz1 hz2 hz4 (by omega)
      (by simp only [noUniqueLowTriple] at h013 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h023 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h034 ⊢; omega)
  · exact no_two_neg_two' a z0 z4 z1 z2 z3 ha hz1 hz2 hz3 (by omega)
      (by simp only [noUniqueLowTriple] at h014 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h024 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h034 ⊢; omega)
  · exact no_two_neg_two' a z1 z2 z0 z3 z4 ha hz0 hz3 hz4 (by omega)
      (by simp only [noUniqueLowTriple] at h012 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h123 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h124 ⊢; omega)
  · exact no_two_neg_two' a z1 z3 z0 z2 z4 ha hz0 hz2 hz4 (by omega)
      (by simp only [noUniqueLowTriple] at h013 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h123 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h134 ⊢; omega)
  · exact no_two_neg_two' a z1 z4 z0 z2 z3 ha hz0 hz2 hz3 (by omega)
      (by simp only [noUniqueLowTriple] at h014 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h124 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h134 ⊢; omega)
  · exact no_two_neg_two' a z2 z3 z0 z1 z4 ha hz0 hz1 hz4 (by omega)
      (by simp only [noUniqueLowTriple] at h023 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h123 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h234 ⊢; omega)
  · exact no_two_neg_two' a z2 z4 z0 z1 z3 ha hz0 hz1 hz3 (by omega)
      (by simp only [noUniqueLowTriple] at h024 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h124 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h234 ⊢; omega)
  · exact no_two_neg_two' a z3 z4 z0 z1 z2 ha hz0 hz1 hz2 (by omega)
      (by simp only [noUniqueLowTriple] at h034 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h134 ⊢; omega)
      (by simp only [noUniqueLowTriple] at h234 ⊢; omega)

private theorem exact_pattern_of_constraints
    (a z0 z1 z2 z3 z4 : ℤ) (ha : 0 < a)
    (hz0 : z0 = 3 * a ∨ z0 = a ∨ z0 = -a ∨ z0 = -2 * a)
    (hz1 : z1 = 3 * a ∨ z1 = a ∨ z1 = -a ∨ z1 = -2 * a)
    (hz2 : z2 = 3 * a ∨ z2 = a ∨ z2 = -a ∨ z2 = -2 * a)
    (hz3 : z3 = 3 * a ∨ z3 = a ∨ z3 = -a ∨ z3 = -2 * a)
    (hz4 : z4 = 3 * a ∨ z4 = a ∨ z4 = -a ∨ z4 = -2 * a)
    (hsum : z0 + z1 + z2 + z3 + z4 = 0)
    (hlow :
      z0 + z1 + z2 ≤ -4 * a ∨ z0 + z1 + z3 ≤ -4 * a ∨
      z0 + z1 + z4 ≤ -4 * a ∨ z0 + z2 + z3 ≤ -4 * a ∨
      z0 + z2 + z4 ≤ -4 * a ∨ z0 + z3 + z4 ≤ -4 * a ∨
      z1 + z2 + z3 ≤ -4 * a ∨ z1 + z2 + z4 ≤ -4 * a ∨
      z1 + z3 + z4 ≤ -4 * a ∨ z2 + z3 + z4 ≤ -4 * a)
    (hpairs :
      ¬(z0 = -2 * a ∧ z1 = -2 * a) ∧
      ¬(z0 = -2 * a ∧ z2 = -2 * a) ∧
      ¬(z0 = -2 * a ∧ z3 = -2 * a) ∧
      ¬(z0 = -2 * a ∧ z4 = -2 * a) ∧
      ¬(z1 = -2 * a ∧ z2 = -2 * a) ∧
      ¬(z1 = -2 * a ∧ z3 = -2 * a) ∧
      ¬(z1 = -2 * a ∧ z4 = -2 * a) ∧
      ¬(z2 = -2 * a ∧ z3 = -2 * a) ∧
      ¬(z2 = -2 * a ∧ z4 = -2 * a) ∧
      ¬(z3 = -2 * a ∧ z4 = -2 * a)) :
    ∀ T : ℤ,
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
        (T - 3 * a) * (T - a) * (T + a) ^ 2 * (T + 2 * a) := by
  obtain ⟨hp01, hp02, hp03, hp04, hp12, hp13, hp14, hp23, hp24, hp34⟩ :=
    hpairs
  rcases hlow with h012 | h013 | h014 | h023 | h024 | h034 |
    h123 | h124 | h134 | h234
  · exact exact_pattern_of_low_triple a z0 z1 z2 z3 z4 ha
      hz0 hz1 hz2 hz3 hz4 hp01 hp02 hp12 hsum h012
  · intro T
    have h := exact_pattern_of_low_triple a z0 z1 z3 z2 z4 ha
      hz0 hz1 hz3 hz2 hz4 hp01 hp03 hp13 (by omega) h013 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z0) * (T - z1) * (T - z3) * (T - z2) * (T - z4) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z0 z1 z4 z2 z3 ha
      hz0 hz1 hz4 hz2 hz3 hp01 hp04 hp14 (by omega) h014 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z0) * (T - z1) * (T - z4) * (T - z2) * (T - z3) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z0 z2 z3 z1 z4 ha
      hz0 hz2 hz3 hz1 hz4 hp02 hp03 hp23 (by omega) h023 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z0) * (T - z2) * (T - z3) * (T - z1) * (T - z4) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z0 z2 z4 z1 z3 ha
      hz0 hz2 hz4 hz1 hz3 hp02 hp04 hp24 (by omega) h024 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z0) * (T - z2) * (T - z4) * (T - z1) * (T - z3) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z0 z3 z4 z1 z2 ha
      hz0 hz3 hz4 hz1 hz2 hp03 hp04 hp34 (by omega) h034 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z0) * (T - z3) * (T - z4) * (T - z1) * (T - z2) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z1 z2 z3 z0 z4 ha
      hz1 hz2 hz3 hz0 hz4 hp12 hp13 hp23 (by omega) h123 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z1) * (T - z2) * (T - z3) * (T - z0) * (T - z4) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z1 z2 z4 z0 z3 ha
      hz1 hz2 hz4 hz0 hz3 hp12 hp14 hp24 (by omega) h124 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z1) * (T - z2) * (T - z4) * (T - z0) * (T - z3) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z1 z3 z4 z0 z2 ha
      hz1 hz3 hz4 hz0 hz2 hp13 hp14 hp34 (by omega) h134 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z1) * (T - z3) * (T - z4) * (T - z0) * (T - z2) := by ring
      _ = _ := h
  · intro T
    have h := exact_pattern_of_low_triple a z2 z3 z4 z0 z1 ha
      hz2 hz3 hz4 hz0 hz1 hp23 hp24 hp34 (by omega) h234 T
    calc
      (T - z0) * (T - z1) * (T - z2) * (T - z3) * (T - z4) =
          (T - z2) * (T - z3) * (T - z4) * (T - z0) * (T - z1) := by ring
      _ = _ := h

private theorem not_unique_below_foldl_sum_valuation
    (q : ℚ) (l : List ℚ) (s : ℚ) (b : ℤ) (hq : q ≠ 0)
    (hs : padicValRat 3 s = b)
    (hfold : l.foldl (· + ·) q = s) :
    ¬(padicValRat 3 q < b ∧
      ∀ r ∈ l, padicValRat 3 q < padicValRat 3 r) := by
  rintro ⟨hbelow, hleast⟩
  have hval := (val_foldl_add_eq_of_head_lt q l hq hleast).2
  rw [hfold, hs] at hval
  omega

/-- Five rational roots of the Lehmer quintic with the Vieta product and
cubic-sum identities have valuation multiset \(\{3a,a,-a,-a,-2a\}\).  The
polynomial identity records multiplicities without ordering the roots. -/
theorem orderTwentyFiveLehmer_fiveRoots_threeAdicValuationMultiset
    (n x0 x1 x2 x3 x4 : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hroot0 : orderTwentyFiveLehmerPolynomial n x0 = 0)
    (hroot1 : orderTwentyFiveLehmerPolynomial n x1 = 0)
    (hroot2 : orderTwentyFiveLehmerPolynomial n x2 = 0)
    (hroot3 : orderTwentyFiveLehmerPolynomial n x3 = 0)
    (hroot4 : orderTwentyFiveLehmerPolynomial n x4 = 0)
    (hproduct : x0 * x1 * x2 * x3 * x4 = 1)
    (hs3 : padicValRat 3
      (x0 * x1 * x2 + x0 * x1 * x3 + x0 * x1 * x4 +
        x0 * x2 * x3 + x0 * x2 * x4 + x0 * x3 * x4 +
        x1 * x2 * x3 + x1 * x2 * x4 + x1 * x3 * x4 +
        x2 * x3 * x4) = -4 * a) :
    ∀ T : ℤ,
      (T - padicValRat 3 x0) * (T - padicValRat 3 x1) *
          (T - padicValRat 3 x2) * (T - padicValRat 3 x3) *
          (T - padicValRat 3 x4) =
        (T - 3 * a) * (T - a) * (T + a) ^ 2 * (T + 2 * a) := by
  have hx0 : x0 ≠ 0 := by
    intro hx
    rw [hx] at hproduct
    norm_num at hproduct
  have hx1 : x1 ≠ 0 := by
    intro hx
    rw [hx] at hproduct
    norm_num at hproduct
  have hx2 : x2 ≠ 0 := by
    intro hx
    rw [hx] at hproduct
    norm_num at hproduct
  have hx3 : x3 ≠ 0 := by
    intro hx
    rw [hx] at hproduct
    norm_num at hproduct
  have hx4 : x4 ≠ 0 := by
    intro hx
    rw [hx] at hproduct
    norm_num at hproduct
  let z0 := padicValRat 3 x0
  let z1 := padicValRat 3 x1
  let z2 := padicValRat 3 x2
  let z3 := padicValRat 3 x3
  let z4 := padicValRat 3 x4
  have hz0 : z0 = 3 * a ∨ z0 = a ∨ z0 = -a ∨ z0 = -2 * a := by
    simpa only [z0] using
      orderTwentyFiveLehmer_root_threeAdicValuation n x0 a ha hn hroot0
  have hz1 : z1 = 3 * a ∨ z1 = a ∨ z1 = -a ∨ z1 = -2 * a := by
    simpa only [z1] using
      orderTwentyFiveLehmer_root_threeAdicValuation n x1 a ha hn hroot1
  have hz2 : z2 = 3 * a ∨ z2 = a ∨ z2 = -a ∨ z2 = -2 * a := by
    simpa only [z2] using
      orderTwentyFiveLehmer_root_threeAdicValuation n x2 a ha hn hroot2
  have hz3 : z3 = 3 * a ∨ z3 = a ∨ z3 = -a ∨ z3 = -2 * a := by
    simpa only [z3] using
      orderTwentyFiveLehmer_root_threeAdicValuation n x3 a ha hn hroot3
  have hz4 : z4 = 3 * a ∨ z4 = a ∨ z4 = -a ∨ z4 = -2 * a := by
    simpa only [z4] using
      orderTwentyFiveLehmer_root_threeAdicValuation n x4 a ha hn hroot4
  have hzsum : z0 + z1 + z2 + z3 + z4 = 0 := by
    have hval :
        padicValRat 3 (x0 * x1 * x2 * x3 * x4) =
          z0 + z1 + z2 + z3 + z4 := by
      dsimp only [z0, z1, z2, z3, z4]
      rw [padicValRat.mul
          (mul_ne_zero (mul_ne_zero (mul_ne_zero hx0 hx1) hx2) hx3) hx4,
        padicValRat.mul (mul_ne_zero (mul_ne_zero hx0 hx1) hx2) hx3,
        padicValRat.mul (mul_ne_zero hx0 hx1) hx2,
        padicValRat.mul hx0 hx1]
    rw [hproduct, padicValRat.one] at hval
    omega
  let t012 := x0 * x1 * x2
  let t013 := x0 * x1 * x3
  let t014 := x0 * x1 * x4
  let t023 := x0 * x2 * x3
  let t024 := x0 * x2 * x4
  let t034 := x0 * x3 * x4
  let t123 := x1 * x2 * x3
  let t124 := x1 * x2 * x4
  let t134 := x1 * x3 * x4
  let t234 := x2 * x3 * x4
  let s3 := t012 + t013 + t014 + t023 + t024 + t034 + t123 +
    t124 + t134 + t234
  have hs3v : padicValRat 3 s3 = -4 * a := by
    simpa only [s3, t012, t013, t014, t023, t024, t034, t123,
      t124, t134, t234] using hs3
  have tripleVal (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
      padicValRat 3 (x * y * z) =
        padicValRat 3 x + padicValRat 3 y + padicValRat 3 z := by
    rw [padicValRat.mul (mul_ne_zero hx hy) hz,
      padicValRat.mul hx hy]
  have ht012 : padicValRat 3 t012 = z0 + z1 + z2 := by
    simpa only [t012, z0, z1, z2] using tripleVal x0 x1 x2 hx0 hx1 hx2
  have ht013 : padicValRat 3 t013 = z0 + z1 + z3 := by
    simpa only [t013, z0, z1, z3] using tripleVal x0 x1 x3 hx0 hx1 hx3
  have ht014 : padicValRat 3 t014 = z0 + z1 + z4 := by
    simpa only [t014, z0, z1, z4] using tripleVal x0 x1 x4 hx0 hx1 hx4
  have ht023 : padicValRat 3 t023 = z0 + z2 + z3 := by
    simpa only [t023, z0, z2, z3] using tripleVal x0 x2 x3 hx0 hx2 hx3
  have ht024 : padicValRat 3 t024 = z0 + z2 + z4 := by
    simpa only [t024, z0, z2, z4] using tripleVal x0 x2 x4 hx0 hx2 hx4
  have ht034 : padicValRat 3 t034 = z0 + z3 + z4 := by
    simpa only [t034, z0, z3, z4] using tripleVal x0 x3 x4 hx0 hx3 hx4
  have ht123 : padicValRat 3 t123 = z1 + z2 + z3 := by
    simpa only [t123, z1, z2, z3] using tripleVal x1 x2 x3 hx1 hx2 hx3
  have ht124 : padicValRat 3 t124 = z1 + z2 + z4 := by
    simpa only [t124, z1, z2, z4] using tripleVal x1 x2 x4 hx1 hx2 hx4
  have ht134 : padicValRat 3 t134 = z1 + z3 + z4 := by
    simpa only [t134, z1, z3, z4] using tripleVal x1 x3 x4 hx1 hx3 hx4
  have ht234 : padicValRat 3 t234 = z2 + z3 + z4 := by
    simpa only [t234, z2, z3, z4] using tripleVal x2 x3 x4 hx2 hx3 hx4
  have ht012z : t012 ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hx1) hx2
  have ht013z : t013 ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hx1) hx3
  have ht014z : t014 ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hx1) hx4
  have ht023z : t023 ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hx2) hx3
  have ht024z : t024 ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hx2) hx4
  have ht034z : t034 ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hx3) hx4
  have ht123z : t123 ≠ 0 := mul_ne_zero (mul_ne_zero hx1 hx2) hx3
  have ht124z : t124 ≠ 0 := mul_ne_zero (mul_ne_zero hx1 hx2) hx4
  have ht134z : t134 ≠ 0 := mul_ne_zero (mul_ne_zero hx1 hx3) hx4
  have ht234z : t234 ≠ 0 := mul_ne_zero (mul_ne_zero hx2 hx3) hx4
  have hlow :
      z0 + z1 + z2 ≤ -4 * a ∨ z0 + z1 + z3 ≤ -4 * a ∨
      z0 + z1 + z4 ≤ -4 * a ∨ z0 + z2 + z3 ≤ -4 * a ∨
      z0 + z2 + z4 ≤ -4 * a ∨ z0 + z3 + z4 ≤ -4 * a ∨
      z1 + z2 + z3 ≤ -4 * a ∨ z1 + z2 + z4 ≤ -4 * a ∨
      z1 + z3 + z4 ≤ -4 * a ∨ z2 + z3 + z4 ≤ -4 * a := by
    by_contra h
    push Not at h
    have hb : -4 * a + 1 ≤ 0 := by omega
    have hbound := le_val_list_sum_of_nonpos (-4 * a + 1) hb
      [t012, t013, t014, t023, t024, t034, t123, t124, t134, t234] (by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | (rw [ht012]; omega)
          | (rw [ht013]; omega)
          | (rw [ht014]; omega)
          | (rw [ht023]; omega)
          | (rw [ht024]; omega)
          | (rw [ht034]; omega)
          | (rw [ht123]; omega)
          | (rw [ht124]; omega)
          | (rw [ht134]; omega)
          | (rw [ht234]; omega))
    have hlist :
        [t012, t013, t014, t023, t024, t034, t123, t124, t134, t234].sum =
          s3 := by
      simp only [List.sum_cons, List.sum_nil, add_zero]
      ring
    rw [hlist, hs3v] at hbound
    omega

  have hnot123 : noUniqueLowTriple a z1 z2 z3 z0 z4 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t123
      [t012, t124, t013, t134, t014, t023, t234, t024, t034]
      s3 (-4 * a) ht123z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht123]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht123, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht123, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht123, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht123, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht123, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht123, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht123, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht123, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht123, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot124 : noUniqueLowTriple a z1 z2 z4 z0 z3 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t124
      [t012, t123, t014, t134, t013, t024, t234, t023, t034]
      s3 (-4 * a) ht124z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht124]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht124, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht124, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht124, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht124, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht124, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht124, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht124, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht124, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht124, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot134 : noUniqueLowTriple a z1 z3 z4 z0 z2 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t134
      [t013, t123, t014, t124, t012, t034, t234, t023, t024]
      s3 (-4 * a) ht134z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht134]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht134, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht134, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht134, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht134, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht134, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht134, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht134, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht134, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht134, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot234 : noUniqueLowTriple a z2 z3 z4 z0 z1 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t234
      [t023, t123, t024, t124, t012, t034, t134, t013, t014]
      s3 (-4 * a) ht234z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht234]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht234, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht234, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht234, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht234, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht234, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht234, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht234, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht234, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht234, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot012 : noUniqueLowTriple a z0 z1 z2 z3 z4 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t012
      [t013, t014, t023, t024, t034, t123, t124, t134, t234]
      s3 (-4 * a) ht012z hs3v rfl
    refine ⟨?_, ?_⟩
    · rw [ht012]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht012, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht012, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht012, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht012, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht012, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht012, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht012, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht012, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht012, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot013 : noUniqueLowTriple a z0 z1 z3 z2 z4 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t013
      [t012, t014, t023, t034, t024, t123, t134, t124, t234]
      s3 (-4 * a) ht013z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht013]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht013, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht013, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht013, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht013, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht013, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht013, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht013, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht013, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht013, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot014 : noUniqueLowTriple a z0 z1 z4 z2 z3 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t014
      [t012, t013, t024, t034, t023, t124, t134, t123, t234]
      s3 (-4 * a) ht014z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht014]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht014, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht014, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht014, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht014, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht014, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht014, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht014, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht014, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht014, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot023 : noUniqueLowTriple a z0 z2 z3 z1 z4 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t023
      [t012, t024, t013, t034, t014, t123, t234, t124, t134]
      s3 (-4 * a) ht023z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht023]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht023, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht023, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht023, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht023, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht023, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht023, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht023, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht023, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht023, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot024 : noUniqueLowTriple a z0 z2 z4 z1 z3 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t024
      [t012, t023, t014, t034, t013, t124, t234, t123, t134]
      s3 (-4 * a) ht024z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht024]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht024, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht024, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht024, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht024, ht034]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht024, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht024, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht024, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht024, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht024, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hnot034 : noUniqueLowTriple a z0 z3 z4 z1 z2 := by
    simp only [noUniqueLowTriple]
    intro h
    rcases h with ⟨hbelow, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    apply not_unique_below_foldl_sum_valuation t034
      [t013, t023, t014, t024, t012, t134, t234, t123, t124]
      s3 (-4 * a) ht034z hs3v (by
        simp only [List.foldl_cons, List.foldl_nil]
        dsimp only [s3]
        ring)
    refine ⟨?_, ?_⟩
    · rw [ht034]
      simpa only [add_comm, add_left_comm, add_assoc] using hbelow
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ht034, ht013]
        simpa only [add_comm, add_left_comm, add_assoc] using h1
      · rw [ht034, ht023]
        simpa only [add_comm, add_left_comm, add_assoc] using h2
      · rw [ht034, ht014]
        simpa only [add_comm, add_left_comm, add_assoc] using h3
      · rw [ht034, ht024]
        simpa only [add_comm, add_left_comm, add_assoc] using h4
      · rw [ht034, ht012]
        simpa only [add_comm, add_left_comm, add_assoc] using h5
      · rw [ht034, ht134]
        simpa only [add_comm, add_left_comm, add_assoc] using h6
      · rw [ht034, ht234]
        simpa only [add_comm, add_left_comm, add_assoc] using h7
      · rw [ht034, ht123]
        simpa only [add_comm, add_left_comm, add_assoc] using h8
      · rw [ht034, ht124]
        simpa only [add_comm, add_left_comm, add_assoc] using h9
  have hpairs := all_pairs_not_neg_two a z0 z1 z2 z3 z4 ha
    hz0 hz1 hz2 hz3 hz4 hzsum hnot012 hnot013 hnot014 hnot023 hnot024
    hnot034 hnot123 hnot124 hnot134 hnot234
  simpa only [z0, z1, z2, z3, z4] using
    exact_pattern_of_constraints a z0 z1 z2 z3 z4 ha
      hz0 hz1 hz2 hz3 hz4 hzsum hlow hpairs

private theorem orbit_vieta
    (n r0 r1 r2 r3 r4 : ℚ) (hr0 : r0 ≠ 1)
    (hn :
      5 * (n - 1) + (r0 * r1 + r1 * r2 + r2 * r3 + r3 * r4 + r4 * r0) +
          (r0 * r1 * r2 * r3 + r0 * r1 * r2 * r4 +
            r0 * r1 * r3 * r4 + r0 * r2 * r3 * r4 +
            r1 * r2 * r3 * r4) -
        (r0 + r1 + r2 + r3 + r4) = 0)
    (h0 : orderTwentyFiveOrbitRelationZero r0 r1 r2 r3 r4 = 0)
    (h1 : orderTwentyFiveOrbitRelationOne r0 r1 r2 r3 r4 = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo r0 r1 r2 r3 r4 = 0)
    (h3 : orderTwentyFiveOrbitRelationThree r0 r1 r2 r3 r4 = 0)
    (h4 : orderTwentyFiveOrbitRelationFour r0 r1 r2 r3 r4 = 0)
    (h5 : orderTwentyFiveOrbitRelationFive r0 r1 r2 r3 r4 = 0) :
    r0 * r1 * r2 * r3 * r4 = 1 ∧
      r0 * r1 * r2 + r0 * r1 * r3 + r0 * r1 * r4 +
          r0 * r2 * r3 + r0 * r2 * r4 + r0 * r3 * r4 +
          r1 * r2 * r3 + r1 * r2 * r4 + r1 * r3 * r4 +
          r2 * r3 * r4 =
        n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5 ∧
      ∀ x : ℚ,
        orderTwentyFiveLehmerPolynomial n x =
          (x - r0) * (x - r1) * (x - r2) * (x - r3) * (x - r4) := by
  simp only [orderTwentyFiveOrbitRelationZero,
    orderTwentyFiveOrbitRelationOne, orderTwentyFiveOrbitRelationTwo,
    orderTwentyFiveOrbitRelationThree, orderTwentyFiveOrbitRelationFour,
    orderTwentyFiveOrbitRelationFive] at h0 h1 h2 h3 h4 h5
  have hsumProduct :
      (r0 - 1) * (r0 + r1 + r2 + r3 + r4 - n ^ 2) = 0 := by
    clear hr0
    grobner
  have hsum : r0 + r1 + r2 + r3 + r4 = n ^ 2 := by
    exact sub_eq_zero.mp <|
      (mul_eq_zero.mp hsumProduct).resolve_left (sub_ne_zero.mpr hr0)
  have hpairs :
      r0 * r1 + r0 * r2 + r0 * r3 + r0 * r4 + r1 * r2 +
          r1 * r3 + r1 * r4 + r2 * r3 + r2 * r4 + r3 * r4 =
        2 * (n ^ 3 - 3 * n ^ 2 + 5 * n - 5) := by
    clear hr0
    grobner
  have htriples :
      r0 * r1 * r2 + r0 * r1 * r3 + r0 * r1 * r4 +
          r0 * r2 * r3 + r0 * r2 * r4 + r0 * r3 * r4 +
          r1 * r2 * r3 + r1 * r2 * r4 + r1 * r3 * r4 +
          r2 * r3 * r4 =
        n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5 := by
    clear hr0
    grobner
  have hquadruples :
      r0 * r1 * r2 * r3 + r0 * r1 * r2 * r4 +
          r0 * r1 * r3 * r4 + r0 * r2 * r3 * r4 +
          r1 * r2 * r3 * r4 =
        -n ^ 3 + 4 * n ^ 2 - 10 * n + 10 := by
    clear hr0
    grobner
  have hproduct : r0 * r1 * r2 * r3 * r4 = 1 :=
    sub_eq_zero.mp h5
  refine ⟨hproduct, htriples, ?_⟩
  intro x
  simp only [orderTwentyFiveLehmerPolynomial]
  rw [← hpairs, ← htriples, ← hquadruples, ← hsum, ← hproduct]
  ring

/-- A rational marked point of order twenty-five supplies one positive scale
`a` for which its five cyclic Brunault coordinates have exact 3-adic
valuation multiset \(\{3a,a,-a,-a,-2a\}\). -/
theorem orderTwentyFive_exactThreeAdicRootValuationMultiset_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ IsCoprime m n ∧
      (m : ZMod 3) = 0 ∧ (n : ZMod 3) ≠ 0 ∧
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
        orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) ∧
      orderTwentyFiveRatIsThreeIntegral
        (-5 / orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ))) ∧
      ∃ a : ℤ, 0 < a ∧
        padicValRat 3 ((m : ℚ) / (n : ℚ)) = a ∧
        ∀ T : ℤ,
          (T - padicValRat 3 (orderTwentyFiveBrunaultXZero b c)) *
              (T - padicValRat 3 (orderTwentyFiveBrunaultXOne b c)) *
              (T - padicValRat 3 (orderTwentyFiveBrunaultXTwo b c)) *
              (T - padicValRat 3 (orderTwentyFiveBrunaultXThree b c)) *
              (T - padicValRat 3 (orderTwentyFiveBrunaultXFour b c)) =
            (T - 3 * a) * (T - a) * (T + a) ^ 2 * (T + 2 * a) := by
  obtain ⟨k, hk, -, hkParameter, hkNotUnit, hreciprocal,
      -, hxOne, hcover⟩ :=
    orderTwentyFive_kummerCover_of_marked_order b c hb h00 horder
  obtain ⟨m, n, hm0, hn0, hmn, hm3, hn3, hhaupt, -⟩ :=
    orderTwentyFiveKummerCover_threeAdicOrientation
      k (orderTwentyFiveBrunaultXZero b c) hk hkNotUnit hcover
  obtain ⟨a, ha, hval⟩ :=
    orderTwentyFiveOrientedFraction_threeAdicValuation
      m n hm0 hn0 hm3 hn3
  let k' : ℚ := (m : ℚ) / (n : ℚ)
  let N : ℚ := -orderTwentyFiveFifthPowerHauptmodul k'
  let r0 := orderTwentyFiveBrunaultXZero b c
  let r1 := orderTwentyFiveBrunaultXOne b c
  let r2 := orderTwentyFiveBrunaultXTwo b c
  let r3 := orderTwentyFiveBrunaultXThree b c
  let r4 := orderTwentyFiveBrunaultXFour b c
  have hN : N = orderTwentyFiveOrbitParameter r0 r1 r2 r3 r4 := by
    dsimp only [N, r0, r1, r2, r3, r4, k']
    rw [hhaupt]
    linarith
  have hNv : padicValRat 3 N = -a := by
    dsimp only [N]
    exact orderTwentyFiveFifthPowerHauptmodul_threeAdicValuation
      k' a ha (by simpa only [k'] using hval)
  have hinvariant :
      5 * (N - 1) + (r0 * r1 + r1 * r2 + r2 * r3 + r3 * r4 + r4 * r0) +
          (r0 * r1 * r2 * r3 + r0 * r1 * r2 * r4 +
            r0 * r1 * r3 * r4 + r0 * r2 * r3 * r4 +
            r1 * r2 * r3 * r4) -
        (r0 + r1 + r2 + r3 + r4) = 0 := by
    rw [hN]
    simp only [orderTwentyFiveOrbitParameter]
    ring
  have hvieta := orbit_vieta N r0 r1 r2 r3 r4
    (by simpa only [r0] using hxOne) hinvariant
    (orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationOne_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
      b c hb h00 horder)
  have hroot0 : orderTwentyFiveLehmerPolynomial N r0 = 0 := by
    rw [hvieta.2.2 r0]
    ring
  have hroot1 : orderTwentyFiveLehmerPolynomial N r1 = 0 := by
    rw [hvieta.2.2 r1]
    ring
  have hroot2 : orderTwentyFiveLehmerPolynomial N r2 = 0 := by
    rw [hvieta.2.2 r2]
    ring
  have hroot3 : orderTwentyFiveLehmerPolynomial N r3 = 0 := by
    rw [hvieta.2.2 r3]
    ring
  have hroot4 : orderTwentyFiveLehmerPolynomial N r4 = 0 := by
    rw [hvieta.2.2 r4]
    ring
  have hcoefficient :=
    (orderTwentyFiveLehmerCoefficient_threeAdicValuations N a ha hNv).2.2.1
  have hcoefficient' :
      padicValRat 3
          (N ^ 4 - 5 * N ^ 3 + 11 * N ^ 2 - 15 * N + 5) =
        -4 * a := by
    simpa only [padicValRat.neg] using hcoefficient
  have hs3 : padicValRat 3
      (r0 * r1 * r2 + r0 * r1 * r3 + r0 * r1 * r4 +
        r0 * r2 * r3 + r0 * r2 * r4 + r0 * r3 * r4 +
        r1 * r2 * r3 + r1 * r2 * r4 + r1 * r3 * r4 +
        r2 * r3 * r4) = -4 * a := by
    rw [hvieta.2.1]
    exact hcoefficient'
  refine ⟨m, n, hm0, hn0, hmn, hm3, hn3, ?_, ?_, a, ha, hval, ?_⟩
  · calc
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
          orderTwentyFiveFifthPowerHauptmodul k := hkParameter
      _ = orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) := hhaupt.symm
  · simpa only [hhaupt] using hreciprocal
  · simpa only [r0, r1, r2, r3, r4] using
      orderTwentyFiveLehmer_fiveRoots_threeAdicValuationMultiset N r0 r1 r2 r3 r4 a ha hNv
        hroot0 hroot1 hroot2 hroot3 hroot4 hvieta.1 hs3

end MazurTorsion.Kubert

