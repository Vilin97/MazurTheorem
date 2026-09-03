/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerNewtonMultiset

/-!
# The cyclic 3-adic root pattern for order twenty-five

This file combines the four Lehmer-root valuation alternatives with the
explicit cyclic deck transformation.  A root of valuation \(3a\) or \(-2a\)
moves to valuation \(-a\), while a root of valuation \(a\) moves to valuation
at most \(-a\).  The norm-one orbit relation then forces the cyclic pattern

\[(3a,-a,a,-2a,-a)\]

up to rotation.  The combinatorial proof uses adjacent-pair inequalities on
the odd five-cycle, rather than an exhaustive enumeration of all assignments.
The final theorem applies the result to the five Brunault coordinates of a
hypothetical rational marked point of exact order twenty-five.
-/

namespace MazurTorsion.Kubert

private theorem val_add_eq_left_of_lt_cycle
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

private theorem val_foldl_add_eq_of_head_lt_cycle
    (q : ℚ) (l : List ℚ) (hq : q ≠ 0)
    (hl : ∀ r ∈ l, padicValRat 3 q < padicValRat 3 r) :
    let s := l.foldl (· + ·) q
    s ≠ 0 ∧ padicValRat 3 s = padicValRat 3 q := by
  induction l generalizing q with
  | nil => simpa using hq
  | cons r l ih =>
      have hr := hl r (by simp)
      obtain ⟨hqr, hvqr⟩ := val_add_eq_left_of_lt_cycle q r hq hr
      have htail : ∀ s ∈ l,
          padicValRat 3 (q + r) < padicValRat 3 s := by
        intro s hs
        rw [hvqr]
        exact hl s (by simp [hs])
      obtain ⟨hs, hvs⟩ := ih (q + r) hqr htail
      exact ⟨hs, hvs.trans hvqr⟩

private theorem le_val_list_sum_of_nonpos_cycle
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

private theorem root_ne_zero_cycle
    (n x : ℚ) (hx : orderTwentyFiveLehmerPolynomial n x = 0) : x ≠ 0 := by
  intro hzero
  simp [orderTwentyFiveLehmerPolynomial, hzero] at hx

private theorem padicValRat_two_cycle : padicValRat 3 (2 : ℚ) = 0 := by
  change padicValRat 3 ((2 : ℤ) : ℚ) = 0
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd
    (by norm_num : ¬(3 : ℤ) ∣ 2)]
  norm_num

private theorem deck_val_of_three
    (n x : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hxv : padicValRat 3 x = 3 * a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0) :
    padicValRat 3 (orderTwentyFiveLehmerDeckTransform n x) = -a := by
  have hn0 : n ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hn
    omega
  have hx0 := root_ne_zero_cycle n x hroot
  have hnum := val_foldl_add_eq_of_head_lt_cycle n
    [x ^ 2, -(n * x), (-2 : ℚ)] hn0 (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [padicValRat.pow, hxv, hn]
        omega
      · rw [padicValRat.neg, padicValRat.mul hn0 hx0, hn, hxv]
        omega
      · rw [padicValRat.neg, padicValRat_two_cycle, hn]
        omega)
  have hnumEq :
      [x ^ 2, -(n * x), (-2 : ℚ)].foldl (· + ·) n =
        x ^ 2 - n * x + n - 2 := by
    norm_num
    ring
  rw [hnumEq, hn] at hnum
  have hdenFold := val_foldl_add_eq_of_head_lt_cycle (1 : ℚ)
    [n * x, -2 * x] (by norm_num) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [padicValRat.mul hn0 hx0, hn, hxv]
        norm_num
        omega
      · rw [padicValRat.mul (by norm_num) hx0,
          padicValRat.neg, padicValRat_two_cycle, hxv]
        norm_num
        omega)
  have hdenEq :
      [n * x, -2 * x].foldl (· + ·) (1 : ℚ) =
        1 + (n - 2) * x := by
    norm_num
    ring
  rw [hdenEq] at hdenFold
  rw [orderTwentyFiveLehmerDeckTransform,
    padicValRat.div hnum.1 hdenFold.1, hnum.2, hdenFold.2]
  norm_num

private theorem deck_val_of_neg_two
    (n x : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hxv : padicValRat 3 x = -2 * a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0) :
    padicValRat 3 (orderTwentyFiveLehmerDeckTransform n x) = -a := by
  have hn0 : n ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hn
    omega
  have hx0 := root_ne_zero_cycle n x hroot
  have hnum := val_foldl_add_eq_of_head_lt_cycle (x ^ 2)
    [-(n * x), n, (-2 : ℚ)] (pow_ne_zero 2 hx0) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [padicValRat.pow, hxv, padicValRat.neg,
          padicValRat.mul hn0 hx0, hn]
        omega
      · rw [padicValRat.pow, hxv, hn]
        omega
      · rw [padicValRat.pow, hxv, padicValRat.neg,
          padicValRat_two_cycle]
        omega)
  have hnumEq :
      [-(n * x), n, (-2 : ℚ)].foldl (· + ·) (x ^ 2) =
        x ^ 2 - n * x + n - 2 := by
    norm_num
    ring
  rw [hnumEq, padicValRat.pow, hxv] at hnum
  have hden := val_foldl_add_eq_of_head_lt_cycle (n * x)
    [(1 : ℚ), -2 * x] (mul_ne_zero hn0 hx0) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [padicValRat.mul hn0 hx0, hn, hxv]
        norm_num
        omega
      · rw [padicValRat.mul hn0 hx0, hn, hxv,
          padicValRat.mul (by norm_num) hx0,
          padicValRat.neg, padicValRat_two_cycle]
        norm_num
        omega)
  have hdenEq :
      [(1 : ℚ), -2 * x].foldl (· + ·) (n * x) =
        1 + (n - 2) * x := by
    norm_num
    ring
  rw [hdenEq, padicValRat.mul hn0 hx0, hn, hxv] at hden
  rw [orderTwentyFiveLehmerDeckTransform,
    padicValRat.div hnum.1 hden.1, hnum.2, hden.2]
  omega

private theorem deck_val_of_one
    (n x : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hxv : padicValRat 3 x = a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0) :
    padicValRat 3 (orderTwentyFiveLehmerDeckTransform n x) = -a ∨
      padicValRat 3 (orderTwentyFiveLehmerDeckTransform n x) = -2 * a := by
  have hn0 : n ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hn
    omega
  have hx0 := root_ne_zero_cycle n x hroot
  have hnum := val_foldl_add_eq_of_head_lt_cycle n
    [x ^ 2, -(n * x), (-2 : ℚ)] hn0 (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [padicValRat.pow, hxv, hn]
        omega
      · rw [padicValRat.neg, padicValRat.mul hn0 hx0, hn, hxv]
        omega
      · rw [padicValRat.neg, padicValRat_two_cycle, hn]
        omega)
  have hnumEq :
      [x ^ 2, -(n * x), (-2 : ℚ)].foldl (· + ·) n =
        x ^ 2 - n * x + n - 2 := by
    norm_num
    ring
  rw [hnumEq, hn] at hnum
  have hdenEq :
      [(1 : ℚ), n * x, -2 * x].sum = 1 + (n - 2) * x := by
    norm_num
    ring
  have hdenLower : 0 ≤ padicValRat 3 (1 + (n - 2) * x) := by
    rw [← hdenEq]
    apply le_val_list_sum_of_nonpos_cycle 0 (by omega)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · rw [padicValRat.mul hn0 hx0, hn, hxv]
      omega
    · rw [padicValRat.mul (by norm_num) hx0,
        padicValRat.neg, padicValRat_two_cycle, hxv]
      norm_num
      omega
  have hden := orderTwentyFiveLehmerDeckTransform_denominator_ne_zero
    n x hroot
  have hyroot := orderTwentyFiveLehmerDeckTransform_isRoot n x hroot
  have hyalts := orderTwentyFiveLehmer_root_threeAdicValuation n
    (orderTwentyFiveLehmerDeckTransform n x) a ha hn hyroot
  have hyv :
      padicValRat 3 (orderTwentyFiveLehmerDeckTransform n x) =
        -a - padicValRat 3 (1 + (n - 2) * x) := by
    rw [orderTwentyFiveLehmerDeckTransform,
      padicValRat.div hnum.1 hden, hnum.2]
  rcases hyalts with hy | hy | hy | hy
  · omega
  · omega
  · exact Or.inl hy
  · exact Or.inr hy

private theorem deck_transition_constraints
    (n x y : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0)
    (hxy : orderTwentyFiveLehmerDeckTransform n x = y) :
    (padicValRat 3 x = 3 * a → padicValRat 3 y = -a) ∧
      (padicValRat 3 x = -2 * a → padicValRat 3 y = -a) ∧
      (padicValRat 3 x = a → padicValRat 3 y ≤ -a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hxv
    rw [← hxy]
    exact deck_val_of_three n x a ha hn hxv hroot
  · intro hxv
    rw [← hxy]
    exact deck_val_of_neg_two n x a ha hn hxv hroot
  · intro hxv
    rw [← hxy]
    rcases deck_val_of_one n x a ha hn hxv hroot with h | h <;> omega

private theorem exists_three_of_cyclic_transitions
    (a z0 z1 z2 z3 z4 : ℤ) (ha : 0 < a)
    (hz0 : z0 = 3 * a ∨ z0 = a ∨ z0 = -a ∨ z0 = -2 * a)
    (hz1 : z1 = 3 * a ∨ z1 = a ∨ z1 = -a ∨ z1 = -2 * a)
    (hz2 : z2 = 3 * a ∨ z2 = a ∨ z2 = -a ∨ z2 = -2 * a)
    (hz3 : z3 = 3 * a ∨ z3 = a ∨ z3 = -a ∨ z3 = -2 * a)
    (hz4 : z4 = 3 * a ∨ z4 = a ∨ z4 = -a ∨ z4 = -2 * a)
    (hsum : z0 + z1 + z2 + z3 + z4 = 0)
    (hn20 : z0 = -2 * a → z1 = -a)
    (hn21 : z1 = -2 * a → z2 = -a)
    (hn22 : z2 = -2 * a → z3 = -a)
    (hn23 : z3 = -2 * a → z4 = -a)
    (hn24 : z4 = -2 * a → z0 = -a)
    (ha0 : z0 = a → z1 ≤ -a)
    (ha1 : z1 = a → z2 ≤ -a)
    (ha2 : z2 = a → z3 ≤ -a)
    (ha3 : z3 = a → z4 ≤ -a)
    (ha4 : z4 = a → z0 ≤ -a) :
    z0 = 3 * a ∨ z1 = 3 * a ∨ z2 = 3 * a ∨ z3 = 3 * a ∨
      z4 = 3 * a := by
  by_contra hnone
  have hn0 : z0 ≠ 3 * a := fun h => hnone (Or.inl h)
  have hn1 : z1 ≠ 3 * a := fun h => hnone (Or.inr (Or.inl h))
  have hn2 : z2 ≠ 3 * a := fun h => hnone (Or.inr (Or.inr (Or.inl h)))
  have hn3 : z3 ≠ 3 * a :=
    fun h => hnone (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hn4 : z4 ≠ 3 * a :=
    fun h => hnone (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hz0le : z0 ≤ a := by rcases hz0 with h | h | h | h <;> omega
  have hz1le : z1 ≤ a := by rcases hz1 with h | h | h | h <;> omega
  have hz2le : z2 ≤ a := by rcases hz2 with h | h | h | h <;> omega
  have hz3le : z3 ≤ a := by rcases hz3 with h | h | h | h <;> omega
  have hz4le : z4 ≤ a := by rcases hz4 with h | h | h | h <;> omega
  have h01 : z0 + z1 ≤ 0 := by
    rcases hz0 with h | h | h | h
    · exact False.elim (hn0 h)
    · have := ha0 h
      omega
    · omega
    · have := hn20 h
      omega
  have h12 : z1 + z2 ≤ 0 := by
    rcases hz1 with h | h | h | h
    · exact False.elim (hn1 h)
    · have := ha1 h
      omega
    · omega
    · have := hn21 h
      omega
  have h23 : z2 + z3 ≤ 0 := by
    rcases hz2 with h | h | h | h
    · exact False.elim (hn2 h)
    · have := ha2 h
      omega
    · omega
    · have := hn22 h
      omega
  have h34 : z3 + z4 ≤ 0 := by
    rcases hz3 with h | h | h | h
    · exact False.elim (hn3 h)
    · have := ha3 h
      omega
    · omega
    · have := hn23 h
      omega
  have h40 : z4 + z0 ≤ 0 := by
    rcases hz4 with h | h | h | h
    · exact False.elim (hn4 h)
    · have := ha4 h
      omega
    · omega
    · have := hn24 h
      omega
  have he01 : z0 + z1 = 0 := by omega
  have he12 : z1 + z2 = 0 := by omega
  have he23 : z2 + z3 = 0 := by omega
  have he34 : z3 + z4 = 0 := by omega
  have he40 : z4 + z0 = 0 := by omega
  rcases hz0 with h | h | h | h <;> omega

private theorem tail_pattern_after_three
    (a u v w : ℤ) (ha : 0 < a)
    (hu : u = 3 * a ∨ u = a ∨ u = -a ∨ u = -2 * a)
    (hv : v = 3 * a ∨ v = a ∨ v = -a ∨ v = -2 * a)
    (hw : w = 3 * a ∨ w = a ∨ w = -a ∨ w = -2 * a)
    (hsum : u + v + w = -2 * a)
    (hn2u : u = -2 * a → v = -a)
    (hw3 : w = 3 * a → False)
    (hwa : w = a → False)
    (hwn2 : w = -2 * a → False) :
    u = a ∧ v = -2 * a ∧ w = -a := by
  have hweq : w = -a := by
    rcases hw with h | h | h | h
    · exact False.elim (hw3 h)
    · exact False.elim (hwa h)
    · exact h
    · exact False.elim (hwn2 h)
  rcases hu with hu | hu | hu | hu <;>
    rcases hv with hv | hv | hv | hv
  all_goals omega

private theorem cyclic_pattern_of_transitions
    (a z0 z1 z2 z3 z4 : ℤ) (ha : 0 < a)
    (hz0 : z0 = 3 * a ∨ z0 = a ∨ z0 = -a ∨ z0 = -2 * a)
    (hz1 : z1 = 3 * a ∨ z1 = a ∨ z1 = -a ∨ z1 = -2 * a)
    (hz2 : z2 = 3 * a ∨ z2 = a ∨ z2 = -a ∨ z2 = -2 * a)
    (hz3 : z3 = 3 * a ∨ z3 = a ∨ z3 = -a ∨ z3 = -2 * a)
    (hz4 : z4 = 3 * a ∨ z4 = a ∨ z4 = -a ∨ z4 = -2 * a)
    (hsum : z0 + z1 + z2 + z3 + z4 = 0)
    (h30 : z0 = 3 * a → z1 = -a)
    (h31 : z1 = 3 * a → z2 = -a)
    (h32 : z2 = 3 * a → z3 = -a)
    (h33 : z3 = 3 * a → z4 = -a)
    (h34 : z4 = 3 * a → z0 = -a)
    (hn20 : z0 = -2 * a → z1 = -a)
    (hn21 : z1 = -2 * a → z2 = -a)
    (hn22 : z2 = -2 * a → z3 = -a)
    (hn23 : z3 = -2 * a → z4 = -a)
    (hn24 : z4 = -2 * a → z0 = -a)
    (ha0 : z0 = a → z1 ≤ -a)
    (ha1 : z1 = a → z2 ≤ -a)
    (ha2 : z2 = a → z3 ≤ -a)
    (ha3 : z3 = a → z4 ≤ -a)
    (ha4 : z4 = a → z0 ≤ -a) :
    (z0 = 3 * a ∧ z1 = -a ∧ z2 = a ∧ z3 = -2 * a ∧ z4 = -a) ∨
      (z0 = -a ∧ z1 = 3 * a ∧ z2 = -a ∧ z3 = a ∧ z4 = -2 * a) ∨
      (z0 = -2 * a ∧ z1 = -a ∧ z2 = 3 * a ∧ z3 = -a ∧ z4 = a) ∨
      (z0 = a ∧ z1 = -2 * a ∧ z2 = -a ∧ z3 = 3 * a ∧ z4 = -a) ∨
      (z0 = -a ∧ z1 = a ∧ z2 = -2 * a ∧ z3 = -a ∧ z4 = 3 * a) := by
  have hthree := exists_three_of_cyclic_transitions a z0 z1 z2 z3 z4 ha
    hz0 hz1 hz2 hz3 hz4 hsum hn20 hn21 hn22 hn23 hn24
    ha0 ha1 ha2 ha3 ha4
  rcases hthree with h0 | h1 | h2 | h3 | h4
  · have h1' := h30 h0
    obtain ⟨h2', h3', h4'⟩ := tail_pattern_after_three
      a z2 z3 z4 ha hz2 hz3 hz4 (by omega) hn22
      (fun h => by have := h34 h; omega)
      (fun h => by have := ha4 h; omega)
      (fun h => by have := hn24 h; omega)
    exact Or.inl ⟨h0, h1', h2', h3', h4'⟩
  · have h2' := h31 h1
    obtain ⟨h3', h4', h0'⟩ := tail_pattern_after_three
      a z3 z4 z0 ha hz3 hz4 hz0 (by omega) hn23
      (fun h => by have := h30 h; omega)
      (fun h => by have := ha0 h; omega)
      (fun h => by have := hn20 h; omega)
    exact Or.inr (Or.inl ⟨h0', h1, h2', h3', h4'⟩)
  · have h3' := h32 h2
    obtain ⟨h4', h0', h1'⟩ := tail_pattern_after_three
      a z4 z0 z1 ha hz4 hz0 hz1 (by omega) hn24
      (fun h => by have := h31 h; omega)
      (fun h => by have := ha1 h; omega)
      (fun h => by have := hn21 h; omega)
    exact Or.inr (Or.inr (Or.inl ⟨h0', h1', h2, h3', h4'⟩))
  · have h4' := h33 h3
    obtain ⟨h0', h1', h2'⟩ := tail_pattern_after_three
      a z0 z1 z2 ha hz0 hz1 hz2 (by omega) hn20
      (fun h => by have := h32 h; omega)
      (fun h => by have := ha2 h; omega)
      (fun h => by have := hn22 h; omega)
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h0', h1', h2', h3, h4'⟩)))
  · have h0' := h34 h4
    obtain ⟨h1', h2', h3'⟩ := tail_pattern_after_three
      a z1 z2 z3 ha hz1 hz2 hz3 (by omega) hn21
      (fun h => by have := h33 h; omega)
      (fun h => by have := ha3 h; omega)
      (fun h => by have := hn23 h; omega)
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h0', h1', h2', h3', h4⟩)))

/-- Five rational Lehmer roots in one norm-one deck cycle have the cyclic
3-adic valuation pattern `(3a,-a,a,-2a,-a)`, up to rotation. -/
theorem orderTwentyFiveLehmer_fiveCycle_threeAdicValuationPattern
    (n x0 x1 x2 x3 x4 : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hroot0 : orderTwentyFiveLehmerPolynomial n x0 = 0)
    (hroot1 : orderTwentyFiveLehmerPolynomial n x1 = 0)
    (hroot2 : orderTwentyFiveLehmerPolynomial n x2 = 0)
    (hroot3 : orderTwentyFiveLehmerPolynomial n x3 = 0)
    (hroot4 : orderTwentyFiveLehmerPolynomial n x4 = 0)
    (h01 : orderTwentyFiveLehmerDeckTransform n x0 = x1)
    (h12 : orderTwentyFiveLehmerDeckTransform n x1 = x2)
    (h23 : orderTwentyFiveLehmerDeckTransform n x2 = x3)
    (h34 : orderTwentyFiveLehmerDeckTransform n x3 = x4)
    (h40 : orderTwentyFiveLehmerDeckTransform n x4 = x0)
    (hproduct : x0 * x1 * x2 * x3 * x4 = 1) :
    (padicValRat 3 x0 = 3 * a ∧ padicValRat 3 x1 = -a ∧
        padicValRat 3 x2 = a ∧ padicValRat 3 x3 = -2 * a ∧
        padicValRat 3 x4 = -a) ∨
      (padicValRat 3 x0 = -a ∧ padicValRat 3 x1 = 3 * a ∧
        padicValRat 3 x2 = -a ∧ padicValRat 3 x3 = a ∧
        padicValRat 3 x4 = -2 * a) ∨
      (padicValRat 3 x0 = -2 * a ∧ padicValRat 3 x1 = -a ∧
        padicValRat 3 x2 = 3 * a ∧ padicValRat 3 x3 = -a ∧
        padicValRat 3 x4 = a) ∨
      (padicValRat 3 x0 = a ∧ padicValRat 3 x1 = -2 * a ∧
        padicValRat 3 x2 = -a ∧ padicValRat 3 x3 = 3 * a ∧
        padicValRat 3 x4 = -a) ∨
      (padicValRat 3 x0 = -a ∧ padicValRat 3 x1 = a ∧
        padicValRat 3 x2 = -2 * a ∧ padicValRat 3 x3 = -a ∧
        padicValRat 3 x4 = 3 * a) := by
  have hx0 := root_ne_zero_cycle n x0 hroot0
  have hx1 := root_ne_zero_cycle n x1 hroot1
  have hx2 := root_ne_zero_cycle n x2 hroot2
  have hx3 := root_ne_zero_cycle n x3 hroot3
  have hx4 := root_ne_zero_cycle n x4 hroot4
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
  have ht0 := deck_transition_constraints n x0 x1 a ha hn hroot0 h01
  have ht1 := deck_transition_constraints n x1 x2 a ha hn hroot1 h12
  have ht2 := deck_transition_constraints n x2 x3 a ha hn hroot2 h23
  have ht3 := deck_transition_constraints n x3 x4 a ha hn hroot3 h34
  have ht4 := deck_transition_constraints n x4 x0 a ha hn hroot4 h40
  simpa only [z0, z1, z2, z3, z4] using
    cyclic_pattern_of_transitions a z0 z1 z2 z3 z4 ha
      hz0 hz1 hz2 hz3 hz4 hzsum ht0.1 ht1.1 ht2.1 ht3.1 ht4.1
      ht0.2.1 ht1.2.1 ht2.2.1 ht3.2.1 ht4.2.1
      ht0.2.2 ht1.2.2 ht2.2.2 ht3.2.2 ht4.2.2

/-- On the `-a` Newton slope, a positive-valued successor forces the root
to approach the diagonal cusp `x = n`: the difference is 3-integral even
though both `x` and `n` have valuation `-a`. -/
theorem orderTwentyFiveLehmer_negOneSlope_cuspCongruence
    (n x y : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hxv : padicValRat 3 x = -a)
    (hyv : padicValRat 3 y = a ∨ padicValRat 3 y = 3 * a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0)
    (hxy : orderTwentyFiveLehmerDeckTransform n x = y) :
    0 ≤ padicValRat 3 (x - n) := by
  have hn0 : n ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hn
    omega
  have hx0 := root_ne_zero_cycle n x hroot
  have hyroot : orderTwentyFiveLehmerPolynomial n y = 0 := by
    rw [← hxy]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n x hroot
  have hy0 := root_ne_zero_cycle n y hyroot
  have hden := val_foldl_add_eq_of_head_lt_cycle (n * x)
    [(1 : ℚ), -2 * x] (mul_ne_zero hn0 hx0) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [padicValRat.mul hn0 hx0, hn, hxv]
        norm_num
        omega
      · rw [padicValRat.mul hn0 hx0, hn, hxv,
          padicValRat.mul (by norm_num) hx0,
          padicValRat.neg, padicValRat_two_cycle]
        norm_num
        omega)
  have hdenEq :
      [(1 : ℚ), -2 * x].foldl (· + ·) (n * x) =
        1 + (n - 2) * x := by
    norm_num
    ring
  rw [hdenEq, padicValRat.mul hn0 hx0, hn, hxv] at hden
  have hnum0 : x ^ 2 - n * x + n - 2 ≠ 0 := by
    intro hzero
    apply hy0
    rw [← hxy, orderTwentyFiveLehmerDeckTransform, hzero, zero_div]
  have hquot :
      padicValRat 3 y =
        padicValRat 3 (x ^ 2 - n * x + n - 2) -
          padicValRat 3 (1 + (n - 2) * x) := by
    rw [← hxy, orderTwentyFiveLehmerDeckTransform,
      padicValRat.div hnum0 hden.1]
  have hnumLower :
      -a ≤ padicValRat 3 (x ^ 2 - n * x + n - 2) := by
    rw [hden.2] at hquot
    rcases hyv with hyv | hyv <;> omega
  have hnMinus := val_add_eq_left_of_lt_cycle n (-2) hn0 (by
    rw [padicValRat.neg, padicValRat_two_cycle, hn]
    omega)
  have hnMinusEq : n + (-2) = n - 2 := by ring
  rw [hnMinusEq, hn] at hnMinus
  by_contra hnot
  have hxnval : padicValRat 3 (x - n) < 0 := by omega
  have hxn0 : x - n ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hxnval
    omega
  have hprod0 : x * (x - n) ≠ 0 := mul_ne_zero hx0 hxn0
  have hprodval :
      padicValRat 3 (x * (x - n)) =
        -a + padicValRat 3 (x - n) := by
    rw [padicValRat.mul hx0 hxn0, hxv]
  have hsum := val_add_eq_left_of_lt_cycle
    (x * (x - n)) (n - 2) hprod0 (by
      rw [hprodval, hnMinus.2]
      omega)
  have hsumEq :
      x * (x - n) + (n - 2) = x ^ 2 - n * x + n - 2 := by ring
  rw [hsumEq, hprodval] at hsum
  omega

private theorem root_infinityChart_of_cuspCongruence
    (n x : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0)
    (hcusp : padicValRat 3 x = -a → 0 ≤ padicValRat 3 (x - n)) :
    (padicValRat 3 x = 3 * a ∧ padicValRat 3 (x / n) = 4 * a) ∨
      (padicValRat 3 x = a ∧ padicValRat 3 (x / n) = 2 * a) ∨
      (padicValRat 3 x = -a ∧
        (x = n ∨ 0 < padicValRat 3 (x / n - 1))) ∨
      (padicValRat 3 x = -2 * a ∧ padicValRat 3 (n / x) = a) := by
  have hn0 : n ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hn
    omega
  have hx0 := root_ne_zero_cycle n x hroot
  rcases orderTwentyFiveLehmer_root_threeAdicValuation
      n x a ha hn hroot with hxv | hxv | hxv | hxv
  · left
    refine ⟨hxv, ?_⟩
    rw [padicValRat.div hx0 hn0, hxv, hn]
    omega
  · right; left
    refine ⟨hxv, ?_⟩
    rw [padicValRat.div hx0 hn0, hxv, hn]
    omega
  · right; right; left
    refine ⟨hxv, ?_⟩
    by_cases hxn : x = n
    · exact Or.inl hxn
    · right
      have hdiff : x - n ≠ 0 := sub_ne_zero.mpr hxn
      have hid : x / n - 1 = (x - n) / n := by
        field_simp [hn0]
      rw [hid, padicValRat.div hdiff hn0, hn]
      have := hcusp hxv
      omega
  · right; right; right
    refine ⟨hxv, ?_⟩
    rw [padicValRat.div hn0 hx0, hn, hxv]
    omega


private theorem negOne_successors_positive_of_cyclic_pattern
    (a z0 z1 z2 z3 z4 : ℤ) (ha : 0 < a)
    (hpattern :
      (z0 = 3 * a ∧ z1 = -a ∧ z2 = a ∧ z3 = -2 * a ∧ z4 = -a) ∨
        (z0 = -a ∧ z1 = 3 * a ∧ z2 = -a ∧ z3 = a ∧ z4 = -2 * a) ∨
        (z0 = -2 * a ∧ z1 = -a ∧ z2 = 3 * a ∧ z3 = -a ∧ z4 = a) ∨
        (z0 = a ∧ z1 = -2 * a ∧ z2 = -a ∧ z3 = 3 * a ∧ z4 = -a) ∨
        (z0 = -a ∧ z1 = a ∧ z2 = -2 * a ∧ z3 = -a ∧ z4 = 3 * a)) :
    (z0 = -a → z1 = a ∨ z1 = 3 * a) ∧
      (z1 = -a → z2 = a ∨ z2 = 3 * a) ∧
      (z2 = -a → z3 = a ∨ z3 = 3 * a) ∧
      (z3 = -a → z4 = a ∨ z4 = 3 * a) ∧
      (z4 = -a → z0 = a ∨ z0 = 3 * a) := by
  rcases hpattern with h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2, h3, h4⟩
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro hz <;> omega

/-- The two `-a`-valued roots in the marked five-cycle approach the diagonal
infinity node `x = n`: after subtracting the negatively valued Lehmer
parameter, the difference is 3-integral.  The ratio valuations for all four
slopes also locate every root in one of the three infinity charts. -/
theorem orderTwentyFive_threeAdicCuspCongruences_of_marked_order
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
        let N := -orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ))
        (∀ x ∈ [orderTwentyFiveBrunaultXZero b c,
              orderTwentyFiveBrunaultXOne b c,
              orderTwentyFiveBrunaultXTwo b c,
              orderTwentyFiveBrunaultXThree b c,
              orderTwentyFiveBrunaultXFour b c],
            padicValRat 3 x = -a → 0 ≤ padicValRat 3 (x - N)) ∧
          ∀ x ∈ [orderTwentyFiveBrunaultXZero b c,
              orderTwentyFiveBrunaultXOne b c,
              orderTwentyFiveBrunaultXTwo b c,
              orderTwentyFiveBrunaultXThree b c,
              orderTwentyFiveBrunaultXFour b c],
            (padicValRat 3 x = 3 * a ∧
                padicValRat 3 (x / N) = 4 * a) ∨
              (padicValRat 3 x = a ∧
                padicValRat 3 (x / N) = 2 * a) ∨
              (padicValRat 3 x = -a ∧
                (x = N ∨ 0 < padicValRat 3 (x / N - 1))) ∨
              (padicValRat 3 x = -2 * a ∧
                padicValRat 3 (N / x) = a) := by
  obtain ⟨k, hk, -, hkParameter, hkNotUnit, hreciprocal,
      -, -, hcover⟩ :=
    orderTwentyFive_kummerCover_of_marked_order b c hb h00 horder
  obtain ⟨m, n, hm0, hn0, hmn, hm3, hn3, hhaupt, -⟩ :=
    orderTwentyFiveKummerCover_threeAdicOrientation
      k (orderTwentyFiveBrunaultXZero b c) hk hkNotUnit hcover
  obtain ⟨a, ha, hval⟩ :=
    orderTwentyFiveOrientedFraction_threeAdicValuation
      m n hm0 hn0 hm3 hn3
  have hparameter :
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
        orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) := hkParameter.trans hhaupt.symm
  have hreciprocal' :
      orderTwentyFiveRatIsThreeIntegral
        (-5 / orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ))) := by
    simpa only [hhaupt] using hreciprocal
  let k' : ℚ := (m : ℚ) / (n : ℚ)
  let N : ℚ := -orderTwentyFiveFifthPowerHauptmodul k'
  let r0 := orderTwentyFiveBrunaultXZero b c
  let r1 := orderTwentyFiveBrunaultXOne b c
  let r2 := orderTwentyFiveBrunaultXTwo b c
  let r3 := orderTwentyFiveBrunaultXThree b c
  let r4 := orderTwentyFiveBrunaultXFour b c
  have hN : N = orderTwentyFiveOrbitParameter r0 r1 r2 r3 r4 := by
    dsimp only [N, r0, r1, r2, r3, r4, k']
    linarith
  have hNv : padicValRat 3 N = -a := by
    dsimp only [N]
    exact orderTwentyFiveFifthPowerHauptmodul_threeAdicValuation
      k' a ha (by simpa only [k'] using hval)
  have hor0 := orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order
    b c hb h00 horder
  have hor1 := orderTwentyFiveOrbitRelationOne_eq_zero_of_marked_order
    b c hb h00 horder
  have hor2 := orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order
    b c hb h00 horder
  have hor3 := orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order
    b c hb h00 horder
  have hor4 := orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order
    b c hb h00 horder
  have hor5 := orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
    b c hb h00 horder
  have hxOne : r0 ≠ 1 := by
    dsimp only [r0]
    rw [orderTwentyFiveBrunaultXZero_eq_U]
    exact orderTwentyFiveBrunaultU_ne_one_of_marked_order
      b c hb h00 horder
  have hroot0 : orderTwentyFiveLehmerPolynomial N r0 = 0 := by
    rw [hN]
    exact (orderTwentyFiveLehmer_selectedRoots_of_orbit
      r0 r1 r2 r3 r4 hxOne hor0 hor1 hor2 hor3 hor4 hor5).1
  have hcycle := orderTwentyFiveLehmerDeckTransform_cycle_of_orbit
    r0 r1 r2 r3 r4 hxOne hor0 hor1 hor2 hor3 hor4 hor5
  dsimp only at hcycle
  rw [← hN] at hcycle
  obtain ⟨h01, h12, h23, h34, h40⟩ := hcycle
  have hroot1 : orderTwentyFiveLehmerPolynomial N r1 = 0 := by
    rw [← h01]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r0 hroot0
  have hroot2 : orderTwentyFiveLehmerPolynomial N r2 = 0 := by
    rw [← h12]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r1 hroot1
  have hroot3 : orderTwentyFiveLehmerPolynomial N r3 = 0 := by
    rw [← h23]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r2 hroot2
  have hroot4 : orderTwentyFiveLehmerPolynomial N r4 = 0 := by
    rw [← h34]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r3 hroot3
  have hproduct : r0 * r1 * r2 * r3 * r4 = 1 := by
    simpa only [orderTwentyFiveOrbitRelationFive, sub_eq_zero] using hor5
  have hpattern :=
    orderTwentyFiveLehmer_fiveCycle_threeAdicValuationPattern
      N r0 r1 r2 r3 r4 a ha hNv hroot0 hroot1 hroot2 hroot3 hroot4
      h01 h12 h23 h34 h40 hproduct
  have hpositive := negOne_successors_positive_of_cyclic_pattern a
    (padicValRat 3 r0) (padicValRat 3 r1) (padicValRat 3 r2)
    (padicValRat 3 r3) (padicValRat 3 r4) ha (by
      simpa only [r0, r1, r2, r3, r4] using hpattern)
  have hcusp : ∀ x ∈ [r0, r1, r2, r3, r4],
      padicValRat 3 x = -a → 0 ≤ padicValRat 3 (x - N) := by
    intro x hx hxv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact orderTwentyFiveLehmer_negOneSlope_cuspCongruence
        N r0 r1 a ha hNv hxv (hpositive.1 hxv) hroot0 h01
    · exact orderTwentyFiveLehmer_negOneSlope_cuspCongruence
        N r1 r2 a ha hNv hxv (hpositive.2.1 hxv) hroot1 h12
    · exact orderTwentyFiveLehmer_negOneSlope_cuspCongruence
        N r2 r3 a ha hNv hxv (hpositive.2.2.1 hxv) hroot2 h23
    · exact orderTwentyFiveLehmer_negOneSlope_cuspCongruence
        N r3 r4 a ha hNv hxv (hpositive.2.2.2.1 hxv) hroot3 h34
    · exact orderTwentyFiveLehmer_negOneSlope_cuspCongruence
        N r4 r0 a ha hNv hxv (hpositive.2.2.2.2 hxv) hroot4 h40
  have hcharts : ∀ x ∈ [r0, r1, r2, r3, r4],
      (padicValRat 3 x = 3 * a ∧ padicValRat 3 (x / N) = 4 * a) ∨
        (padicValRat 3 x = a ∧ padicValRat 3 (x / N) = 2 * a) ∨
        (padicValRat 3 x = -a ∧
          (x = N ∨ 0 < padicValRat 3 (x / N - 1))) ∨
        (padicValRat 3 x = -2 * a ∧
          padicValRat 3 (N / x) = a) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact root_infinityChart_of_cuspCongruence
        N r0 a ha hNv hroot0 (hcusp r0 (by simp))
    · exact root_infinityChart_of_cuspCongruence
        N r1 a ha hNv hroot1 (hcusp r1 (by simp))
    · exact root_infinityChart_of_cuspCongruence
        N r2 a ha hNv hroot2 (hcusp r2 (by simp))
    · exact root_infinityChart_of_cuspCongruence
        N r3 a ha hNv hroot3 (hcusp r3 (by simp))
    · exact root_infinityChart_of_cuspCongruence
        N r4 a ha hNv hroot4 (hcusp r4 (by simp))
  refine ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
    hreciprocal', a, ha, hval, ?_⟩
  constructor
  · simpa only [N, k', r0, r1, r2, r3, r4] using hcusp
  · simpa only [N, k', r0, r1, r2, r3, r4] using hcharts


/-- A rational marked point of order twenty-five has cyclic Brunault-root
valuations `(3a,-a,a,-2a,-a)`, up to the choice of starting coordinate. -/
theorem orderTwentyFive_exactThreeAdicRootValuationCycle_of_marked_order
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
        ((padicValRat 3 (orderTwentyFiveBrunaultXZero b c) = 3 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXOne b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXTwo b c) = a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXThree b c) = -2 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXFour b c) = -a) ∨
          (padicValRat 3 (orderTwentyFiveBrunaultXZero b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXOne b c) = 3 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXTwo b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXThree b c) = a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXFour b c) = -2 * a) ∨
          (padicValRat 3 (orderTwentyFiveBrunaultXZero b c) = -2 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXOne b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXTwo b c) = 3 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXThree b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXFour b c) = a) ∨
          (padicValRat 3 (orderTwentyFiveBrunaultXZero b c) = a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXOne b c) = -2 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXTwo b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXThree b c) = 3 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXFour b c) = -a) ∨
          (padicValRat 3 (orderTwentyFiveBrunaultXZero b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXOne b c) = a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXTwo b c) = -2 * a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXThree b c) = -a ∧
            padicValRat 3 (orderTwentyFiveBrunaultXFour b c) = 3 * a)) := by
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
  have hor0 := orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order
    b c hb h00 horder
  have hor1 := orderTwentyFiveOrbitRelationOne_eq_zero_of_marked_order
    b c hb h00 horder
  have hor2 := orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order
    b c hb h00 horder
  have hor3 := orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order
    b c hb h00 horder
  have hor4 := orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order
    b c hb h00 horder
  have hor5 := orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
    b c hb h00 horder
  have hroot0 : orderTwentyFiveLehmerPolynomial N r0 = 0 := by
    rw [hN]
    exact (orderTwentyFiveLehmer_selectedRoots_of_orbit
      r0 r1 r2 r3 r4 (by simpa only [r0] using hxOne)
      hor0 hor1 hor2 hor3 hor4 hor5).1
  have hcycle := orderTwentyFiveLehmerDeckTransform_cycle_of_orbit
    r0 r1 r2 r3 r4 (by simpa only [r0] using hxOne)
    hor0 hor1 hor2 hor3 hor4 hor5
  dsimp only at hcycle
  rw [← hN] at hcycle
  obtain ⟨h01, h12, h23, h34, h40⟩ := hcycle
  have hroot1 : orderTwentyFiveLehmerPolynomial N r1 = 0 := by
    rw [← h01]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r0 hroot0
  have hroot2 : orderTwentyFiveLehmerPolynomial N r2 = 0 := by
    rw [← h12]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r1 hroot1
  have hroot3 : orderTwentyFiveLehmerPolynomial N r3 = 0 := by
    rw [← h23]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r2 hroot2
  have hroot4 : orderTwentyFiveLehmerPolynomial N r4 = 0 := by
    rw [← h34]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r3 hroot3
  have hproduct : r0 * r1 * r2 * r3 * r4 = 1 := by
    simpa only [orderTwentyFiveOrbitRelationFive, sub_eq_zero] using hor5
  have hpattern :=
    orderTwentyFiveLehmer_fiveCycle_threeAdicValuationPattern
      N r0 r1 r2 r3 r4 a ha hNv hroot0 hroot1 hroot2 hroot3 hroot4
      h01 h12 h23 h34 h40 hproduct
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
  · simpa only [r0, r1, r2, r3, r4] using hpattern

end MazurTorsion.Kubert
