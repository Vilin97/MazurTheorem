/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Torsion

/-!
# An abstract halving descent for the `X₁(13)` endpoint

This file records the elementary infinite-descent argument needed after a
Kummer-height construction.  It deliberately makes no claim that the data
below have already been constructed for the Jacobian of `X₁(13)`.

Suppose doubling is surjective on an abelian group, a Kummer map identifies
only a point with itself or its negative, and a natural-valued Kummer height
has finite sublevel sets.  If the height of a half is bounded by the larger of
a fixed constant and the height of the original point, then every point is
torsion.  Indeed, repeated halves stay in one finite Kummer-height sublevel,
so two Kummer images collide.  If the colliding indices are `i < j`, the
original point is killed by one of the explicit odd integers
`2 ^ (j - i) - 1` and `2 ^ (j - i) + 1`.

The natural-valued formulation avoids any real-height limit argument.  The
final two corollaries are genuine downstream consumers: the group is torsion,
and a finitely generated such group is finite (and has free rank zero).
-/

namespace MazurTorsion.XOneThirteenAbstractHalvingDescent

/-- The exact abstract inputs to the elementary repeated-halving argument.

The finiteness hypothesis concerns Kummer images, rather than group points;
the `collision` field supplies the missing two-to-one control. -/
structure Certificate (A K : Type*) [AddCommGroup A] where
  kummer : A → K
  height : K → ℕ
  baseBound : ℕ
  double_surjective : ∀ P : A, ∃ Q : A, 2 • Q = P
  collision : ∀ {P Q : A}, kummer P = kummer Q → P = Q ∨ P = -Q
  finite_sublevel : ∀ N : ℕ, Finite {x : K // height x ≤ N}
  height_of_half : ∀ Q : A,
    height (kummer Q) ≤ max baseBound (height (kummer (2 • Q)))

variable {A K : Type*} [AddCommGroup A]

namespace Certificate

/-- A chosen half.  No uniqueness is required. -/
noncomputable def half (D : Certificate A K) (P : A) : A :=
  Classical.choose (D.double_surjective P)

@[simp]
theorem two_nsmul_half (D : Certificate A K) (P : A) :
    2 • D.half P = P :=
  Classical.choose_spec (D.double_surjective P)

/-- A coherent sequence of repeated chosen halves, starting at `P`. -/
noncomputable def halves (D : Certificate A K) (P : A) : ℕ → A
  | 0 => P
  | n + 1 => D.half (D.halves P n)

@[simp]
theorem halves_zero (D : Certificate A K) (P : A) : D.halves P 0 = P :=
  rfl

@[simp]
theorem two_nsmul_halves_succ (D : Certificate A K) (P : A) (n : ℕ) :
    2 • D.halves P (n + 1) = D.halves P n := by
  rw [halves]
  exact D.two_nsmul_half _

/-- Moving `k` steps backwards in the halving sequence is multiplication by
`2 ^ k`. -/
theorem pow_two_nsmul_halves_add (D : Certificate A K) (P : A) (n k : ℕ) :
    2 ^ k • D.halves P (n + k) = D.halves P n := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        2 ^ (k + 1) • D.halves P (n + (k + 1)) =
            2 ^ k • (2 • D.halves P ((n + k) + 1)) := by
              simp only [pow_succ', mul_nsmul, Nat.add_assoc]
        _ = 2 ^ k • D.halves P (n + k) := by
              rw [D.two_nsmul_halves_succ]
        _ = D.halves P n := ih

/-- Repeated halves of a fixed point remain in one natural-height sublevel. -/
theorem height_halves_le (D : Certificate A K) (P : A) (n : ℕ) :
    D.height (D.kummer (D.halves P n)) ≤
      max D.baseBound (D.height (D.kummer P)) := by
  induction n with
  | zero => exact le_max_right _ _
  | succ n ih =>
      calc
        D.height (D.kummer (D.halves P (n + 1))) ≤
            max D.baseBound
              (D.height (D.kummer (2 • D.halves P (n + 1)))) :=
          D.height_of_half _
        _ = max D.baseBound (D.height (D.kummer (D.halves P n))) := by
          rw [D.two_nsmul_halves_succ]
        _ ≤ max D.baseBound (D.height (D.kummer P)) :=
          max_le (le_max_left _ _) ih

private theorem annihilator_moves_to_start (D : Certificate A K) (P : A)
    {j r : ℕ} (hr : r • D.halves P j = 0) : r • P = 0 := by
  have hstart : 2 ^ j • D.halves P j = P := by
    simpa using D.pow_two_nsmul_halves_add P 0 j
  calc
    r • P = r • (2 ^ j • D.halves P j) := by rw [hstart]
    _ = 2 ^ j • (r • D.halves P j) := by
      rw [← mul_nsmul', ← mul_nsmul]
    _ = 0 := by rw [hr, nsmul_zero]

private theorem annihilator_of_collision (D : Certificate A K) (P : A)
    {i j : ℕ} (hij : i < j)
    (hcollision : D.kummer (D.halves P i) = D.kummer (D.halves P j)) :
    (2 ^ (j - i) - 1) • P = 0 ∨ (2 ^ (j - i) + 1) • P = 0 := by
  have hscale : 2 ^ (j - i) • D.halves P j = D.halves P i := by
    have hi : i ≤ j := Nat.le_of_lt hij
    simpa [Nat.add_sub_of_le hi] using
      D.pow_two_nsmul_halves_add P i (j - i)
  rcases D.collision hcollision with heq | hneg
  · left
    apply D.annihilator_moves_to_start P (j := j)
    have hpow : 1 ≤ 2 ^ (j - i) :=
      Nat.one_le_pow (j - i) 2 (by norm_num)
    rw [sub_nsmul _ hpow, hscale, heq, one_nsmul, add_neg_cancel]
  · right
    apply D.annihilator_moves_to_start P (j := j)
    rw [add_nsmul, hscale, hneg, one_nsmul, neg_add_cancel]

/-- The quantitative conclusion of repeated halving: two distinct indices
collide, and one of the corresponding explicit odd integers kills `P`. -/
theorem exists_explicit_annihilator (D : Certificate A K) (P : A) :
    ∃ i j : ℕ, i < j ∧
      ((2 ^ (j - i) - 1) • P = 0 ∨ (2 ^ (j - i) + 1) • P = 0) := by
  let M := max D.baseBound (D.height (D.kummer P))
  let boundedKummer : ℕ → {x : K // D.height x ≤ M} := fun n ↦
    ⟨D.kummer (D.halves P n), D.height_halves_le P n⟩
  letI : Finite {x : K // D.height x ≤ M} := D.finite_sublevel M
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite boundedKummer
  have hk : D.kummer (D.halves P i) = D.kummer (D.halves P j) :=
    congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact ⟨i, j, hij', D.annihilator_of_collision P hij' hk⟩
  · exact ⟨j, i, hji', D.annihilator_of_collision P hji' hk.symm⟩

/-- The explicit alternatives in `exists_explicit_annihilator` always supply
a positive odd annihilator. -/
theorem exists_odd_annihilator (D : Certificate A K) (P : A) :
    ∃ n : ℕ, Odd n ∧ 0 < n ∧ n • P = 0 := by
  obtain ⟨i, j, hij, hannihilator⟩ := D.exists_explicit_annihilator P
  have hdiff : j - i ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hij)
  have heven : Even (2 ^ (j - i)) := even_two.pow_of_ne_zero hdiff
  rcases hannihilator with hminus | hplus
  · refine ⟨2 ^ (j - i) - 1, ?_, ?_, hminus⟩
    · exact Nat.Even.sub_odd (one_le_pow₀ one_le_two) heven odd_one
    · have htwo : 2 ≤ 2 ^ (j - i) := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j - i) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.sub_pos_of_lt hij)
      omega
  · exact ⟨2 ^ (j - i) + 1, Even.add_odd heven odd_one, by positivity, hplus⟩

/-- Every point has finite additive order. -/
theorem isOfFinAddOrder (D : Certificate A K) (P : A) : IsOfFinAddOrder P := by
  obtain ⟨n, _, hn, hkill⟩ := D.exists_odd_annihilator P
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  exact ⟨n, hn, hkill⟩

/-- A certificate makes the entire source group torsion. -/
theorem isTorsion (D : Certificate A K) : AddMonoid.IsTorsion A := fun P ↦
  D.isOfFinAddOrder P

/-- A finitely generated abelian group admitting such a certificate is
finite.  This is a concrete downstream consumer of `isTorsion`. -/
theorem finite [AddGroup.FG A] (D : Certificate A K) : Finite A :=
  AddCommGroup.finite_of_fg_torsion A (D.isTorsion)

/-- Equivalently, a finitely generated source has free rank zero. -/
theorem freeRank_eq_zero [AddGroup.FG A] (D : Certificate A K) :
    AddCommGroup.freeRank A = 0 :=
  AddCommGroup.freeRank_eq_zero (D.isTorsion)

end Certificate

end MazurTorsion.XOneThirteenAbstractHalvingDescent
