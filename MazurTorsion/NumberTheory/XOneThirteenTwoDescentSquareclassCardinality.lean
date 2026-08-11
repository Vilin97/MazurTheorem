/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.GroupTheory.IndexNSmulFG
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Squareclass cardinality for rank-two finitely generated abelian groups

This file proves a generic counting lemma used after a unit-group
calculation.  If a finitely generated abelian group has `ℤ`-rank two and
cyclic torsion, then its quotient by doubles has cardinality at most eight.
If the group contains an element of exact additive order two, the cardinality
is exactly eight.

No number-field or unit-group hypothesis is asserted here.  A downstream
consumer must separately supply finite generation, the rank, cyclicity of
the torsion subgroup, and the element of order two.
-/

namespace MazurTorsion.XOneThirteenTwoDescentSquareclassCardinality

variable {A : Type*} [AddCommGroup A]

/-- The kernel of doubling in a finitely generated abelian group is finite. -/
theorem finite_double_kernel [AddGroup.FG A] :
    Finite (nsmulAddMonoidHom (α := A) 2).ker := by
  letI : (nsmulAddMonoidHom (α := A) 2).range.FiniteIndex :=
    AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A (by decide)
  have hindex := AddSubgroup.index_range_nsmul_of_fg A (n := 2) (by decide)
  apply Nat.finite_of_card_ne_zero
  intro hzero
  have hne : (nsmulAddMonoidHom (α := A) 2).range.index ≠ 0 :=
    AddSubgroup.FiniteIndex.index_ne_zero
  apply hne
  rw [hindex, hzero, mul_zero]

/-- If the torsion subgroup is cyclic, the kernel of doubling has at most
two elements. -/
theorem natCard_double_kernel_le_two [AddGroup.FG A]
    [IsAddCyclic (AddCommGroup.torsion A)] :
    Nat.card (nsmulAddMonoidHom (α := A) 2).ker ≤ 2 := by
  classical
  let K := (nsmulAddMonoidHom (α := A) 2).ker
  letI : Finite K := finite_double_kernel
  have hKle : K ≤ AddCommGroup.torsion A := by
    intro x hx
    rw [AddCommGroup.mem_torsion]
    rw [AddMonoidHom.mem_ker] at hx
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    exact ⟨2, by decide, by simpa only [nsmulAddMonoidHom_apply] using hx⟩
  letI : IsAddCyclic K := AddSubgroup.isAddCyclic_of_le hKle
  letI : Fintype K := Fintype.ofFinite K
  have hzero (x : K) : 2 • x = 0 := by
    apply Subtype.ext
    change 2 • (x : A) = 0
    simpa only [K, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] using x.property
  have hall : (Finset.univ.filter fun x : K => 2 • x = 0) = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (hzero x)
  have hbound :=
    IsAddCyclic.card_nsmul_eq_zero_le (α := K) (n := 2) (by decide)
  rw [hall, Finset.card_univ, Fintype.card_eq_nat_card] at hbound
  exact hbound

/-- A rank-two finitely generated abelian group with cyclic torsion has at
most eight squareclasses modulo doubles. -/
theorem natCard_quotient_doubles_le_eight [AddGroup.FG A]
    [IsAddCyclic (AddCommGroup.torsion A)]
    (hrank : Module.finrank ℤ A = 2) :
    Nat.card (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) ≤ 8 := by
  calc
    Nat.card (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) =
        4 * Nat.card (nsmulAddMonoidHom (α := A) 2).ker := by
      simpa [AddSubgroup.index_eq_card, hrank] using
        (AddSubgroup.index_range_nsmul_of_fg A (n := 2) (by decide))
    _ ≤ 4 * 2 := Nat.mul_le_mul_left 4 natCard_double_kernel_le_two
    _ = 8 := by norm_num

/-- If a rank-two finitely generated abelian group with cyclic torsion has
an element of exact order two, then it has exactly eight squareclasses
modulo doubles. -/
theorem natCard_quotient_doubles_eq_eight [AddGroup.FG A]
    [IsAddCyclic (AddCommGroup.torsion A)]
    (hrank : Module.finrank ℤ A = 2) (a : A) (ha : addOrderOf a = 2) :
    Nat.card (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) = 8 := by
  let K := (nsmulAddMonoidHom (α := A) 2).ker
  letI : Finite K := finite_double_kernel
  have ha_ne : a ≠ 0 := by
    intro h
    subst a
    simp at ha
  have ha_double : 2 • a = 0 := by
    rw [← ha]
    exact addOrderOf_nsmul_eq_zero a
  have haK : a ∈ K := by
    rw [AddMonoidHom.mem_ker]
    simpa only [nsmulAddMonoidHom_apply] using ha_double
  let k : K := ⟨a, haK⟩
  have hk_ne : k ≠ 0 := by
    intro hk
    apply ha_ne
    exact congrArg Subtype.val hk
  letI : Nontrivial K := ⟨⟨k, 0, hk_ne⟩⟩
  have hcard_ge : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard_le : Nat.card K ≤ 2 :=
    natCard_double_kernel_le_two (A := A)
  have hcard : Nat.card K = 2 := Nat.le_antisymm hcard_le hcard_ge
  calc
    Nat.card (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) =
        4 * Nat.card K := by
      simpa [K, AddSubgroup.index_eq_card, hrank] using
        (AddSubgroup.index_range_nsmul_of_fg A (n := 2) (by decide))
    _ = 8 := by norm_num [hcard]

end MazurTorsion.XOneThirteenTwoDescentSquareclassCardinality
