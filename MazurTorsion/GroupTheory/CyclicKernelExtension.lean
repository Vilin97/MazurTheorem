/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Order

/-!
# Cyclic extensions by a kernel of order two

This file isolates a finite-group argument used at an exceptional endpoint of the torsion
classification. Suppose that a finite additive group maps onto an even-order cyclic group with
kernel of cardinality two. If every element killed by two belongs to that kernel, then the source
is cyclic.

The proof lifts a generator of the quotient. Its order is a multiple of the quotient cardinality
and divides twice that cardinality. The smaller possibility would make the half-multiple of the
lift a two-torsion element outside the kernel, so the lift has order equal to the cardinality of
the source.
-/

@[expose] public section

namespace MazurTorsion

/-- A finite extension of an even-order cyclic group by a two-element kernel is cyclic if all
two-torsion in the source lies in the kernel. -/
theorem isAddCyclic_of_surjective_card_ker_eq_two
    {A B : Type*} [AddGroup A] [AddGroup B] [Finite A] [Finite B]
    [IsAddCyclic B] (f : A →+ B) (hf : Function.Surjective f)
    (hker : Nat.card f.ker = 2) (heven : Even (Nat.card B))
    (h_two_torsion : ∀ x : A, 2 • x = 0 → x ∈ f.ker) :
    IsAddCyclic A := by
  obtain ⟨b, hb⟩ := IsAddCyclic.exists_generator (α := B)
  obtain ⟨a, ha⟩ := hf b
  have hb_order : addOrderOf b = Nat.card B :=
    addOrderOf_eq_card_of_forall_mem_zmultiples hb
  have h_card_A : Nat.card A = 2 * Nat.card B := by
    calc
      Nat.card A = Nat.card (A ⧸ f.ker) * Nat.card f.ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
      _ = Nat.card B * 2 := by
        rw [Nat.card_congr
          (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv, hker]
      _ = 2 * Nat.card B := Nat.mul_comm _ _
  have h_kernel_two (x : A) (hx : x ∈ f.ker) : 2 • x = 0 := by
    let x' : f.ker := ⟨x, hx⟩
    have hx' : 2 • x' = 0 := by
      apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      rw [← hker]
      exact addOrderOf_dvd_natCard x'
    exact congrArg Subtype.val hx'
  have h_card_B_dvd : Nat.card B ∣ addOrderOf a := by
    rw [← hb_order, ← ha]
    exact addOrderOf_map_dvd f a
  have h_card_B_smul_mem : Nat.card B • a ∈ f.ker := by
    apply AddMonoidHom.mem_ker.mpr
    rw [map_nsmul, ha, ← hb_order, addOrderOf_nsmul_eq_zero]
  have h_twice_card_B_smul : (2 * Nat.card B) • a = 0 := by
    simpa [Nat.mul_comm, mul_nsmul] using h_kernel_two _ h_card_B_smul_mem
  have h_order_dvd : addOrderOf a ∣ 2 * Nat.card B :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_twice_card_B_smul
  have h_order_eq : addOrderOf a = 2 * Nat.card B := by
    obtain ⟨k, hk⟩ := h_card_B_dvd
    have h_card_B_pos : 0 < Nat.card B := Nat.card_pos
    have hk_dvd_two : k ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_left h_card_B_pos
      simpa [hk, Nat.mul_comm] using h_order_dvd
    have hk_cases : k = 1 ∨ k = 2 := (Nat.dvd_prime Nat.prime_two).mp hk_dvd_two
    rcases hk_cases with rfl | rfl
    · exfalso
      obtain ⟨m, hm⟩ := heven
      have hm_pos : 0 < m := by omega
      have h_card_B_smul_zero : Nat.card B • a = 0 := by
        simpa [hk] using addOrderOf_nsmul_eq_zero a
      have hma_two : 2 • (m • a) = 0 := by
        rw [smul_smul, two_mul, ← hm]
        exact h_card_B_smul_zero
      have hma_mem : m • a ∈ f.ker := h_two_torsion _ hma_two
      have hmb_zero : m • b = 0 := by
        rw [← ha, ← map_nsmul]
        exact AddMonoidHom.mem_ker.mp hma_mem
      have h_card_B_dvd_m : Nat.card B ∣ m := by
        rw [← hb_order]
        exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hmb_zero
      have h_card_B_le_m : Nat.card B ≤ m := Nat.le_of_dvd hm_pos h_card_B_dvd_m
      omega
    · simp [hk, Nat.mul_comm]
  apply isAddCyclic_of_addOrderOf_eq_card a
  rw [h_order_eq, h_card_A]

end MazurTorsion
