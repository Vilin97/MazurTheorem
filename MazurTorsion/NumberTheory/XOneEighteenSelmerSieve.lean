/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-!
# The final finite sieve for the `X₁(18)` two-descent

This file isolates the last group-theoretic step of the concrete descent.
Its named downstream consumer is the final `X₁(18)` rank-zero module: the
global calculation enumerates sixteen possible square classes, while the
dyadic calculation admits only the identity representative.

No Selmer, local-image, or Mordell--Weil conclusion is assumed here.
-/

namespace MazurTorsion.XOneEighteenSelmerSieve

/-- If every element of `T` satisfies both a global and a local condition,
the global subgroup is exhausted by sixteen displayed representatives, and
only its identity representative satisfies the local condition, then `T` is
trivial. -/
theorem subgroup_eq_bot_of_sixteen_representatives
    {G : Type*} [Group G]
    (T global localCondition : Subgroup G)
    (representative : Fin 16 → global)
    (hglobal : T ≤ global)
    (hlocal : T ≤ localCondition)
    (hsurjective : Function.Surjective representative)
    (hone : representative 0 = 1)
    (hexclude : ∀ i, (representative i : G) ∈ localCondition → i = 0) :
    T = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨i, hi⟩ := hsurjective ⟨x, hglobal hx⟩
  have hiLocal : (representative i : G) ∈ localCondition := by
    rw [hi]
    exact hlocal hx
  have hiZero : i = 0 := hexclude i hiLocal
  subst i
  rw [hone] at hi
  have hxOne : x = 1 := by
    simpa only [Subgroup.coe_one] using congrArg Subtype.val hi.symm
  simpa only [Subgroup.mem_bot] using hxOne

/-! ## Cardinality from opposing injections -/

/-- If a group of cardinality `256` maps to an arbitrary group, an
injected sixteen-element subgroup of its image and sixteen injected
elements of its kernel force those kernel elements to be exhaustive.

This formulation is useful for relative norms: the codomain itself need
not be finite, and the norm need not be restricted to a supported
codomain. -/
theorem kernel_representatives_bijective_of_card_256
    {G H A : Type*} [Group G] [Group H] [Group A]
    (N : G →* H)
    (representative : Fin 16 → N.ker)
    (rangeWitness : A → N.range)
    (hG : Nat.card G = 256)
    (hA : Nat.card A = 16)
    (hRepresentative : Function.Injective representative)
    (hRangeWitness : Function.Injective rangeWitness) :
    Function.Bijective representative := by
  letI : Finite G :=
    Nat.finite_of_card_ne_zero (hG.trans_ne (by norm_num))
  letI : Finite N.ker :=
    Finite.of_injective (fun x : N.ker ↦ (x : G)) Subtype.val_injective
  letI : Finite N.range :=
    Finite.of_surjective N.rangeRestrict N.rangeRestrict_surjective
  letI : Finite A :=
    Nat.finite_of_card_ne_zero (hA.trans_ne (by norm_num))
  have hkernelRange : Nat.card N.ker * Nat.card N.range = 256 := by
    rw [← Subgroup.index_ker N, N.ker.card_mul_index, hG]
  have hkernelLower : 16 ≤ Nat.card N.ker := by
    simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective representative hRepresentative
  have hrangeLower : 16 ≤ Nat.card N.range := by
    rw [← hA]
    exact Nat.card_le_card_of_injective rangeWitness hRangeWitness
  have hscaled : 16 * Nat.card N.ker ≤ 256 := by
    calc
      16 * Nat.card N.ker ≤ Nat.card N.range * Nat.card N.ker :=
        Nat.mul_le_mul_right (Nat.card N.ker) hrangeLower
      _ = Nat.card N.ker * Nat.card N.range := Nat.mul_comm _ _
      _ = 256 := hkernelRange
  have hkernelCard : Nat.card N.ker = 16 := by omega
  exact (Nat.bijective_iff_injective_and_card representative).2
    ⟨hRepresentative, by simpa only [Nat.card_fin] using hkernelCard.symm⟩

end MazurTorsion.XOneEighteenSelmerSieve
