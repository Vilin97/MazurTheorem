/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import Mathlib.Algebra.Group.Subgroup.Basic

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

end MazurTorsion.XOneEighteenSelmerSieve
