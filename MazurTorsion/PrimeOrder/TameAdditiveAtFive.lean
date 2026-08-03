/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TameAdditiveFiltration
import Mathlib.Tactic.NormNum

/-!
# The tame additive contradiction at residue characteristic five

This is the prime-route consumer of the algebraic Néron filtration boundary.
It remains conditional on construction of that filtration from the actual
local elliptic curve.
-/

namespace MazurTorsion.PrimeOrder

open MazurTorsion.EllipticCurve

universe u v

/-- A tame additive filtration with five-element residue group has no point
of prime exact order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive
    {G : Type u} [AddCommGroup G]
    (F : TameAdditiveFiltrationData.{u, v} G)
    (hresidue : Nat.card F.ResidueAdditive = 5)
    (P : G) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  letI : AddCommGroup F.Component := F.componentAddCommGroup
  letI : Finite F.Component := F.componentFinite
  letI : AddCommGroup F.ResidueAdditive := F.residueAddCommGroup
  letI : Finite F.ResidueAdditive := F.residueFinite
  intro horder
  have hcomponentCoprime : N.Coprime (Nat.card F.Component) :=
    Nat.coprime_of_lt_prime Nat.card_pos.ne'
      (lt_of_le_of_lt F.component_card_le_four (by omega)) hprime
  have hresidueCoprime : N.Coprime (Nat.card F.ResidueAdditive) := by
    rw [hresidue]
    exact Nat.coprime_of_lt_prime (by norm_num) (by omega) hprime
  have hzero := F.point_eq_zero_of_coprime_card hprime.ne_zero
    hcomponentCoprime hresidueCoprime horder
  rw [hzero] at horder
  simp at horder
  omega

end MazurTorsion.PrimeOrder
