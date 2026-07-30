/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Torsion

/-!
# The cardinality consequence of Mazur's torsion classification

This file separates the elementary final step of Mazur's theorem from its arithmetic-geometric
proof. Once the rational torsion subgroup is known to be one of Mazur's fifteen groups, its
cardinality is at most sixteen.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace MazurTorsion

/-- The orders of the cyclic groups in Mazur's classification. -/
def cyclicOrders : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}

/-- The parameters `m` for the groups `ℤ/2ℤ × ℤ/(2m)ℤ` in Mazur's classification. -/
def bicyclicParameters : Finset ℕ :=
  {1, 2, 3, 4}

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The torsion subgroup of the rational points of `E`. -/
abbrev RationalTorsion :=
  AddCommGroup.torsion (E⁄ℚ).Point

/-- The group-structure conclusion of Mazur's torsion theorem. -/
def HasMazurClassification : Prop :=
  (∃ n ∈ cyclicOrders, Nonempty (RationalTorsion E ≃+ ZMod n)) ∨
    ∃ m ∈ bicyclicParameters, Nonempty (RationalTorsion E ≃+ (ZMod 2 × ZMod (2 * m)))

/-- The exact arithmetic input needed by the LeanPool statement.

Because `Set.ncard` is zero for an infinite set, it is enough to classify the rational torsion
subgroup under the explicit hypothesis that its underlying set is finite. This formulation avoids
making Mordell--Weil finiteness a dependency of the challenge proof. -/
def HasMazurClassificationIfFinite : Prop :=
  ∀ _h : (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite,
    HasMazurClassification E

omit [E.IsElliptic] in
/-- Mazur's fifteen-group classification implies the numerical bound in the LeanPool challenge. -/
theorem torsion_ncard_le_of_classification (h : HasMazurClassification E) :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 := by
  change Nat.card (RationalTorsion E) ≤ 16
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
    simp only [bicyclicParameters, Finset.mem_insert, Finset.mem_singleton] at hm
    omega

omit [E.IsElliptic] in
/-- Classifying only finite rational torsion subgroups is enough for the exact LeanPool target. -/
theorem torsion_ncard_le_of_classification_if_finite
    (h : HasMazurClassificationIfFinite E) :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 := by
  rcases (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).finite_or_infinite with
    hfinite | hinfinite
  · exact torsion_ncard_le_of_classification E (h hfinite)
  · rw [hinfinite.ncard]
    omega

end MazurTorsion
