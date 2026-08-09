/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.Mathlib.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import MazurTorsion.GroupTheory.IndexNSmulFG

/-!
# Unit square classes in the degree-nine `X₁(18)` two-division field

This file computes the size of the unit square-class group from the
signature alone.  It uses Dirichlet's unit theorem and the fact that an
odd-degree number field has only the roots of unity `±1`; no choice of
explicit fundamental units is required.
-/

open NumberField NumberField.InfinitePlace

namespace MazurTorsion.XOneEighteenDescent

noncomputable section

variable (L : Type*) [Field L] [NumberField L]

private theorem unitRank_eq_five
    (hdegree : Module.finrank ℚ L = 9)
    (hreal : nrRealPlaces L = 3) :
    NumberField.Units.rank L = 5 := by
  have hsignature := card_add_two_mul_card_eq_rank L
  have hcomplex : nrComplexPlaces L = 3 := by
    rw [hdegree, hreal] at hsignature
    omega
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    hreal, hcomplex]

private theorem unitTorsionOrder_eq_two
    (hdegree : Module.finrank ℚ L = 9) :
    NumberField.Units.torsionOrder L = 2 := by
  apply NumberField.Units.torsionOrder_eq_two_of_odd_finrank
  rw [hdegree]
  norm_num

private theorem natCard_ker_two_units_eq_two
    (hdegree : Module.finrank ℚ L = 9) :
    Nat.card
        (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).ker = 2 := by
  have htorsion : NumberField.Units.torsionOrder L = 2 :=
    unitTorsionOrder_eq_two L hdegree
  have hker :
      (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).ker =
        (NumberField.Units.torsion L).toAddSubgroup := by
    ext x
    change x.toMul ^ 2 = 1 ↔ x.toMul ∈ NumberField.Units.torsion L
    rw [← NumberField.Units.rootsOfUnity_eq_torsion]
    simp [htorsion]
  rw [hker]
  change Nat.card (NumberField.Units.torsion L) = 2
  exact htorsion

/-- A degree-nine number field of signature `(3,3)` has exactly `64`
integral-unit square classes. -/
theorem natCard_unitsModSq_of_degree_nine_of_nrRealPlaces_eq_three
    (hdegree : Module.finrank ℚ L = 9)
    (hreal : nrRealPlaces L = 3) :
    Nat.card (Units.modPow (𝓞 L) 2) = 64 := by
  have hrank : NumberField.Units.rank L = 5 :=
    unitRank_eq_five L hdegree hreal
  letI : Group.FG (𝓞 L)ˣ :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  have hindex := AddSubgroup.index_range_nsmul_of_fg
    (Additive (𝓞 L)ˣ) (by norm_num : (2 : ℕ) ≠ 0)
  rw [NumberField.Units.finrank_eq, hrank,
    natCard_ker_two_units_eq_two L hdegree] at hindex
  change
    (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).range.index = 64
  norm_num at hindex ⊢
  exact hindex

end

end MazurTorsion.XOneEighteenDescent
