/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentSquareclassCardinality
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentUnitSquareclasses

/-!
# Cardinality of the unit squareclass group for the `X₁(13)` descent field

The unit group of the sextic descent field has free rank two and cyclic
torsion.  Since `-1` has exact order two, the generic finitely generated
abelian-group count gives exactly eight unit classes modulo squares.

This count does not identify any particular basis of the quotient and does
not assert that the previously displayed units generate the full unit group.
-/

namespace MazurTorsion.XOneThirteenTwoDescentUnitSquareclassCardinality

open Module NumberField NumberField.Units Polynomial
open XOneThirteenTwoDescentSextic
open XOneThirteenTwoDescentUnitSquareclasses
open XOneThirteenTwoDescentSquareclassCardinality

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

private abbrev UnitAddGroup := Additive ((𝓞 SexticField)ˣ)

private instance : Group.FG ((𝓞 SexticField)ˣ) :=
  Group.fg_iff_monoid_fg.mpr inferInstance

private instance : IsAddCyclic (AddCommGroup.torsion UnitAddGroup) := by
  change IsAddCyclic (Subgroup.toAddSubgroup (NumberField.Units.torsion SexticField))
  exact isAddCyclic_additive_iff.mpr
    (inferInstance : IsCyclic (NumberField.Units.torsion SexticField))

/-- The unit group of the sextic `X₁(13)` descent field has exactly eight
classes modulo squares, expressed additively as a quotient by doubling. -/
theorem natCard_unitSquareclasses :
    Nat.card
      (Additive ((𝓞 SexticField)ˣ) ⧸
        (nsmulAddMonoidHom (α := Additive ((𝓞 SexticField)ˣ)) 2).range) = 8 := by
  apply natCard_quotient_doubles_eq_eight
      (a := Additive.ofMul (-1 : (𝓞 SexticField)ˣ))
  · rw [NumberField.Units.finrank_eq, sexticField_unitRank]
  · rw [addOrderOf_ofMul_eq_orderOf, ← orderOf_units, Units.val_neg,
      Units.val_one, orderOf_neg_one, ringChar.eq_zero, if_neg (by decide)]

end

end MazurTorsion.XOneThirteenTwoDescentUnitSquareclassCardinality
