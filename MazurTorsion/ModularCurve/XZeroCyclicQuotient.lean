/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroModuli

/-!
# The point-group quotient attached to a rational cyclic subgroup

A cyclic subgroup `C` of order `N` is killed by multiplication by `N`.
Consequently multiplication by `N` on the ambient rational point group
descends through the quotient by `C`.  If

`π : A → A ⧸ C`,

the descended map `π dual : A ⧸ C → A` satisfies

`dual ∘ π = [N]` and `π ∘ dual = [N]`.

These are the point-group identities expected from an isogeny and its dual.
They are useful compatibility conditions for the future elliptic quotient in
the `X₀(N)` moduli construction.  This file does not claim that the abstract
quotient group is represented by an elliptic curve or construct a quotient
group scheme.
-/

namespace MazurTorsion.ModularCurve.XZeroModuli
namespace RationalCyclicSubgroup

universe u

variable {A : Type u} [AddCommGroup A]
  {N : ℕ} [NeZero N]

/-- The abstract quotient of the rational point group by the supplied cyclic
subgroup.  Representability by an elliptic quotient remains separate
geometry. -/
abbrev PointQuotient (C : RationalCyclicSubgroup A N) :=
  A ⧸ C.carrier

/-- The canonical projection to the point-group quotient. -/
def quotientMap (C : RationalCyclicSubgroup A N) :
    A →+ C.PointQuotient :=
  QuotientAddGroup.mk' C.carrier

/-- The point-group quotient projection is surjective. -/
theorem quotientMap_surjective (C : RationalCyclicSubgroup A N) :
    Function.Surjective C.quotientMap :=
  QuotientAddGroup.mk'_surjective C.carrier

/-- The kernel of the point-group quotient projection is exactly the supplied
cyclic subgroup. -/
@[simp]
theorem quotientMap_ker (C : RationalCyclicSubgroup A N) :
    C.quotientMap.ker = C.carrier :=
  QuotientAddGroup.ker_mk' C.carrier

/-- Every element of a cyclic subgroup of cardinality `N` is killed by
multiplication by `N`. -/
theorem carrier_le_nsmul_ker (C : RationalCyclicSubgroup A N) :
    C.carrier ≤ (nsmulAddMonoidHom N : A →+ A).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp <| by
    rw [← C.card_eq]
    exact C.carrier.addOrderOf_dvd_natCard hx

/-- Multiplication by `N` descended through the quotient by `C`.

For an elliptic quotient this is the rational-point map expected from the
dual isogeny. -/
def dualMap (C : RationalCyclicSubgroup A N) :
    C.PointQuotient →+ A :=
  QuotientAddGroup.lift C.carrier (nsmulAddMonoidHom N)
    C.carrier_le_nsmul_ker

@[simp]
theorem dualMap_mk (C : RationalCyclicSubgroup A N) (x : A) :
    C.dualMap (C.quotientMap x) = N • x :=
  rfl

/-- The descended dual after the quotient projection is multiplication by
`N` on the ambient point group. -/
theorem dualMap_comp_quotientMap (C : RationalCyclicSubgroup A N) :
    C.dualMap.comp C.quotientMap = nsmulAddMonoidHom N := by
  ext x
  exact C.dualMap_mk x

/-- The quotient projection after the descended dual is multiplication by
`N` on the quotient point group. -/
theorem quotientMap_comp_dualMap (C : RationalCyclicSubgroup A N) :
    C.quotientMap.comp C.dualMap = nsmulAddMonoidHom N := by
  ext x
  simp [quotientMap, dualMap]

/-- The kernel of the descended dual is the image in `A/C` of the full
`N`-torsion kernel in `A`. -/
theorem dualMap_ker (C : RationalCyclicSubgroup A N) :
    C.dualMap.ker =
      (nsmulAddMonoidHom N : A →+ A).ker.map C.quotientMap := by
  exact QuotientAddGroup.ker_lift
    (N := C.carrier) (nsmulAddMonoidHom N) C.carrier_le_nsmul_ker

end RationalCyclicSubgroup

namespace RationalDatum

universe u

variable {K : Type u} [Field K] [DecidableEq K]
  {N : ℕ} [NeZero N]

/-- The abstract quotient of the rational point group attached to a split
`Γ₀(N)` datum. -/
abbrev PointQuotient (x : RationalDatum K N) :=
  x.subgroup.PointQuotient

/-- The point-group quotient projection attached to a split rational modular
datum. -/
def pointQuotientMap (x : RationalDatum K N) :
    x.curve.toAffine.Point →+ x.PointQuotient :=
  x.subgroup.quotientMap

/-- The descended multiplication map attached to a split rational modular
datum. -/
def pointQuotientDualMap (x : RationalDatum K N) :
    x.PointQuotient →+ x.curve.toAffine.Point :=
  x.subgroup.dualMap

/-- A real `RationalDatum` consumer of the quotient/dual API: composing the
two point maps in the ambient direction is multiplication by the level. -/
theorem pointQuotientDualMap_comp_pointQuotientMap
    (x : RationalDatum K N) :
    x.pointQuotientDualMap.comp x.pointQuotientMap =
      nsmulAddMonoidHom N :=
  x.subgroup.dualMap_comp_quotientMap

/-- In the quotient direction the same two maps also compose to
multiplication by the level. -/
theorem pointQuotientMap_comp_pointQuotientDualMap
    (x : RationalDatum K N) :
    x.pointQuotientMap.comp x.pointQuotientDualMap =
      nsmulAddMonoidHom N :=
  x.subgroup.quotientMap_comp_dualMap

end RationalDatum
end MazurTorsion.ModularCurve.XZeroModuli
