/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneFunctoriality
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfSerreQuotient

/-!
# Degree-one fppf cohomology after removing the bad fibre

An isomorphism of commutative coefficient presheaves induces a multiplicative equivalence on the
checked common-refinement model of global fppf `H¹`.  We apply this to the represented additive
point sheaves after restriction to the good principal open.  The supported point-cokernel exact
sequence makes the subgroup inclusion an isomorphism there, so the actual constant-flat and
multiplicative-flat models have the same sheaf-level `H¹` as their ambient models on that open.

The coefficient sheaves in this file are the universe-lifted additive sheaves used by the actual
cokernel sequence, converted to multiplicative commutative groups.  A later bridge must compare
this spelling with the original represented group-scheme `FppfHOne`; no global bad-fibre
cohomological localization sequence or finiteness assertion is made here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FppfHOne

universe w v u

open CategoryTheory.PresheafOfCommGroups

variable {X : Scheme.{u}}
variable {A B : (Over X)ᵒᵖ ⥤ CommGrpCat.{w}}

/-- An isomorphism of commutative coefficient presheaves induces an equivalence on global fppf
`H¹`.  The inverse is the map induced by the inverse natural transformation. -/
noncomputable def mulEquivOfIso (e : A ≅ B) :
    Scheme.FppfHOne.{w, v, u} X (toGroups A) ≃*
      Scheme.FppfHOne.{w, v, u} X (toGroups B) where
  toFun := mapHom e.hom
  invFun := mapHom e.inv
  left_inv x := by
    change mapHom e.inv (mapHom e.hom x) = x
    rw [← MonoidHom.comp_apply, ← mapHom_comp, e.hom_inv_id, mapHom_id]
    rfl
  right_inv x := by
    change mapHom e.hom (mapHom e.inv x) = x
    rw [← MonoidHom.comp_apply, ← mapHom_comp, e.inv_hom_id, mapHom_id]
    rfl
  map_mul' x y := (mapHom e.hom).map_mul x y

end AlgebraicGeometry.Scheme.FppfHOne

namespace AlgebraicGeometry.CommGroupScheme

universe v u

open CategoryTheory.PresheafOfCommGroups

variable {S : Scheme.{u}} {G H : CommGroupScheme S}

/-- The universe-lifted additive represented-point sheaf on an open, viewed as a commutative
multiplicative coefficient presheaf. -/
noncomputable abbrev addPointFppfCommPresheafOverOpen
    (G : CommGroupScheme S) (U : S.Opens) :
    (Over U.toScheme)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  (addPointFppfSheafOverOpen G U).obj ⋙ AddCommGrpCat.toCommGrp

/-- Global fppf `H¹` of the universe-lifted represented additive point sheaf on an open. -/
noncomputable abbrev AddPointFppfHOneOverOpen
    (G : CommGroupScheme S) (U : S.Opens) :=
  Scheme.FppfHOne.{u + 1, v, u} U.toScheme
    (toGroups (addPointFppfCommPresheafOverOpen G U))

/-- An isomorphism of represented additive point sheaves gives the corresponding isomorphism of
commutative coefficient presheaves. -/
noncomputable def addPointFppfCommPresheafIsoOverOpen
    (U : S.Opens) (e : addPointFppfSheafOverOpen G U ≅
      addPointFppfSheafOverOpen H U) :
    addPointFppfCommPresheafOverOpen G U ≅
      addPointFppfCommPresheafOverOpen H U :=
  Functor.isoWhiskerRight
    ((sheafToPresheaf (Scheme.fppfTopology.over U.toScheme)
      AddCommGrpCat.{u + 1}).mapIso e) AddCommGrpCat.toCommGrp

/-- A sheaf isomorphism on the good open induces an equivalence on its sheaf-level global fppf
`H¹`. -/
noncomputable def addPointFppfHOneOverOpenMulEquivOfIso
    (U : S.Opens) (e : addPointFppfSheafOverOpen G U ≅
      addPointFppfSheafOverOpen H U) :
    AddPointFppfHOneOverOpen.{v} G U ≃*
      AddPointFppfHOneOverOpen.{v} H U :=
  Scheme.FppfHOne.mulEquivOfIso (addPointFppfCommPresheafIsoOverOpen U e)

/-- If the actual point-cokernel sheaf is supported on the removed fibre, the subgroup and
ambient represented additive point sheaves have equivalent global fppf `H¹` on the open. -/
noncomputable def addPointFppfHOneOverOpenMulEquiv_of_supported
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] (U : S.Opens)
    (h : IsZero (pointCokernelFppfSheafOverOpen f U)) :
    AddPointFppfHOneOverOpen.{v} G U ≃*
      AddPointFppfHOneOverOpen.{v} H U := by
  letI := addPointFppfMapOverOpen_isIso_of_supported f U h
  exact addPointFppfHOneOverOpenMulEquivOfIso U
    (asIso (addPointFppfMapOverOpen f U))

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe v u

open CommGroupScheme

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- On `D(level)`, the actual constant-flat bad-level model and the ambient constant group have
equivalent sheaf-level global fppf `H¹`. -/
noncomputable def constantFlatAddPointFppfHOneAwayMulEquiv (level : R) :
    AddPointFppfHOneOverOpen.{v} (constantFlat R G level).obj (levelOpen level) ≃*
      AddPointFppfHOneOverOpen.{v}
        (FiniteFlatCommGroupScheme.constantScheme R G).obj (levelOpen level) :=
  addPointFppfHOneOverOpenMulEquiv_of_supported
    (constantFlatInclusion (G := G) level) (levelOpen level)
    (constantFlatPointCokernelFppfSheafAway_isZero (G := G) level)

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- On `D(level)`, the actual multiplicative-flat bad-level model and `mu_p` have equivalent
sheaf-level global fppf `H¹`. -/
noncomputable def muFlatAddPointFppfHOneAwayMulEquiv
    (datum : MuFlatDatum coeffPrime level) :
    AddPointFppfHOneOverOpen.{v} (muFlat coeffPrime level datum).obj
        (levelOpen (level : ℤ)) ≃*
      AddPointFppfHOneOverOpen.{v}
        (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj
        (levelOpen (level : ℤ)) :=
  addPointFppfHOneOverOpenMulEquiv_of_supported
    (muFlatInclusion coeffPrime level datum) (levelOpen (level : ℤ))
    (muFlatPointCokernelFppfSheafAway_isZero datum)

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
