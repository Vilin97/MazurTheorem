/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AdjunctionUnitIsoTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoAdjunction
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pullback--pushforward units and composition

The pullback functor for a composite morphism is naturally isomorphic to
the composite of the pullback functors.  Consequently, invertibility of
the geometric unit can be checked using the unit of the composite
adjunction.  We also record the two forms needed when one factor is an
isomorphism.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/--
The unit for a composite scheme morphism is invertible exactly when the
unit of the composite pullback--pushforward adjunction is invertible.
-/
theorem isIso_pullbackPushforward_unit_comp_iff
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    IsIso
        ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M) ↔
      IsIso
        (((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f)).unit.app M) :=
  Adjunction.isIso_unit_app_iff_of_natIso_left
    (pullbackPushforwardAdjunction (f ≫ g))
    ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f))
    (pullbackComp f g) M

/--
If the two successive unit components are isomorphisms, then so is the
unit for the composite morphism.
-/
theorem isIso_pullbackPushforward_unit_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    [IsIso
      ((pullbackPushforwardAdjunction g).unit.app M)]
    [IsIso
      ((pullbackPushforwardAdjunction f).unit.app
        ((pullback g).obj M))] :
    IsIso
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M) := by
  haveI hMapped :
      IsIso
        ((pushforward g).map
          ((pullbackPushforwardAdjunction f).unit.app
            ((pullback g).obj M))) :=
    inferInstance
  apply
    (isIso_pullbackPushforward_unit_comp_iff
      f g M).mpr
  rw [Adjunction.comp_unit_app]
  exact
    IsIso.comp_isIso'
      (inferInstanceAs
        (IsIso
          ((pullbackPushforwardAdjunction g).unit.app M)))
      hMapped

/--
Precomposing a morphism by an isomorphism does not change whether its
unit component is invertible.
-/
theorem isIso_pullbackPushforward_unit_of_comp_of_isIso_left
    (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Z) (M : Z.Modules)
    [IsIso
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M)] :
    IsIso
      ((pullbackPushforwardAdjunction g).unit.app M) := by
  haveI hCompositeAdjunctionUnit :
      IsIso
        (((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f)).unit.app M) :=
    (isIso_pullbackPushforward_unit_comp_iff
      f g M).mp
      (inferInstanceAs
        (IsIso
          ((pullbackPushforwardAdjunction
            (f ≫ g)).unit.app M)))
  haveI hLeftUnit :
      IsIso
        ((pullbackPushforwardAdjunction f).unit.app
          ((pullback g).obj M)) :=
    pullbackPushforwardAdjunction_unit_app_isIso_of_isIso
      f ((pullback g).obj M)
  haveI hMappedLeftUnit :
      IsIso
        ((pushforward g).map
          ((pullbackPushforwardAdjunction f).unit.app
            ((pullback g).obj M))) :=
    inferInstance
  haveI hComposite :
      IsIso
        ((pullbackPushforwardAdjunction g).unit.app M ≫
          (pushforward g).map
            ((pullbackPushforwardAdjunction f).unit.app
              ((pullback g).obj M))) := by
    exact Eq.mp
      (congrArg (fun q => IsIso q)
        (Adjunction.comp_unit_app
          (pullbackPushforwardAdjunction g)
          (pullbackPushforwardAdjunction f) M))
      hCompositeAdjunctionUnit
  exact
    @IsIso.of_isIso_comp_right _ _ _ _ _
      ((pullbackPushforwardAdjunction g).unit.app M)
      ((pushforward g).map
        ((pullbackPushforwardAdjunction f).unit.app
          ((pullback g).obj M)))
      hMappedLeftUnit hComposite

/--
Postcomposing by an isomorphism preserves invertibility of the unit,
provided the unit before that isomorphism is invertible on the pulled
back object.
-/
theorem isIso_pullbackPushforward_unit_comp_of_isIso_right
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
    (M : Z.Modules)
    [IsIso
      ((pullbackPushforwardAdjunction f).unit.app
        ((pullback g).obj M))] :
    IsIso
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M) := by
  haveI hRightUnit :
      IsIso
        ((pullbackPushforwardAdjunction g).unit.app M) :=
    pullbackPushforwardAdjunction_unit_app_isIso_of_isIso
      g M
  exact
    isIso_pullbackPushforward_unit_comp f g M

end AlgebraicGeometry.Scheme.Modules
