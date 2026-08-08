/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# The additive sheaf underlying a scheme module

This is the narrow scheme-module bridge used by sheaf cohomology. It follows
the API proposed upstream in Mathlib PR #36345: forget the module structure,
then sheafify the underlying additive presheaf. The resulting functor is
additive, faithful, and preserves finite limits and all colimits.

This is a source-preserving Apache-2.0 port of AINTLIB's
`ForMathlib/SchemeModuleSheaf.lean` at commit
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.
-/

open CategoryTheory Limits TopologicalSpace

universe u v u₁ u₂ u₃ v₁ v₂ v₃

private theorem preservesColimitsOfShape_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (R : C ⥤ D) [Reflective R]
    {J : Type u} [Category.{v} J] (F : C ⥤ E)
    [PreservesColimitsOfShape J ((reflector R) ⋙ F)] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  refine @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _
    (NatIso.hcomp (asIso (𝟙 K)) (asIso (reflectorAdjunction R).counit).symm).symm
      ⟨fun hc ↦ ⟨?_⟩⟩
  let hc₂ := colimit.isColimit (K ⋙ R)
  let ψ := IsColimit.uniqueUpToIso (isColimitOfPreserves (reflector R) hc₂) hc
  have φ := IsColimit.ofIsoColimit
    (isColimitOfPreserves (reflector R ⋙ F) hc₂)
    (Functor.mapCoconeMapCocone (H := reflector R) (H' := F)
      (colimit.cocone (K ⋙ R))).symm
  exact IsColimit.ofIsoColimit φ ((Cocone.functoriality _ F).mapIso ψ)

private theorem preservesColimitsOfSize_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (R : C ⥤ D) [Reflective R]
    (F : C ⥤ E) [PreservesColimitsOfSize.{v, u} ((reflector R) ⋙ F)]
    [HasColimitsOfSize.{v, u} D] : PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape := preservesColimitsOfShape_of_reflector_comp R F

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

variable (X) in
/-- The additive sheaf underlying a scheme module. -/
@[simps!]
noncomputable def toSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance : (toSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance : PreservesFiniteLimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.toSheaf X.ringCatSheaf))

instance : (toSheaf X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful

instance : PreservesColimitsOfSize.{v, u} (toSheaf X) := by
  letI : Reflective (toPresheafOfModules X) :=
    { L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
      adj := PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj) }
  have : PreservesColimitsOfSize.{v, u}
      (reflector (toPresheafOfModules X) ⋙ toSheaf X) :=
    comp_preservesColimits (PresheafOfModules.toPresheaf
      X.ringCatSheaf.obj)
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)
  exact preservesColimitsOfSize_of_reflector_comp
    (toPresheafOfModules X) _

instance : PreservesColimits (toSheaf X) where

/-- The additive sheaf underlying a scheme module. -/
noncomputable abbrev sheaf : TopCat.Sheaf AddCommGrpCat X :=
  (toSheaf X).obj M

/-- The additive-sheaf morphism underlying a morphism of scheme modules. -/
noncomputable abbrev Hom.sheafHom {M N : X.Modules} (f : M ⟶ N) :
    M.sheaf ⟶ N.sheaf :=
  (toSheaf X).map f

end AlgebraicGeometry.Scheme.Modules
