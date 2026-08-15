/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleTopSectionHom
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafPresentationRestriction

/-!
# Transporting top-section maps across a scheme isomorphism

Restriction along an isomorphism is an equivalence on module sheaves.
This file names the top section obtained by transporting a unit-module
morphism through that equivalence and identifies the transported
morphism with the usual top-section map.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)

/-- Two morphisms from the structure module agree if they agree on `1`
over the terminal open. -/
lemma unit_hom_ext_top
    {N : Y.Modules}
    (f g : SheafOfModules.unit Y.ringCatSheaf ⟶ N)
    (h :
      f.val.app (op (⊤ : Y.Opens))
          (1 : Y.ringCatSheaf.obj.obj (op ⊤)) =
        g.val.app (op (⊤ : Y.Opens))
          (1 : Y.ringCatSheaf.obj.obj (op ⊤))) :
    f = g := by
  apply N.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let q : op (⊤ : Y.Opens) ⟶ V :=
    (homOfLE le_top).op
  have hf :=
    PresheafOfModules.sections_property
      (N.unitHomEquiv f) q
  have hg :=
    PresheafOfModules.sections_property
      (N.unitHomEquiv g) q
  change
    N.val.map q
        (f.val.app (op (⊤ : Y.Opens))
          (1 : Y.ringCatSheaf.obj.obj (op ⊤))) =
      f.val.app V
        (1 : Y.ringCatSheaf.obj.obj V) at hf
  change
    N.val.map q
        (g.val.app (op (⊤ : Y.Opens))
          (1 : Y.ringCatSheaf.obj.obj (op ⊤))) =
      g.val.app V
        (1 : Y.ringCatSheaf.obj.obj V) at hg
  exact
    hf.symm.trans
      ((congrArg (fun z => N.val.map q z) h).trans hg)

/-- The top section obtained after transporting a top-section morphism
from `X` back to `Y` along `e`. -/
def isoTransportedTopSection
    (x : Γ(M.restrict e.hom, ⊤)) :
    Γ(M, ⊤) :=
  (((restrictUnitIso e.inv).inv ≫
      (restrictFunctor e.inv).map
        (homOfTopSection (M.restrict e.hom) x) ≫
      (restrictIsoOfIso e.symm M).hom).val.app
        (op (⊤ : Y.Opens)))
    (1 : Y.ringCatSheaf.obj.obj (op ⊤))

/-- Transporting a top-section morphism across a scheme isomorphism
gives the morphism associated to the transported top section. -/
theorem homOfTopSection_to_isoTransport
    (x : Γ(M.restrict e.hom, ⊤)) :
    (restrictUnitIso e.inv).inv ≫
        (restrictFunctor e.inv).map
          (homOfTopSection (M.restrict e.hom) x) ≫
        (restrictIsoOfIso e.symm M).hom =
      homOfTopSection M
        (isoTransportedTopSection e M x) := by
  apply unit_hom_ext_top
  erw [homOfTopSection_app_top_one]
  rfl

end AlgebraicGeometry.Scheme.Modules
