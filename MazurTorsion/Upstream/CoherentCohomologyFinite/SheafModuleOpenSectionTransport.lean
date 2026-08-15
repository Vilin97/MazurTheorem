/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionHom
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleTopSectionHom
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverEquivalence

/-!
# Transporting section maps to an ambient open

The equivalence between modules on an open subscheme and modules on the
corresponding slice site carries the morphism defined by a top section to
the morphism defined by the associated ambient-open section.  The same
calculation transports epimorphic coproducts of section maps.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- Two maps out of the unit on `Over U` agree if they agree on `1` at
the terminal slice object. -/
lemma unitOver_hom_ext_terminal
    {N : SheafOfModules (X.ringCatSheaf.over U)}
    (f g : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ N)
    (h :
      f.val.app (op (Over.mk (𝟙 U)))
          (1 : X.ringCatSheaf.obj.obj (op U)) =
        g.val.app (op (Over.mk (𝟙 U)))
          (1 : X.ringCatSheaf.obj.obj (op U))) :
    f = g := by
  apply N.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let q : V.unop ⟶ Over.mk (𝟙 U) :=
    Over.homMk V.unop.hom
  have hf :=
    PresheafOfModules.sections_property
      (N.unitHomEquiv f) q.op
  have hg :=
    PresheafOfModules.sections_property
      (N.unitHomEquiv g) q.op
  change
    N.val.map q.op
        (f.val.app (op (Over.mk (𝟙 U)))
          (1 : X.ringCatSheaf.obj.obj (op U))) =
      f.val.app V
        (1 : (X.ringCatSheaf.over U).obj.obj V) at hf
  change
    N.val.map q.op
        (g.val.app (op (Over.mk (𝟙 U)))
          (1 : X.ringCatSheaf.obj.obj (op U))) =
      g.val.app V
        (1 : (X.ringCatSheaf.over U).obj.obj V) at hg
  exact
    hf.symm.trans
      ((congrArg (fun z => N.val.map q.op z) h).trans hg)

/-- Two endomorphisms of the unit on `Over U` agree if their values on `1`
at the terminal slice object agree as sections over the ambient open `U`.
This version exposes the section type and avoids unfolding the implementation
of the sliced structure sheaf at use sites. -/
lemma unitOver_end_hom_ext_terminal
    (f g : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U))
    (h :
      (show Γ(X, U) from
        f.val.app (op (Over.mk (𝟙 U)))
          (1 : Γ(X, U))) =
      (show Γ(X, U) from
        g.val.app (op (Over.mk (𝟙 U)))
          (1 : Γ(X, U)))) :
    f = g := by
  apply unitOver_hom_ext_terminal U f g
  exact h

/-- The top-section morphism on the open subscheme becomes the
ambient-open section morphism under the open-slice equivalence. -/
theorem homOfTopSection_to_homOfOpenSection
    (x : Γ(M.restrict U.ι, ⊤)) :
    (unitOverIso U).inv ≫
        (overEquivalence U).functor.map
          (homOfTopSection (M.restrict U.ι) x) ≫
        (restrictOverIso U M).hom =
      homOfOpenSection M U
        ((eqToIso (congrArg (fun V => Γ(M, V))
            U.ι_image_top)).hom
          ((M.restrictAppIso U.ι ⊤).hom x)) := by
  apply unitOver_hom_ext_terminal (U := U)
  change
    (((unitOverIso U).inv ≫
        (overEquivalence U).functor.map
          (homOfTopSection (M.restrict U.ι) x) ≫
        (restrictOverIso U M).hom).val.app
          (op (Over.mk (𝟙 U))))
          (1 : X.ringCatSheaf.obj.obj (op U)) =
      (homOfOpenSection M U
        ((eqToIso (congrArg (fun W => Γ(M, W))
            U.ι_image_top)).hom
          ((M.restrictAppIso U.ι ⊤).hom x))).val.app
            (op (Over.mk (𝟙 U)))
          (1 : X.ringCatSheaf.obj.obj (op U))
  rw [show (𝟙 U) =
      (homOfLE (le_refl U) : U ⟶ U)
    from Subsingleton.elim _ _]
  erw [homOfOpenSection_app_one]
  change
    (restrictOverIso U M).hom.val.app
        (op (Over.mk (𝟙 U)))
        (((overEquivalence U).functor.map
          (homOfTopSection (M.restrict U.ι) x)).val.app
            (op (Over.mk (𝟙 U)))
          ((unitOverIso U).inv.val.app
            (op (Over.mk (𝟙 U)))
            (1 : X.ringCatSheaf.obj.obj (op U)))) = _
  erw [overEquivalence_map_unitOverIso_inv_app_one]
  erw [homOfTopSection_app_one]
  erw [restrictOverIso_hom_app_terminal_restrict_top]
  rw [show
    (homOfLE (le_refl U) : U ⟶ U) = 𝟙 U
    from Subsingleton.elim _ _]
  rw [show (𝟙 U).op = 𝟙 (op U)
    from Subsingleton.elim _ _]
  rw [M.val.map_id]
  rfl

end AlgebraicGeometry.Scheme.Modules
