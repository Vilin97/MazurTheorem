/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Sheaves.Stalks

/-!
# Detecting module isomorphisms on an open cover

A morphism of scheme modules is an isomorphism if its restriction to
every member of a pointwise open cover is an isomorphism.  The proof
transfers the local isomorphisms to stalks and then uses the stalkwise
isomorphism criterion for sheaves.
-/

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/--
Isomorphisms of scheme modules can be detected after restriction to a
family of opens covering every point.
-/
theorem isIso_of_isIso_restrict_openCover
    {M N : X.Modules} (α : M ⟶ N)
    {ι : Type v} (U : ι → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    [∀ i, IsIso ((restrictFunctor (U i).ι).map α)] :
    IsIso α := by
  let FM : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let FN : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let f : FM ⟶ FN :=
    ObjectProperty.homMk ((toPresheaf X).map α)
  letI (x : X) :
      IsIso
        ((TopCat.Presheaf.stalkFunctor Ab x).map
          f.1) := by
    change
      IsIso
        ((toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor
            (X := X.toPresheafedSpace) Ab x).map α)
    obtain ⟨i, hxi⟩ := hcover x
    let y : (U i).toScheme := ⟨x, hxi⟩
    let E := restrictStalkNatIso (U i).ι y
    haveI hEM : IsIso (E.hom.app M) := (E.app M).isIso_hom
    haveI hEN : IsIso (E.hom.app N) := (E.app N).isIso_hom
    haveI hLocal :
        IsIso
          ((restrictFunctor (U i).ι ⋙ toPresheaf (U i).toScheme ⋙
            TopCat.Presheaf.stalkFunctor
              (X := (U i).toScheme.toPresheafedSpace) Ab y).map α) := by
      change
        IsIso
          ((TopCat.Presheaf.stalkFunctor
              (X := (U i).toScheme.toPresheafedSpace) Ab y).map
            ((toPresheaf (U i).toScheme).map
              ((restrictFunctor (U i).ι).map α)))
      infer_instance
    have hAtImage :
        IsIso
          ((toPresheaf X ⋙
            TopCat.Presheaf.stalkFunctor
              (X := X.toPresheafedSpace) Ab ((U i).ι y)).map α) := by
      haveI hcomp :
          IsIso
            (E.hom.app M ≫
              (toPresheaf X ⋙
                TopCat.Presheaf.stalkFunctor
                  (X := X.toPresheafedSpace) Ab ((U i).ι y)).map α) := by
        rw [← E.hom.naturality α]
        exact IsIso.comp_isIso' hLocal hEN
      exact
        @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hEM hcomp
    simpa only [y, Scheme.Opens.ι_apply] using hAtImage
  haveI hf : IsIso f :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso f
  haveI hfPresheaf : IsIso f.1 := by
    change IsIso ((TopCat.Sheaf.forget Ab X).map f)
    infer_instance
  rw [Hom.isIso_iff_isIso_app]
  intro V
  haveI hfV : IsIso (f.1.app (Opposite.op V)) := by
    infer_instance
  simpa only [f, FM, FN, ObjectProperty.homMk, toPresheaf_map,
    mapPresheaf_app] using hfV

end AlgebraicGeometry.Scheme.Modules
