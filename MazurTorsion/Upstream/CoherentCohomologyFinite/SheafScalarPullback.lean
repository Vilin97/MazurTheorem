/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafPullbackUnitCoherence

/-!
# Pullback of rank-one scalar transition maps

This file turns the naturality square for scalar multiplication into the
conjugation formula used by line-bundle transition maps, and then packages
that formula through the descent pullback transport.
-/

open CategoryTheory

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

open _root_.AlgebraicGeometry

/-- Pullback of a scalar endomorphism, expressed by conjugating with the
canonical comparison `f⁎𝒪 ≅ 𝒪`. -/
lemma pullback_endomorphism_iso {T S : Scheme.{0}} (f : T ⟶ S)
    (a : Γ(S, ⊤)) :
    (Scheme.Modules.pullback f).map (endomorphism a) =
      (pullbackUnitIso f).hom ≫ endomorphism (f.appTop a) ≫
        (pullbackUnitIso f).inv := by
  have h :
      (Scheme.Modules.pullback f).map (endomorphism a) ≫
          (pullbackUnitIso f).hom =
        (pullbackUnitIso f).hom ≫ endomorphism (f.appTop a) :=
    pullback_endomorphism f a
  exact (Category.comp_id _).symm.trans
    ((CategoryTheory.whisker_eq _
      (pullbackUnitIso f).hom_inv_id.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((CategoryTheory.eq_whisker h
          (pullbackUnitIso f).inv).trans
          (Category.assoc _ _ _))))

/-- A transition formed by conjugating scalar multiplication with the unit
pullback comparisons keeps the same form after descent transport. -/
lemma pullbackTransport_unitIso
    {W V Y₁ Y₂ : Scheme.{0}} (p : W ⟶ V)
    (a : V ⟶ Y₁) (b : V ⟶ Y₂) (v : Γ(V, ⊤)ˣ) :
    (ModuleDescent.pullbackTransport p a b
      (pullbackUnitIso a ≪≫ unitIso v ≪≫
        (pullbackUnitIso b).symm)).hom =
      (pullbackUnitIso (p ≫ a)).hom ≫
        endomorphism (p.appTop v.val) ≫
        (pullbackUnitIso (p ≫ b)).inv := by
  simp only [ModuleDescent.pullbackTransport, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, unitIso_hom]
  have hfront :
      ((Scheme.Modules.pullbackComp p a).symm.app
          (SheafOfModules.unit Y₁.ringCatSheaf)).hom ≫
          (Scheme.Modules.pullback p).map
            (pullbackUnitIso a).hom ≫
          (pullbackUnitIso p).hom =
        (pullbackUnitIso (p ≫ a)).hom := by
    let A := (Scheme.Modules.pullbackComp p a).app
      (SheafOfModules.unit Y₁.ringCatSheaf)
    change A.inv ≫
        (Scheme.Modules.pullback p).map
          (pullbackUnitIso a).hom ≫
        (pullbackUnitIso p).hom =
      (pullbackUnitIso (p ≫ a)).hom
    exact
      (CategoryTheory.whisker_eq A.inv
          (pullbackUnitIso_comp a p).symm).trans
        (A.inv_hom_id_assoc
          (pullbackUnitIso (p ≫ a)).hom)
  have hback :
      (pullbackUnitIso p).inv ≫
          (Scheme.Modules.pullback p).map
            (pullbackUnitIso b).inv ≫
          ((Scheme.Modules.pullbackComp p b).app
            (SheafOfModules.unit Y₂.ringCatSheaf)).hom =
        (pullbackUnitIso (p ≫ b)).inv := by
    have h :
        (Scheme.Modules.pullbackComp p b).app
              (SheafOfModules.unit Y₂.ringCatSheaf) ≪≫
            pullbackUnitIso (p ≫ b) =
          (Scheme.Modules.pullback p).mapIso
              (pullbackUnitIso b) ≪≫
            pullbackUnitIso p := by
      apply Iso.ext
      change
        (Scheme.Modules.pullbackComp p b).hom.app
              (SheafOfModules.unit Y₂.ringCatSheaf) ≫
            (pullbackUnitIso (p ≫ b)).hom =
          (Scheme.Modules.pullback p).map
              (pullbackUnitIso b).hom ≫
            (pullbackUnitIso p).hom
      exact pullbackUnitIso_comp b p
    have hinv := congrArg Iso.inv h
    change
      (pullbackUnitIso (p ≫ b)).inv ≫
          (Scheme.Modules.pullbackComp p b).inv.app
            (SheafOfModules.unit Y₂.ringCatSheaf) =
        (pullbackUnitIso p).inv ≫
          (Scheme.Modules.pullback p).map
            (pullbackUnitIso b).inv at hinv
    let B := (Scheme.Modules.pullbackComp p b).app
      (SheafOfModules.unit Y₂.ringCatSheaf)
    change
      (pullbackUnitIso p).inv ≫
          (Scheme.Modules.pullback p).map
            (pullbackUnitIso b).inv ≫ B.hom =
        (pullbackUnitIso (p ≫ b)).inv
    calc
      _ = ((pullbackUnitIso p).inv ≫
          (Scheme.Modules.pullback p).map
            (pullbackUnitIso b).inv) ≫ B.hom :=
        (Category.assoc _ _ _).symm
      _ = ((pullbackUnitIso (p ≫ b)).inv ≫ B.inv) ≫
          B.hom :=
        CategoryTheory.eq_whisker hinv.symm B.hom
      _ = _ :=
        (Category.assoc _ _ _).trans
          ((CategoryTheory.whisker_eq _ B.inv_hom_id).trans
            (Category.comp_id _))
  have hIsoHom :
      (pullbackUnitIso a ≪≫ unitIso v ≪≫
          (pullbackUnitIso b).symm).hom =
        (pullbackUnitIso a).hom ≫ endomorphism v.val ≫
          (pullbackUnitIso b).inv := by
    rfl
  rw [hIsoHom]
  have hmap :
      (Scheme.Modules.pullback p).map
          ((pullbackUnitIso a).hom ≫
            endomorphism v.val ≫ (pullbackUnitIso b).inv) =
        (Scheme.Modules.pullback p).map
            (pullbackUnitIso a).hom ≫
          (Scheme.Modules.pullback p).map
            (endomorphism v.val) ≫
          (Scheme.Modules.pullback p).map
            (pullbackUnitIso b).inv := by
    exact
      ((Scheme.Modules.pullback p).map_comp
        (pullbackUnitIso a).hom
        (endomorphism v.val ≫ (pullbackUnitIso b).inv)).trans
      (CategoryTheory.whisker_eq
        ((Scheme.Modules.pullback p).map
          (pullbackUnitIso a).hom)
        ((Scheme.Modules.pullback p).map_comp
          (endomorphism v.val)
          (pullbackUnitIso b).inv))
  rw [hmap, pullback_endomorphism_iso]
  rw [← hfront, ← hback]
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar
