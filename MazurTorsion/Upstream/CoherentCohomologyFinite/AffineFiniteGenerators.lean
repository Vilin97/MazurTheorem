/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineBasicOpenDirectRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentTilde

/-!
# Finite generators on affine basic opens

Finite generating sections on an open neighbourhood of a distinguished open
transport to the corresponding spectrum of an away localization.  We also
record the affine algebra fact that a finite global generating family for a
quasicoherent module sheaf makes its module of global sections finite.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

open SheafOfModules

private theorem epiIsoHom {C : Type*} [Category C]
    {X Y : C} (e : X ≅ Y) : Epi e.hom := by
  constructor
  intro Z g h w
  have hcancel := congrArg (fun k => e.inv ≫ k) w
  exact (e.inv_hom_id_assoc g).symm.trans
    (hcancel.trans (e.inv_hom_id_assoc h))

/-- Modules on the iterated over site above `W ⟶ U` are equivalent to
modules on the over site above `W.left`. -/
noncomputable def iteratedOverModulesEquivalence
    (U : (Spec R).Opens) (W : Over U) :
    SheafOfModules.{u} ((Spec R).ringCatSheaf.over W.left) ≌
      SheafOfModules.{u} (((Spec R).ringCatSheaf.over U).over W) :=
  pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv W)
    (S := ((Spec R).ringCatSheaf.over U).over W)
    (R := (Spec R).ringCatSheaf.over W.left)
    (𝟙 _) (𝟙 _)
    (by ext : 2; exact (Spec R).ringCatSheaf.1.map_id _)
    (by ext : 2; exact (Spec R).ringCatSheaf.1.map_id _)

/-- The inverse of the iterated-over equivalence sends the iterated
restriction of a module sheaf to its direct restriction. -/
noncomputable def iteratedOverModulesIso
    (M : (Spec R).Modules) (U : (Spec R).Opens) (W : Over U) :
    (iteratedOverModulesEquivalence U W).inverse.obj
        ((M.over U).over W) ≅
      M.over W.left :=
  (iteratedOverModulesEquivalence U W).fullyFaithfulFunctor.preimageIso
    (by
      exact
        (iteratedOverModulesEquivalence U W).counitIso.app
          ((M.over U).over W))

/-- Generating sections on an over site restrict to a smaller basic-open
over site. -/
noncomputable def generatingSectionsOverBasicOpen
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (M.over (specBasicOpen g)).GeneratingSections := by
  let W : Over U := Over.mk (homOfLE hg)
  let G₁ : ((M.over U).over W).GeneratingSections :=
    G.map (pushforward (𝟙 (((Spec R).ringCatSheaf.over U).over W)))
      (by rfl)
  let G₂ :
      ((iteratedOverModulesEquivalence U W).inverse.obj
        ((M.over U).over W)).GeneratingSections :=
    G₁.map (iteratedOverModulesEquivalence U W).inverse (.refl _)
  exact G₂.ofEpi (iteratedOverModulesIso M U W).hom

@[simp]
theorem generatingSectionsOverBasicOpen_I
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (generatingSectionsOverBasicOpen M U G g hg).I = G.I := by
  rfl

instance generatingSectionsOverBasicOpen_isFiniteType
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) [G.IsFiniteType] :
    (generatingSectionsOverBasicOpen M U G g hg).IsFiniteType where
  finite := by
    rw [generatingSectionsOverBasicOpen_I]
    infer_instance

/-- Generating sections near `D(g)` transport to the affine scheme
`Spec R_g`. -/
noncomputable def generatingSectionsModulesRestrictBasicOpen
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (modulesRestrictBasicOpen g M).GeneratingSections := by
  let G₂ : (M.over (specBasicOpen g)).GeneratingSections :=
    generatingSectionsOverBasicOpen M U G g hg
  let E := modulesOverBasicOpenEquivalence g
  let invF := E.inverse
  let G₃ :
      (invF.obj
        (M.over (specBasicOpen g))).GeneratingSections :=
    @SheafOfModules.GeneratingSections.map
      _ _ _ _ _ _ _ _ _ _ _ _ _ G₂ invF
      (E.symm.toAdjunction.leftAdjoint_preservesColimits)
      (.refl _)
  let e := overBasicOpenIsoRestrict g M
  let G₄ : (M.restrict (specBasicOpen g).ι).GeneratingSections :=
    @SheafOfModules.GeneratingSections.ofEpi
      _ _ _ _ _ _ _ _ G₃ e.hom (epiIsoHom e)
  let restrictF := Scheme.Modules.restrictFunctor.{u}
    (basicOpenIsoSpecAway g).inv
  exact @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G₄ restrictF
    (restrictBasicOpenPreservesColimits g)
    (restrictBasicOpenUnitIso g).symm

@[simp]
theorem generatingSectionsModulesRestrictBasicOpen_I
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (generatingSectionsModulesRestrictBasicOpen M U G g hg).I = G.I := by
  unfold generatingSectionsModulesRestrictBasicOpen
  rfl

instance generatingSectionsModulesRestrictBasicOpen_isFiniteType
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) [G.IsFiniteType] :
    (generatingSectionsModulesRestrictBasicOpen M U G g hg).IsFiniteType where
  finite := by
    rw [generatingSectionsModulesRestrictBasicOpen_I]
    infer_instance

/-- The direct restriction along `Spec R_g ⟶ Spec R` inherits finite
generating sections from any neighbourhood of `D(g)`. -/
noncomputable def generatingSectionsDirectAwayOfOver
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (M.restrict
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (Localization.Away g))))).GeneratingSections := by
  let e := modulesRestrictBasicOpenDirectIso g M
  exact
    @SheafOfModules.GeneratingSections.ofEpi
      _ _ _ _ _ _ _ _
      (generatingSectionsModulesRestrictBasicOpen M U G g hg)
      e.hom (epiIsoHom e)

@[simp]
theorem generatingSectionsDirectAwayOfOver_I
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (generatingSectionsDirectAwayOfOver M U G g hg).I = G.I := by
  unfold generatingSectionsDirectAwayOfOver
  rfl

instance generatingSectionsDirectAwayOfOver_isFiniteType
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (G : (M.over U).GeneratingSections) (g : R)
    (hg : specBasicOpen g ≤ U) [G.IsFiniteType] :
    (generatingSectionsDirectAwayOfOver M U G g hg).IsFiniteType where
  finite := by
    rw [generatingSectionsDirectAwayOfOver_I]
    infer_instance

namespace Scheme.Modules

private theorem epi_iso_hom {C : Type*} [Category C]
    {X Y : C} (e : X ≅ Y) : Epi e.hom := by
  constructor
  intro Z g h w
  have := congrArg (fun k => e.inv ≫ k) w
  simpa only [Category.assoc, e.inv_hom_id_assoc] using this

/-- A global generating family indexed by a finite type gives a finite module
of global sections for an affine quasicoherent sheaf. -/
theorem finite_top_sections_of_finite_generatingSections_of_finite
    (F : (Spec R).Modules) [IsIso F.fromTildeΓ]
    (G : F.GeneratingSections) (hG : Finite G.I) :
    Module.Finite R Γ(F, ⊤) := by
  letI : Finite G.I := hG
  let A : ModuleCat.{u} R := ModuleCat.of R (G.I →₀ R)
  let B : ModuleCat.{u} R := moduleSpecΓFunctor.obj F
  let eFree := tildeFinsupp (R := R) G.I
  let eCounit := asIso F.fromTildeΓ
  let h : (tilde.functor R).obj A ⟶ (tilde.functor R).obj B :=
    (eFree.hom ≫ G.π) ≫ eCounit.inv
  let q : A ⟶ B := (tilde.functor R).preimage h
  haveI : Epi h := by
    dsimp only [h]
    exact epi_comp'
      (epi_comp' (epi_iso_hom eFree) G.epi)
      (epi_iso_hom eCounit.symm)
  haveI : Epi ((tilde.functor R).map q) := by
    rw [Functor.map_preimage]
    infer_instance
  haveI : Epi q :=
    (tilde.functor R).epi_of_epi_map (by infer_instance)
  exact Module.Finite.of_surjective q.hom
    ((ModuleCat.epi_iff_surjective q).mp inferInstance)

/-- A finite global generating family of an affine quasicoherent module sheaf
gives a finite module of global sections. -/
theorem finite_top_sections_of_finite_generatingSections
    (F : (Spec R).Modules) [IsIso F.fromTildeΓ]
    (G : F.GeneratingSections) [G.IsFiniteType] :
    Module.Finite R Γ(F, ⊤) :=
  finite_top_sections_of_finite_generatingSections_of_finite
    F G (SheafOfModules.GeneratingSections.IsFiniteType.finite
      (self := inferInstance))

end Scheme.Modules

end AlgebraicGeometry
