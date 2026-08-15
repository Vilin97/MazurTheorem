/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.KempfLocalVanishing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Finite affine covers and underlying abelian sheaves

This file contains the cover-theoretic and categorical machinery used by
affine vanishing.  It deliberately makes no quasicoherence assumptions;
those enter only in the capstone file.
-/

open CategoryTheory TopologicalSpace

universe u v

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open Limits

universe u₁ u₂ u₃ v₁ v₂ v₃

/--
If the composite with a reflector preserves colimits, then so does the
original functor out of the ambient category.
-/
theorem preservesColimitsOfShape_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    (R : C ⥤ D) [Reflective R]
    {J : Type u} [Category.{v} J]
    (F : C ⥤ E)
    [PreservesColimitsOfShape J (reflector R ⋙ F)]
    [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  refine @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _
    (NatIso.hcomp (asIso (𝟙 K))
      (asIso (reflectorAdjunction R).counit).symm).symm
    ⟨fun hc => ⟨?_⟩⟩
  let hc₂ := colimit.isColimit (K ⋙ R)
  let ψ :=
    IsColimit.uniqueUpToIso
      (isColimitOfPreserves (reflector R) hc₂) hc
  have φ :=
    IsColimit.ofIsoColimit
      (isColimitOfPreserves (reflector R ⋙ F) hc₂)
      (Functor.mapCoconeMapCocone
        (H := reflector R) (H' := F)
        (colimit.cocone (K ⋙ R))).symm
  exact
    IsColimit.ofIsoColimit φ
      ((Cocone.functoriality _ F).mapIso ψ)

/-- Universe-polymorphic version of the reflector preservation lemma. -/
theorem preservesColimitsOfSize_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    (R : C ⥤ D) [Reflective R]
    (F : C ⥤ E)
    [PreservesColimitsOfSize.{v, u} (reflector R ⋙ F)]
    [HasColimitsOfSize.{v, u} D] :
    PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape :=
    preservesColimitsOfShape_of_reflector_comp R F

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

namespace CompactSpace

/-- A cover of a compact space has a finite subcover, as an open cover. -/
lemma isOpenCover_elim_finite_subcover
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
    {ι : Type v} {U : ι → Opens Y} (h : IsOpenCover U) :
    ∃ t : Finset ι,
      IsOpenCover (Finset.restrict t U) := by
  obtain ⟨t, ht⟩ :=
    IsCompact.elim_finite_subcover
      (isCompact_univ (X := Y))
      (fun i => U i) (fun i => (U i).2)
      (by rw [IsOpenCover.iSup_set_eq_univ h])
  use t
  apply IsOpenCover.of_sets
  rw [Set.univ_subset_iff] at ht
  rw [← ht, Set.iUnion_subtype]
  rfl

end CompactSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance sheafAffineCoverCohomologyAddCommGroup
    {Y : TopCat.{u}}
    (G : TopCat.Sheaf AddCommGrpCat.{u} Y) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

private lemma additive_map_piLift_apply_eq_zero
    {C : Type (u + 1)} [Category.{u} C] [Preadditive C]
    (G : C ⥤ AddCommGrpCat.{u}) [G.Additive]
    {ι : Type u} [Finite ι] {A : C} {B : ι → C}
    [Limits.HasProduct B] (f : ∀ i, A ⟶ B i) (x : G.obj A)
    (h : ∀ i, G.map (f i) x = 0) :
    G.map (Limits.Pi.lift f) x = 0 := by
  apply Limits.Concrete.Pi.map_ext
  intro i
  calc
    G.map (Limits.Pi.π B i) (G.map (Limits.Pi.lift f) x) =
        (G.map (Limits.Pi.lift f) ≫ G.map (Limits.Pi.π B i)) x :=
      (ConcreteCategory.comp_apply _ _ _).symm
    _ = G.map (Limits.Pi.lift f ≫ Limits.Pi.π B i) x :=
      congrArg
        (fun q : G.obj A ⟶ G.obj (B i) => q x)
        (G.map_comp (Limits.Pi.lift f) (Limits.Pi.π B i)).symm
    _ = G.map (f i) x := by rw [Limits.Pi.lift_π]
    _ = 0 := h i
    _ = G.map (Limits.Pi.π B i) 0 := (map_zero _).symm

open Limits Opposite TopCat TopCat.Sheaf

variable {X : Scheme.{u}} (F : X.Modules)

/-- Forget the module structure of a sheaf of modules. -/
@[simps!]
noncomputable def toUnderlyingSheaf (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance toUnderlyingSheaf_additive :
    (toUnderlyingSheaf X).Additive :=
  inferInstanceAs
    (SheafOfModules.toSheaf X.ringCatSheaf).Additive

noncomputable instance toUnderlyingSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (toUnderlyingSheaf X) := by
  change PreservesFiniteLimits
    (SheafOfModules.toSheaf X.ringCatSheaf)
  infer_instance

instance toUnderlyingSheaf_faithful :
    (toUnderlyingSheaf X).Faithful :=
  inferInstanceAs
    (SheafOfModules.toSheaf X.ringCatSheaf).Faithful

noncomputable instance toPresheafOfModules_reflective :
    Reflective (toPresheafOfModules X) where
  L := PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)
  adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)

instance toUnderlyingSheaf_preservesColimitsOfSize :
    PreservesColimitsOfSize.{v, u}
      (toUnderlyingSheaf X) :=
  letI :
      PreservesColimitsOfSize.{v, u}
        (reflector (toPresheafOfModules X) ⋙
          toUnderlyingSheaf X) :=
    comp_preservesColimits
      (PresheafOfModules.toPresheaf
        X.ringCatSheaf.obj)
      (presheafToSheaf
        (Opens.grothendieckTopology X)
        AddCommGrpCat)
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.preservesColimitsOfSize_of_reflector_comp
    (toPresheafOfModules X) _

instance toUnderlyingSheaf_preservesColimits :
    PreservesColimits (toUnderlyingSheaf X) where

/-- The underlying sheaf of abelian groups of a sheaf of modules. -/
noncomputable abbrev underlyingSheaf :
    TopCat.Sheaf AddCommGrpCat X :=
  (toUnderlyingSheaf X).obj F

/-- The underlying morphism of sheaves of abelian groups. -/
noncomputable abbrev Hom.underlyingSheafHom
    {F G : X.Modules} (φ : F ⟶ G) :
    F.underlyingSheaf ⟶ G.underlyingSheaf :=
  (toUnderlyingSheaf X).map φ

variable {U : Scheme.{u}} (f : U ⟶ X)
variable [hf : IsOpenImmersion f]

example :
    ((restrictFunctor f ⋙ pushforward f).obj F).underlyingSheaf =
      (TopCat.Sheaf.restrict _ hf.base_open ⋙
        TopCat.Sheaf.pushforward _ f.base).obj
        F.underlyingSheaf :=
  rfl

lemma restrictAdjunction_underlyingSheafHom :
    ((restrictAdjunction f).unit.app F).underlyingSheafHom =
      (TopCat.Sheaf.restrictPushforwardAdjunction
        _ hf.base_open).unit.app F.underlyingSheaf :=
  rfl

lemma restrictAdjunction_toUnderlyingSheaf_map :
    (SheafOfModules.toSheaf X.ringCatSheaf).map
        ((restrictAdjunction f).unit.app F) =
      (TopCat.Sheaf.restrictPushforwardAdjunction
        _ hf.base_open).unit.app F.underlyingSheaf :=
  rfl

lemma restrictAdjunction_toRestrict (U : X.Opens) :
    ((restrictAdjunction U.ι).unit.app F).underlyingSheafHom =
      (TopCat.Sheaf.restrictPushforwardAdjunction _
        U.instIsOpenImmersionι.base_open).unit.app
        F.underlyingSheaf := by
  apply restrictAdjunction_underlyingSheafHom

section Cover

variable {I : Type u} (U : I → X.Opens)

/-- Map a sheaf of modules into the product of its open restrictions. -/
noncomputable def toCoverSheaf :
    F ⟶
      ∏ᶜ fun i =>
        (restrictFunctor (U i).ι ⋙
          pushforward (U i).ι).obj F :=
  Pi.lift
    (fun i => ((restrictAdjunction (U i).ι).unit.app F))

@[simp]
lemma toCoverSheaf_def :
    F.toCoverSheaf U =
      Pi.lift
        (fun i =>
          ((restrictAdjunction (U i).ι).unit.app F)) :=
  rfl

lemma toCoverSheaf_comp_pi (i : I) :
    F.toCoverSheaf U ≫
        Pi.π
          (fun i =>
            (restrictFunctor (U i).ι ⋙
              pushforward (U i).ι).obj F) i =
      (restrictAdjunction (U i).ι).unit.app F := by
  simp [Pi.lift_π]

lemma toCoverSheaf_comp_pi_underlyingSheafHom_hom_app
    {V : X.Opens}
    (s : F.underlyingSheaf.obj.obj (op V)) (i : I) :
    (Hom.underlyingSheafHom
      (Pi.π
        (fun i =>
          (restrictFunctor (U i).ι ⋙
            pushforward (U i).ι).obj F) i)).hom.app (op V)
        ((F.toCoverSheaf U).underlyingSheafHom.hom.app
          (op V) s) =
      (Hom.underlyingSheafHom
        ((restrictAdjunction (U i).ι).unit.app F)).hom.app
          (op V) s := by
  have hhom :=
    congrArg Hom.underlyingSheafHom
      (toCoverSheaf_comp_pi F U i)
  exact congrArg
    (fun k => k.hom.app (op V) s) hhom

variable {U} in
/-- The map into restrictions over an open cover is a monomorphism. -/
theorem toCoverSheaf_mono (h : IsOpenCover U) :
    Mono (F.toCoverSheaf U) := by
  have hmono :
      Mono (Hom.underlyingSheafHom
        (F.toCoverSheaf U)) := by
    refine Sheaf.mono_of_injective _ (fun W => ?_)
    rw [injective_iff_map_eq_zero]
    refine fun s hs =>
      TopCat.Presheaf.IsSheaf.section_ext
        F.underlyingSheaf.property (fun x hx => ?_)
    obtain ⟨i, hi⟩ := h.exists_mem x
    use (unop W) ⊓ (U i), inf_le_left
    refine
      ⟨by
        rw [Opens.mem_inf]
        exact ⟨hx, hi⟩,
      ?_⟩
    rw [map_zero]
    have reszero :
        ((Hom.underlyingSheafHom
          ((restrictAdjunction (U i).ι).unit.app F)).hom.app W) s = 0 := by
      have hcomponent :=
        congrArg
          (fun z =>
            (Hom.underlyingSheafHom
              (Pi.π
                (fun i =>
                  (restrictFunctor (U i).ι ⋙
                    pushforward (U i).ι).obj F) i)).hom.app W z)
          hs
      rw [toCoverSheaf_comp_pi_underlyingSheafHom_hom_app,
        map_zero] at hcomponent
      simpa using hcomponent
    rw [restrictAdjunction_underlyingSheafHom] at reszero
    simp only [Functor.id_obj,
      Adjunction.sheafPushforwardContinuous_unit_app_hom_app] at reszero
    have hopen :
        (unop W) ⊓ (U i) ≤
          (U i).isOpenEmbedding.functor.obj
            ((Opens.map (U i).inclusion').obj
              (unop W)) := by
      aesop
    let α :=
      ((U i).isOpenEmbedding.isOpenMap.adjunction.counit.app
        (unop W)).op
    let β := (homOfLE hopen).op
    let γ := (homOfLE (inf_le_left : (unop W) ⊓ U i ≤ unop W)).op
    have hopenEq : α ≫ β = γ := Subsingleton.elim _ _
    have hmap :
        F.underlyingSheaf.obj.map γ s =
          F.underlyingSheaf.obj.map β
            (F.underlyingSheaf.obj.map α s) := by
      calc
        F.underlyingSheaf.obj.map γ s =
            F.underlyingSheaf.obj.map (α ≫ β) s :=
          congrArg (fun q => q s)
            (congrArg F.underlyingSheaf.obj.map hopenEq).symm
        _ = (F.underlyingSheaf.obj.map α ≫
              F.underlyingSheaf.obj.map β) s :=
          congrArg (fun q => q s)
            (F.underlyingSheaf.obj.map_comp α β)
        _ = F.underlyingSheaf.obj.map β
              (F.underlyingSheaf.obj.map α s) := rfl
    exact hmap.trans
      ((congrArg (F.underlyingSheaf.obj.map β) reszero).trans
        (map_zero (F.underlyingSheaf.obj.map β).hom))
  exact
    Functor.mono_of_mono_map
      (SheafOfModules.toSheaf X.ringCatSheaf) hmono

/--
If a class restricts to zero on every member of a finite family, its
image in the product of those restrictions is zero.
-/
theorem toCoverSheaf_H_map_zero
    (n : ℕ)
    (c : CategoryTheory.Sheaf.H F.underlyingSheaf n)
    [Finite I]
    (h : ∀ i,
      CategoryTheory.Sheaf.H.map
        ((TopCat.Sheaf.toRestrict _ (U i)).app
          F.underlyingSheaf) n c = 0) :
    CategoryTheory.Sheaf.H.map
      (Hom.underlyingSheafHom (F.toCoverSheaf U)) n c = 0 := by
  let G := SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) n
  letI : G.Additive := inferInstance
  change G.map (F.toCoverSheaf U) c = 0
  delta toCoverSheaf
  apply additive_map_piLift_apply_eq_zero G _ c
  intro i
  dsimp only [G]
  have hmor := restrictAdjunction_toUnderlyingSheaf_map
    (F := F) (U i).ι
  have hmapped := congrArg
    (fun q => (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) n).map q) hmor
  have happ := congrArg (fun q => q c) hmapped
  have hfunctor := CategoryTheory.Sheaf.functorH_map
    (Opens.grothendieckTopology X) n
      ((TopCat.Sheaf.toRestrict AddCommGrpCat (U i)).app
        F.underlyingSheaf)
  exact happ.trans
    ((congrArg (fun q => q c) hfunctor).trans (h i))

end Cover

end AlgebraicGeometry.Scheme.Modules
