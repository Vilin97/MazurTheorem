/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenSliceDenseSubsite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Module sheaves on an open and on the corresponding slice site

For an open `U` of a scheme `X`, this file lifts the equivalence
`Over U ≌ Opens U` to sheaves of modules.  It also identifies geometric
restriction of an `X`-module with the ordinary slice-site restriction.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- Continuity of the inverse leg of the open-slice equivalence. -/
instance overEquivInverseIsContinuous :
    (TopologicalSpace.Opens.overEquivalence U).inverse.IsContinuous
      (Opens.grothendieckTopology ↥(↑U : Scheme))
      ((Opens.grothendieckTopology ↥X).over U) := by
  change (TopologicalSpace.Opens.overEquivalence U).inverse.IsContinuous
    (Opens.grothendieckTopology ↥U)
    ((Opens.grothendieckTopology ↥X).over U)
  infer_instance

/-- Continuity of the functor leg of the open-slice equivalence. -/
instance overEquivFunctorIsContinuous :
    (TopologicalSpace.Opens.overEquivalence U).functor.IsContinuous
      ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥(↑U : Scheme)) := by
  change (TopologicalSpace.Opens.overEquivalence U).functor.IsContinuous
    ((Opens.grothendieckTopology ↥X).over U)
    (Opens.grothendieckTopology ↥U)
  infer_instance

/-- The image of the reindexed open is its left object in the slice. -/
private lemma image_overEquiv_functor_obj (V : Over U) :
    U.ι ''ᵁ ((TopologicalSpace.Opens.overEquivalence U).functor.obj V) =
      V.left := by
  apply TopologicalSpace.Opens.ext
  ext y
  simp only [SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨y, leOfHom V.hom hy⟩, hy, rfl⟩

/-- The structure-ring comparison along the open-slice equivalence. -/
private noncomputable def phiOver :
    X.ringCatSheaf.over U ⟶
      ((TopologicalSpace.Opens.overEquivalence U).functor.sheafPushforwardContinuous RingCat
          ((Opens.grothendieckTopology ↥X).over U)
          (Opens.grothendieckTopology ↥(↑U : Scheme))).obj
        (↑U : Scheme).ringCatSheaf :=
  ⟨
    { app := fun V =>
        X.ringCatSheaf.obj.map
          (eqToHom (image_overEquiv_functor_obj U V.unop)).op
      naturality := by
        intro a b f
        simp only [Functor.sheafPushforwardContinuous_obj_obj_map]
        erw [← Functor.map_comp, ← Functor.map_comp]
        congr 1 }⟩

/-- The left component of inverse reindexing is the image in `X`. -/
private lemma left_overEquiv_inverse_obj
    (W : TopologicalSpace.Opens ↥(↑U : Scheme)) :
    ((TopologicalSpace.Opens.overEquivalence U).inverse.obj W).left =
      U.ι ''ᵁ W := by
  apply TopologicalSpace.Opens.ext
  ext y
  simp only [Scheme.Hom.coe_image, SetLike.mem_coe]
  rfl

/-- The inverse structure-ring comparison. -/
private noncomputable def psiOver :
    (↑U : Scheme).ringCatSheaf ⟶
      ((TopologicalSpace.Opens.overEquivalence U).inverse.sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology ↥(↑U : Scheme))
          ((Opens.grothendieckTopology ↥X).over U)).obj
        (X.ringCatSheaf.over U) :=
  ⟨
    { app := fun W =>
        X.ringCatSheaf.obj.map
          (eqToHom (left_overEquiv_inverse_obj U W.unop)).op
      naturality := by
        intro a b f
        rw [show
          (↑U : Scheme).ringCatSheaf.obj.map f =
            X.ringCatSheaf.obj.map (U.ι.opensFunctor.op.map f) from rfl]
        change
          (forget₂ CommRingCat RingCat).map _ ≫
              (forget₂ CommRingCat RingCat).map _ =
            (forget₂ CommRingCat RingCat).map _ ≫
              (forget₂ CommRingCat RingCat).map _
        erw [← (forget₂ CommRingCat RingCat).map_comp,
          ← (forget₂ CommRingCat RingCat).map_comp]
        congr 1
        exact
          (Functor.map_comp _ _ _).symm.trans
            ((congrArg _ (Subsingleton.elim _ _)).trans
              (Functor.map_comp _ _ _)) }⟩

/--
Sheaves of modules on the open subscheme are equivalent to sheaves of
modules on the ambient opens site sliced over `U`.
-/
noncomputable def overEquivalence :
    SheafOfModules ((↑U : Scheme).ringCatSheaf) ≌
      SheafOfModules (X.ringCatSheaf.over U) := by
  refine SheafOfModules.pushforwardPushforwardEquivalence
    (TopologicalSpace.Opens.overEquivalence U)
    (phiOver U) (psiOver U) ?_ ?_
  · ext W : 2
    simp only [Functor.whiskerRight_app, NatTrans.op_app,
      Functor.op_obj, phiOver, psiOver]
    change
      X.ringCatSheaf.obj.map
          (U.ι.opensFunctor.op.map
            ((TopologicalSpace.Opens.overEquivalence U).counit.app
              W.unop).op) =
        _
    change
      (forget₂ CommRingCat RingCat).map _ =
        (forget₂ CommRingCat RingCat).map _ ≫
          (forget₂ CommRingCat RingCat).map _
    erw [← (forget₂ CommRingCat RingCat).map_comp]
    congr 1
    exact
      (congrArg _ (Subsingleton.elim _ _)).trans
        (Functor.map_comp _ _ _)
  · ext W : 2
    simp only [NatTrans.comp_app, Functor.op_obj, phiOver, psiOver,
      NatTrans.id_app]
    rw [show
      (𝟙 ((Sheaf.over X.ringCatSheaf U).obj.obj W)) =
        X.ringCatSheaf.obj.map (𝟙 (Opposite.op W.unop.left))
      from (X.ringCatSheaf.obj.map_id _).symm]
    ext x
    change X.ringCatSheaf.obj.map _
        (X.ringCatSheaf.obj.map _
          (X.ringCatSheaf.obj.map _ x)) =
      X.ringCatSheaf.obj.map _ x
    erw [← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    apply ConcreteCategory.congr_hom
    congr 1

/-- Morphisms transported by the open-slice equivalence are evaluated by
reindexing along the underlying equivalence of opens. -/
lemma overEquivalence_map_app
    {M N : (↑U : Scheme).Modules} (f : M ⟶ N)
    (V : (Over U)ᵒᵖ)
    (x : ((overEquivalence U).functor.obj M).val.obj V) :
    ((overEquivalence U).functor.map f).val.app V x =
      f.val.app
        (.op
          ((TopologicalSpace.Opens.overEquivalence U).functor.obj
            V.unop)) x := by
  rfl

/-- Ring morphism underlying geometric restriction to `U`. -/
private noncomputable def psiRestrict :
    (↑U : Scheme).ringCatSheaf ⟶
      (U.ι.opensFunctor.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology ↥(↑U : Scheme))
        (Opens.grothendieckTopology ↥X)).obj X.ringCatSheaf :=
  letI α :
      (↑U : Scheme).presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf :=
    { app := fun W => (U.ι.appIso W.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- The slice forgetful functor and geometric image functor agree. -/
private noncomputable def overForgetNatIso :
    Over.forget U ≅
      (TopologicalSpace.Opens.overEquivalence U).functor ⋙
        U.ι.opensFunctor :=
  NatIso.ofComponents
    (fun V => eqToIso (image_overEquiv_functor_obj U V).symm)
    (fun _ => Subsingleton.elim _ _)

/--
Under `overEquivalence`, geometric restriction to `U` is naturally
isomorphic to slice-site restriction over `U`.
-/
noncomputable def restrictOverNatIso :
    restrictFunctor U.ι ⋙ (overEquivalence U).functor ≅
      SheafOfModules.overFunctor X.ringCatSheaf U := by
  haveI hF1 :
      (TopologicalSpace.Opens.overEquivalence U).functor.IsContinuous
        ((Opens.grothendieckTopology ↥X).over U)
        (Opens.grothendieckTopology ↥(↑U : Scheme)) :=
    inferInstance
  haveI hF2 :
      U.ι.opensFunctor.IsContinuous
        (Opens.grothendieckTopology ↥(↑U : Scheme))
        (Opens.grothendieckTopology ↥X) :=
    inferInstance
  letI hcomp :
      ((TopologicalSpace.Opens.overEquivalence U).functor ⋙
          U.ι.opensFunctor).IsContinuous
        ((Opens.grothendieckTopology ↥X).over U)
        (Opens.grothendieckTopology ↥X) :=
    @Functor.isContinuous_comp _ _ _ _ _ _
      (TopologicalSpace.Opens.overEquivalence U).functor
      U.ι.opensFunctor
      ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥(↑U : Scheme))
      (Opens.grothendieckTopology ↥X) hF1 hF2
  refine
    (@SheafOfModules.pushforwardComp
      (Over U) _
      (TopologicalSpace.Opens ↥(↑U : Scheme)) _
      (TopologicalSpace.Opens ↥X) _
      ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥(↑U : Scheme))
      (TopologicalSpace.Opens.overEquivalence U).functor
      (X.ringCatSheaf.over U) (↑U : Scheme).ringCatSheaf
      hF1 (phiOver U)
      (Opens.grothendieckTopology ↥X) U.ι.opensFunctor
      X.ringCatSheaf hF2 (psiRestrict U)) ≪≫ ?_
  refine
    SheafOfModules.pushforwardNatIso _
      (overForgetNatIso U) ≪≫ ?_
  refine SheafOfModules.pushforwardCongr ?_
  ext V : 3
  erw [ObjectProperty.FullSubcategory.comp_hom]
  erw [NatTrans.comp_app]
  erw [ObjectProperty.FullSubcategory.comp_hom]
  erw [NatTrans.comp_app]
  erw [Functor.sheafPushforwardContinuous_map_hom_app]
  erw [Functor.sheafPushforwardContinuousNatTrans_app_hom]
  erw [Functor.whiskerRight_app]
  erw [Functor.whiskerRight_app]
  erw [ObjectProperty.FullSubcategory.id_hom]
  erw [NatTrans.id_app]
  dsimp only [phiOver, psiRestrict, overForgetNatIso]
  rw [Scheme.Opens.ι_appIso]
  rw [Iso.refl_inv]
  erw [(forget₂ CommRingCat RingCat).map_id]
  erw [Category.comp_id]
  change X.ringCatSheaf.obj.map _ ≫
      X.ringCatSheaf.obj.map _ = 𝟙 _
  erw [← Functor.map_comp]
  let p :=
    (eqToHom (image_overEquiv_functor_obj U V.unop)).op
  let q :=
    (NatTrans.op (overForgetNatIso U).hom).app V
  change X.ringCatSheaf.obj.map (p ≫ q) = 𝟙 _
  have hpq : p ≫ q = 𝟙 _ := Subsingleton.elim _ _
  rw [hpq]
  exact X.ringCatSheaf.obj.map_id _

/--
Under `overEquivalence`, geometric restriction of `M` to `U` is its
slice-site restriction `M.over U`.
-/
noncomputable def restrictOverIso (M : X.Modules) :
    (overEquivalence U).functor.obj (M.restrict U.ι) ≅ M.over U :=
  (restrictOverNatIso U).app M

/-- Naturality of the comparison between geometric restriction and
slice-site restriction. -/
theorem restrictOverIso_naturality
    {M N : X.Modules} (f : M ⟶ N) :
    (overEquivalence U).functor.map
          ((restrictFunctor U.ι).map f) ≫
        (restrictOverIso U N).hom =
      (restrictOverIso U M).hom ≫
        f.over U := by
  exact (restrictOverNatIso U).hom.naturality f

/-- Pointwise description of the comparison between geometric restriction
and slice-site restriction. -/
lemma restrictOverIso_hom_app (M : X.Modules)
    (V : (Over U)ᵒᵖ)
    (x :
      ((overEquivalence U).functor.obj
        (M.restrict U.ι)).val.obj V) :
    (restrictOverIso U M).hom.val.app V x =
      M.val.map
        ((overForgetNatIso U).hom.app V.unop).op x := by
  rfl

/-- The image in `X` of the open corresponding to a slice object is its
left-hand open.  This public form is useful for writing pointwise formulas
for the open-slice equivalence. -/
lemma overEquivalence_image_functor_obj (V : Over U) :
    U.ι ''ᵁ
        ((TopologicalSpace.Opens.overEquivalence U).functor.obj V) =
      V.left :=
  image_overEquiv_functor_obj U V

/-- Pointwise formula for the inverse comparison from a slice restriction
to geometric restriction on the open subscheme. -/
lemma restrictOverIso_inv_app (M : X.Modules)
    (V : (Over U)ᵒᵖ)
    (x : (M.over U).val.obj V) :
    (restrictOverIso U M).inv.val.app V x =
      (M.restrictAppIso U.ι
          ((TopologicalSpace.Opens.overEquivalence U).functor.obj
            V.unop)).inv.hom
        ((M.presheaf.mapIso
          (eqToIso
            (overEquivalence_image_functor_obj U V.unop)).op).hom.hom
          x) := by
  let W :=
    (TopologicalSpace.Opens.overEquivalence U).functor.obj V.unop
  let e : U.ι ''ᵁ W = V.unop.left :=
    overEquivalence_image_functor_obj U V.unop
  let y : Γ(M.restrict U.ι, W) :=
    (M.restrictAppIso U.ι W).inv.hom
      ((M.presheaf.mapIso (eqToIso e).op).hom.hom x)
  have hy :
      (restrictOverIso U M).hom.val.app V y = x := by
    erw [restrictOverIso_hom_app]
    change
      M.val.map ((overForgetNatIso U).hom.app V.unop).op
          (M.val.map (eqToIso e).op.hom x) =
        x
    let p := ((overForgetNatIso U).hom.app V.unop).op
    let q := (eqToIso e).op.hom
    exact
      (ConcreteCategory.congr_hom
        (M.val.map_comp q p).symm x).trans
        ((congrArg (fun a => M.val.map a x)
          (Subsingleton.elim (q ≫ p)
            (𝟙 (Opposite.op V.unop.left)))).trans
          (ConcreteCategory.congr_hom
            (M.val.map_id (Opposite.op V.unop.left)) x))
  change (restrictOverIso U M).inv.val.app V x = y
  erw [← hy]
  change
    ((restrictOverIso U M).hom ≫
      (restrictOverIso U M).inv).val.app V y = y
  rw [Iso.hom_inv_id]
  rfl

/-- Restricting a terminal section to the open corresponding to the
terminal slice object and then applying `restrictOverIso` recovers the
usual ambient section on `U`. -/
lemma restrictOverIso_hom_app_terminal_restrict_top
    (M : X.Modules) (x : Γ(M.restrict U.ι, ⊤)) :
    (restrictOverIso U M).hom.val.app
        (.op (Over.mk (𝟙 U)))
        ((M.restrict U.ι).val.map
          (homOfLE
            (show
              (TopologicalSpace.Opens.overEquivalence U).functor.obj
                    (Over.mk (𝟙 U)) ≤
                (⊤ : (↑U : Scheme).Opens)
              from le_top)).op x) =
      (eqToIso
        (congrArg (fun W => Γ(M, W))
          U.ι_image_top)).hom
        ((M.restrictAppIso U.ι ⊤).hom x) := by
  erw [restrictOverIso_hom_app]
  change
    M.val.map
        ((overForgetNatIso U).hom.app
          (Over.mk (𝟙 U))).op
        (M.val.map
          (U.ι.opensFunctor.op.map
            (homOfLE
              (show
                (TopologicalSpace.Opens.overEquivalence U).functor.obj
                      (Over.mk (𝟙 U)) ≤
                  (⊤ : (↑U : Scheme).Opens)
                from le_top)).op) x) =
      _
  have cast_apply :
      ∀ {A B : X.Opens} (h : A = B) (y : Γ(M, A)),
        (eqToIso
          (congrArg (fun W => Γ(M, W)) h)).hom y =
        M.val.map (eqToHom h.symm).op y := by
    intro A B h y
    subst B
    change y = M.val.map (𝟙 (Opposite.op A)) y
    exact
      (ConcreteCategory.congr_hom
        (M.val.map_id (Opposite.op A)) y).symm
  rw [cast_apply U.ι_image_top]
  rw [show (M.restrictAppIso U.ι ⊤).hom x = x from rfl]
  let p :=
    ((overForgetNatIso U).hom.app
      (Over.mk (𝟙 U))).op
  let q :=
    U.ι.opensFunctor.op.map
      (homOfLE
        (show
          (TopologicalSpace.Opens.overEquivalence U).functor.obj
                (Over.mk (𝟙 U)) ≤
            (⊤ : (↑U : Scheme).Opens)
          from le_top)).op
  change M.val.map p (M.val.map q x) =
    M.val.map (eqToHom U.ι_image_top.symm).op x
  have hcomp : M.val.map p (M.val.map q x) =
      M.val.map (q ≫ p) x :=
    ConcreteCategory.congr_hom
      (M.val.map_comp q p).symm x
  exact hcomp

/-- The equivalence sends the structure module to the structure module. -/
noncomputable def unitOverIso :
    (overEquivalence U).functor.obj
        (SheafOfModules.unit (↑U : Scheme).ringCatSheaf) ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) := by
  haveI hφ : IsIso (phiOver U) := by
    have hmap :
        IsIso
          ((sheafToPresheaf
            ((Opens.grothendieckTopology ↥X).over U) RingCat).map
              (phiOver U)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro W
      exact inferInstanceAs
        (IsIso
          (X.ringCatSheaf.obj.map
            (eqToHom
              (image_overEquiv_functor_obj U W.unop)).op))
    exact isIso_of_reflects_iso (phiOver U)
      (sheafToPresheaf _ RingCat)
  haveI :
      IsIso
        (SheafOfModules.unitToPushforwardObjUnit (phiOver U)) := by
    rw [← isIso_iff_of_reflects_iso _
        (SheafOfModules.forget _),
      ← isIso_iff_of_reflects_iso _
        (PresheafOfModules.toPresheaf _),
      NatTrans.isIso_iff_isIso_app]
    intro W
    haveI hval : IsIso ((phiOver U).hom) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      exact inferInstanceAs
        (IsIso
          (X.ringCatSheaf.obj.map
            (eqToHom
              (image_overEquiv_functor_obj U V.unop)).op))
    haveI happ : IsIso ((phiOver U).hom.app W) := inferInstance
    change
      IsIso
        ((forget₂ RingCat AddCommGrpCat).map
          ((phiOver U).hom.app W))
    infer_instance
  exact
    (asIso
      (SheafOfModules.unitToPushforwardObjUnit
        (phiOver U))).symm

/-- Pointwise, the inverse unit comparison is the structure-ring map used
to define the open-slice pushforward. -/
lemma unitOverIso_inv_app
    (V : (Over U)ᵒᵖ)
    (r : (X.ringCatSheaf.over U).obj.obj V) :
    (unitOverIso U).inv.val.app V r =
      (phiOver U).hom.app V r := by
  rfl

/-- Pointwise formula for transporting a regular function from the open
subscheme back to the ambient slice site. -/
lemma unitOverIso_hom_app
    (V : (Over U)ᵒᵖ)
    (r :
      ((overEquivalence U).functor.obj
        (SheafOfModules.unit
          (↑U : Scheme).ringCatSheaf)).val.obj V) :
    (unitOverIso U).hom.val.app V r =
      (X.presheaf.mapIso
        (eqToIso
          (overEquivalence_image_functor_obj U V.unop)).op).inv.hom
        ((U.ι.appIso
          ((TopologicalSpace.Opens.overEquivalence U).functor.obj
            V.unop)).inv.hom r) := by
  let W :=
    (TopologicalSpace.Opens.overEquivalence U).functor.obj V.unop
  let e : U.ι ''ᵁ W = V.unop.left :=
    overEquivalence_image_functor_obj U V.unop
  let z : Γ(X, V.unop.left) :=
    (X.presheaf.mapIso (eqToIso e).op).inv.hom
      ((U.ι.appIso W).inv.hom r)
  have hz : (unitOverIso U).inv.val.app V z = r := by
    erw [unitOverIso_inv_app]
    dsimp only [phiOver]
    change
      X.presheaf.map (eqToHom
          (image_overEquiv_functor_obj U V.unop)).op z = r
    have happ : (U.ι.appIso W).inv.hom r = r := by
      erw [Scheme.Opens.ι_appIso]
      rfl
    unfold z
    erw [happ]
    rw [show
      (eqToHom (image_overEquiv_functor_obj U V.unop)).op =
        (eqToIso e).op.hom
      from Subsingleton.elim _ _]
    exact (X.presheaf.mapIso
      (eqToIso e).op).inv_hom_id_apply r
  change (unitOverIso U).hom.val.app V r = z
  erw [← hz]
  change
    ((unitOverIso U).inv ≫
      (unitOverIso U).hom).val.app V z = z
  rw [Iso.inv_hom_id]
  rfl

/-- Transporting a unit-module morphism through the open-slice
equivalence and the unit comparison still evaluates it on `1`. -/
lemma overEquivalence_map_unitOverIso_inv_app_one
    {M : (↑U : Scheme).Modules}
    (f :
      SheafOfModules.unit (↑U : Scheme).ringCatSheaf ⟶ M)
    (V : (Over U)ᵒᵖ) :
    ((overEquivalence U).functor.map f).val.app V
        ((unitOverIso U).inv.val.app V
          (1 : (X.ringCatSheaf.over U).obj.obj V)) =
      f.val.app
        (.op
          ((TopologicalSpace.Opens.overEquivalence U).functor.obj
            V.unop))
        (1 : (↑U : Scheme).ringCatSheaf.obj.obj
          (.op
            ((TopologicalSpace.Opens.overEquivalence U).functor.obj
              V.unop))) := by
  erw [overEquivalence_map_app, unitOverIso_inv_app]
  exact congrArg
    (fun r => f.val.app
      (.op
        ((TopologicalSpace.Opens.overEquivalence U).functor.obj
          V.unop)) r)
    ((phiOver U).hom.app V).hom.map_one

/-- A trivialization after restriction to an open subscheme induces the
corresponding trivialization on the slice site over that open. -/
noncomputable def chartOverIso (M : X.Modules)
    (e : M.restrict U.ι ≅
      SheafOfModules.unit (↑U : Scheme).ringCatSheaf) :
    M.over U ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (restrictOverIso U M).symm ≪≫
    (overEquivalence U).functor.mapIso e ≪≫
    unitOverIso U

/-- Pointwise expansion of the slice-site trivialization induced by a
trivialization on the corresponding open subscheme. -/
lemma chartOverIso_hom_app (M : X.Modules)
    (e : M.restrict U.ι ≅
      SheafOfModules.unit (↑U : Scheme).ringCatSheaf)
    (V : (Over U)ᵒᵖ)
    (x : (M.over U).val.obj V) :
    (chartOverIso U M e).hom.val.app V x =
      (X.presheaf.mapIso
          (eqToIso
            (overEquivalence_image_functor_obj U V.unop)).op).inv.hom
        ((U.ι.appIso
          ((TopologicalSpace.Opens.overEquivalence U).functor.obj
            V.unop)).inv.hom
          (e.hom.val.app
            (.op
              ((TopologicalSpace.Opens.overEquivalence U).functor.obj
                V.unop))
            ((M.restrictAppIso U.ι
                ((TopologicalSpace.Opens.overEquivalence U).functor.obj
                  V.unop)).inv.hom
              ((M.presheaf.mapIso
                (eqToIso
                  (overEquivalence_image_functor_obj U V.unop)).op).hom.hom
                x)))) := by
  unfold chartOverIso
  simp only [Iso.trans_hom]
  change
    (unitOverIso U).hom.val.app V
      (((overEquivalence U).functor.map e.hom).val.app V
        ((restrictOverIso U M).inv.val.app V x)) = _
  let W :=
    (TopologicalSpace.Opens.overEquivalence U).functor.obj V.unop
  let y : Γ(M.restrict U.ι, W) :=
    (M.restrictAppIso U.ι W).inv.hom
      ((M.presheaf.mapIso
        (eqToIso
          (overEquivalence_image_functor_obj U V.unop)).op).hom.hom x)
  have hrestrict :
      (restrictOverIso U M).inv.val.app V x = y :=
    restrictOverIso_inv_app U M V x
  have hmap :
      ((overEquivalence U).functor.map e.hom).val.app V y =
        e.hom.val.app (.op W) y :=
    overEquivalence_map_app U e.hom V y
  have hunit :=
    unitOverIso_hom_app U V (e.hom.val.app (.op W) y)
  exact
    (congrArg
      (fun z =>
        (unitOverIso U).hom.val.app V
          (((overEquivalence U).functor.map e.hom).val.app V z))
      hrestrict).trans <|
      (congrArg (fun z => (unitOverIso U).hom.val.app V z) hmap).trans <|
        hunit

/-- The open-slice equivalence carries finite or infinite free modules to
free modules on the same basis. -/
noncomputable def freeOverIso (I : Type u) :
    (overEquivalence U).functor.obj
        (SheafOfModules.free
          (R := (↑U : Scheme).ringCatSheaf) I) ≅
      SheafOfModules.free
        (R := X.ringCatSheaf.over U) I :=
  (SheafOfModules.mapFreeIso
    (overEquivalence U).functor I
    (unitOverIso U).symm).symm

/-- A free trivialization after restriction to an open subscheme induces
the corresponding free trivialization on its slice site. -/
noncomputable def chartFreeOverIso (M : X.Modules)
    (I : Type u)
    (e : M.restrict U.ι ≅
      SheafOfModules.free
        (R := (↑U : Scheme).ringCatSheaf) I) :
    M.over U ≅
      SheafOfModules.free
        (R := X.ringCatSheaf.over U) I :=
  (restrictOverIso U M).symm ≪≫
    (overEquivalence U).functor.mapIso e ≪≫
    freeOverIso U I

end AlgebraicGeometry.Scheme.Modules
