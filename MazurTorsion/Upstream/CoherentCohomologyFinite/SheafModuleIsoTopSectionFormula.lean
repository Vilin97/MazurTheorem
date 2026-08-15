/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoTopSectionTransport

/-!
# A concrete formula for top-section transport across a scheme isomorphism

The categorical transport from `SheafModuleIsoTopSectionTransport` agrees
with the direct identification of sections obtained from the fact that an
isomorphism maps the terminal open to the terminal open.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

namespace SheafOfModules

universe v v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- Evaluation of a composite morphism of sheaves of modules. -/
lemma comp_val_app_apply
    {P Q S : SheafOfModules.{v} R}
    (f : P ⟶ Q) (g : Q ⟶ S)
    (U : Cᵒᵖ) (x : P.val.obj U) :
    (f ≫ g).val.app U x =
      g.val.app U (f.val.app U x) := by
  rfl

/-- The elementary tail in the inverse restriction-composition comparison
acts as the identity on underlying sections. -/
lemma pushforwardComp_hom_comp_pushforwardCongr_inv_app_apply
    {D : Type u₁} [Category.{v₁} D]
    {D' : Type u₁} [Category.{v₁} D']
    {K : GrothendieckTopology D}
    {K' : GrothendieckTopology D'}
    {F : C ⥤ D} {G : D ⥤ D'}
    {S : Sheaf J RingCat.{u}}
    {T : Sheaf K RingCat.{u}}
    {T' : Sheaf K' RingCat.{u}}
    [F.IsContinuous J K]
    [G.IsContinuous K K']
    [(F ⋙ G).IsContinuous J K']
    (φ : S ⟶ (F.sheafPushforwardContinuous
      RingCat.{u} J K).obj T)
    (ψ : T ⟶ (G.sheafPushforwardContinuous
      RingCat.{u} K K').obj T')
    {θ : S ⟶ ((F ⋙ G).sheafPushforwardContinuous
      RingCat.{u} J K').obj T'}
    (h : θ =
      φ ≫ (F.sheafPushforwardContinuous
        RingCat.{u} J K).map ψ)
    (P : SheafOfModules.{v} T')
    (U : Cᵒᵖ)
    (x : (((pushforward ψ).obj P).val.obj
      ((F.op).obj U))) :
    (((pushforwardComp φ ψ).hom.app P ≫
      (pushforwardCongr h).inv.app P).val.app U) x = x := by
  change
    ((pushforwardCongr h).inv.app P).val.app U
      (((pushforwardComp φ ψ).hom.app P).val.app U x) = x
  rfl

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)

/-- An isomorphism of schemes maps the terminal open to the terminal open. -/
lemma iso_hom_image_top :
    e.hom ''ᵁ (⊤ : X.Opens) = (⊤ : Y.Opens) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  apply TopologicalSpace.Opens.ext
  ext y
  constructor
  · intro
    trivial
  · intro
    refine ⟨e.inv.base y, ?_⟩
    have h :=
      congrArg
        (fun f : Y ⟶ Y => f.base y)
        e.inv_hom_id
    simpa using h

/-- The inverse unit comparison along an isomorphism preserves `1`. -/
lemma restrictUnitIso_inv_app_one
    (V : Y.Opens) :
    (restrictUnitIso e.inv).inv.val.app (op V)
        (1 : Y.ringCatSheaf.obj.obj (op V)) =
      (show
        X.ringCatSheaf.obj.obj
          (op (e.inv ''ᵁ V))
        from 1) := by
  change
    (e.inv.appIso V).symm.commRingCatIsoToRingEquiv
        (1 : Y.ringCatSheaf.obj.obj (op V)) =
      (1 : X.ringCatSheaf.obj.obj
        (op (e.inv ''ᵁ V)))
  exact RingEquiv.map_one _

/-- Transport along an equality of opens is the corresponding presheaf
restriction map. -/
lemma eqToIso_sections_hom_eq_map
    {U V : Y.Opens} (h : U = V) :
    (eqToIso
      (congrArg (fun W => Γ(M, W)) h)).hom =
      M.presheaf.map (eqToHom h.symm).op := by
  subst h
  simp

/-- Direct transport of a terminal section along a scheme isomorphism. -/
def directIsoTransportedTopSection
    (x : Γ(M.restrict e.hom, ⊤)) :
    Γ(M, ⊤) :=
  (eqToIso
    (congrArg (fun U => Γ(M, U))
      (iso_hom_image_top e))).hom
    ((M.restrictAppIso e.hom ⊤).hom x)

/-- The categorical and direct transports of a terminal section agree. -/
theorem isoTransportedTopSection_eq_direct
    (x : Γ(M.restrict e.hom, ⊤)) :
    isoTransportedTopSection e M x =
      directIsoTransportedTopSection e M x := by
  let A := (restrictUnitIso e.inv).inv
  let B :=
    (restrictFunctor e.inv).map
      (MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom.homOfTopSection
        (M.restrict e.hom) x)
  let C :=
    (restrictFunctorComp e.inv e.hom).inv.app M
  let D :=
    (restrictFunctorCongr e.inv_hom_id).hom.app M
  let E := restrictFunctorId.hom.app M
  let U₁ : Y.Opens :=
    e.hom ''ᵁ (e.inv ''ᵁ (⊤ : Y.Opens))
  let U₂ : Y.Opens :=
    (e.inv ≫ e.hom) ''ᵁ (⊤ : Y.Opens)
  let U₃ : Y.Opens :=
    (𝟙 Y) ''ᵁ (⊤ : Y.Opens)
  have hU₁ : U₁ = ⊤ := by
    dsimp only [U₁]
    rw [← Scheme.Hom.comp_image]
    exact iso_hom_image_top (e.symm ≪≫ e)
  have hU₂ : U₂ = ⊤ := by
    dsimp only [U₂]
    exact iso_hom_image_top (e.symm ≪≫ e)
  have hU₃ : U₃ = ⊤ := by
    dsimp only [U₃]
    exact iso_hom_image_top (Iso.refl Y)
  let cMap :
      Γ(M, U₁) ⟶ Γ(M, U₂) :=
    M.presheaf.map
      (homOfLE (by rw [hU₁, hU₂])).op
  let dMap :
      Γ(M, U₂) ⟶ Γ(M, U₃) :=
    M.presheaf.map
      (homOfLE (by rw [hU₂, hU₃])).op
  let eMap :
      Γ(M, U₃) ⟶ Γ(M, ⊤) :=
    M.presheaf.map
      (homOfLE (by rw [hU₃])).op
  have hCmap : C.app ⊤ = cMap := by
    refine
      (restrictFunctorComp_inv_app_app
        e.inv e.hom M).trans ?_
    dsimp only [cMap]
    exact congrArg
      (fun q : U₂ ⟶ U₁ =>
        M.presheaf.map q.op)
      (Subsingleton.elim _ _)
  have hDmap : D.app ⊤ = dMap := by
    refine
      (restrictFunctorCongr_hom_app_app
        e.inv_hom_id M).trans ?_
    dsimp only [dMap]
    exact congrArg
      (fun q : U₃ ⟶ U₂ =>
        M.presheaf.map q.op)
      (Subsingleton.elim _ _)
  have hEmap : E.app ⊤ = eMap := by
    refine
      restrictFunctorId_hom_app_app.trans ?_
    dsimp only [eMap]
    exact congrArg
      (fun q : (⊤ : Y.Opens) ⟶ U₃ =>
        M.presheaf.map q.op)
      (Subsingleton.elim _ _)
  change
    E.val.app (op (⊤ : Y.Opens))
      (D.val.app (op (⊤ : Y.Opens))
        (C.val.app (op (⊤ : Y.Opens))
          (B.val.app (op (⊤ : Y.Opens))
            (A.val.app (op (⊤ : Y.Opens))
              (1 : Y.ringCatSheaf.obj.obj (op ⊤)))))) =
      directIsoTransportedTopSection e M x
  have hA :
      A.val.app (op (⊤ : Y.Opens))
          (1 : Y.ringCatSheaf.obj.obj (op ⊤)) =
        (show
          X.ringCatSheaf.obj.obj
            (op (e.inv ''ᵁ (⊤ : Y.Opens)))
          from 1) := by
    dsimp only [A]
    exact restrictUnitIso_inv_app_one e ⊤
  rw [hA]
  have hB :
      B.val.app (op (⊤ : Y.Opens))
          (show
            X.ringCatSheaf.obj.obj
              (op (e.inv ''ᵁ (⊤ : Y.Opens)))
            from 1) =
        (M.restrict e.hom).val.map
          (homOfLE
            (show
              e.inv ''ᵁ (⊤ : Y.Opens) ≤
                (⊤ : X.Opens)
              from le_top)).op x := by
    dsimp only [B]
    exact
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom.homOfTopSection_app_one
        (M.restrict e.hom) x
        (e.inv ''ᵁ (⊤ : Y.Opens))
  rw [hB]
  refine
    (congrArg
      (fun z =>
        E.val.app (op (⊤ : Y.Opens))
          (D.val.app (op (⊤ : Y.Opens))
            (C.val.app (op (⊤ : Y.Opens)) z)))
      (ConcreteCategory.congr_hom
        (restrict_map M e.hom
          (homOfLE
            (show
              e.inv ''ᵁ (⊤ : Y.Opens) ≤
                (⊤ : X.Opens)
              from le_top))) x)).trans ?_
  refine
    (congrArg
      (fun z =>
        E.val.app (op (⊤ : Y.Opens))
          (D.val.app (op (⊤ : Y.Opens)) z))
      (ConcreteCategory.congr_hom
        hCmap _)).trans ?_
  erw [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv]
  let z₀ : Γ(M, U₁) :=
    M.presheaf.map
      ((e.hom.opensFunctor).map
        (homOfLE
          (show
            e.inv ''ᵁ (⊤ : Y.Opens) ≤
              (⊤ : X.Opens)
            from le_top))).op x
  refine
    (congrArg
      (fun z =>
        E.val.app (op (⊤ : Y.Opens))
          (D.val.app (op (⊤ : Y.Opens))
            (cMap z)))
      (show _ = z₀ from ?_)).trans ?_
  dsimp only [z₀]
  exact
    SheafOfModules.pushforwardComp_hom_comp_pushforwardCongr_inv_app_apply
      _ _ _ M (op (⊤ : Y.Opens)) _
  refine
    (congrArg
      (fun z =>
        E.val.app (op (⊤ : Y.Opens)) z)
      (ConcreteCategory.congr_hom
        hDmap _)).trans ?_
  refine
    (ConcreteCategory.congr_hom
      hEmap _).trans ?_
  let V₀ : Y.Opens :=
    e.hom ''ᵁ (⊤ : X.Opens)
  let q₀ : op V₀ ⟶ op U₁ :=
    ((e.hom.opensFunctor).map
      (homOfLE
        (show
          e.inv ''ᵁ (⊤ : Y.Opens) ≤
            (⊤ : X.Opens)
          from le_top))).op
  let q₁ : op U₁ ⟶ op U₂ :=
    (homOfLE (by rw [hU₁, hU₂])).op
  let q₂ : op U₂ ⟶ op U₃ :=
    (homOfLE (by rw [hU₂, hU₃])).op
  let q₃ : op U₃ ⟶ op (⊤ : Y.Opens) :=
    (homOfLE (by rw [hU₃])).op
  let qDirect : op V₀ ⟶ op (⊤ : Y.Opens) :=
    (eqToHom (iso_hom_image_top e).symm).op
  have hz :
      z₀ = M.presheaf.map q₀ x := by
    rfl
  have hc :
      cMap = M.presheaf.map q₁ := by
    dsimp only [cMap, q₁]
  have hd :
      dMap = M.presheaf.map q₂ := by
    dsimp only [dMap, q₂]
  have he :
      eMap = M.presheaf.map q₃ := by
    dsimp only [eMap, q₃]
  rw [hz, hc, hd, he]
  simp only [directIsoTransportedTopSection]
  rw [eqToIso_sections_hom_eq_map M (iso_hom_image_top e)]
  change
    M.presheaf.map q₃
      (M.presheaf.map q₂
        (M.presheaf.map q₁
          (M.presheaf.map q₀ x))) =
      M.presheaf.map qDirect x
  have hmaps :
      ((M.presheaf.map q₀ ≫ M.presheaf.map q₁) ≫
          M.presheaf.map q₂) ≫ M.presheaf.map q₃ =
        M.presheaf.map qDirect := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun q => M.presheaf.map q)
      (Subsingleton.elim
        (((q₀ ≫ q₁) ≫ q₂) ≫ q₃)
        qDirect)
  exact ConcreteCategory.congr_hom hmaps x

end AlgebraicGeometry.Scheme.Modules
