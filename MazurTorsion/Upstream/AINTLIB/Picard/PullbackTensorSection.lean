/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.Picard.Pullback

/-!
# Pullback of pure tensor sections

This is an option-free selective port of the generic tensor-section kernel from
`projects/ModularCurves/ModularCurves/EllipticCurve/PoleSheaf.lean` and the canonical
pullback evaluator from
`projects/ModularCurves/ModularCurves/EllipticCurve/PullbackTensorSection.lean` at AINTLIB
commit `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.

Only the generic, option-free cone needed to evaluate the pullback cotensorator is retained.
The sheafification comparison and its coherence lemmas stay private, and its target is written
directly as a sheafification rather than reintroducing AINTLIB's broader
`Scheme.Modules.tensorObj` API.  The public surface consists of `tensorSection`, its functoriality
theorem `tensorSection_map`, and the named downstream consumer
`pullback_δ_unit_tensorSection`.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

noncomputable section

noncomputable local instance pullbackTensorSectionMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

noncomputable local instance pullbackTensorSectionSheafModulesMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory (SheafOfModules X.ringCatSheaf) := by
  change MonoidalCategory X.Modules
  exact Scheme.Modules.monoidalCategory X

private local instance pullbackTensorSectionPresheafMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules := by
  change MonoidalCategory
    (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

namespace ModularCurves

private abbrev pullbackTensorRingSheaf (X : Scheme.{u}) :=
  (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
    X.ringCatSheaf.property⟩ : Sheaf _ RingCat.{u})

private abbrev pullbackTensorSheafificationUnit (X : Scheme.{u}) :=
  𝟙 (pullbackTensorRingSheaf X).obj

private abbrev pullbackTensorSheafification (X : Scheme.{u}) :=
  PresheafOfModules.sheafification.{u} (pullbackTensorSheafificationUnit X)

private abbrev pullbackTensorSheafificationW (X : Scheme.{u}) :=
  PresheafOfModules.sheafificationW.{u} (pullbackTensorSheafificationUnit X)

private local instance pullbackTensorSheafificationLocalization (X : Scheme.{u}) :
    (pullbackTensorSheafification X).IsLocalization
      (pullbackTensorSheafificationW X) :=
  PresheafOfModules.sheafificationW_isLocalization (pullbackTensorRingSheaf X)

private local instance pullbackTensorSheafificationWMonoidal (X : Scheme.{u}) :
    (pullbackTensorSheafificationW X).IsMonoidal :=
  PresheafOfModules.sheafificationW_isMonoidal _

private local instance pullbackTensorLiteralSheafificationWMonoidal (X : Scheme.{u}) :
    (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (PresheafOfModules.sheafificationW
    (𝟙 (pullbackTensorRingSheaf X).obj)).IsMonoidal
  exact pullbackTensorSheafificationWMonoidal X

private local instance pullbackTensorSheafModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules (pullbackTensorRingSheaf X)) := by
  change MonoidalCategory X.Modules
  exact Scheme.Modules.monoidalCategory X

private abbrev pullbackTensorLocalizedSheafification (X : Scheme.{u}) :=
  Localization.Monoidal.toMonoidalCategory
    (L := pullbackTensorSheafification X)
    (W := pullbackTensorSheafificationW X) (Iso.refl _)

private local instance pullbackTensorLocalizedSheafificationMonoidal
    (X : Scheme.{u}) :
    (pullbackTensorLocalizedSheafification X).Monoidal :=
  inferInstance

private local instance pullbackTensorSheafificationMonoidal (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Monoidal :=
  inferInstanceAs ((pullbackTensorLocalizedSheafification X).Monoidal)

/-- The localized coherent tensor agrees with the sheafification of the underlying
presheaf tensor.  Kept private to avoid exposing a second tensor-object API. -/
private noncomputable def monoidalTensorObjIso {X : Scheme.{u}} (M N : X.Modules) :
    M ⊗ N ≅ (pullbackTensorSheafification X).obj (M.val ⊗ N.val) :=
  ((Scheme.Modules.sheafifyValIso M).symm ⊗ᵢ
      (Scheme.Modules.sheafifyValIso N).symm) ≪≫
    Localization.Monoidal.μ
      (pullbackTensorSheafification X)
      (pullbackTensorSheafificationW X)
      (Iso.refl _) M.val N.val

/-- The pure tensor of two sections over the same open, regarded as a section of the
localized tensor product of sheaves of modules. -/
noncomputable def tensorSection {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) : Γ(M ⊗ N, U) :=
  (monoidalTensorObjIso M N).inv.val.app (.op U)
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val)).app
        (.op U) (x ⊗ₜ y))

/-- The cotensorator of module sheafification is obtained by mapping the tensor of the
two sheafification units and then applying the canonical inverse tensor comparison. -/
private theorem sheafification_δ_eq_map_unit_tensor_comp_monoidalTensorObjIso_inv
    {X : Scheme.{u}} (A B : X.PresheafOfModules) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    Functor.OplaxMonoidal.δ L A B =
      L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
        (monoidalTensorObjIso (L.obj A) (L.obj B)).inv := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let cA := Scheme.Modules.sheafifyValIso (L.obj A)
  let cB := Scheme.Modules.sheafifyValIso (L.obj B)
  have hδ := Functor.OplaxMonoidal.δ_natural L
    (adj.unit.app A) (adj.unit.app B)
  change
    Functor.OplaxMonoidal.δ L A B ≫
        (L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B)) =
      L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
        Functor.OplaxMonoidal.δ L (L.obj A).val (L.obj B).val at hδ
  have hA : L.map (adj.unit.app A) ≫ cA.hom = 𝟙 (L.obj A) := by
    change L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A) = 𝟙 (L.obj A)
    exact adj.left_triangle_components A
  have hB : L.map (adj.unit.app B) ≫ cB.hom = 𝟙 (L.obj B) := by
    change L.map (adj.unit.app B) ≫ adj.counit.app (L.obj B) = 𝟙 (L.obj B)
    exact adj.left_triangle_components B
  have hmono :
      (monoidalTensorObjIso (L.obj A) (L.obj B)).inv =
        (Localization.Monoidal.μ L
          (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
          (Iso.refl _) (L.obj A).val (L.obj B).val).inv ≫
            (cA.hom ⊗ₘ cB.hom) :=
    rfl
  rw [hmono]
  change
    Functor.OplaxMonoidal.δ L A B =
      L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
        Functor.OplaxMonoidal.δ L (L.obj A).val (L.obj B).val ≫
          (cA.hom ⊗ₘ cB.hom)
  have hcancel :
      (L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B)) ≫
          (cA.hom ⊗ₘ cB.hom) = 𝟙 (L.obj A ⊗ L.obj B) := by
    calc
      _ = (L.map (adj.unit.app A) ≫ cA.hom) ⊗ₘ
          (L.map (adj.unit.app B) ≫ cB.hom) :=
        tensorHom_comp_tensorHom _ _ _ _
      _ = (𝟙 _) ⊗ₘ (𝟙 _) := congrArg₂ (· ⊗ₘ ·) hA hB
      _ = 𝟙 _ := by
        simpa only [Functor.id_obj] using id_tensorHom_id (L.obj A) (L.obj B)
  calc
    _ = Functor.OplaxMonoidal.δ L A B ≫ 𝟙 _ :=
      (Category.comp_id _).symm
    _ = Functor.OplaxMonoidal.δ L A B ≫
        ((L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B)) ≫
          (cA.hom ⊗ₘ cB.hom)) :=
      congrArg (Functor.OplaxMonoidal.δ L A B ≫ ·) hcancel.symm
    _ = (Functor.OplaxMonoidal.δ L A B ≫
          (L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B))) ≫
            (cA.hom ⊗ₘ cB.hom) :=
      Category.assoc _ _ _
    _ = (L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
          Functor.OplaxMonoidal.δ L (L.obj A).val (L.obj B).val) ≫
            (cA.hom ⊗ₘ cB.hom) :=
      congrArg (· ≫ (cA.hom ⊗ₘ cB.hom)) hδ
    _ = _ := (Category.assoc _ _ _).symm

/-- Applying the sheafification cotensorator to the unit image of a pure tensor gives
the canonical pure tensor section of the two unit images. -/
private theorem sheafification_δ_unit_tmul_eq_tensorSection
    {X : Scheme.{u}} (A B : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (.op U)) (y : B.obj (.op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (Functor.OplaxMonoidal.δ L A B).val.app (.op U)
        ((adj.unit.app (A ⊗ B)).app (.op U) (x ⊗ₜ y)) =
      tensorSection (L.obj A) (L.obj B) U
        ((adj.unit.app A).app (.op U) x)
        ((adj.unit.app B).app (.op U) y) := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let f := adj.unit.app A ⊗ₘ adj.unit.app B
  have hδ :=
    sheafification_δ_eq_map_unit_tensor_comp_monoidalTensorObjIso_inv A B
  have hδapp := congrArg
    (fun q => q.val.app (.op U)
      ((adj.unit.app (A ⊗ B)).app (.op U) (x ⊗ₜ y))) hδ
  conv_rhs at hδapp =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  have hnat := adj.unit.naturality f
  have hnatapp := congrArg (fun q => q.app (.op U) (x ⊗ₜ y)) hnat
  conv_lhs at hnatapp =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hnatapp =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  let S := X.sheaf.obj.obj (.op U)
  let AA : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact A.obj (.op U)
  let BB : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact B.obj (.op U)
  let LA : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact (L.obj A).val.obj (.op U)
  let LB : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact (L.obj B).val.obj (.op U)
  let uA : AA ⟶ LA := by
    change A.obj (.op U) ⟶ (L.obj A).val.obj (.op U)
    exact (adj.unit.app A).app (.op U)
  let uB : BB ⟶ LB := by
    change B.obj (.op U) ⟶ (L.obj B).val.obj (.op U)
    exact (adj.unit.app B).app (.op U)
  let xx : AA := x
  let yy : BB := y
  let x' : LA := uA xx
  let y' : LB := uB yy
  let t' : TensorProduct S LA LB := x' ⊗ₜ[S] y'
  have htmul : f.app (.op U) (x ⊗ₜ y) =
      (show ((L.obj A).val ⊗ (L.obj B).val).obj (.op U) from t') :=
    ModuleCat.MonoidalCategory.tensorHom_tmul uA uB xx yy
  change
    (adj.unit.app ((L.obj A).val ⊗ (L.obj B).val)).app (.op U)
        (f.app (.op U) (x ⊗ₜ y)) =
      (L.map f).val.app (.op U)
        ((adj.unit.app (A ⊗ B)).app (.op U) (x ⊗ₜ y)) at hnatapp
  unfold tensorSection
  exact hδapp.trans (congrArg
    (fun z => (monoidalTensorObjIso (L.obj A) (L.obj B)).inv.val.app (.op U) z)
    (hnatapp.symm.trans (congrArg
      (fun z => (adj.unit.app ((L.obj A).val ⊗ (L.obj B).val)).app (.op U) z)
      htmul)))

private theorem monoidalTensorObjIso_inv_natural
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val) ≫
        (monoidalTensorObjIso M' N').inv =
      (monoidalTensorObjIso M N).inv ≫ (f ⊗ₘ g) := by
  letI : (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  letI : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let sh (A : X.PresheafOfModules) : X.Modules := L.obj A
  let δ (A B : X.PresheafOfModules) : sh (A ⊗ B) ⟶ sh A ⊗ sh B :=
    Functor.OplaxMonoidal.δ F A B
  let ε (A : X.Modules) : sh A.val ⟶ A :=
    (Scheme.Modules.sheafifyValIso A).hom
  have hIso (A B : X.Modules) :
      (monoidalTensorObjIso A B).inv =
        δ A.val B.val ≫ (ε A ⊗ₘ ε B) := by
    rfl
  have hδ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
        δ M.val N.val ≫ (L.map f.val ⊗ₘ L.map g.val) :=
    (Functor.OplaxMonoidal.δ_natural F f.val g.val).symm
  have hεf : L.map f.val ≫ ε M' = ε M ≫ f :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality f
  have hεg : L.map g.val ≫ ε N' = ε N ≫ g :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality g
  let e' : (sh M'.val ⊗ sh N'.val) ⟶ (M' ⊗ N') :=
    ε M' ⊗ₘ ε N'
  let e₀ : (sh M.val ⊗ sh N.val) ⟶ (M ⊗ N) :=
    ε M ⊗ₘ ε N
  let lfg : (sh M.val ⊗ sh N.val) ⟶ (sh M'.val ⊗ sh N'.val) :=
    L.map f.val ⊗ₘ L.map g.val
  let fg : (M ⊗ N) ⟶ (M' ⊗ N') := f ⊗ₘ g
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
    δ M.val N.val ≫ lfg at hδ
  have hTensorComp : lfg ≫ e' = e₀ ≫ fg := by
    let c₁ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (L.map f.val ≫ ε M') ⊗ₘ (L.map g.val ≫ ε N')
    let c₀ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (ε M ≫ f) ⊗ₘ (ε N ≫ g)
    have hleft : lfg ≫ e' = c₁ := by
      dsimp only [lfg, e', c₁]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    have hmiddle : c₁ = c₀ := by
      dsimp only [c₁, c₀]
      exact congrArg₂
        (fun (a : sh M.val ⟶ M') (b : sh N.val ⟶ N') ↦ a ⊗ₘ b)
        hεf hεg
    have hright : e₀ ≫ fg = c₀ := by
      dsimp only [e₀, fg, c₀]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    exact hleft.trans (hmiddle.trans hright.symm)
  rw [hIso M' N', hIso M N]
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
    δ M.val N.val ≫ e₀ ≫ fg
  have h₁ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
        (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' :=
    (Category.assoc _ _ _).symm
  have h₂ :
      (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' =
        (δ M.val N.val ≫ lfg) ≫ e' :=
    congrArg (fun k ↦ k ≫ e') hδ
  have h₃ :
      (δ M.val N.val ≫ lfg) ≫ e' =
        δ M.val N.val ≫ (lfg ≫ e') :=
    Category.assoc _ _ _
  have h₄ :
      δ M.val N.val ≫ (lfg ≫ e') =
        δ M.val N.val ≫ (e₀ ≫ fg) :=
    congrArg (fun k ↦ δ M.val N.val ≫ k) hTensorComp
  have h₅ :
      δ M.val N.val ≫ (e₀ ≫ fg) =
        δ M.val N.val ≫ e₀ ≫ fg :=
    (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Forming a pure tensor section commutes with morphisms in both module factors. -/
theorem tensorSection_map
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    (f ⊗ₘ g).val.app (.op U) (tensorSection M N U x y) =
      tensorSection M' N' U
        (f.val.app (.op U) x) (g.val.app (.op U) y) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let t : (M.val ⊗ N.val).obj (.op U) := x ⊗ₜ y
  let t' : (M'.val ⊗ N'.val).obj (.op U) :=
    f.val.app (.op U) x ⊗ₜ g.val.app (.op U) y
  let q := adj.unit.app (M.val ⊗ N.val)
  let q' := adj.unit.app (M'.val ⊗ N'.val)
  let a := q.app (.op U) t
  let a' := q'.app (.op U) t'
  have ht : (f.val ⊗ₘ g.val).app (.op U) t = t' := by
    rfl
  have hunit := adj.unit_naturality (f.val ⊗ₘ g.val)
  change adj.unit.app (M.val ⊗ N.val) ≫
      (L.map (f.val ⊗ₘ g.val)).val =
    (f.val ⊗ₘ g.val) ≫ adj.unit.app (M'.val ⊗ N'.val) at hunit
  have hunitU := congrArg (fun k ↦ k.app (.op U)) hunit
  have hunitApply := ConcreteCategory.congr_hom hunitU t
  conv_lhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hLa : (L.map (f.val ⊗ₘ g.val)).val.app (.op U) a = a' := by
    dsimp only [a, a', q, q']
    have hright := congrArg
      (fun b ↦ (adj.unit.app (M'.val ⊗ N'.val)).app (.op U) b) ht
    exact hunitApply.trans hright
  have hk := monoidalTensorObjIso_inv_natural f g
  have hkU := congrArg (fun k ↦ k.val.app (.op U)) hk
  have hkApply := ConcreteCategory.congr_hom hkU a
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hkApply
  change (f ⊗ₘ g).val.app (.op U)
      ((monoidalTensorObjIso M N).inv.val.app (.op U) a) =
    (monoidalTensorObjIso M' N').inv.val.app (.op U) a'
  exact hkApply.symm.trans
    (congrArg
      (fun b ↦ (monoidalTensorObjIso M' N').inv.val.app (.op U) b) hLa)

private abbrev pullbackTensorPresheafPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  PresheafOfModules.pullback.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private abbrev pullbackTensorSheafHom
    {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  (⟨_root_.PresheafOfModules.schemeRingPresheafHom f⟩ :
    pullbackTensorRingSheaf X ⟶
      ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
        RingCat.{u} _ _).obj (pullbackTensorRingSheaf Y))

private abbrev pullbackTensorSheafPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  SheafOfModules.pullback.{u} (pullbackTensorSheafHom f)

@[implicit_reducible]
private noncomputable def pullbackTensorSheafPullbackLifting
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Localization.Lifting (pullbackTensorLocalizedSheafification X)
      (pullbackTensorSheafificationW X)
      (pullbackTensorPresheafPullback f ⋙
        pullbackTensorLocalizedSheafification Y)
      (pullbackTensorSheafPullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback (pullbackTensorSheafHom f)⟩

private theorem pullback_μ_formula
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    let G := pullbackTensorPresheafPullback f ⋙
      pullbackTensorLocalizedSheafification Y
    letI : (pullbackTensorPresheafPullback f).Monoidal :=
      _root_.PresheafOfModules.pullbackMonoidal f
    letI : G.Monoidal := inferInstance
    let e := SheafOfModules.sheafificationCompPullback
      (pullbackTensorSheafHom f)
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) M N =
      (((Scheme.Modules.pullback f).map
          (Scheme.Modules.sheafifyValIso M).inv ≫ e.hom.app M.val) ⊗ₘ
        ((Scheme.Modules.pullback f).map
          (Scheme.Modules.sheafifyValIso N).inv ≫ e.hom.app N.val)) ≫
        Functor.LaxMonoidal.μ G M.val N.val ≫
        e.inv.app (M.val ⊗ N.val) ≫
        (Scheme.Modules.pullback f).map (monoidalTensorObjIso M N).inv := by
  dsimp only
  let L := pullbackTensorLocalizedSheafification X
  let W := pullbackTensorSheafificationW X
  let F := pullbackTensorSheafPullback f
  let G := pullbackTensorPresheafPullback f ⋙
    pullbackTensorLocalizedSheafification Y
  letI lX : (pullbackTensorLocalizedSheafification X).Monoidal := inferInstance
  letI lY : (pullbackTensorLocalizedSheafification Y).Monoidal := inferInstance
  letI pF : (pullbackTensorPresheafPullback f).Monoidal :=
    _root_.PresheafOfModules.pullbackMonoidal f
  letI pgF : G.Monoidal := inferInstance
  letI liftF : Localization.Lifting L W G F :=
    pullbackTensorSheafPullbackLifting f
  letI fM : F.Monoidal :=
    @Localization.Monoidal.functorMonoidalOfComp
      _ _ _ _ _ _ _ _ _ L W _ lX F G pgF _ liftF
  let eM := (Scheme.Modules.sheafifyValIso M).symm
  let eN := (Scheme.Modules.sheafifyValIso N).symm
  have h := @Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
    _ _ _ _ _ _ _ _ _ L W _ lX F G pgF _ liftF _ _ _ _ eM eN
  exact h

private theorem pullback_factor_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) :
    let PB := pullbackTensorPresheafPullback f
    let shAdjY := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    let e := SheafOfModules.sheafificationCompPullback
      (pullbackTensorSheafHom f)
    ((((Scheme.Modules.pullback f).map
        (Scheme.Modules.sheafifyValIso M).inv ≫ e.hom.app M.val).val.app
          (.op (f ⁻¹ᵁ U)))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
        (.op U) x)) =
      (shAdjY.unit.app (PB.obj M.val)).app (.op (f ⁻¹ᵁ U))
        ((preAdj.unit.app M.val).app (.op U) x) := by
  dsimp only
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let pbAdj := Scheme.Modules.pullbackPushforwardAdjunction f
  let c := Scheme.Modules.sheafifyValIso M
  let e := SheafOfModules.sheafificationCompPullback
    (pullbackTensorSheafHom f)
  have hnat := pbAdj.unit.naturality c.inv
  have happ := congrArg (fun q => q.val.app (.op U) x) hnat
  conv_lhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    ((pbAdj.unit.app (LX.obj M.val)).val.app (.op U))
        (c.inv.val.app (.op U) x) =
      (((Scheme.Modules.pullback f).map c.inv).val.app
        (.op (f ⁻¹ᵁ U)))
          ((pbAdj.unit.app M).val.app (.op U) x) at happ
  have hc := Scheme.Modules.sheafifyValIso_inv_app_apply M U x
  have he := Scheme.Modules.sheafificationCompPullback_hom_unit_app_apply
    f M.val U x
  conv_lhs =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  rw [← happ, hc]
  exact he

private theorem composite_pullback_μ_tensorSection
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P Q : X.PresheafOfModules) (U : X.Opens)
    (x : P.obj (.op U)) (y : Q.obj (.op U)) :
    let PB := pullbackTensorPresheafPullback f
    let LY := pullbackTensorLocalizedSheafification Y
    let G := PB ⋙ LY
    let shAdjY := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    letI : PB.Monoidal := _root_.PresheafOfModules.pullbackMonoidal f
    letI : G.Monoidal := inferInstance
    (Functor.LaxMonoidal.μ G P Q).val.app (.op (f ⁻¹ᵁ U))
        (tensorSection (G.obj P) (G.obj Q) (f ⁻¹ᵁ U)
          ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app P).app (.op U) x))
          ((shAdjY.unit.app (PB.obj Q)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app Q).app (.op U) y))) =
      (shAdjY.unit.app (PB.obj (P ⊗ Q))).app (.op (f ⁻¹ᵁ U))
        ((preAdj.unit.app (P ⊗ Q)).app (.op U) (x ⊗ₜ y)) := by
  dsimp only
  let PB := pullbackTensorPresheafPullback f
  let LY := pullbackTensorLocalizedSheafification Y
  let G := PB ⋙ LY
  let shAdjY := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
  letI pF : PB.Monoidal := _root_.PresheafOfModules.pullbackMonoidal f
  letI gF : G.Monoidal := inferInstance
  let r := (shAdjY.unit.app (PB.obj (P ⊗ Q))).app
    (.op (f ⁻¹ᵁ U))
      ((preAdj.unit.app (P ⊗ Q)).app (.op U) (x ⊗ₜ y))
  have hmap := PresheafOfModules.sheafification_map_pullback_δ_unit_tmul
    (φ := _root_.PresheafOfModules.schemeRingPresheafHom f)
    Y.ringCatSheaf.property P Q (.op U) x y
  have hsh := sheafification_δ_unit_tmul_eq_tensorSection
    (X := Y) (PB.obj P) (PB.obj Q) (f ⁻¹ᵁ U)
      ((preAdj.unit.app P).app (.op U) x)
      ((preAdj.unit.app Q).app (.op U) y)
  dsimp only at hmap hsh
  change
    (LY.map (Functor.OplaxMonoidal.δ PB P Q)).val.app
        (.op (f ⁻¹ᵁ U)) r =
      (shAdjY.unit.app (PB.obj P ⊗ PB.obj Q)).app
        (.op (f ⁻¹ᵁ U))
          (((preAdj.unit.app P).app (.op U) x) ⊗ₜ
            ((preAdj.unit.app Q).app (.op U) y)) at hmap
  change
    (Functor.OplaxMonoidal.δ LY (PB.obj P) (PB.obj Q)).val.app
        (.op (f ⁻¹ᵁ U))
          ((shAdjY.unit.app (PB.obj P ⊗ PB.obj Q)).app
            (.op (f ⁻¹ᵁ U))
              (((preAdj.unit.app P).app (.op U) x) ⊗ₜ
                ((preAdj.unit.app Q).app (.op U) y))) =
      tensorSection (G.obj P) (G.obj Q) (f ⁻¹ᵁ U)
        ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
          ((preAdj.unit.app P).app (.op U) x))
        ((shAdjY.unit.app (PB.obj Q)).app (.op (f ⁻¹ᵁ U))
          ((preAdj.unit.app Q).app (.op U) y)) at hsh
  have hdelta :
      (Functor.OplaxMonoidal.δ G P Q).val.app (.op (f ⁻¹ᵁ U)) r =
        tensorSection (G.obj P) (G.obj Q) (f ⁻¹ᵁ U)
          ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app P).app (.op U) x))
          ((shAdjY.unit.app (PB.obj Q)).app (.op (f ⁻¹ᵁ U))
            ((preAdj.unit.app Q).app (.op U) y)) := by
    change
      ((LY.map (Functor.OplaxMonoidal.δ PB P Q) ≫
          Functor.OplaxMonoidal.δ LY (PB.obj P) (PB.obj Q)).val.app
        (.op (f ⁻¹ᵁ U))) r = _
    conv_lhs =>
      erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
    rw [hmap, hsh]
  have hinv := Functor.Monoidal.δ_μ G P Q
  have hinvApply := congrArg (fun q => q.val.app (.op (f ⁻¹ᵁ U)) r) hinv
  conv_lhs at hinvApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    (Functor.LaxMonoidal.μ G P Q).val.app (.op (f ⁻¹ᵁ U))
        ((Functor.OplaxMonoidal.δ G P Q).val.app
          (.op (f ⁻¹ᵁ U)) r) = r at hinvApply
  rw [hdelta] at hinvApply
  exact hinvApply

private theorem sheafificationCompPullback_inv_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) (P : X.PresheafOfModules)
    (U : X.Opens) (x : P.obj (.op U)) :
    let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let PB := pullbackTensorPresheafPullback f
    let shAdjX := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let shAdjY := PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
    let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
      (_root_.PresheafOfModules.schemeRingPresheafHom f)
    let e := SheafOfModules.sheafificationCompPullback
      (pullbackTensorSheafHom f)
    (e.inv.app P).val.app (.op (f ⁻¹ᵁ U))
        ((shAdjY.unit.app (PB.obj P)).app (.op (f ⁻¹ᵁ U))
          ((preAdj.unit.app P).app (.op U) x)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (LX.obj P)).val.app (.op U))
          ((shAdjX.unit.app P).app (.op U) x) := by
  dsimp only
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let pbAdj := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := SheafOfModules.sheafificationCompPullback
    (pullbackTensorSheafHom f)
  let a := ((pbAdj.unit.app (LX.obj P)).val.app (.op U))
    ((shAdjX.unit.app P).app (.op U) x)
  have he := Scheme.Modules.sheafificationCompPullback_hom_unit_app_apply
    f P U x
  have heInv := congrArg
    (fun z => (e.inv.app P).val.app (.op (f ⁻¹ᵁ U)) z) he
  have hcancel := congrArg (fun q => q.val.app (.op (f ⁻¹ᵁ U)) a)
    (e.app P).hom_inv_id
  conv_lhs at hcancel =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  exact heInv.symm.trans hcancel

private theorem pullback_monoidalTensorObjIso_inv_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) (y : N.val.obj (.op U)) :
    let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let shAdjX := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let h := (monoidalTensorObjIso M N).inv
    (((Scheme.Modules.pullback f).map h).val.app (.op (f ⁻¹ᵁ U)))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (LX.obj (M.val ⊗ N.val))).val.app (.op U))
            ((shAdjX.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) := by
  dsimp only
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let pbAdj := Scheme.Modules.pullbackPushforwardAdjunction f
  let h := (monoidalTensorObjIso M N).inv
  let t := (shAdjX.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y)
  have hnat := pbAdj.unit.naturality h
  have happ := congrArg (fun q => q.val.app (.op U) t) hnat
  conv_lhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at happ =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    ((pbAdj.unit.app (M ⊗ N)).val.app (.op U))
        (h.val.app (.op U) t) =
      (((Scheme.Modules.pullback f).map h).val.app (.op (f ⁻¹ᵁ U)))
        (((pbAdj.unit.app (LX.obj (M.val ⊗ N.val))).val.app (.op U)) t) at happ
  exact happ.symm

private theorem pullback_μ_unit_tensorSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) (y : N.val.obj (.op U)) :
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    (Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) M N).val.app
        (.op (f ⁻¹ᵁ U))
        (tensorSection
          ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
            (.op U) x)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
            (.op U) y)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) := by
  dsimp only
  let PB := Scheme.Modules.pullback f
  let prePB := pullbackTensorPresheafPullback f
  let LY := pullbackTensorLocalizedSheafification Y
  let G := prePB ⋙ LY
  let e := SheafOfModules.sheafificationCompPullback
    (pullbackTensorSheafHom f)
  let cM := Scheme.Modules.sheafifyValIso M
  let cN := Scheme.Modules.sheafifyValIso N
  let aM := PB.map cM.inv ≫ e.hom.app M.val
  let aN := PB.map cN.inv ≫ e.hom.app N.val
  let h := (monoidalTensorObjIso M N).inv
  let uM := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op U) x
  let uN := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
    (.op U) y
  let t := tensorSection (PB.obj M) (PB.obj N) (f ⁻¹ᵁ U) uM uN
  let shAdjY := PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let preAdj := PresheafOfModules.pullbackPushforwardAdjunction
    (_root_.PresheafOfModules.schemeRingPresheafHom f)
  let vM := (shAdjY.unit.app (prePB.obj M.val)).app (.op (f ⁻¹ᵁ U))
    ((preAdj.unit.app M.val).app (.op U) x)
  let vN := (shAdjY.unit.app (prePB.obj N.val)).app (.op (f ⁻¹ᵁ U))
    ((preAdj.unit.app N.val).app (.op U) y)
  let raw := (shAdjY.unit.app (prePB.obj (M.val ⊗ N.val))).app
    (.op (f ⁻¹ᵁ U))
      ((preAdj.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y))
  let LX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let shAdjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let source := (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
    (LX.obj (M.val ⊗ N.val))).val.app (.op U))
      ((shAdjX.unit.app (M.val ⊗ N.val)).app (.op U) (x ⊗ₜ y))
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  letI prePBMonoidal : prePB.Monoidal :=
    _root_.PresheafOfModules.pullbackMonoidal f
  letI gMonoidal : G.Monoidal := inferInstance
  have hformula := pullback_μ_formula f M N
  dsimp only at hformula
  have hformulaApply := congrArg
    (fun q => q.val.app (.op (f ⁻¹ᵁ U)) t) hformula
  change
    (Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t =
      (PB.map h).val.app (.op (f ⁻¹ᵁ U))
        ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
          ((Functor.LaxMonoidal.μ G M.val N.val).val.app
            (.op (f ⁻¹ᵁ U))
              ((aM ⊗ₘ aN).val.app (.op (f ⁻¹ᵁ U)) t))) at hformulaApply
  have hmap := tensorSection_map aM aN (f ⁻¹ᵁ U) uM uN
  have hfactorM := pullback_factor_unit f M U x
  have hfactorN := pullback_factor_unit f N U y
  have hmiddle := composite_pullback_μ_tensorSection
    f M.val N.val U x y
  have heInv := sheafificationCompPullback_inv_unit
    f (M.val ⊗ N.val) U (x ⊗ₜ y)
  have hfinal := pullback_monoidalTensorObjIso_inv_unit
    f M N U x y
  dsimp only at hfactorM hfactorN hmiddle heInv hfinal
  change aM.val.app (.op (f ⁻¹ᵁ U)) uM = vM at hfactorM
  change aN.val.app (.op (f ⁻¹ᵁ U)) uN = vN at hfactorN
  change
    (Functor.LaxMonoidal.μ G M.val N.val).val.app (.op (f ⁻¹ᵁ U))
        (tensorSection (G.obj M.val) (G.obj N.val) (f ⁻¹ᵁ U) vM vN) =
      raw at hmiddle
  change (e.inv.app (M.val ⊗ N.val)).val.app
    (.op (f ⁻¹ᵁ U)) raw = source at heInv
  change (PB.map h).val.app (.op (f ⁻¹ᵁ U)) source =
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) at hfinal
  have hchain :
      (Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t =
        (PB.map h).val.app (.op (f ⁻¹ᵁ U)) source := by
    calc
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            ((Functor.LaxMonoidal.μ G M.val N.val).val.app
              (.op (f ⁻¹ᵁ U))
                ((aM ⊗ₘ aN).val.app (.op (f ⁻¹ᵁ U)) t))) :=
        hformulaApply
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            ((Functor.LaxMonoidal.μ G M.val N.val).val.app
              (.op (f ⁻¹ᵁ U))
                (tensorSection (G.obj M.val) (G.obj N.val) (f ⁻¹ᵁ U)
                  (aM.val.app (.op (f ⁻¹ᵁ U)) uM)
                  (aN.val.app (.op (f ⁻¹ᵁ U)) uN)))) :=
        congrArg
          (fun z => (PB.map h).val.app (.op (f ⁻¹ᵁ U))
            ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
              ((Functor.LaxMonoidal.μ G M.val N.val).val.app
                (.op (f ⁻¹ᵁ U)) z))) hmap
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            ((Functor.LaxMonoidal.μ G M.val N.val).val.app
              (.op (f ⁻¹ᵁ U))
                (tensorSection (G.obj M.val) (G.obj N.val) (f ⁻¹ᵁ U)
                  vM vN))) := by
        rw [hfactorM, hfactorN]
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U))
          ((e.inv.app (M.val ⊗ N.val)).val.app (.op (f ⁻¹ᵁ U))
            raw) :=
        congrArg
          (fun z => (PB.map h).val.app (.op (f ⁻¹ᵁ U))
            ((e.inv.app (M.val ⊗ N.val)).val.app
              (.op (f ⁻¹ᵁ U)) z)) hmiddle
      _ = (PB.map h).val.app (.op (f ⁻¹ᵁ U)) source :=
        congrArg (fun z => (PB.map h).val.app (.op (f ⁻¹ᵁ U)) z) heInv
  exact hchain.trans hfinal

/-- The canonical pullback cotensorator sends the pullback-unit image of a pure
tensor section to the pure tensor of the two pullback-unit sections. -/
theorem pullback_δ_unit_tensorSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N).val.app
        (.op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (M ⊗ N)).val.app (.op U) (tensorSection M N U x y)) =
      tensorSection
        ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
          (.op U) x)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
          (.op U) y) := by
  dsimp only
  let PB := Scheme.Modules.pullback f
  let uM := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op U) x
  let uN := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
    (.op U) y
  let t := tensorSection (PB.obj M) (PB.obj N) (f ⁻¹ᵁ U) uM uN
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  have hμ := pullback_μ_unit_tensorSection f M N U x y
  dsimp only at hμ
  change
    (Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (M ⊗ N)).val.app (.op U)) (tensorSection M N U x y) at hμ
  have hinv := Functor.Monoidal.μ_δ PB M N
  have hinvApply := congrArg (fun q => q.val.app (.op (f ⁻¹ᵁ U)) t) hinv
  conv_lhs at hinvApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    (Functor.OplaxMonoidal.δ PB M N).val.app (.op (f ⁻¹ᵁ U))
        ((Functor.LaxMonoidal.μ PB M N).val.app (.op (f ⁻¹ᵁ U)) t) = t at hinvApply
  rw [hμ] at hinvApply
  exact hinvApply

end ModularCurves
