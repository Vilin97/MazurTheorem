/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleDescent
import MazurTorsion.Upstream.AINTLIB.ForMathlib.PullbackCompMonoidal

/-!
# Tensor products of canonical module descent data

Canonical descent of a tensor product is transported to the chartwise tensor of the two
canonical descent data, and its chosen-overlap transition is computed from the two factor
transitions and the pullback tensorators.  The file also supplies the full/chosen descent
comparison and a factorwise tensor-square lemma.

This is the generic tensor-descent boundary.  It does not mention divisors or effectivity; its
named downstream consumer is `CurveDivisorGlobalTensorAdd`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open _root_.AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

section

universe u

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

@[reducible]
noncomputable local instance schemeModulesMonoidalForGlobalTensorAdd
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

@[reducible]
noncomputable local instance pullbackMonoidalForGlobalTensorAdd
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f

private noncomputable abbrev moduleFiber (Y : Scheme.{u}) :=
  MazurTorsion.AlgebraicGeometry.LineBundleDescent.modulesPseudofunctor.obj
    (.mk (.op Y))

private noncomputable abbrev modulePullback {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (MazurTorsion.AlgebraicGeometry.LineBundleDescent.modulesPseudofunctor.map
    g.op.toLoc).toFunctor

@[reducible]
noncomputable local instance (priority := 100) moduleFiberMonoidalForGlobalTensorAdd
    (Y : Scheme.{u}) : MonoidalCategory (moduleFiber Y) :=
  Scheme.Modules.monoidalCategory Y

@[reducible]
noncomputable local instance (priority := 100) modulePullbackMonoidalForGlobalTensorAdd
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (modulePullback g).Monoidal :=
  Scheme.Modules.pullbackMonoidal g

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

private theorem modulesPseudofunctor_mapComp'_inv_app
    {X Y Z : Scheme.{u}} (b : X ⟶ Y) (a : Y ⟶ Z)
    (c : X ⟶ Z) (h : b ≫ a = c) (M : Z.Modules) :
    (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc c.op.toLoc (by cases h; rfl)).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp b a).hom.app M ≫
        (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst c
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom]
  change (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc (a.op.toLoc ≫ b.op.toLoc) _).inv.toNatTrans.app M = _
  calc
    _ = (modulesPseudofunctor.mapComp a.op.toLoc b.op.toLoc).inv.toNatTrans.app M := by
      simpa only [] using congrArg (fun e ↦ e.inv.toNatTrans.app M)
        (modulesPseudofunctor.mapComp'_eq_mapComp a.op.toLoc b.op.toLoc)
    _ = _ := by
      unfold modulesPseudofunctor
      rw [Pseudofunctor.comp_mapComp]
      dsimp
      exact congrArg (fun k ↦ k.toNatTrans.app M)
        (Scheme.Modules.pseudofunctor_mapComp_inv_τl a.op.toLoc b.op.toLoc)

private theorem modulesPseudofunctor_mapComp'_hom_app
    {X Y Z : Scheme.{u}} (b : X ⟶ Y) (a : Y ⟶ Z)
    (c : X ⟶ Z) (h : b ≫ a = c) (M : Z.Modules) :
    (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc c.op.toLoc (by cases h; rfl)).hom.toNatTrans.app M =
      (Scheme.Modules.pullbackCongr h).inv.app M ≫
        (Scheme.Modules.pullbackComp b a).inv.app M := by
  subst c
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv]
  change (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc (a.op.toLoc ≫ b.op.toLoc) _).hom.toNatTrans.app M = _
  calc
    _ = (modulesPseudofunctor.mapComp a.op.toLoc b.op.toLoc).hom.toNatTrans.app M := by
      simpa only [] using congrArg (fun e ↦ e.hom.toNatTrans.app M)
        (modulesPseudofunctor.mapComp'_eq_mapComp a.op.toLoc b.op.toLoc)
    _ = _ := by
      unfold modulesPseudofunctor
      rw [Pseudofunctor.comp_mapComp]
      dsimp
      exact congrArg (fun k ↦ k.toNatTrans.app M)
        (Scheme.Modules.pseudofunctor_mapComp_hom_τl a.op.toLoc b.op.toLoc)

private theorem pullbackCompCongr_hom_isMonoidal
    {X Y Z : Scheme.{u}} (b : X ⟶ Y) (a : Y ⟶ Z)
    (c : X ⟶ Z) (h : b ≫ a = c) :
    ((Scheme.Modules.pullbackComp b a ≪≫
      Scheme.Modules.pullbackCongr h).hom).IsMonoidal := by
  subst c
  dsimp [Scheme.Modules.pullbackCongr]
  letI hc : (Scheme.Modules.pullbackComp b a).hom.IsMonoidal :=
    Scheme.Modules.pullbackComp_hom_isMonoidal b a
  letI hr : NatTrans.IsMonoidal
      (Iso.refl (Scheme.Modules.pullback (b ≫ a))).hom := by
    change NatTrans.IsMonoidal (𝟙 (Scheme.Modules.pullback (b ≫ a)))
    infer_instance
  exact NatTrans.IsMonoidal.comp _ _

private theorem toDescentData_hom_eq_pullbackComp
    {X : Scheme.{u}} (cov : X.OpenCover) (M : X.Modules)
    (i j : cov.I₀) :
    let P := overlap cov i j
    ((modulesPseudofunctor.toDescentData cov.f).obj M).hom
        P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
      (Scheme.Modules.pullbackComp P.p₁ (cov.f i) ≪≫
          Scheme.Modules.pullbackCongr P.hp₁).hom.app M ≫
        (Scheme.Modules.pullbackComp P.p₂ (cov.f j) ≪≫
          Scheme.Modules.pullbackCongr P.hp₂).inv.app M := by
  let P := overlap cov i j
  dsimp only
  change (modulesPseudofunctor.mapComp'
        (cov.f i).op.toLoc P.p₁.op.toLoc P.p.op.toLoc _).inv.toNatTrans.app M ≫
      (modulesPseudofunctor.mapComp'
        (cov.f j).op.toLoc P.p₂.op.toLoc P.p.op.toLoc _).hom.toNatTrans.app M = _
  rw [modulesPseudofunctor_mapComp'_inv_app P.p₁ (cov.f i) P.p P.hp₁ M]
  rw [modulesPseudofunctor_mapComp'_hom_app P.p₂ (cov.f j) P.p P.hp₂ M]
  rfl

/-- Canonical descent of `M ⊗ N`, transported so that each chart carries the tensor of the two
separate restrictions. -/
noncomputable def tensorOfObjDescentData
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules) :
    modulesPseudofunctor.DescentData cov.f :=
  PseudofunctorDescent.changeObjects
    cov.f
    ((modulesPseudofunctor.toDescentData cov.f).obj (M ⊗ N))
    (fun i ↦ (Scheme.Modules.pullback (cov.f i)).obj M ⊗
      (Scheme.Modules.pullback (cov.f i)).obj N)
    (fun i ↦ (Functor.Monoidal.μIso
      (Scheme.Modules.pullback (cov.f i)) M N).symm)

/-- Canonical descent of `M ⊗ N` is isomorphic to its chartwise tensor presentation. -/
noncomputable def tensorOfObjDescentIso
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules) :
    (modulesPseudofunctor.toDescentData cov.f).obj (M ⊗ N) ≅
      tensorOfObjDescentData cov M N :=
  PseudofunctorDescent.changeObjectsIso
    cov.f
    ((modulesPseudofunctor.toDescentData cov.f).obj (M ⊗ N))
    (fun i ↦ (Scheme.Modules.pullback (cov.f i)).obj M ⊗
      (Scheme.Modules.pullback (cov.f i)).obj N)
    (fun i ↦ (Functor.Monoidal.μIso
      (Scheme.Modules.pullback (cov.f i)) M N).symm)

/-- The component isomorphism of an isomorphism of full descent data.  This generic bridge
is consumed by `CurveDivisorGlobalTensorAdd` when comparing global divisor descent with its
raw chartwise tensor presentation. -/
noncomputable def descentDataIsoComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D E : modulesPseudofunctor.DescentData cov.f}
    (e : D ≅ E) (i : cov.I₀) : D.obj i ≅ E.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) e.hom_inv_id
    change e.hom.hom i ≫ e.inv.hom i = 𝟙 _
    exact hi
  inv_hom_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) e.inv_hom_id
    change e.inv.hom i ≫ e.hom.hom i = 𝟙 _
    exact hi

private theorem canonicalTensorTransition_eq
    {S X₁ X₂ Y : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : Y ⟶ X₁) (p₂ : Y ⟶ X₂) (q : Y ⟶ S)
    (hp₁ : p₁ ≫ f₁ = q) (hp₂ : p₂ ≫ f₂ = q)
    (M N : S.Modules) :
    (Scheme.Modules.pullback p₁).map
          (Functor.Monoidal.μIso (Scheme.Modules.pullback f₁) M N).hom ≫
        (Scheme.Modules.pullbackComp p₁ f₁ ≪≫
          Scheme.Modules.pullbackCongr hp₁).hom.app (M ⊗ N) ≫
        (Scheme.Modules.pullbackComp p₂ f₂ ≪≫
          Scheme.Modules.pullbackCongr hp₂).inv.app (M ⊗ N) ≫
        (Scheme.Modules.pullback p₂).map
          (Functor.Monoidal.μIso (Scheme.Modules.pullback f₂) M N).inv =
      (Functor.Monoidal.μIso (Scheme.Modules.pullback p₁)
          ((Scheme.Modules.pullback f₁).obj M)
          ((Scheme.Modules.pullback f₁).obj N)).inv ≫
        (((Scheme.Modules.pullbackComp p₁ f₁ ≪≫
              Scheme.Modules.pullbackCongr hp₁).hom.app M ≫
            (Scheme.Modules.pullbackComp p₂ f₂ ≪≫
              Scheme.Modules.pullbackCongr hp₂).inv.app M) ⊗ₘ
          ((Scheme.Modules.pullbackComp p₁ f₁ ≪≫
              Scheme.Modules.pullbackCongr hp₁).hom.app N ≫
            (Scheme.Modules.pullbackComp p₂ f₂ ≪≫
              Scheme.Modules.pullbackCongr hp₂).inv.app N)) ≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback p₂)
          ((Scheme.Modules.pullback f₂).obj M)
          ((Scheme.Modules.pullback f₂).obj N)).hom := by
  let C₁ := Scheme.Modules.pullbackComp p₁ f₁ ≪≫
    Scheme.Modules.pullbackCongr hp₁
  let C₂ := Scheme.Modules.pullbackComp p₂ f₂ ≪≫
    Scheme.Modules.pullbackCongr hp₂
  letI hC₁ : C₁.hom.IsMonoidal :=
    pullbackCompCongr_hom_isMonoidal p₁ f₁ q hp₁
  letI hC₂ : C₂.hom.IsMonoidal :=
    pullbackCompCongr_hom_isMonoidal p₂ f₂ q hp₂
  letI hC₂inv : C₂.inv.IsMonoidal := inferInstance
  let μ₁ := Functor.Monoidal.μIso (Scheme.Modules.pullback p₁)
    ((Scheme.Modules.pullback f₁).obj M)
    ((Scheme.Modules.pullback f₁).obj N)
  let μ₂ := Functor.Monoidal.μIso (Scheme.Modules.pullback p₂)
    ((Scheme.Modules.pullback f₂).obj M)
    ((Scheme.Modules.pullback f₂).obj N)
  change _ ≫ C₁.hom.app (M ⊗ N) ≫ C₂.inv.app (M ⊗ N) ≫ _ =
    μ₁.inv ≫ ((C₁.hom.app M ≫ C₂.inv.app M) ⊗ₘ
      (C₁.hom.app N ≫ C₂.inv.app N)) ≫ μ₂.hom
  apply (cancel_epi μ₁.hom).1
  apply (cancel_mono μ₂.inv).1
  unfold μ₁ μ₂
  simp only [Category.assoc]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv]
  slice_lhs 1 2 => rw [← Functor.LaxMonoidal.comp_μ]
  simp only [Category.assoc]
  rw [NatTrans.IsMonoidal.tensor_assoc
    (X := M) (Y := N) (self := hC₁)]
  rw [NatTrans.IsMonoidal.tensor_assoc
    (X := M) (Y := N) (self := hC₂inv)]
  rw [Functor.LaxMonoidal.comp_μ]
  simp only [Category.assoc]
  slice_lhs 4 5 =>
    rw [← Functor.map_comp, Functor.Monoidal.μ_δ]
  rw [(Scheme.Modules.pullback p₂).map_id]
  rw [Category.id_comp]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [← tensorHom_comp_tensorHom]
  simp

private theorem tensorOfObjDescentData_hom_eq_untransported
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules)
    (i j : cov.I₀) :
    let P := overlap cov i j
    (tensorOfObjDescentData cov M N).hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
      (Scheme.Modules.pullback P.p₁).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f i)) M N).hom ≫
        ((modulesPseudofunctor.toDescentData cov.f).obj (M ⊗ N)).hom
          P.p P.p₁ P.p₂ P.hp₁ P.hp₂ ≫
        (Scheme.Modules.pullback P.p₂).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f j)) M N).inv := by
  let P := overlap cov i j
  dsimp only
  unfold tensorOfObjDescentData
  unfold PseudofunctorDescent.changeObjects
  rfl

private theorem untransportedTensorDescent_hom_eq_pullbackComp
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules)
    (i j : cov.I₀) :
    let P := overlap cov i j
    (Scheme.Modules.pullback P.p₁).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f i)) M N).hom ≫
        ((modulesPseudofunctor.toDescentData cov.f).obj (M ⊗ N)).hom
          P.p P.p₁ P.p₂ P.hp₁ P.hp₂ ≫
        (Scheme.Modules.pullback P.p₂).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f j)) M N).inv =
      (Scheme.Modules.pullback P.p₁).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f i)) M N).hom ≫
        (Scheme.Modules.pullbackComp P.p₁ (cov.f i) ≪≫
          Scheme.Modules.pullbackCongr P.hp₁).hom.app (M ⊗ N) ≫
        (Scheme.Modules.pullbackComp P.p₂ (cov.f j) ≪≫
          Scheme.Modules.pullbackCongr P.hp₂).inv.app (M ⊗ N) ≫
        (Scheme.Modules.pullback P.p₂).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f j)) M N).inv := by
  let P := overlap cov i j
  dsimp only
  have hMN := toDescentData_hom_eq_pullbackComp cov (M ⊗ N) i j
  dsimp only at hMN
  change ((modulesPseudofunctor.toDescentData cov.f).obj (M ⊗ N)).hom
      P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
        (Scheme.Modules.pullbackComp P.p₁ (cov.f i) ≪≫
          Scheme.Modules.pullbackCongr P.hp₁).hom.app (M ⊗ N) ≫
        (Scheme.Modules.pullbackComp P.p₂ (cov.f j) ≪≫
          Scheme.Modules.pullbackCongr P.hp₂).inv.app (M ⊗ N) at hMN
  simp only [P] at hMN
  rw [hMN]
  erw [Category.assoc]

private theorem whiskered_tensorHom_congr
    {C : Type*} [Category C] [MonoidalCategory C]
    {X₁ Y₁ X₂ Y₂ A B : C}
    (l : A ⟶ X₁ ⊗ X₂) (r : Y₁ ⊗ Y₂ ⟶ B)
    {f f' : X₁ ⟶ Y₁} {g g' : X₂ ⟶ Y₂}
    (hf : f = f') (hg : g = g') :
    l ≫ (f ⊗ₘ g) ≫ r = l ≫ (f' ⊗ₘ g') ≫ r := by
  subst f'
  subst g'
  rfl

private theorem untransportedTensorDescent_hom_on_overlap
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules)
    (i j : cov.I₀) :
    let P := overlap cov i j
    (Scheme.Modules.pullback P.p₁).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f i)) M N).hom ≫
        ((modulesPseudofunctor.toDescentData cov.f).obj (M ⊗ N)).hom
          P.p P.p₁ P.p₂ P.hp₁ P.hp₂ ≫
        (Scheme.Modules.pullback P.p₂).map
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (cov.f j)) M N).inv =
      (Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
          ((Scheme.Modules.pullback (cov.f i)).obj M)
          ((Scheme.Modules.pullback (cov.f i)).obj N)).inv ≫
        (((modulesPseudofunctor.toDescentData cov.f).obj M).hom
            P.p P.p₁ P.p₂ P.hp₁ P.hp₂ ⊗ₘ
          ((modulesPseudofunctor.toDescentData cov.f).obj N).hom
            P.p P.p₁ P.p₂ P.hp₁ P.hp₂) ≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
          ((Scheme.Modules.pullback (cov.f j)).obj M)
          ((Scheme.Modules.pullback (cov.f j)).obj N)).hom := by
  let P := overlap cov i j
  dsimp only
  have hM := toDescentData_hom_eq_pullbackComp cov M i j
  have hN := toDescentData_hom_eq_pullbackComp cov N i j
  dsimp only at hM hN
  have hWhiskered := whiskered_tensorHom_congr
    (Functor.Monoidal.μIso
      (Scheme.Modules.pullback (overlap cov i j).p₁)
      ((Scheme.Modules.pullback (cov.f i)).obj M)
      ((Scheme.Modules.pullback (cov.f i)).obj N)).inv
    (Functor.Monoidal.μIso
      (Scheme.Modules.pullback (overlap cov i j).p₂)
      ((Scheme.Modules.pullback (cov.f j)).obj M)
      ((Scheme.Modules.pullback (cov.f j)).obj N)).hom
    hM.symm hN.symm
  exact (untransportedTensorDescent_hom_eq_pullbackComp cov M N i j).trans
    ((canonicalTensorTransition_eq
      (cov.f i) (cov.f j)
      (overlap cov i j).p₁ (overlap cov i j).p₂ (overlap cov i j).p
      (overlap cov i j).hp₁ (overlap cov i j).hp₂ M N).trans hWhiskered)

/-- On a chosen overlap, canonical tensor descent is the tensor of the two canonical
transitions, conjugated by the pullback tensorators. -/
theorem tensorOfObjDescentData_hom_on_overlap
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules)
    (i j : cov.I₀) :
    let P := overlap cov i j
    (tensorOfObjDescentData cov M N).hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
      ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
          ((Scheme.Modules.pullback (cov.f i)).obj M)
          ((Scheme.Modules.pullback (cov.f i)).obj N)).symm ≪≫
        (((modulesPseudofunctor.toDescentData cov.f).obj M).iso
            P.p P.p₁ P.p₂ P.hp₁ P.hp₂ ⊗ᵢ
          ((modulesPseudofunctor.toDescentData cov.f).obj N).iso
            P.p P.p₁ P.p₂ P.hp₁ P.hp₂) ≪≫
        Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
          ((Scheme.Modules.pullback (cov.f j)).obj M)
          ((Scheme.Modules.pullback (cov.f j)).obj N)).hom := by
  let P := overlap cov i j
  dsimp only
  simp only [Iso.trans_hom, Iso.symm_hom]
  exact (tensorOfObjDescentData_hom_eq_untransported cov M N i j).trans
    (untransportedTensorDescent_hom_on_overlap cov M N i j)

/-- Build an isomorphism on chosen overlaps from modeled source and target transitions.  This
keeps the chosen/full descent constructor independent of the concrete definitions whose
transitions are being normalized; `CurveDivisorGlobalTensorAdd` is its named consumer. -/
noncomputable def primeIsoOfChosenTransitionModels
    {X : Scheme.{u}} (cov : X.OpenCover)
    (D E : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ E.obj i)
    (s : ∀ i j,
      (Scheme.Modules.pullback (overlap cov i j).p₁).obj (E.obj i) ⟶
        (Scheme.Modules.pullback (overlap cov i j).p₂).obj (E.obj j))
    (t : ∀ i j,
      (Scheme.Modules.pullback (overlap cov i j).p₁).obj (D.obj i) ⟶
        (Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j))
    (hs : ∀ i j,
      E.hom (overlap cov i j).p (overlap cov i j).p₁
          (overlap cov i j).p₂ (overlap cov i j).hp₁
          (overlap cov i j).hp₂ = s i j)
    (ht : ∀ i j,
      D.hom (overlap cov i j).p (overlap cov i j).p₁
          (overlap cov i j).p₂ (overlap cov i j).hp₁
          (overlap cov i j).hp₂ = t i j)
    (hcomm : ∀ i j,
      (Scheme.Modules.pullback (overlap cov i j).p₁).map (e i).hom ≫ s i j =
        t i j ≫ (Scheme.Modules.pullback (overlap cov i j).p₂).map (e j).hom) :
    Pseudofunctor.DescentData'.ofDescentData
        (overlap cov) (tripleOverlap cov) D ≅
      Pseudofunctor.DescentData'.ofDescentData
        (overlap cov) (tripleOverlap cov) E :=
  Pseudofunctor.DescentData'.isoMk e (fun i j ↦ by
    change (Scheme.Modules.pullback (overlap cov i j).p₁).map (e i).hom ≫
        E.hom (overlap cov i j).p (overlap cov i j).p₁
          (overlap cov i j).p₂ (overlap cov i j).hp₁
          (overlap cov i j).hp₂ =
      D.hom (overlap cov i j).p (overlap cov i j).p₁
          (overlap cov i j).p₂ (overlap cov i j).hp₁
          (overlap cov i j).hp₂ ≫
        (Scheme.Modules.pullback (overlap cov i j).p₂).map (e j).hom
    rw [hs i j, ht i j]
    exact hcomm i j)

/-- An isomorphism on chosen overlaps lifts through the chosen/full descent equivalence. -/
noncomputable def fullIsoOfChosenOverlaps
    {X : Scheme.{u}} (cov : X.OpenCover)
    (D E : modulesPseudofunctor.DescentData cov.f)
    (e : Pseudofunctor.DescentData'.ofDescentData
          (overlap cov) (tripleOverlap cov) D ≅
        Pseudofunctor.DescentData'.ofDescentData
          (overlap cov) (tripleOverlap cov) E) :
    D ≅ E :=
  (DescentDataPrime.descentDataOfDescentDataIso
      (overlap cov) (tripleOverlap cov) D).symm ≪≫
    (Pseudofunctor.DescentData'.toDescentDataFunctor modulesPseudofunctor
      (overlap cov) (tripleOverlap cov)).mapIso e ≪≫
    DescentDataPrime.descentDataOfDescentDataIso
      (overlap cov) (tripleOverlap cov) E

/-- Tensoring two commuting overlap squares gives a commuting square for their factorwise tensor
transitions. -/
theorem tensorTransition_comm
    {Y X₁ X₂ : Scheme.{u}} (p₁ : Y ⟶ X₁) (p₂ : Y ⟶ X₂)
    {A₁ B₁ C₁ D₁ : X₁.Modules} {A₂ B₂ C₂ D₂ : X₂.Modules}
    (eM₁ : A₁ ≅ B₁) (eN₁ : C₁ ≅ D₁)
    (eM₂ : A₂ ≅ B₂) (eN₂ : C₂ ≅ D₂)
    (tAM : (Scheme.Modules.pullback p₁).obj A₁ ≅
      (Scheme.Modules.pullback p₂).obj A₂)
    (tAN : (Scheme.Modules.pullback p₁).obj C₁ ≅
      (Scheme.Modules.pullback p₂).obj C₂)
    (tBM : (Scheme.Modules.pullback p₁).obj B₁ ≅
      (Scheme.Modules.pullback p₂).obj B₂)
    (tBN : (Scheme.Modules.pullback p₁).obj D₁ ≅
      (Scheme.Modules.pullback p₂).obj D₂)
    (hM : (Scheme.Modules.pullback p₁).map eM₁.hom ≫ tBM.hom =
      tAM.hom ≫ (Scheme.Modules.pullback p₂).map eM₂.hom)
    (hN : (Scheme.Modules.pullback p₁).map eN₁.hom ≫ tBN.hom =
      tAN.hom ≫ (Scheme.Modules.pullback p₂).map eN₂.hom) :
    (Scheme.Modules.pullback p₁).map (eM₁ ⊗ᵢ eN₁).hom ≫
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback p₁) B₁ D₁).symm ≪≫
          (tBM ⊗ᵢ tBN) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback p₂) B₂ D₂).hom =
      ((Functor.Monoidal.μIso (Scheme.Modules.pullback p₁) A₁ C₁).symm ≪≫
          (tAM ⊗ᵢ tAN) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback p₂) A₂ C₂).hom ≫
        (Scheme.Modules.pullback p₂).map (eM₂ ⊗ᵢ eN₂).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom]
  simp only [Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_hom]
  rw [Functor.Monoidal.map_tensor (Scheme.Modules.pullback p₁)]
  rw [Functor.Monoidal.map_tensor (Scheme.Modules.pullback p₂)]
  simp only [Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [hM, hN]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc]

/-- Tensoring the component isomorphisms of two descent comparisons gives a commuting modeled
transition square.  `CurveDivisorGlobalTensorAdd` uses this to keep concrete effective objects
out of the monoidal coherence calculation. -/
theorem tensorDescentIsoComponents_comm_on_overlap
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules)
    {D E : modulesPseudofunctor.DescentData cov.f}
    (eM : (modulesPseudofunctor.toDescentData cov.f).obj M ≅ D)
    (eN : (modulesPseudofunctor.toDescentData cov.f).obj N ≅ E)
    (i j : cov.I₀)
    (tM : (Scheme.Modules.pullback (overlap cov i j).p₁).obj (D.obj i) ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j))
    (tN : (Scheme.Modules.pullback (overlap cov i j).p₁).obj (E.obj i) ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (E.obj j))
    (htM : D.hom (overlap cov i j).p (overlap cov i j).p₁
        (overlap cov i j).p₂ (overlap cov i j).hp₁
        (overlap cov i j).hp₂ = tM.hom)
    (htN : E.hom (overlap cov i j).p (overlap cov i j).p₁
        (overlap cov i j).p₂ (overlap cov i j).hp₁
        (overlap cov i j).hp₂ = tN.hom) :
    let P := overlap cov i j
    let rM₁ := descentDataIsoComponent eM i
    let rN₁ := descentDataIsoComponent eN i
    let rM₂ := descentDataIsoComponent eM j
    let rN₂ := descentDataIsoComponent eN j
    let cM := ((modulesPseudofunctor.toDescentData cov.f).obj M).iso
      P.p P.p₁ P.p₂ P.hp₁ P.hp₂
    let cN := ((modulesPseudofunctor.toDescentData cov.f).obj N).iso
      P.p P.p₁ P.p₂ P.hp₁ P.hp₂
    (Scheme.Modules.pullback P.p₁).map (rM₁ ⊗ᵢ rN₁).hom ≫
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
            (D.obj i) (E.obj i)).symm ≪≫
          (tM ⊗ᵢ tN) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
            (D.obj j) (E.obj j)).hom =
      ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
            ((Scheme.Modules.pullback (cov.f i)).obj M)
            ((Scheme.Modules.pullback (cov.f i)).obj N)).symm ≪≫
          (cM ⊗ᵢ cN) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
            ((Scheme.Modules.pullback (cov.f j)).obj M)
            ((Scheme.Modules.pullback (cov.f j)).obj N)).hom ≫
        (Scheme.Modules.pullback P.p₂).map (rM₂ ⊗ᵢ rN₂).hom := by
  let P := overlap cov i j
  let rM₁ := descentDataIsoComponent eM i
  let rN₁ := descentDataIsoComponent eN i
  let rM₂ := descentDataIsoComponent eM j
  let rN₂ := descentDataIsoComponent eN j
  let cM := ((modulesPseudofunctor.toDescentData cov.f).obj M).iso
    P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  let cN := ((modulesPseudofunctor.toDescentData cov.f).obj N).iso
    P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  dsimp only
  have hM := eM.hom.comm P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  have hN := eN.hom.comm P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  rw [htM] at hM
  rw [htN] at hN
  exact tensorTransition_comm P.p₁ P.p₂
    rM₁ rN₁ rM₂ rN₂ cM cN tM tN hM hN

private theorem tensorThenInverseTransition_comm
    {C₁ C₂ C : Type*} [Category C₁] [Category C₂] [Category C]
    (F : C₁ ⥤ C) (G : C₂ ⥤ C)
    {A₁ B₁ R₁ : C₁} {A₂ B₂ R₂ : C₂}
    (r₁ : A₁ ≅ B₁) (r₂ : A₂ ≅ B₂)
    (a₁ : R₁ ≅ B₁) (a₂ : R₂ ≅ B₂)
    (c : F.obj A₁ ≅ G.obj A₂)
    (t : F.obj B₁ ≅ G.obj B₂)
    (s : F.obj R₁ ≅ G.obj R₂)
    (hr : F.map r₁.hom ≫ t.hom = c.hom ≫ G.map r₂.hom)
    (ha : F.map a₁.hom ≫ t.hom = s.hom ≫ G.map a₂.hom) :
    F.map (r₁ ≪≫ a₁.symm).hom ≫ s.hom =
      c.hom ≫ G.map (r₂ ≪≫ a₂.symm).hom := by
  have ha' : F.map a₁.inv ≫ s.hom = t.hom ≫ G.map a₂.inv := by
    apply (cancel_epi (F.map a₁.hom)).1
    rw [← Category.assoc, ← Functor.map_comp, a₁.hom_inv_id,
      F.map_id, Category.id_comp]
    rw [← Category.assoc, ha]
    rw [Category.assoc, ← Functor.map_comp, a₂.hom_inv_id,
      G.map_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [ha']
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ G.map a₂.inv) hr

/-- Compose the factorwise tensor square of two descent comparisons with a modeled local
addition square.  The result is the chosen-overlap square from the tensor of the effective
objects directly to the source of the addition isomorphisms. -/
theorem tensorThenInverseDescentIsoComponents_comm_on_overlap
    {X : Scheme.{u}} (cov : X.OpenCover) (M N : X.Modules)
    {D E R : modulesPseudofunctor.DescentData cov.f}
    (eM : (modulesPseudofunctor.toDescentData cov.f).obj M ≅ D)
    (eN : (modulesPseudofunctor.toDescentData cov.f).obj N ≅ E)
    (i j : cov.I₀)
    (tM : (Scheme.Modules.pullback (overlap cov i j).p₁).obj (D.obj i) ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j))
    (tN : (Scheme.Modules.pullback (overlap cov i j).p₁).obj (E.obj i) ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (E.obj j))
    (tR : (Scheme.Modules.pullback (overlap cov i j).p₁).obj (R.obj i) ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (R.obj j))
    (a₁ : R.obj i ≅ D.obj i ⊗ E.obj i)
    (a₂ : R.obj j ≅ D.obj j ⊗ E.obj j)
    (htM : D.hom (overlap cov i j).p (overlap cov i j).p₁
        (overlap cov i j).p₂ (overlap cov i j).hp₁
        (overlap cov i j).hp₂ = tM.hom)
    (htN : E.hom (overlap cov i j).p (overlap cov i j).p₁
        (overlap cov i j).p₂ (overlap cov i j).hp₁
        (overlap cov i j).hp₂ = tN.hom)
    (ha :
      (Scheme.Modules.pullback (overlap cov i j).p₁).map a₁.hom ≫
          ((Functor.Monoidal.μIso
              (Scheme.Modules.pullback (overlap cov i j).p₁)
              (D.obj i) (E.obj i)).symm ≪≫
            (tM ⊗ᵢ tN) ≪≫
            Functor.Monoidal.μIso
              (Scheme.Modules.pullback (overlap cov i j).p₂)
              (D.obj j) (E.obj j)).hom =
        tR.hom ≫
          (Scheme.Modules.pullback (overlap cov i j).p₂).map a₂.hom) :
    let P := overlap cov i j
    let rM₁ := descentDataIsoComponent eM i
    let rN₁ := descentDataIsoComponent eN i
    let rM₂ := descentDataIsoComponent eM j
    let rN₂ := descentDataIsoComponent eN j
    let cM := ((modulesPseudofunctor.toDescentData cov.f).obj M).iso
      P.p P.p₁ P.p₂ P.hp₁ P.hp₂
    let cN := ((modulesPseudofunctor.toDescentData cov.f).obj N).iso
      P.p P.p₁ P.p₂ P.hp₁ P.hp₂
    (Scheme.Modules.pullback P.p₁).map
          ((rM₁ ⊗ᵢ rN₁) ≪≫ a₁.symm).hom ≫
        tR.hom =
      ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
            ((Scheme.Modules.pullback (cov.f i)).obj M)
            ((Scheme.Modules.pullback (cov.f i)).obj N)).symm ≪≫
          (cM ⊗ᵢ cN) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
            ((Scheme.Modules.pullback (cov.f j)).obj M)
            ((Scheme.Modules.pullback (cov.f j)).obj N)).hom ≫
        (Scheme.Modules.pullback P.p₂).map
          ((rM₂ ⊗ᵢ rN₂) ≪≫ a₂.symm).hom := by
  let P := overlap cov i j
  let rM₁ := descentDataIsoComponent eM i
  let rN₁ := descentDataIsoComponent eN i
  let rM₂ := descentDataIsoComponent eM j
  let rN₂ := descentDataIsoComponent eN j
  let cM := ((modulesPseudofunctor.toDescentData cov.f).obj M).iso
    P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  let cN := ((modulesPseudofunctor.toDescentData cov.f).obj N).iso
    P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  let tTensor :=
    (Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
        (D.obj i) (E.obj i)).symm ≪≫
      (tM ⊗ᵢ tN) ≪≫
      Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
        (D.obj j) (E.obj j)
  let cTensor :=
    (Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
        ((Scheme.Modules.pullback (cov.f i)).obj M)
        ((Scheme.Modules.pullback (cov.f i)).obj N)).symm ≪≫
      (cM ⊗ᵢ cN) ≪≫
      Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
        ((Scheme.Modules.pullback (cov.f j)).obj M)
        ((Scheme.Modules.pullback (cov.f j)).obj N)
  exact tensorThenInverseTransition_comm
    (Scheme.Modules.pullback P.p₁) (Scheme.Modules.pullback P.p₂)
    (rM₁ ⊗ᵢ rN₁) (rM₂ ⊗ᵢ rN₂) a₁ a₂
    cTensor tTensor tR
    (tensorDescentIsoComponents_comm_on_overlap
      cov M N eM eN i j tM tN htM htN) ha

end MazurTorsion.AlgebraicGeometry.LineBundleDescent

end
