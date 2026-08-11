/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorTensorAddOverlap
import MazurTorsion.Upstream.CurveLineBundleRawCocyclePrime

/-!
# Tensor addition on the chosen overlap of two curve charts

This file transports the checked pairwise-intersection tensor/addition square to Mathlib's
chosen pullback.  The tensor transition is transported as one whole model isomorphism; its
separate identification with the tensor product of the two transported factor transitions is a
further monoidal-pseudofunctor coherence statement and is not asserted here.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

universe u v

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForChosenOverlapTensor (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- Four objects and four composable arrows forming the boundary of a square. -/
private structure SquareDiagram (C : Type*) [Category C] where
  source₁ : C
  target₁ : C
  source₂ : C
  target₂ : C
  a : source₁ ⟶ target₁
  t : target₁ ⟶ target₂
  s : source₁ ⟶ source₂
  b : source₂ ⟶ target₂

/-- Commutativity of a cached square diagram. -/
private structure SquareDiagram.IsComm
    {C : Type*} [Category C] (d : SquareDiagram C) : Prop where
  out : d.a ≫ d.t = d.s ≫ d.b

/-- A square remains commutative after replacing all four objects by conjugate models. -/
private theorem hom_square_of_conjugacies
    {C : Type*} [Category C]
    {S₁ T₁ S₂ T₂ S₁' T₁' S₂' T₂' : C}
    (A₁ : S₁ ⟶ T₁) (tT : T₁ ⟶ T₂) (tS : S₁ ⟶ S₂) (A₂ : S₂ ⟶ T₂)
    (qS₁ : S₁ ≅ S₁') (qT₁ : T₁ ≅ T₁')
    (qS₂ : S₂ ≅ S₂') (qT₂ : T₂ ≅ T₂')
    (a₁ : S₁' ⟶ T₁') (eT : T₁' ⟶ T₂') (eS : S₁' ⟶ S₂') (a₂ : S₂' ⟶ T₂')
    (hA₁ : A₁ ≫ qT₁.hom = qS₁.hom ≫ a₁)
    (hT : qT₁.hom ≫ eT = tT ≫ qT₂.hom)
    (hS : qS₁.hom ≫ eS = tS ≫ qS₂.hom)
    (hA₂ : A₂ ≫ qT₂.hom = qS₂.hom ≫ a₂)
    (h : A₁ ≫ tT = tS ≫ A₂) :
    a₁ ≫ eT = eS ≫ a₂ := by
  apply (cancel_epi qS₁.hom).1
  calc
    qS₁.hom ≫ (a₁ ≫ eT) = (A₁ ≫ qT₁.hom) ≫ eT := by
      rw [hA₁, Category.assoc]
    _ = A₁ ≫ (tT ≫ qT₂.hom) := by rw [Category.assoc, hT]
    _ = (tS ≫ A₂) ≫ qT₂.hom := by rw [← Category.assoc, h]
    _ = tS ≫ (qS₂.hom ≫ a₂) := by rw [Category.assoc, hA₂]
    _ = (qS₁.hom ≫ eS) ≫ a₂ := by rw [← Category.assoc, hS]
    _ = qS₁.hom ≫ (eS ≫ a₂) := Category.assoc _ _ _

/-- Restoring the target tensorator on both sides of a core square preserves commutativity. -/
private theorem hom_square_restore_target_tensorator
    {C : Type*} [Category C]
    {S₁ T₁ U₁ S₂ T₂ U₂ : C}
    (A₁ : S₁ ≅ T₁) (μ₁ : U₁ ≅ T₁) (e : U₁ ≅ U₂)
    (s : S₁ ≅ S₂) (A₂ : S₂ ≅ T₂) (μ₂ : U₂ ≅ T₂)
    (h : (A₁ ≪≫ μ₁.symm).hom ≫ e.hom =
      s.hom ≫ (A₂ ≪≫ μ₂.symm).hom) :
    A₁.hom ≫ (μ₁.symm ≪≫ e ≪≫ μ₂).hom = s.hom ≫ A₂.hom := by
  apply (cancel_mono μ₂.inv).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] using h

/-- Tensoring two conjugacy squares gives the conjugacy square on tensor products. -/
private theorem tensor_hom_conjugacy
    {C : Type*} [Category C] [MonoidalCategory C]
    {A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : C}
    (q₁D : A₁ ≅ B₁) (eD : B₁ ≅ C₁)
    (tD : A₁ ≅ D₁) (q₂D : D₁ ≅ C₁)
    (q₁E : A₂ ≅ B₂) (eE : B₂ ≅ C₂)
    (tE : A₂ ≅ D₂) (q₂E : D₂ ≅ C₂)
    (hD : q₁D.hom ≫ eD.hom = tD.hom ≫ q₂D.hom)
    (hE : q₁E.hom ≫ eE.hom = tE.hom ≫ q₂E.hom) :
    (q₁D ⊗ᵢ q₁E).hom ≫ (eD ⊗ᵢ eE).hom =
      (tD ⊗ᵢ tE).hom ≫ (q₂D ⊗ᵢ q₂E).hom := by
  calc
    (q₁D ⊗ᵢ q₁E).hom ≫ (eD ⊗ᵢ eE).hom =
        (q₁D.hom ≫ eD.hom) ⊗ₘ (q₁E.hom ≫ eE.hom) :=
      tensorHom_comp_tensorHom q₁D.hom q₁E.hom eD.hom eE.hom
    _ = (tD.hom ≫ q₂D.hom) ⊗ₘ (tE.hom ≫ q₂E.hom) :=
      congrArg₂ (fun a b ↦ a ⊗ₘ b) hD hE
    _ = (tD ⊗ᵢ tE).hom ≫ (q₂D ⊗ᵢ q₂E).hom :=
      (tensorHom_comp_tensorHom tD.hom tE.hom q₂D.hom q₂E.hom).symm

/-- The restriction tensor comparison, expressed without divisor-specific aliases. -/
private noncomputable def restrictionTensorIsoViaPullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor f).obj (M ⊗ N) ≅
      (Scheme.Modules.restrictFunctor f).obj M ⊗
        (Scheme.Modules.restrictFunctor f).obj N := by
  let PB := Scheme.Modules.pullback f
  let q := Scheme.Modules.restrictFunctorIsoPullback f
  letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  exact q.app (M ⊗ N) ≪≫
    (Functor.Monoidal.μIso PB M N).symm ≪≫
    ((q.app M).symm ⊗ᵢ (q.app N).symm)

/-- Mapping a tensor-valued isomorphism by restriction and then passing to pullback agrees with
first passing to pullback and using its inverse tensorator. -/
private theorem restrictionTensorIsoViaPullback_conjugacy
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (S M N : X.Modules) (a : S ≅ M ⊗ N) :
    let F := Scheme.Modules.restrictFunctor f
    let PB := Scheme.Modules.pullback f
    let q := Scheme.Modules.restrictFunctorIsoPullback f
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
    ((F.mapIso a ≪≫ restrictionTensorIsoViaPullback f M N) ≪≫
        (q.app M ⊗ᵢ q.app N)).hom =
      (q.app S ≪≫
        (PB.mapIso a ≪≫ (Functor.Monoidal.μIso PB M N).symm)).hom := by
  let F := Scheme.Modules.restrictFunctor f
  let PB := Scheme.Modules.pullback f
  let q := Scheme.Modules.restrictFunctorIsoPullback f
  letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  let qS := (q.app S).hom
  let qT := (q.app (M ⊗ N)).hom
  let δ := Functor.OplaxMonoidal.δ PB M N
  let qInvPair := (q.app M).inv ⊗ₘ (q.app N).inv
  let qHomPair := (q.app M).hom ⊗ₘ (q.app N).hom
  have hq := q.hom.naturality a.hom
  change F.map a.hom ≫ qT = qS ≫ PB.map a.hom at hq
  have hpair₁ : qInvPair ≫ qHomPair =
      ((q.app M).inv ≫ (q.app M).hom) ⊗ₘ
        ((q.app N).inv ≫ (q.app N).hom) :=
    tensorHom_comp_tensorHom (q.app M).inv (q.app N).inv
      (q.app M).hom (q.app N).hom
  have hpair₂ :
      ((q.app M).inv ≫ (q.app M).hom) ⊗ₘ
          ((q.app N).inv ≫ (q.app N).hom) =
        𝟙 (PB.obj M ⊗ PB.obj N) :=
    (congrArg₂ (fun x y ↦ x ⊗ₘ y) (q.app M).inv_hom_id
      (q.app N).inv_hom_id).trans (MonoidalCategory.id_tensorHom_id _ _)
  have hpair : qInvPair ≫ qHomPair = 𝟙 (PB.obj M ⊗ PB.obj N) :=
    hpair₁.trans hpair₂
  change
    (((F.map a.hom ≫ qT ≫ δ ≫ qInvPair) ≫ qHomPair)) =
      qS ≫ PB.map a.hom ≫ δ
  calc
    ((F.map a.hom ≫ qT ≫ δ ≫ qInvPair) ≫ qHomPair) =
        (qS ≫ PB.map a.hom ≫ δ ≫ qInvPair) ≫ qHomPair := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ (z ≫ δ ≫ qInvPair) ≫ qHomPair) hq
    _ = qS ≫ PB.map a.hom ≫ δ ≫ (qInvPair ≫ qHomPair) := by
      simp only [Category.assoc]
    _ = qS ≫ PB.map a.hom ≫ δ := by rw [hpair, Category.comp_id]

/-- The pairwise-intersection model transition is the restriction transition conjugated by the
restriction-to-pullback comparisons on the two charts. -/
private theorem localLineBundlePairwiseOverlapModelIso_conjugacy
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (G : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    letI := hnonempty i
    letI := hnonempty j
    let W := U i ⊓ U j
    letI : Nonempty W := nonempty_inf_of_isIntegral X (U i) (U j)
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    let hW : IsAffineOpen W := (hU i).inf (hU j)
    letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
    letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X (U i) W inf_le_left
    letI := restrictionAlgebra X (U j) W inf_le_right
    letI : IsOpenImmersion (extensionMap Γ(X, U i) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X (U i) W (hU i) hW inf_le_left
    letI : IsOpenImmersion (extensionMap Γ(X, U j) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X (U j) W (hU j) hW inf_le_right
    let q₁ := Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap Γ(X, U i) Γ(X, W))
    let q₂ := Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap Γ(X, U j) Γ(X, W))
    let L₁ := (localLineBundles X U hnonempty hcover hU h G i).obj
    let L₂ := (localLineBundles X U hnonempty hcover hU h G j).obj
    let t := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right
        (h i) (h j) G
    let e := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h G i j
    (q₁.app L₁).hom ≫ e.hom = t.hom ≫ (q₂.app L₂).hom := by
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI : Nonempty W := nonempty_inf_of_isIntegral X (U i) (U j)
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hW : IsAffineOpen W := (hU i).inf (hU j)
  letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  letI : IsOpenImmersion (extensionMap Γ(X, U i) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X (U i) W (hU i) hW inf_le_left
  letI : IsOpenImmersion (extensionMap Γ(X, U j) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X (U j) W (hU j) hW inf_le_right
  let q₁ := Scheme.Modules.restrictFunctorIsoPullback
    (extensionMap Γ(X, U i) Γ(X, W))
  let q₂ := Scheme.Modules.restrictFunctorIsoPullback
    (extensionMap Γ(X, U j) Γ(X, W))
  let L₁ := (localLineBundles X U hnonempty hcover hU h G i).obj
  let L₂ := (localLineBundles X U hnonempty hcover hU h G j).obj
  let t := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right
      (h i) (h j) G
  let t' := localLineBundleRestrictionIsoOnProperSmoothCurveIntersection
    K X f (U i) (U j) (hU i) (hU j) (h i) (h j) G
  let e := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h G i j
  have ht := localLineBundleRestrictionIsoViaPairwiseIntersection_eq_direct
    K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right
      (h i) (h j) G
  change t = t' at ht
  have he : e = (q₁.app L₁).symm ≪≫ t' ≪≫ q₂.app L₂ := by
    rfl
  have heHom := congrArg Iso.hom he
  change e.hom = ((q₁.app L₁).symm ≪≫ t' ≪≫ q₂.app L₂).hom at heHom
  dsimp only
  change (q₁.app L₁).hom ≫ e.hom = t.hom ≫ (q₂.app L₂).hom
  rw [heHom]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  change (t' ≪≫ q₂.app L₂).hom = (t ≪≫ q₂.app L₂).hom
  exact congrArg Iso.hom (congrArg (fun z ↦ z ≪≫ q₂.app L₂) ht.symm)

/-- Tensoring the two single-factor model conjugacies gives the corresponding conjugacy for
the pairwise tensor transition. -/
private theorem localLineBundlePairwiseTensorOverlapModelIso_conjugacy
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    letI := hnonempty i
    letI := hnonempty j
    let W := U i ⊓ U j
    letI : Nonempty W := nonempty_inf_of_isIntegral X (U i) (U j)
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    let hW : IsAffineOpen W := (hU i).inf (hU j)
    letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
    letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X (U i) W inf_le_left
    letI := restrictionAlgebra X (U j) W inf_le_right
    letI : IsOpenImmersion (extensionMap Γ(X, U i) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X (U i) W (hU i) hW inf_le_left
    letI : IsOpenImmersion (extensionMap Γ(X, U j) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X (U j) W (hU j) hW inf_le_right
    let q₁ := Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap Γ(X, U i) Γ(X, W))
    let q₂ := Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap Γ(X, U j) Γ(X, W))
    let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
    let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
    let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
    let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
    let tD := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right
        (h i) (h j) D
    let tE := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right
        (h i) (h j) E
    let eD := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j
    let eE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h E i j
    ((q₁.app L₁D) ⊗ᵢ (q₁.app L₁E)).hom ≫ (eD ⊗ᵢ eE).hom =
      (tD ⊗ᵢ tE).hom ≫ ((q₂.app L₂D) ⊗ᵢ (q₂.app L₂E)).hom := by
  dsimp only
  apply tensor_hom_conjugacy
  · exact localLineBundlePairwiseOverlapModelIso_conjugacy
      K X f U hnonempty hcover hU h D i j
  · exact localLineBundlePairwiseOverlapModelIso_conjugacy
      K X f U hnonempty hcover hU h E i j

/-- Pulling a commuting square along one further map preserves its commutativity. -/
private theorem pullHom_naturality
    {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {X₁ X₂ Y Y' : C}
    {M₁ N₁ : F.obj (.mk (.op X₁))}
    {M₂ N₂ : F.obj (.mk (.op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a₁ : M₁ ⟶ N₁) (a₂ : M₂ ⟶ N₂)
    (eM : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (eN : (F.map f₁.op.toLoc).toFunctor.obj N₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj N₂)
    (h : (F.map f₁.op.toLoc).toFunctor.map a₁ ≫ eN =
      eM ≫ (F.map f₂.op.toLoc).toFunctor.map a₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map gf₁.op.toLoc).toFunctor.map a₁ ≫
        pullHom (F := F) eN g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom (F := F) eM g gf₁ gf₂ hgf₁ hgf₂ ≫
        (F.map gf₂.op.toLoc).toFunctor.map a₂ := by
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
    F.mapComp'_inv_naturality]
  simp only [Category.assoc]

/-- Naturality of a model square after transporting both comparison isomorphisms to the
standard chosen pullback. -/
private theorem pullbackOverlapIsoOfModel_hom_naturality
    {S X₁ X₂ W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    {M₁ N₁ : LineBundleDescent.modulesPseudofunctor.obj (.mk (.op X₁))}
    {M₂ N₂ : LineBundleDescent.modulesPseudofunctor.obj (.mk (.op X₂))}
    (a₁ : M₁ ⟶ N₁) (a₂ : M₂ ⟶ N₂)
    (eM : (LineBundleDescent.modulesPseudofunctor.map p₁.op.toLoc).toFunctor.obj M₁ ≅
      (LineBundleDescent.modulesPseudofunctor.map p₂.op.toLoc).toFunctor.obj M₂)
    (eN : (LineBundleDescent.modulesPseudofunctor.map p₁.op.toLoc).toFunctor.obj N₁ ≅
      (LineBundleDescent.modulesPseudofunctor.map p₂.op.toLoc).toFunctor.obj N₂)
    (hcomm : (LineBundleDescent.modulesPseudofunctor.map p₁.op.toLoc).toFunctor.map a₁ ≫
        eN.hom =
      eM.hom ≫
        (LineBundleDescent.modulesPseudofunctor.map p₂.op.toLoc).toFunctor.map a₂) :
    (LineBundleDescent.modulesPseudofunctor.map
        (pullback.fst f₁ f₂).op.toLoc).toFunctor.map a₁ ≫
        (LineBundleDescent.pullbackOverlapIsoOfModel
          f₁ f₂ p₁ p₂ hpb N₁ N₂ eN).hom =
      (LineBundleDescent.pullbackOverlapIsoOfModel
        f₁ f₂ p₁ p₂ hpb M₁ M₂ eM).hom ≫
        (LineBundleDescent.modulesPseudofunctor.map
          (pullback.snd f₁ f₂).op.toLoc).toFunctor.map a₂ := by
  have hIsoN :
      (LineBundleDescent.pullbackOverlapIsoOfModel
        f₁ f₂ p₁ p₂ hpb N₁ N₂ eN).hom =
        LineBundleDescent.pullbackOverlapHomOfModel
          f₁ f₂ p₁ p₂ hpb N₁ N₂ eN := rfl
  have hIsoM :
      (LineBundleDescent.pullbackOverlapIsoOfModel
        f₁ f₂ p₁ p₂ hpb M₁ M₂ eM).hom =
        LineBundleDescent.pullbackOverlapHomOfModel
          f₁ f₂ p₁ p₂ hpb M₁ M₂ eM := rfl
  rw [hIsoN, hIsoM]
  have hN := LineBundleDescent.pullHom_pullbackOverlapHomOfModel
    f₁ f₂ p₁ p₂ hpb N₁ N₂ eN (𝟙 (pullback f₁ f₂))
      (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
      (Category.id_comp _) (Category.id_comp _)
  have hM := LineBundleDescent.pullHom_pullbackOverlapHomOfModel
    f₁ f₂ p₁ p₂ hpb M₁ M₂ eM (𝟙 (pullback f₁ f₂))
      (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
      (Category.id_comp _) (Category.id_comp _)
  have hidN :
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (LineBundleDescent.pullbackOverlapHomOfModel
            f₁ f₂ p₁ p₂ hpb N₁ N₂ eN)
          (𝟙 (pullback f₁ f₂)) (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
          (Category.id_comp _) (Category.id_comp _) =
        LineBundleDescent.pullbackOverlapHomOfModel
          f₁ f₂ p₁ p₂ hpb N₁ N₂ eN :=
    pullHom_id _
  have hidM :
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (LineBundleDescent.pullbackOverlapHomOfModel
            f₁ f₂ p₁ p₂ hpb M₁ M₂ eM)
          (𝟙 (pullback f₁ f₂)) (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
          (Category.id_comp _) (Category.id_comp _) =
        LineBundleDescent.pullbackOverlapHomOfModel
          f₁ f₂ p₁ p₂ hpb M₁ M₂ eM :=
    pullHom_id _
  have hN' := hidN.symm.trans hN
  have hM' := hidM.symm.trans hM
  simp only [Category.id_comp] at hN' hM'
  rw [hN', hM']
  apply pullHom_naturality
    (F := LineBundleDescent.modulesPseudofunctor) a₁ a₂ eM.hom eN.hom hcomm

/-- The module pseudofunctor map has the exact pullback-functor implementation. -/
private theorem modulesPseudofunctor_map_eq_pullback
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (LineBundleDescent.modulesPseudofunctor.map g.op.toLoc).toFunctor =
      Scheme.Modules.pullback g := by
  rfl

/-- The action on a morphism has the exact pullback-functor implementation. -/
private theorem modulesPseudofunctor_map_map_eq_pullback_map
    {X Y : Scheme.{u}} (g : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (LineBundleDescent.modulesPseudofunctor.map g.op.toLoc).toFunctor.map a =
      (Scheme.Modules.pullback g).map a := by
  rfl

/-- The transported model Hom, with endpoints kept in the exact pseudofunctor presentation. -/
private noncomputable def pullbackOverlapHomOfModelPseudo
    {S X₁ X₂ W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (e : (Scheme.Modules.pullback p₁).obj M₁ ≅
      (Scheme.Modules.pullback p₂).obj M₂) :
    (LineBundleDescent.modulesPseudofunctor.map
      (pullback.fst f₁ f₂).op.toLoc).toFunctor.obj M₁ ⟶
      (LineBundleDescent.modulesPseudofunctor.map
        (pullback.snd f₁ f₂).op.toLoc).toFunctor.obj M₂ := by
  rw [modulesPseudofunctor_map_eq_pullback,
    modulesPseudofunctor_map_eq_pullback]
  exact LineBundleDescent.pullbackOverlapHomOfModel
    f₁ f₂ p₁ p₂ hpb M₁ M₂ e

/-- The forward map of the transported model Iso equals its exact-pseudofunctor Hom. -/
private theorem pullbackOverlapIsoOfModel_hom_eq_pseudo
    {S X₁ X₂ W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (e : (Scheme.Modules.pullback p₁).obj M₁ ≅
      (Scheme.Modules.pullback p₂).obj M₂) :
    (LineBundleDescent.pullbackOverlapIsoOfModel
      f₁ f₂ p₁ p₂ hpb M₁ M₂ e).hom =
      pullbackOverlapHomOfModelPseudo f₁ f₂ p₁ p₂ hpb M₁ M₂ e := by
  unfold pullbackOverlapHomOfModelPseudo
  exact LineBundleDescent.pullbackOverlapIsoOfModel_hom
    f₁ f₂ p₁ p₂ hpb M₁ M₂ e

/-- Naturality of transported model Homs, entirely in exact pseudofunctor heads. -/
private theorem pullbackOverlapHomOfModelPseudo_naturality
    {S X₁ X₂ W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    {M₁ N₁ : X₁.Modules} {M₂ N₂ : X₂.Modules}
    (a₁ : M₁ ⟶ N₁) (a₂ : M₂ ⟶ N₂)
    (eM : (Scheme.Modules.pullback p₁).obj M₁ ≅
      (Scheme.Modules.pullback p₂).obj M₂)
    (eN : (Scheme.Modules.pullback p₁).obj N₁ ≅
      (Scheme.Modules.pullback p₂).obj N₂)
    (hcomm :
      (LineBundleDescent.modulesPseudofunctor.map p₁.op.toLoc).toFunctor.map a₁ ≫
          eN.hom =
        eM.hom ≫
          (LineBundleDescent.modulesPseudofunctor.map p₂.op.toLoc).toFunctor.map a₂) :
    (LineBundleDescent.modulesPseudofunctor.map
        (pullback.fst f₁ f₂).op.toLoc).toFunctor.map a₁ ≫
        pullbackOverlapHomOfModelPseudo f₁ f₂ p₁ p₂ hpb N₁ N₂ eN =
      pullbackOverlapHomOfModelPseudo f₁ f₂ p₁ p₂ hpb M₁ M₂ eM ≫
        (LineBundleDescent.modulesPseudofunctor.map
          (pullback.snd f₁ f₂).op.toLoc).toFunctor.map a₂ := by
  rw [← pullbackOverlapIsoOfModel_hom_eq_pseudo,
    ← pullbackOverlapIsoOfModel_hom_eq_pseudo]
  exact pullbackOverlapIsoOfModel_hom_naturality
    f₁ f₂ p₁ p₂ hpb a₁ a₂ eM eN hcomm

/-- The tensor of the two pairwise model transitions, conjugated so that its endpoints are
pullbacks of the chartwise tensor products. -/
private noncomputable def localLineBundlePairwiseTensorModelIso
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    let W := U i ⊓ U j
    letI := restrictionAlgebra X (U i) W inf_le_left
    letI := restrictionAlgebra X (U j) W inf_le_right
    let p₁ := extensionMap Γ(X, U i) Γ(X, W)
    let p₂ := extensionMap Γ(X, U j) Γ(X, W)
    let PB₁ := Scheme.Modules.pullback p₁
    let PB₂ := Scheme.Modules.pullback p₂
    let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
    let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
    let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
    let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
    PB₁.obj (L₁D ⊗ L₁E) ≅ PB₂.obj (L₂D ⊗ L₂E) := by
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  let PB₁ := Scheme.Modules.pullback p₁
  let PB₂ := Scheme.Modules.pullback p₂
  letI : PB₁.Monoidal := Scheme.Modules.pullbackMonoidal p₁
  letI : PB₂.Monoidal := Scheme.Modules.pullbackMonoidal p₂
  let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
  let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
  let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
  let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
  let eD := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j
  let eE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h E i j
  exact (Functor.Monoidal.μIso PB₁ L₁D L₁E).symm ≪≫
    (eD ⊗ᵢ eE) ≪≫ Functor.Monoidal.μIso PB₂ L₂D L₂E

/-- The chart-one sum bundle pulled to the pairwise model. -/
private noncomputable def localLineBundlePairwiseModelSourceOne
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) := by
  letI := hnonempty i
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  exact (Scheme.Modules.pullback p₁).obj
    (localLineBundles X U hnonempty hcover hU h (D + E) i).obj

/-- The chart-one tensor product pulled to the pairwise model. -/
private noncomputable def localLineBundlePairwiseModelTargetOne
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) := by
  letI := hnonempty i
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  exact (Scheme.Modules.pullback p₁).obj
    ((localLineBundles X U hnonempty hcover hU h D i).obj ⊗
      (localLineBundles X U hnonempty hcover hU h E i).obj)

/-- The chart-two sum bundle pulled to the pairwise model. -/
private noncomputable def localLineBundlePairwiseModelSourceTwo
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) := by
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  exact (Scheme.Modules.pullback p₂).obj
    (localLineBundles X U hnonempty hcover hU h (D + E) j).obj

/-- The chart-two tensor product pulled to the pairwise model. -/
private noncomputable def localLineBundlePairwiseModelTargetTwo
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) := by
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  exact (Scheme.Modules.pullback p₂).obj
    ((localLineBundles X U hnonempty hcover hU h D j).obj ⊗
      (localLineBundles X U hnonempty hcover hU h E j).obj)

/-- The tensor product of the two chart-one bundles after pulling back each factor. -/
private noncomputable def localLineBundlePairwiseCoreTargetOne
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) := by
  letI := hnonempty i
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let PB₁ := Scheme.Modules.pullback p₁
  exact PB₁.obj (localLineBundles X U hnonempty hcover hU h D i).obj ⊗
    PB₁.obj (localLineBundles X U hnonempty hcover hU h E i).obj

/-- The tensor product of the two chart-two bundles after pulling back each factor. -/
private noncomputable def localLineBundlePairwiseCoreTargetTwo
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) := by
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  let PB₂ := Scheme.Modules.pullback p₂
  exact PB₂.obj (localLineBundles X U hnonempty hcover hU h D j).obj ⊗
    PB₂.obj (localLineBundles X U hnonempty hcover hU h E j).obj

/-- The chart-one addition map pulled to the pairwise model. -/
private noncomputable def localLineBundlePairwiseLeftPulledAddHom
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    localLineBundlePairwiseModelSourceOne
        X U hnonempty hcover hU h D E i j ⟶
      localLineBundlePairwiseModelTargetOne
        X U hnonempty hcover hU h D E i j := by
  letI := hnonempty i
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  exact (Scheme.Modules.pullback p₁).map
    (localLineBundleAddIso X (U i) (hU i) (h i) D E).hom

/-- The transported tensor-model transition as a morphism. -/
private noncomputable def localLineBundlePairwiseTensorModelHom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    localLineBundlePairwiseModelTargetOne
        X U hnonempty hcover hU h D E i j ⟶
      localLineBundlePairwiseModelTargetTwo
        X U hnonempty hcover hU h D E i j :=
  (localLineBundlePairwiseTensorModelIso
    K X f U hnonempty hcover hU h D E i j).hom

/-- The sum-divisor transition on the pairwise model as a morphism. -/
private noncomputable def localLineBundlePairwiseSumModelHom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    localLineBundlePairwiseModelSourceOne
        X U hnonempty hcover hU h D E i j ⟶
      localLineBundlePairwiseModelSourceTwo
        X U hnonempty hcover hU h D E i j :=
  (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j).hom

/-- The chart-two addition map pulled to the pairwise model. -/
private noncomputable def localLineBundlePairwiseRightPulledAddHom
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    localLineBundlePairwiseModelSourceTwo
        X U hnonempty hcover hU h D E i j ⟶
      localLineBundlePairwiseModelTargetTwo
        X U hnonempty hcover hU h D E i j := by
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  exact (Scheme.Modules.pullback p₂).map
    (localLineBundleAddIso X (U j) (hU j) (h j) D E).hom

/-- The chart-one pulled addition followed by the inverse pullback tensorator. -/
private noncomputable def localLineBundlePairwiseCoreLeftHom
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    localLineBundlePairwiseModelSourceOne
        X U hnonempty hcover hU h D E i j ⟶
      localLineBundlePairwiseCoreTargetOne
        X U hnonempty hcover hU h D E i j := by
  letI := hnonempty i
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let PB₁ := Scheme.Modules.pullback p₁
  letI : PB₁.Monoidal := Scheme.Modules.pullbackMonoidal p₁
  let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
  let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
  exact localLineBundlePairwiseLeftPulledAddHom
      X U hnonempty hcover hU h D E i j ≫
    (Functor.Monoidal.μIso PB₁ L₁D L₁E).inv

/-- The tensor of the two factor transitions on the pairwise model. -/
private noncomputable def localLineBundlePairwiseCoreTensorHom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    localLineBundlePairwiseCoreTargetOne
        X U hnonempty hcover hU h D E i j ⟶
      localLineBundlePairwiseCoreTargetTwo
        X U hnonempty hcover hU h D E i j :=
  (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j ⊗ᵢ
    localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h E i j).hom

/-- The chart-two pulled addition followed by the inverse pullback tensorator. -/
private noncomputable def localLineBundlePairwiseCoreRightHom
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    localLineBundlePairwiseModelSourceTwo
        X U hnonempty hcover hU h D E i j ⟶
      localLineBundlePairwiseCoreTargetTwo
        X U hnonempty hcover hU h D E i j := by
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  let PB₂ := Scheme.Modules.pullback p₂
  letI : PB₂.Monoidal := Scheme.Modules.pullbackMonoidal p₂
  let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
  let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
  exact localLineBundlePairwiseRightPulledAddHom
      X U hnonempty hcover hU h D E i j ≫
    (Functor.Monoidal.μIso PB₂ L₂D L₂E).inv

/-- The cached core square before restoring the outer pullback tensorators. -/
private noncomputable def localLineBundlePairwiseCoreDiagram
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    SquareDiagram ((Spec (.of Γ(X, U i ⊓ U j))).Modules) := by
  let source₁ := localLineBundlePairwiseModelSourceOne
    X U hnonempty hcover hU h D E i j
  let target₁ := localLineBundlePairwiseCoreTargetOne
    X U hnonempty hcover hU h D E i j
  let source₂ := localLineBundlePairwiseModelSourceTwo
    X U hnonempty hcover hU h D E i j
  let target₂ := localLineBundlePairwiseCoreTargetTwo
    X U hnonempty hcover hU h D E i j
  exact {
    source₁ := source₁
    target₁ := target₁
    source₂ := source₂
    target₂ := target₂
    a := localLineBundlePairwiseCoreLeftHom
      X U hnonempty hcover hU h D E i j
    t := localLineBundlePairwiseCoreTensorHom
      K X f U hnonempty hcover hU h D E i j
    s := localLineBundlePairwiseSumModelHom
      K X f U hnonempty hcover hU h D E i j
    b := localLineBundlePairwiseCoreRightHom
      X U hnonempty hcover hU h D E i j }

/-- The four cached arrows of the addition square on the pairwise pullback model. -/
private noncomputable def localLineBundlePairwiseModelDiagram
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    SquareDiagram ((Spec (.of Γ(X, U i ⊓ U j))).Modules) := by
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let source₁ := localLineBundlePairwiseModelSourceOne
    X U hnonempty hcover hU h D E i j
  let target₁ := localLineBundlePairwiseModelTargetOne
    X U hnonempty hcover hU h D E i j
  let source₂ := localLineBundlePairwiseModelSourceTwo
    X U hnonempty hcover hU h D E i j
  let target₂ := localLineBundlePairwiseModelTargetTwo
    X U hnonempty hcover hU h D E i j
  let a := localLineBundlePairwiseLeftPulledAddHom
    X U hnonempty hcover hU h D E i j
  let t := localLineBundlePairwiseTensorModelHom
    K X f U hnonempty hcover hU h D E i j
  let s := localLineBundlePairwiseSumModelHom
    K X f U hnonempty hcover hU h D E i j
  let b := localLineBundlePairwiseRightPulledAddHom
    X U hnonempty hcover hU h D E i j
  exact {
    source₁ := source₁
    target₁ := target₁
    source₂ := source₂
    target₂ := target₂
    a := a
    t := t
    s := s
    b := b }

/-- The core pairwise-model square before restoring the two outer pullback tensorators. -/
private theorem localLineBundleAddIso_pairwisePullbackModelCore_naturality
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    SquareDiagram.IsComm
      (localLineBundlePairwiseCoreDiagram
        K X f U hnonempty hcover hU h D E i j) := by
  refine ⟨?_⟩
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI : Nonempty W := nonempty_inf_of_isIntegral X (U i) (U j)
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hW : IsAffineOpen W := (hU i).inf (hU j)
  letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  letI : Module.IsTorsionFree Γ(X, U i) Γ(X, W) :=
    restrictionTorsionFree X (U i) W inf_le_left
  letI : Module.IsTorsionFree Γ(X, U j) Γ(X, W) :=
    restrictionTorsionFree X (U j) W inf_le_right
  letI : IsFractionRing Γ(X, U i) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U i) (hU i)
  letI : IsFractionRing Γ(X, U j) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U j) (hU j)
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  letI : IsOpenImmersion p₁ :=
    restrictionExtensionMapIsOpenImmersion X (U i) W (hU i) hW inf_le_left
  letI : IsOpenImmersion p₂ :=
    restrictionExtensionMapIsOpenImmersion X (U j) W (hU j) hW inf_le_right
  let F₁ := Scheme.Modules.restrictFunctor p₁
  let F₂ := Scheme.Modules.restrictFunctor p₂
  let PB₁ := Scheme.Modules.pullback p₁
  let PB₂ := Scheme.Modules.pullback p₂
  let q₁ := Scheme.Modules.restrictFunctorIsoPullback p₁
  let q₂ := Scheme.Modules.restrictFunctorIsoPullback p₂
  letI : PB₁.Monoidal := Scheme.Modules.pullbackMonoidal p₁
  letI : PB₂.Monoidal := Scheme.Modules.pullbackMonoidal p₂
  let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
  let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
  let L₁S := (localLineBundles X U hnonempty hcover hU h (D + E) i).obj
  let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
  let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
  let L₂S := (localLineBundles X U hnonempty hcover hU h (D + E) j).obj
  let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
  let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
  let κ₁ := restrictionTensorIsoViaPullback p₁ L₁D L₁E
  let κ₂ := restrictionTensorIsoViaPullback p₂ L₂D L₂E
  let A₁ := F₁.mapIso add₁ ≪≫ κ₁
  let A₂ := F₂.mapIso add₂ ≪≫ κ₂
  let a₁ := PB₁.mapIso add₁ ≪≫ (Functor.Monoidal.μIso PB₁ L₁D L₁E).symm
  let a₂ := PB₂.mapIso add₂ ≪≫ (Functor.Monoidal.μIso PB₂ L₂D L₂E).symm
  let tD := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right (h i) (h j) D
  let tE := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right (h i) (h j) E
  let tDE := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right
      (h i) (h j) (D + E)
  let eD := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j
  let eE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h E i j
  let eDE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  let eP := eD ⊗ᵢ eE
  let q₁P := q₁.app L₁D ⊗ᵢ q₁.app L₁E
  let q₂P := q₂.app L₂D ⊗ᵢ q₂.app L₂E
  have hA₁ := restrictionTensorIsoViaPullback_conjugacy
    p₁ L₁S L₁D L₁E add₁
  dsimp only at hA₁
  change A₁.hom ≫ q₁P.hom = (q₁.app L₁S).hom ≫ a₁.hom at hA₁
  have hA₂ := restrictionTensorIsoViaPullback_conjugacy
    p₂ L₂S L₂D L₂E add₂
  dsimp only at hA₂
  change A₂.hom ≫ q₂P.hom = (q₂.app L₂S).hom ≫ a₂.hom at hA₂
  have hP := localLineBundlePairwiseTensorOverlapModelIso_conjugacy
    K X f U hnonempty hcover hU h D E i j
  dsimp only at hP
  change q₁P.hom ≫ eP.hom = (tD ⊗ᵢ tE).hom ≫ q₂P.hom at hP
  have hDE := localLineBundlePairwiseOverlapModelIso_conjugacy
    K X f U hnonempty hcover hU h (D + E) i j
  dsimp only at hDE
  change (q₁.app L₁S).hom ≫ eDE.hom = tDE.hom ≫ (q₂.app L₂S).hom at hDE
  have hGlobal := localLineBundleAddIso_restrictViaPullback_naturalityViaPairwiseIntersection_global
    K X f (U i) (U j) W (hU i) (hU j) hW inf_le_left inf_le_right
      (h i) (h j) D E
  dsimp only at hGlobal
  change A₁ ≪≫ (tD ⊗ᵢ tE) = tDE ≪≫ A₂ at hGlobal
  have hGlobalHom := congrArg Iso.hom hGlobal
  change A₁.hom ≫ (tD ⊗ᵢ tE).hom = tDE.hom ≫ A₂.hom at hGlobalHom
  have hFactor := hom_square_of_conjugacies
    A₁.hom (tD ⊗ᵢ tE).hom tDE.hom A₂.hom
    (q₁.app L₁S) q₁P (q₂.app L₂S) q₂P
    a₁.hom eP.hom eDE.hom a₂.hom hA₁ hP hDE hA₂ hGlobalHom
  unfold localLineBundlePairwiseCoreDiagram
  dsimp only
  change a₁.hom ≫ eP.hom = eDE.hom ≫ a₂.hom
  exact hFactor

/-- The checked restriction square, rewritten on the explicit pullback model of the pairwise
intersection.  The tensor transition is conjugated by the two model pullback tensorators. -/
private theorem localLineBundleAddIso_pairwisePullbackModel_naturality
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) (i j : I) :
    SquareDiagram.IsComm
      (localLineBundlePairwiseModelDiagram
        K X f U hnonempty hcover hU h D E i j) := by
  refine ⟨?_⟩
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  let PB₁ := Scheme.Modules.pullback p₁
  let PB₂ := Scheme.Modules.pullback p₂
  letI : PB₁.Monoidal := Scheme.Modules.pullbackMonoidal p₁
  letI : PB₂.Monoidal := Scheme.Modules.pullbackMonoidal p₂
  let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
  let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
  let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
  let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
  let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
  let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
  let eD := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j
  let eE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h E i j
  let eDE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  let eP := eD ⊗ᵢ eE
  let μ₁ := Functor.Monoidal.μIso PB₁ L₁D L₁E
  let μ₂ := Functor.Monoidal.μIso PB₂ L₂D L₂E
  have hCore := (localLineBundleAddIso_pairwisePullbackModelCore_naturality
    K X f U hnonempty hcover hU h D E i j).out
  unfold localLineBundlePairwiseCoreDiagram at hCore
  change (PB₁.mapIso add₁ ≪≫ μ₁.symm).hom ≫ eP.hom =
    eDE.hom ≫ (PB₂.mapIso add₂ ≪≫ μ₂.symm).hom at hCore
  unfold localLineBundlePairwiseModelDiagram
  dsimp only
  change PB₁.map add₁.hom ≫ (μ₁.symm ≪≫ eP ≪≫ μ₂).hom =
    eDE.hom ≫ PB₂.map add₂.hom
  apply hom_square_restore_target_tensorator
    (PB₁.mapIso add₁) μ₁ eP eDE (PB₂.mapIso add₂) μ₂
  exact hCore

/-- The pairwise-model square with its cached diagram projected to the exact Hom equation used
by chosen-pullback transport. -/
private theorem localLineBundleAddIso_pairwisePullbackModel_hom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    letI := hnonempty i
    letI := hnonempty j
    let W := U i ⊓ U j
    letI := restrictionAlgebra X (U i) W inf_le_left
    letI := restrictionAlgebra X (U j) W inf_le_right
    let p₁ := extensionMap Γ(X, U i) Γ(X, W)
    let p₂ := extensionMap Γ(X, U j) Γ(X, W)
    let PB₁ := Scheme.Modules.pullback p₁
    let PB₂ := Scheme.Modules.pullback p₂
    letI : PB₁.Monoidal := Scheme.Modules.pullbackMonoidal p₁
    letI : PB₂.Monoidal := Scheme.Modules.pullbackMonoidal p₂
    let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
    let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
    let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
    let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
    let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
    let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
    let eD := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j
    let eE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h E i j
    let eDE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E) i j
    let eTensor := (Functor.Monoidal.μIso PB₁ L₁D L₁E).symm ≪≫
      (eD ⊗ᵢ eE) ≪≫ Functor.Monoidal.μIso PB₂ L₂D L₂E
    PB₁.map add₁.hom ≫ eTensor.hom =
      eDE.hom ≫ PB₂.map add₂.hom := by
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI : Nonempty W := nonempty_inf_of_isIntegral X (U i) (U j)
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hW : IsAffineOpen W := (hU i).inf (hU j)
  letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  letI : Module.IsTorsionFree Γ(X, U i) Γ(X, W) :=
    restrictionTorsionFree X (U i) W inf_le_left
  letI : Module.IsTorsionFree Γ(X, U j) Γ(X, W) :=
    restrictionTorsionFree X (U j) W inf_le_right
  letI : IsFractionRing Γ(X, U i) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U i) (hU i)
  letI : IsFractionRing Γ(X, U j) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U j) (hU j)
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  letI : IsOpenImmersion p₁ :=
    restrictionExtensionMapIsOpenImmersion X (U i) W (hU i) hW inf_le_left
  letI : IsOpenImmersion p₂ :=
    restrictionExtensionMapIsOpenImmersion X (U j) W (hU j) hW inf_le_right
  let PB₁ := Scheme.Modules.pullback p₁
  let PB₂ := Scheme.Modules.pullback p₂
  letI : PB₁.Monoidal := Scheme.Modules.pullbackMonoidal p₁
  letI : PB₂.Monoidal := Scheme.Modules.pullbackMonoidal p₂
  let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
  let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
  let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
  let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
  let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
  let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
  let eD := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j
  let eE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h E i j
  let eDE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  let eTensor := (Functor.Monoidal.μIso PB₁ L₁D L₁E).symm ≪≫
    (eD ⊗ᵢ eE) ≪≫ Functor.Monoidal.μIso PB₂ L₂D L₂E
  have hModel := (localLineBundleAddIso_pairwisePullbackModel_naturality
    K X f U hnonempty hcover hU h D E i j).out
  unfold localLineBundlePairwiseModelDiagram at hModel
  change PB₁.map add₁.hom ≫ eTensor.hom =
    eDE.hom ≫ PB₂.map add₂.hom at hModel
  dsimp only
  change PB₁.map add₁.hom ≫ eTensor.hom =
    eDE.hom ≫ PB₂.map add₂.hom
  exact hModel

/-- The chosen-overlap Hom obtained from the pairwise model for one divisor, kept in exact
pseudofunctor heads. -/
private noncomputable def localLineBundleChosenModelPseudoHom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (G : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (LineBundleDescent.modulesPseudofunctor.map
      (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₁.op.toLoc).toFunctor.obj
        (localLineBundles X U hnonempty hcover hU h G i).obj ⟶
      (LineBundleDescent.modulesPseudofunctor.map
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₂.op.toLoc).toFunctor.obj
          (localLineBundles X U hnonempty hcover hU h G j).obj := by
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  let e := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h G i j
  let hpb := properCurveIntersectionSpectrumIsPullback
    K X f (U i) (U j) (hU i) (hU j)
  exact pullbackOverlapHomOfModelPseudo
    (hU i).fromSpec (hU j).fromSpec
    (extensionMap Γ(X, U i) Γ(X, U i ⊓ U j))
    (extensionMap Γ(X, U j) Γ(X, U i ⊓ U j)) hpb
    (localLineBundles X U hnonempty hcover hU h G i).obj
    (localLineBundles X U hnonempty hcover hU h G j).obj e

/-- The chartwise tensor object, cached with its Scheme-module category visible. -/
private noncomputable def localLineBundleChartTensorObject
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    ((coordinateCover U hcover hU).X i).Modules := by
  letI := Scheme.Modules.monoidalCategory ((coordinateCover U hcover hU).X i)
  exact (localLineBundles X U hnonempty hcover hU h D i).obj ⊗
    (localLineBundles X U hnonempty hcover hU h E i).obj

/-- The chartwise addition Hom with its tensor target kept behind the cached chart object. -/
private noncomputable def localLineBundleChartAddHom
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    (localLineBundles X U hnonempty hcover hU h (D + E) i).obj ⟶
      localLineBundleChartTensorObject X U hnonempty hcover hU h D E i := by
  letI := hnonempty i
  letI := Scheme.Modules.monoidalCategory ((coordinateCover U hcover hU).X i)
  exact (localLineBundleAddIso X (U i) (hU i) (h i) D E).hom

/-- The chosen-overlap isomorphism obtained by transporting the whole pairwise-intersection
tensor model.  This packages the transported two-factor comparison; it does not identify it
with the tensor of the two separately transported chosen-overlap transitions. -/
noncomputable def localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    (Scheme.Modules.pullback P.p₁).obj
        ((localLineBundles X U hnonempty hcover hU h D i).obj ⊗
          (localLineBundles X U hnonempty hcover hU h E i).obj) ≅
      (Scheme.Modules.pullback P.p₂).obj
        ((localLineBundles X U hnonempty hcover hU h D j).obj ⊗
          (localLineBundles X U hnonempty hcover hU h E j).obj) := by
  letI := hnonempty i
  letI := hnonempty j
  letI := Scheme.Modules.monoidalCategory ((coordinateCover U hcover hU).X i)
  letI := Scheme.Modules.monoidalCategory ((coordinateCover U hcover hU).X j)
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  let PB₁ := Scheme.Modules.pullback p₁
  let PB₂ := Scheme.Modules.pullback p₂
  letI : PB₁.Monoidal := Scheme.Modules.pullbackMonoidal p₁
  letI : PB₂.Monoidal := Scheme.Modules.pullbackMonoidal p₂
  let L₁D := (localLineBundles X U hnonempty hcover hU h D i).obj
  let L₁E := (localLineBundles X U hnonempty hcover hU h E i).obj
  let L₂D := (localLineBundles X U hnonempty hcover hU h D j).obj
  let L₂E := (localLineBundles X U hnonempty hcover hU h E j).obj
  let eTensor := localLineBundlePairwiseTensorModelIso
    K X f U hnonempty hcover hU h D E i j
  exact LineBundleDescent.pullbackOverlapIsoOfModel
    (hU i).fromSpec (hU j).fromSpec p₁ p₂
    (properCurveIntersectionSpectrumIsPullback
      K X f (U i) (U j) (hU i) (hU j))
    (L₁D ⊗ L₁E) (L₂D ⊗ L₂E) eTensor

/-- The whole tensor-model transition transported to the chosen overlap in exact pseudofunctor
heads. -/
private noncomputable def localLineBundlePairwiseTensorModelPseudoHom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (LineBundleDescent.modulesPseudofunctor.map
      (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₁.op.toLoc).toFunctor.obj
        (localLineBundleChartTensorObject
          X U hnonempty hcover hU h D E i) ⟶
      (LineBundleDescent.modulesPseudofunctor.map
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p₂.op.toLoc).toFunctor.obj
          (localLineBundleChartTensorObject
            X U hnonempty hcover hU h D E j) := by
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let eTensor := localLineBundlePairwiseTensorModelIso
    K X f U hnonempty hcover hU h D E i j
  let hpb := properCurveIntersectionSpectrumIsPullback
    K X f (U i) (U j) (hU i) (hU j)
  exact pullbackOverlapHomOfModelPseudo
    (hU i).fromSpec (hU j).fromSpec
    (extensionMap Γ(X, U i) Γ(X, W))
    (extensionMap Γ(X, U j) Γ(X, W)) hpb
    (localLineBundleChartTensorObject X U hnonempty hcover hU h D E i)
    (localLineBundleChartTensorObject X U hnonempty hcover hU h D E j) eTensor

/-- The chosen tensor-model Iso has the specialized exact-pseudofunctor Hom. -/
private theorem localLineBundlePairwiseTensorModelIso_hom_eq_pseudo
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    letI := hnonempty i
    letI := hnonempty j
    let W := U i ⊓ U j
    letI := restrictionAlgebra X (U i) W inf_le_left
    letI := restrictionAlgebra X (U j) W inf_le_right
    let eTensor := localLineBundlePairwiseTensorModelIso
      K X f U hnonempty hcover hU h D E i j
    (LineBundleDescent.pullbackOverlapIsoOfModel
      (hU i).fromSpec (hU j).fromSpec
      (extensionMap Γ(X, U i) Γ(X, W))
      (extensionMap Γ(X, U j) Γ(X, W))
      (properCurveIntersectionSpectrumIsPullback
        K X f (U i) (U j) (hU i) (hU j))
      (localLineBundleChartTensorObject X U hnonempty hcover hU h D E i)
      (localLineBundleChartTensorObject X U hnonempty hcover hU h D E j) eTensor).hom =
        localLineBundlePairwiseTensorModelPseudoHom
          K X f U hnonempty hcover hU h D E i j := by
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  dsimp only
  unfold localLineBundlePairwiseTensorModelPseudoHom
  exact pullbackOverlapIsoOfModel_hom_eq_pseudo
    (hU i).fromSpec (hU j).fromSpec
    (extensionMap Γ(X, U i) Γ(X, U i ⊓ U j))
    (extensionMap Γ(X, U j) Γ(X, U i ⊓ U j))
    (properCurveIntersectionSpectrumIsPullback
      K X f (U i) (U j) (hU i) (hU j))
    (localLineBundleChartTensorObject X U hnonempty hcover hU h D E i)
    (localLineBundleChartTensorObject X U hnonempty hcover hU h D E j)
    (localLineBundlePairwiseTensorModelIso
      K X f U hnonempty hcover hU h D E i j)

/-- The public transported tensor-model Iso has the cached exact-pseudofunctor Hom. -/
private theorem
    localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve_hom_eq_pseudo
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E i j).hom =
        localLineBundlePairwiseTensorModelPseudoHom
          K X f U hnonempty hcover hU h D E i j := by
  letI := hnonempty i
  letI := hnonempty j
  letI := Scheme.Modules.monoidalCategory ((coordinateCover U hcover hU).X i)
  letI := Scheme.Modules.monoidalCategory ((coordinateCover U hcover hU).X j)
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  unfold localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
  exact localLineBundlePairwiseTensorModelIso_hom_eq_pseudo
    K X f U hnonempty hcover hU h D E i j

/-- The opaque raw overlap family has the specialized exact-pseudofunctor model Hom. -/
private theorem localLineBundleRawOverlapIsoFamily_hom_eq_pseudo
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (G : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h G i j).hom =
      localLineBundleChosenModelPseudoHom
        K X f U hnonempty hcover hU h G i j := by
  rw [localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve_def]
  rw [localLineBundleChosenOverlapIsoOnProperSmoothCurve_hom]
  unfold localLineBundleChosenModelPseudoHom
  unfold pullbackOverlapHomOfModelPseudo
  exact localLineBundleChosenOverlapHomOnProperSmoothCurve_eq_model
    K X f U hnonempty hcover hU h G i j

/-- The pairwise-intersection tensor/addition square normalized to exact pseudofunctor maps. -/
private theorem localLineBundleAddIso_pairwisePullbackModel_pseudo_hom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    letI := hnonempty i
    letI := hnonempty j
    let W := U i ⊓ U j
    letI := restrictionAlgebra X (U i) W inf_le_left
    letI := restrictionAlgebra X (U j) W inf_le_right
    let p₁ := extensionMap Γ(X, U i) Γ(X, W)
    let p₂ := extensionMap Γ(X, U j) Γ(X, W)
    let eDE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E) i j
    let eTensor := localLineBundlePairwiseTensorModelIso
      K X f U hnonempty hcover hU h D E i j
    (LineBundleDescent.modulesPseudofunctor.map p₁.op.toLoc).toFunctor.map
          (localLineBundleChartAddHom X U hnonempty hcover hU h D E i) ≫
        eTensor.hom =
      eDE.hom ≫
        (LineBundleDescent.modulesPseudofunctor.map p₂.op.toLoc).toFunctor.map
          (localLineBundleChartAddHom X U hnonempty hcover hU h D E j) := by
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  have hModel := localLineBundleAddIso_pairwisePullbackModel_hom
    K X f U hnonempty hcover hU h D E i j
  dsimp only at hModel
  dsimp only
  unfold localLineBundleChartAddHom
  have hMap₁ := modulesPseudofunctor_map_map_eq_pullback_map
    (extensionMap Γ(X, U i) Γ(X, U i ⊓ U j))
    (localLineBundleAddIso X (U i) (hU i) (h i) D E).hom
  have hMap₂ := modulesPseudofunctor_map_map_eq_pullback_map
    (extensionMap Γ(X, U j) Γ(X, U i ⊓ U j))
    (localLineBundleAddIso X (U j) (hU j) (h j) D E).hom
  have hLeft := congrArg
    (fun z ↦ z ≫
      (localLineBundlePairwiseTensorModelIso
        K X f U hnonempty hcover hU h D E i j).hom) hMap₁
  have hRight := congrArg
    (fun z ↦
      (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E) i j).hom ≫ z) hMap₂.symm
  exact hLeft.trans (hModel.trans hRight)

/-- The four exact-pseudofunctor arrows of the chosen-overlap tensor/addition square. -/
private noncomputable def localLineBundleChosenPseudoDiagram
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let f₁ := (hU i).fromSpec
    let f₂ := (hU j).fromSpec
    SquareDiagram
      (LineBundleDescent.modulesPseudofunctor.obj
        (.mk (.op (pullback f₁ f₂)))) := by
  let f₁ := (hU i).fromSpec
  let f₂ := (hU j).fromSpec
  let F₁ := (LineBundleDescent.modulesPseudofunctor.map
    (pullback.fst f₁ f₂).op.toLoc).toFunctor
  let F₂ := (LineBundleDescent.modulesPseudofunctor.map
    (pullback.snd f₁ f₂).op.toLoc).toFunctor
  exact {
    source₁ := F₁.obj (localLineBundles X U hnonempty hcover hU h (D + E) i).obj
    target₁ := F₁.obj (localLineBundleChartTensorObject
      X U hnonempty hcover hU h D E i)
    source₂ := F₂.obj (localLineBundles X U hnonempty hcover hU h (D + E) j).obj
    target₂ := F₂.obj (localLineBundleChartTensorObject
      X U hnonempty hcover hU h D E j)
    a := F₁.map (localLineBundleChartAddHom X U hnonempty hcover hU h D E i)
    t := localLineBundlePairwiseTensorModelPseudoHom
      K X f U hnonempty hcover hU h D E i j
    s := localLineBundleChosenModelPseudoHom
      K X f U hnonempty hcover hU h (D + E) i j
    b := F₂.map (localLineBundleChartAddHom X U hnonempty hcover hU h D E j) }

/-- The chosen-overlap tensor/addition square in exact pseudofunctor heads. -/
private theorem localLineBundleAddIso_chosenOverlap_commViaTransportedTensorModel_pseudo
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let f₁ := (hU i).fromSpec
    let f₂ := (hU j).fromSpec
    @SquareDiagram.IsComm
      (LineBundleDescent.modulesPseudofunctor.obj
        (.mk (.op (pullback f₁ f₂))))
      (by infer_instance)
      (localLineBundleChosenPseudoDiagram
        K X f U hnonempty hcover hU h D E i j) := by
  refine ⟨?_⟩
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  let add₁ := localLineBundleChartAddHom X U hnonempty hcover hU h D E i
  let add₂ := localLineBundleChartAddHom X U hnonempty hcover hU h D E j
  let eDE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  let eTensor := localLineBundlePairwiseTensorModelIso
    K X f U hnonempty hcover hU h D E i j
  let f₁ := (hU i).fromSpec
  let f₂ := (hU j).fromSpec
  let hpb := properCurveIntersectionSpectrumIsPullback
    K X f (U i) (U j) (hU i) (hU j)
  have hModel := localLineBundleAddIso_pairwisePullbackModel_pseudo_hom
    K X f U hnonempty hcover hU h D E i j
  dsimp only at hModel
  unfold localLineBundleChosenPseudoDiagram
  dsimp only
  let tensorDirect := pullbackOverlapHomOfModelPseudo
    f₁ f₂ p₁ p₂ hpb
    (localLineBundleChartTensorObject X U hnonempty hcover hU h D E i)
    (localLineBundleChartTensorObject X U hnonempty hcover hU h D E j) eTensor
  let sumDirect := pullbackOverlapHomOfModelPseudo
    f₁ f₂ p₁ p₂ hpb
    (localLineBundles X U hnonempty hcover hU h (D + E) i).obj
    (localLineBundles X U hnonempty hcover hU h (D + E) j).obj eDE
  have hNat := pullbackOverlapHomOfModelPseudo_naturality
    f₁ f₂ p₁ p₂ hpb add₁ add₂ eDE eTensor hModel
  have hTensor :
      localLineBundlePairwiseTensorModelPseudoHom
          K X f U hnonempty hcover hU h D E i j = tensorDirect := by
    rfl
  have hSum :
      localLineBundleChosenModelPseudoHom
          K X f U hnonempty hcover hU h (D + E) i j = sumDirect := by
    rfl
  have hLeft := congrArg
    (fun z ↦
      (LineBundleDescent.modulesPseudofunctor.map
        (pullback.fst f₁ f₂).op.toLoc).toFunctor.map add₁ ≫ z) hTensor
  have hRight := congrArg
    (fun z ↦ z ≫
      (LineBundleDescent.modulesPseudofunctor.map
        (pullback.snd f₁ f₂).op.toLoc).toFunctor.map add₂) hSum.symm
  exact hLeft.trans (hNat.trans hRight)

/-- On Mathlib's chosen overlap, the two local addition maps commute with the transition
obtained by transporting the whole tensor-product model comparison.  This is the Hom equation
needed by a descent-data morphism; identifying this whole transported comparison with the
tensor of the two separately transported factor transitions is a further coherence statement. -/
theorem localLineBundleAddIso_chosenOverlap_commViaTransportedTensorModel
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    letI := hnonempty i
    letI := hnonempty j
    let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
    let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
    let tensorTransition :=
      localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
        K X f U hnonempty hcover hU h D E i j
    let sumTransition := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E) i j
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    (Scheme.Modules.pullback P.p₁).map add₁.hom ≫ tensorTransition.hom =
      sumTransition.hom ≫ (Scheme.Modules.pullback P.p₂).map add₂.hom := by
  letI := hnonempty i
  letI := hnonempty j
  let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
  let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
  let tensorTransition :=
    localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E i j
  let sumTransition := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
  let tensorPseudo := localLineBundlePairwiseTensorModelPseudoHom
    K X f U hnonempty hcover hU h D E i j
  let sumPseudo := localLineBundleChosenModelPseudoHom
    K X f U hnonempty hcover hU h (D + E) i j
  have hPseudo :=
    (localLineBundleAddIso_chosenOverlap_commViaTransportedTensorModel_pseudo
      K X f U hnonempty hcover hU h D E i j).out
  unfold localLineBundleChosenPseudoDiagram at hPseudo
  dsimp only at hPseudo
  unfold localLineBundleChartAddHom at hPseudo
  change
    (LineBundleDescent.modulesPseudofunctor.map P.p₁.op.toLoc).toFunctor.map
          add₁.hom ≫ tensorPseudo =
      sumPseudo ≫
        (LineBundleDescent.modulesPseudofunctor.map P.p₂.op.toLoc).toFunctor.map
          add₂.hom at hPseudo
  have hTensor :=
    localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve_hom_eq_pseudo
    K X f U hnonempty hcover hU h D E i j
  change tensorTransition.hom = tensorPseudo at hTensor
  have hSum := localLineBundleRawOverlapIsoFamily_hom_eq_pseudo
    K X f U hnonempty hcover hU h (D + E) i j
  change sumTransition.hom = sumPseudo at hSum
  dsimp only
  change (Scheme.Modules.pullback P.p₁).map add₁.hom ≫ tensorTransition.hom =
    sumTransition.hom ≫ (Scheme.Modules.pullback P.p₂).map add₂.hom
  rw [hTensor, hSum]
  have hMap₁ := modulesPseudofunctor_map_map_eq_pullback_map P.p₁ add₁.hom
  have hMap₂ := modulesPseudofunctor_map_map_eq_pullback_map P.p₂ add₂.hom
  have hLeft := congrArg (fun z ↦ z ≫ tensorPseudo) hMap₁.symm
  have hRight := congrArg (fun z ↦ sumPseudo ≫ z) hMap₂
  exact hLeft.trans (hPseudo.trans hRight)

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
