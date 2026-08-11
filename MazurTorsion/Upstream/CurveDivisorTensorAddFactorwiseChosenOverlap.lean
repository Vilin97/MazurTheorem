/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.PullbackCompMonoidal
import MazurTorsion.Upstream.CurveDivisorTensorAddChosenOverlap

/-!
# Factorwise tensor addition on chosen curve overlaps

The canonical comparison from iterated pullback to pullback along a composite is monoidal.
Consequently, transporting a tensor-product model isomorphism to a chosen pullback agrees with
tensoring the two separately transported model isomorphisms, with the canonical pullback
tensorators at the endpoints.  The curve specialization identifies the whole tensor transition
constructed on the pairwise affine model with the tensor of the two raw divisor transitions and
then rewrites the checked local-addition square in that factorwise form.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry

universe u v

@[reducible]
noncomputable local instance schemeModulesMonoidalForFactorwiseChosenOverlap
    (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

namespace LineBundleDescent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private noncomputable abbrev moduleFiber (Y : Scheme.{u}) :=
  modulesPseudofunctor.obj (.mk (.op Y))

private noncomputable abbrev modulePullback {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (modulesPseudofunctor.map g.op.toLoc).toFunctor

@[reducible]
noncomputable local instance moduleFiberMonoidalForFactorwiseChosenOverlap
    (Y : Scheme.{u}) : MonoidalCategory (moduleFiber Y) :=
  schemeModulesMonoidalForFactorwiseChosenOverlap Y

noncomputable local instance pullbackMonoidalForFactorwiseChosenOverlap
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (Scheme.Modules.pullback g).Monoidal :=
  Scheme.Modules.pullbackMonoidal g

@[reducible]
noncomputable local instance modulePullbackMonoidalForFactorwiseChosenOverlap
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (modulePullback g).Monoidal :=
  pullbackMonoidalForFactorwiseChosenOverlap g

/-- For exact composites, `pullIso` is the composite of the inverse pullback-composition
comparison, the mapped model isomorphism, and the forward pullback-composition comparison. -/
private theorem pullIso_comp_eq
    {X₁ X₂ Y Y' : Scheme.{u}}
    {M₁ : moduleFiber X₁} {M₂ : moduleFiber X₂}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (modulePullback f₁).obj M₁ ≅
      (modulePullback f₂).obj M₂)
    (g : Y' ⟶ Y) :
    pullIso (F := modulesPseudofunctor) e g (g ≫ f₁) (g ≫ f₂) rfl rfl =
      ((Scheme.Modules.pullbackComp g f₁).app M₁).symm ≪≫
        (Scheme.Modules.pullback g).mapIso e ≪≫
        (Scheme.Modules.pullbackComp g f₂).app M₂ := by
  rfl

/-- The scheme-module form of the monoidal pullback-composition calculation.  Keeping this
calculation out of the exact pseudofunctor presentation prevents elaboration from having to
match two definitionally equal presentations of the module fibre while rewriting tensorators. -/
private theorem pullbackComp_tensor_transport
    {X₁ X₂ Y Y' : Scheme.{u}}
    {M₁ N₁ : X₁.Modules} {M₂ N₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (eM : (Scheme.Modules.pullback f₁).obj M₁ ≅
      (Scheme.Modules.pullback f₂).obj M₂)
    (eN : (Scheme.Modules.pullback f₁).obj N₁ ≅
      (Scheme.Modules.pullback f₂).obj N₂)
    (g : Y' ⟶ Y) :
    ((Scheme.Modules.pullbackComp g f₁).app (M₁ ⊗ N₁)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          ((Functor.Monoidal.μIso (Scheme.Modules.pullback f₁) M₁ N₁).symm ≪≫
            (eM ⊗ᵢ eN) ≪≫
            Functor.Monoidal.μIso (Scheme.Modules.pullback f₂) M₂ N₂) ≪≫
        (Scheme.Modules.pullbackComp g f₂).app (M₂ ⊗ N₂) =
      (Functor.Monoidal.μIso
          (Scheme.Modules.pullback (g ≫ f₁)) M₁ N₁).symm ≪≫
        ((((Scheme.Modules.pullbackComp g f₁).app M₁).symm ≪≫
              (Scheme.Modules.pullback g).mapIso eM ≪≫
              (Scheme.Modules.pullbackComp g f₂).app M₂) ⊗ᵢ
          (((Scheme.Modules.pullbackComp g f₁).app N₁).symm ≪≫
              (Scheme.Modules.pullback g).mapIso eN ≪≫
              (Scheme.Modules.pullbackComp g f₂).app N₂)) ≪≫
        Functor.Monoidal.μIso
          (Scheme.Modules.pullback (g ≫ f₂)) M₂ N₂ := by
  letI hc₁ : (Scheme.Modules.pullbackComp g f₁).hom.IsMonoidal :=
    Scheme.Modules.pullbackComp_hom_isMonoidal g f₁
  letI hc₂ : (Scheme.Modules.pullbackComp g f₂).hom.IsMonoidal :=
    Scheme.Modules.pullbackComp_hom_isMonoidal g f₂
  letI hc₁inv : (Scheme.Modules.pullbackComp g f₁).inv.IsMonoidal := inferInstance
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorIso_hom]
  let μH₁ := Functor.Monoidal.μIso
    (Scheme.Modules.pullback (g ≫ f₁)) M₁ N₁
  let μH₂ := Functor.Monoidal.μIso
    (Scheme.Modules.pullback (g ≫ f₂)) M₂ N₂
  apply (cancel_epi μH₁.hom).1
  apply (cancel_mono μH₂.inv).1
  unfold μH₁ μH₂
  simp only [Category.assoc]
  change Functor.LaxMonoidal.μ
      (Scheme.Modules.pullback (g ≫ f₁)) M₁ N₁ ≫
      (Scheme.Modules.pullbackComp g f₁).inv.app (M₁ ⊗ N₁) ≫ _ = _
  rw [NatTrans.IsMonoidal.tensor_assoc
    (X := M₁) (Y := N₁) (self := hc₁inv)]
  rw [Functor.LaxMonoidal.comp_μ]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [Functor.Monoidal.μIso_inv (Scheme.Modules.pullback f₁) M₁ N₁]
  rw [← (Scheme.Modules.pullback g).map_comp_assoc,
    Functor.Monoidal.μ_δ,
    (Scheme.Modules.pullback g).map_id, Category.id_comp]
  rw [Functor.Monoidal.map_tensor]
  simp only [Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [← tensorHom_comp_tensorHom]
  simp only [Iso.app_hom]
  rw [Functor.Monoidal.μIso_hom (Scheme.Modules.pullback f₂) M₂ N₂]
  have hcompμ :
      Functor.LaxMonoidal.μ (Scheme.Modules.pullback g)
          ((Scheme.Modules.pullback f₂).obj M₂)
          ((Scheme.Modules.pullback f₂).obj N₂) ≫
        ((Scheme.Modules.pullback g).map
            (Functor.LaxMonoidal.μ (Scheme.Modules.pullback f₂) M₂ N₂) ≫
          (Scheme.Modules.pullbackComp g f₂).hom.app (M₂ ⊗ N₂) ≫
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (g ≫ f₂)) M₂ N₂).inv) =
        Functor.LaxMonoidal.μ
            (Scheme.Modules.pullback f₂ ⋙ Scheme.Modules.pullback g) M₂ N₂ ≫
          (Scheme.Modules.pullbackComp g f₂).hom.app (M₂ ⊗ N₂) ≫
          (Functor.Monoidal.μIso
            (Scheme.Modules.pullback (g ≫ f₂)) M₂ N₂).inv := by
    rw [← Category.assoc, ← Functor.LaxMonoidal.comp_μ]
  rw [hcompμ]
  rw [NatTrans.IsMonoidal.tensor_assoc
    (X := M₂) (Y := N₂) (self := hc₂)]
  simp only [Category.assoc]
  simp

/-- Pulling a tensor-model isomorphism along a further scheme map agrees with tensoring the
separately pulled factor isomorphisms. -/
private theorem pullIso_tensor
    {X₁ X₂ Y Y' : Scheme.{u}}
    {M₁ N₁ : X₁.Modules} {M₂ N₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (eM : (Scheme.Modules.pullback f₁).obj M₁ ≅
      (Scheme.Modules.pullback f₂).obj M₂)
    (eN : (Scheme.Modules.pullback f₁).obj N₁ ≅
      (Scheme.Modules.pullback f₂).obj N₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullIso (F := modulesPseudofunctor)
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback f₁) M₁ N₁).symm ≪≫
          (eM ⊗ᵢ eN) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback f₂) M₂ N₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (Functor.Monoidal.μIso (Scheme.Modules.pullback gf₁) M₁ N₁).symm ≪≫
        (pullIso (F := modulesPseudofunctor) eM
            g gf₁ gf₂ hgf₁ hgf₂ ⊗ᵢ
          pullIso (F := modulesPseudofunctor) eN
            g gf₁ gf₂ hgf₁ hgf₂) ≪≫
        Functor.Monoidal.μIso (Scheme.Modules.pullback gf₂) M₂ N₂ := by
  subst gf₁
  subst gf₂
  calc
    _ = ((Scheme.Modules.pullbackComp g f₁).app (M₁ ⊗ N₁)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          ((Functor.Monoidal.μIso (Scheme.Modules.pullback f₁) M₁ N₁).symm ≪≫
            (eM ⊗ᵢ eN) ≪≫
            Functor.Monoidal.μIso (Scheme.Modules.pullback f₂) M₂ N₂) ≪≫
        (Scheme.Modules.pullbackComp g f₂).app (M₂ ⊗ N₂) :=
      pullIso_comp_eq _ g
    _ = _ := by
      let tM := ((Scheme.Modules.pullbackComp g f₁).app M₁).symm ≪≫
        (Scheme.Modules.pullback g).mapIso eM ≪≫
        (Scheme.Modules.pullbackComp g f₂).app M₂
      let tN := ((Scheme.Modules.pullbackComp g f₁).app N₁).symm ≪≫
        (Scheme.Modules.pullback g).mapIso eN ≪≫
        (Scheme.Modules.pullbackComp g f₂).app N₂
      have hM : pullIso (F := modulesPseudofunctor) eM
          g (g ≫ f₁) (g ≫ f₂) rfl rfl = tM :=
        pullIso_comp_eq eM g
      have hN : pullIso (F := modulesPseudofunctor) eN
          g (g ≫ f₁) (g ≫ f₂) rfl rfl = tN :=
        pullIso_comp_eq eN g
      calc
        _ = (Functor.Monoidal.μIso
              (Scheme.Modules.pullback (g ≫ f₁)) M₁ N₁).symm ≪≫
            (tM ⊗ᵢ tN) ≪≫
            Functor.Monoidal.μIso
              (Scheme.Modules.pullback (g ≫ f₂)) M₂ N₂ :=
          pullbackComp_tensor_transport eM eN g
        _ = _ := congrArg
          (fun z ↦
            (Functor.Monoidal.μIso
              (Scheme.Modules.pullback (g ≫ f₁)) M₁ N₁).symm ≪≫
              z ≪≫
              Functor.Monoidal.μIso
                (Scheme.Modules.pullback (g ≫ f₂)) M₂ N₂)
          (congrArg₂ (fun a b ↦ a ⊗ᵢ b) hM.symm hN.symm)

/-- Transporting the tensor of two model transitions to a chosen pullback is the tensor of
the separately transported transitions, conjugated by the two chosen-pullback tensorators. -/
theorem pullbackOverlapIsoOfModel_tensor
    {S X₁ X₂ W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    (M₁ N₁ : X₁.Modules) (M₂ N₂ : X₂.Modules)
    (eM : (Scheme.Modules.pullback p₁).obj M₁ ≅
      (Scheme.Modules.pullback p₂).obj M₂)
    (eN : (Scheme.Modules.pullback p₁).obj N₁ ≅
      (Scheme.Modules.pullback p₂).obj N₂) :
    pullbackOverlapIsoOfModel f₁ f₂ p₁ p₂ hpb
        (M₁ ⊗ N₁) (M₂ ⊗ N₂)
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback p₁) M₁ N₁).symm ≪≫
          (eM ⊗ᵢ eN) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback p₂) M₂ N₂) =
      (Functor.Monoidal.μIso
          (Scheme.Modules.pullback (pullback.fst f₁ f₂)) M₁ N₁).symm ≪≫
        (pullbackOverlapIsoOfModel f₁ f₂ p₁ p₂ hpb M₁ M₂ eM ⊗ᵢ
          pullbackOverlapIsoOfModel f₁ f₂ p₁ p₂ hpb N₁ N₂ eN) ≪≫
        Functor.Monoidal.μIso
          (Scheme.Modules.pullback (pullback.snd f₁ f₂)) M₂ N₂ := by
  unfold pullbackOverlapIsoOfModel
  exact pullIso_tensor eM eN hpb.isoPullback.inv
    (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
    hpb.isoPullback_inv_fst hpb.isoPullback_inv_snd

end LineBundleDescent

namespace CurveDivisorDescent

@[reducible]
noncomputable local instance curveModulesPseudofunctorObjMonoidalForFactorwiseChosenOverlap
    (Y : Scheme.{u}) :
    MonoidalCategory (LineBundleDescent.modulesPseudofunctor.obj (.mk (.op Y))) :=
  schemeModulesMonoidalForFactorwiseChosenOverlap Y

noncomputable local instance curvePullbackMonoidalForFactorwiseChosenOverlap
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (Scheme.Modules.pullback g).Monoidal :=
  Scheme.Modules.pullbackMonoidal g

open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

/-- The chosen-overlap transition obtained by transporting the whole pairwise tensor model is
the tensor of the two raw divisor transitions, conjugated by the pullback tensorators. -/
theorem localLineBundleTensorChosenOverlapIsoOfPairwiseModel_eq_tensorRawOverlapIsoFamily
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
        K X f U hnonempty hcover hU h D E i j =
      (Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
          (localLineBundles X U hnonempty hcover hU h D i).obj
          (localLineBundles X U hnonempty hcover hU h E i).obj).symm ≪≫
        (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h D i j ⊗ᵢ
          localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h E i j) ≪≫
        Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
          (localLineBundles X U hnonempty hcover hU h D j).obj
          (localLineBundles X U hnonempty hcover hU h E j).obj := by
  letI := hnonempty i
  letI := hnonempty j
  let W := U i ⊓ U j
  letI := restrictionAlgebra X (U i) W inf_le_left
  letI := restrictionAlgebra X (U j) W inf_le_right
  let p₁ := extensionMap Γ(X, U i) Γ(X, W)
  let p₂ := extensionMap Γ(X, U j) Γ(X, W)
  let eD := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j
  let eE := localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h E i j
  rw [localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve_def,
    localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve_def]
  unfold localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
  exact LineBundleDescent.pullbackOverlapIsoOfModel_tensor
    (hU i).fromSpec (hU j).fromSpec p₁ p₂
    (properCurveIntersectionSpectrumIsPullback
      K X f (U i) (U j) (hU i) (hU j))
    (localLineBundles X U hnonempty hcover hU h D i).obj
    (localLineBundles X U hnonempty hcover hU h E i).obj
    (localLineBundles X U hnonempty hcover hU h D j).obj
    (localLineBundles X U hnonempty hcover hU h E j).obj eD eE

/-- The chosen-overlap local-addition square in factorwise form: its target transition is the
tensor of the two raw divisor transitions, conjugated by the endpoint pullback tensorators. -/
theorem localLineBundleAddIso_chosenOverlap_commViaFactorwiseRawTensor
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
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
    let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
    let rawD := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j
    let rawE := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h E i j
    let rawDE := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E) i j
    let μ₁ := Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
      (localLineBundles X U hnonempty hcover hU h D i).obj
      (localLineBundles X U hnonempty hcover hU h E i).obj
    let μ₂ := Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
      (localLineBundles X U hnonempty hcover hU h D j).obj
      (localLineBundles X U hnonempty hcover hU h E j).obj
    (Scheme.Modules.pullback P.p₁).map add₁.hom ≫
        (μ₁.symm ≪≫ (rawD ⊗ᵢ rawE) ≪≫ μ₂).hom =
      rawDE.hom ≫ (Scheme.Modules.pullback P.p₂).map add₂.hom := by
  letI := hnonempty i
  letI := hnonempty j
  let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
  let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
  let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
  let rawD := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j
  let rawE := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h E i j
  let rawDE := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  let μ₁ := Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
    (localLineBundles X U hnonempty hcover hU h D i).obj
    (localLineBundles X U hnonempty hcover hU h E i).obj
  let μ₂ := Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
    (localLineBundles X U hnonempty hcover hU h D j).obj
    (localLineBundles X U hnonempty hcover hU h E j).obj
  have hTensor :=
    localLineBundleTensorChosenOverlapIsoOfPairwiseModel_eq_tensorRawOverlapIsoFamily
      K X f U hnonempty hcover hU h D E i j
  have hComm := localLineBundleAddIso_chosenOverlap_commViaTransportedTensorModel
    K X f U hnonempty hcover hU h D E i j
  dsimp only at hTensor hComm ⊢
  rw [hTensor] at hComm
  exact hComm

end CurveDivisorDescent

end MazurTorsion.AlgebraicGeometry
