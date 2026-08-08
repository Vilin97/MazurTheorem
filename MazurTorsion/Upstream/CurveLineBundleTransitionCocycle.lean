/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleTripleTower

/-!
# Pullback coherence boundary for divisor transition maps

The inverse-ideal comparison underlying a pairwise divisor transition is already compatible with
scalar towers.  This file proves the surrounding pseudofunctorial composition statement: pulling
the pairwise model first to a common affine open and then to a test scheme agrees with pulling it
along the composite map.

It also exposes the independently constructed direct comparison on the common affine open.  The
affine inverse-ideal naturality theorem identifies this direct comparison with the pullback of the
pairwise model, giving an unconditional further-pullback theorem and the resulting cocycle law.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped AlgebraicGeometry

universe u u' v v'

private theorem modulesPseudofunctor_mapComp_hom_app
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : X.Modules) :
    (((LineBundleDescent.modulesPseudofunctor.mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans).app M) =
      (((Scheme.Modules.pullbackComp g f).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M).inv) := by
  subst gf
  rfl

private theorem modulesPseudofunctor_mapComp_inv_app
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : X.Modules) :
    (((LineBundleDescent.modulesPseudofunctor.mapComp'
        f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans).app M) =
      (((Scheme.Modules.pullbackComp g f).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M).hom) := by
  subst gf
  rfl

private theorem pullHom_eq_of_naturality
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (e' : (F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map gf₂.op.toLoc).toFunctor.obj M₂)
    (hnaturality :
      (F.map g.op.toLoc).toFunctor.map e ≫
          (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₂])).inv.toNatTrans.app M₂ =
        (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₁])).inv.toNatTrans.app M₁ ≫
          e') :
    pullHom e g gf₁ gf₂ hgf₁ hgf₂ = e' := by
  let iPull := F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)
  let iNat := F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₁])
  have hi : iPull = iNat := by rfl
  unfold pullHom
  rw [hnaturality]
  change iPull.hom.toNatTrans.app M₁ ≫ iNat.inv.toNatTrans.app M₁ ≫ e' = e'
  rw [← hi]
  simp [← reassoc_of% Cat.Hom₂.comp_app]

/-- The affine overlap naturality theorem in the `pullHom` language used by line-bundle descent. -/
theorem pullHom_chosenLineBundlePullbackIsoOfOverlapExtensionEq
    (R₁ R₂ B C K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [Module.IsTorsionFree R₁ B]
    [Algebra R₂ B] [Module.IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R₁ C] [Module.IsTorsionFree R₁ C]
    [Algebra R₂ C] [Module.IsTorsionFree R₂ C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R₁ B C] [IsScalarTower R₂ B C]
    [IsScalarTower B C K]
    [IsScalarTower R₁ B K] [IsScalarTower R₂ B K]
    [IsScalarTower R₁ C K] [IsScalarTower R₂ C K]
    [IsOpenImmersion (extensionMap R₁ B)]
    [IsOpenImmersion (extensionMap R₂ B)]
    [IsOpenImmersion (extensionMap R₁ C)]
    [IsOpenImmersion (extensionMap R₂ C)]
    [IsOpenImmersion (extensionMap B C)]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂)
    (hcomp₁ : extensionMap B C ≫ extensionMap R₁ B = extensionMap R₁ C)
    (hcomp₂ : extensionMap B C ≫ extensionMap R₂ B = extensionMap R₂ C) :
    let hC := overlapInverseIdealExtensionEq_baseChange
      R₁ R₂ B C K D₁ D₂ h
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (f₁ := extensionMap R₁ B) (f₂ := extensionMap R₂ B)
        (chosenLineBundlePullbackIsoOfOverlapExtensionEq
          R₁ R₂ B K D₁ D₂ h).hom
        (extensionMap B C) (extensionMap R₁ C) (extensionMap R₂ C)
        hcomp₁ hcomp₂ =
      (chosenLineBundlePullbackIsoOfOverlapExtensionEq
        R₁ R₂ C K D₁ D₂ hC).hom := by
  let hC := overlapInverseIdealExtensionEq_baseChange
    R₁ R₂ B C K D₁ D₂ h
  dsimp only
  refine pullHom_eq_of_naturality
    (F := LineBundleDescent.modulesPseudofunctor)
    (M₁ := (AffineDedekind.lineBundle R₁ K D₁).obj)
    (M₂ := (AffineDedekind.lineBundle R₂ K D₂).obj)
    (f₁ := extensionMap R₁ B) (f₂ := extensionMap R₂ B)
    (chosenLineBundlePullbackIsoOfOverlapExtensionEq
      R₁ R₂ B K D₁ D₂ h).hom
    (extensionMap B C) (extensionMap R₁ C) (extensionMap R₂ C)
    hcomp₁ hcomp₂
    (chosenLineBundlePullbackIsoOfOverlapExtensionEq
      R₁ R₂ C K D₁ D₂ hC).hom ?_
  have hn := chosenLineBundlePullbackIsoOfOverlapExtensionEq_naturality
    R₁ R₂ B C K D₁ D₂ h hcomp₁ hcomp₂
  have hm₁ := modulesPseudofunctor_mapComp_inv_app
    (extensionMap R₁ B) (extensionMap B C) (extensionMap R₁ C) hcomp₁
      (AffineDedekind.lineBundle R₁ K D₁).obj
  have hm₂ := modulesPseudofunctor_mapComp_inv_app
    (extensionMap R₂ B) (extensionMap B C) (extensionMap R₂ C) hcomp₂
      (AffineDedekind.lineBundle R₂ K D₂).obj
  have hc₁ :
      ((Scheme.Modules.pullbackComp
            (extensionMap B C) (extensionMap R₁ B)).app
          (AffineDedekind.lineBundle R₁ K D₁).obj ≪≫
        (Scheme.Modules.pullbackCongr hcomp₁).app
          (AffineDedekind.lineBundle R₁ K D₁).obj).hom =
        (chosenLineBundlePullbackCompIso R₁ B C K D₁ hcomp₁).hom := by
    rfl
  have hc₂ :
      ((Scheme.Modules.pullbackComp
            (extensionMap B C) (extensionMap R₂ B)).app
          (AffineDedekind.lineBundle R₂ K D₂).obj ≪≫
        (Scheme.Modules.pullbackCongr hcomp₂).app
          (AffineDedekind.lineBundle R₂ K D₂).obj).hom =
        (chosenLineBundlePullbackCompIso R₂ B C K D₂ hcomp₂).hom := by
    rfl
  have hpull :
      (LineBundleDescent.modulesPseudofunctor.map
          (extensionMap B C).op.toLoc).toFunctor.map
          (chosenLineBundlePullbackIsoOfOverlapExtensionEq
            R₁ R₂ B K D₁ D₂ h).hom =
        (Scheme.Modules.pullback (extensionMap B C)).map
          (chosenLineBundlePullbackIsoOfOverlapExtensionEq
            R₁ R₂ B K D₁ D₂ h).hom := by
    rfl
  let qP := (LineBundleDescent.modulesPseudofunctor.map
    (extensionMap B C).op.toLoc).toFunctor.map
      (chosenLineBundlePullbackIsoOfOverlapExtensionEq
        R₁ R₂ B K D₁ D₂ h).hom
  let qS := (Scheme.Modules.pullback (extensionMap B C)).map
    (chosenLineBundlePullbackIsoOfOverlapExtensionEq
      R₁ R₂ B K D₁ D₂ h).hom
  let m₁ := (LineBundleDescent.modulesPseudofunctor.mapComp'
    (extensionMap R₁ B).op.toLoc (extensionMap B C).op.toLoc
    (extensionMap R₁ C).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hcomp₁])).inv.toNatTrans.app
        (AffineDedekind.lineBundle R₁ K D₁).obj
  let m₂ := (LineBundleDescent.modulesPseudofunctor.mapComp'
    (extensionMap R₂ B).op.toLoc (extensionMap B C).op.toLoc
    (extensionMap R₂ C).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hcomp₂])).inv.toNatTrans.app
        (AffineDedekind.lineBundle R₂ K D₂).obj
  let A₁ := chosenLineBundlePullbackCompIso R₁ B C K D₁ hcomp₁
  let A₂ := chosenLineBundlePullbackCompIso R₂ B C K D₂ hcomp₂
  let eC := (chosenLineBundlePullbackIsoOfOverlapExtensionEq
    R₁ R₂ C K D₁ D₂ hC).hom
  have h₁ : m₁ = A₁.hom := hm₁.trans hc₁
  have h₂ : m₂ = A₂.hom := hm₂.trans hc₂
  have hleft : qP ≫ m₂ = qS ≫ m₂ :=
    congrArg (fun q ↦ q ≫ m₂) hpull
  have hmid : qS ≫ m₂ = qS ≫ A₂.hom :=
    congrArg (fun q ↦ qS ≫ q) h₂
  have hright : A₁.hom ≫ eC = m₁ ≫ eC :=
    congrArg (fun q ↦ q ≫ eC) h₁.symm
  change qP ≫ m₂ = m₁ ≫ eC
  exact hleft.trans (hmid.trans (hn.trans hright))

/-- The pairwise-intersection model pulled once to a smaller common affine open. -/
noncomputable def localLineBundlePairwiseModelHomOnCommonAffine
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hWab : W ≤ U a ⊓ U b) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    (Scheme.Modules.pullback (extensionMap Γ(X, U a) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D a).obj ⟶
      (Scheme.Modules.pullback (extensionMap Γ(X, U b) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D b).obj := by
  let V := U a ⊓ U b
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI := restrictionAlgebra X (U a) V inf_le_left
  letI := restrictionAlgebra X (U b) V inf_le_right
  letI := restrictionAlgebra X V W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  letI : IsScalarTower Γ(X, U a) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X (U a) V W inf_le_left hWab hWa
  letI : IsScalarTower Γ(X, U b) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X (U b) V W inf_le_right hWab hWb
  exact pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (f₁ := extensionMap Γ(X, U a) Γ(X, V))
    (f₂ := extensionMap Γ(X, U b) Γ(X, V))
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
    (extensionMap Γ(X, V) Γ(X, W))
    (extensionMap Γ(X, U a) Γ(X, W))
    (extensionMap Γ(X, U b) Γ(X, W))
    (restrictionExtensionMap_comp X (U a) V W inf_le_left hWab hWa)
    (restrictionExtensionMap_comp X (U b) V W inf_le_right hWab hWb)

/-- Pulling the pairwise model in two stages is its pullback along the composite map. -/
theorem pullHom_localLineBundlePairwiseModelHomOnCommonAffine
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ (coordinateCover U hcover hU).X a)
    (q_b : Y ⟶ (coordinateCover U hcover hU).X b)
    (hgₐ :
      let hWa : W ≤ U a := hWab.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      let hWb : W ≤ U b := hWab.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hgPairₐ :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseModelHomOnCommonAffine
          K X f U hnonempty hcover hU h D a b W hWab)
        g qₐ q_b hgₐ hg_b =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b
        hgPairₐ hgPair_b := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U b) W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  letI : IsScalarTower Γ(X, U a) Γ(X, U a ⊓ U b) Γ(X, W) :=
    restrictionAlgebraTower X (U a) (U a ⊓ U b) W inf_le_left hWab hWa
  letI : IsScalarTower Γ(X, U b) Γ(X, U a ⊓ U b) Γ(X, W) :=
    restrictionAlgebraTower X (U b) (U a ⊓ U b) W inf_le_right hWab hWb
  unfold localLineBundlePairwiseModelHomOnCommonAffine
  exact pullHom_pullHom
    (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
    (extensionMap Γ(X, U a ⊓ U b) Γ(X, W))
    (extensionMap Γ(X, U a) Γ(X, W))
    (extensionMap Γ(X, U b) Γ(X, W)) g qₐ q_b
    (restrictionExtensionMap_comp X (U a) (U a ⊓ U b) W
      inf_le_left hWab hWa)
    (restrictionExtensionMap_comp X (U b) (U a ⊓ U b) W
      inf_le_right hWab hWb)
    hgₐ hg_b

/-- The separately constructed direct inverse-ideal comparison on a common affine open. -/
noncomputable def localLineBundleDirectModelHomOnCommonAffine
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    (Scheme.Modules.pullback (extensionMap Γ(X, U a) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D a).obj ⟶
      (Scheme.Modules.pullback (extensionMap Γ(X, U b) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D b).obj := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI : Nonempty (U a) := hnonempty a
  letI : Nonempty (U b) := hnonempty b
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  exact (localLineBundlePullbackIsoViaPairwiseIntersection
    K X f (U a) (U b) W (hU a) (hU b) hW hWa hWb (h a) (h b) D).hom

/-- Pullback of the pairwise model is the independently constructed direct comparison on the
smaller common affine open. -/
def PairwiseCommonAffinePullbackCompatibility
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b) : Prop :=
  localLineBundlePairwiseModelHomOnCommonAffine
      K X f U hnonempty hcover hU h D a b W hWab =
    localLineBundleDirectModelHomOnCommonAffine
      K X f U hnonempty hcover hU h D a b W hW hWab

/-- The pairwise model is compatible with restriction to every common affine subopen. -/
theorem pairwiseCommonAffinePullbackCompatibility
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b) :
    PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D a b W hW hWab := by
  let V := U a ⊓ U b
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hV : IsAffineOpen V := (hU a).inf (hU b)
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI : Nonempty (U a) := hnonempty a
  letI : Nonempty (U b) := hnonempty b
  letI : Nonempty V := nonempty_inf_of_isIntegral X (U a) (U b)
  letI : IsDedekindDomain Γ(X, U a) := (h a).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U b) := (h b).isDedekindDomain
  let hcompatV := AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve
    K X f V hV
  let hcompatW := AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve
    K X f W hW
  letI : IsDedekindDomain Γ(X, V) := hcompatV.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) := hcompatW.isDedekindDomain
  letI := restrictionAlgebra X (U a) V inf_le_left
  letI := restrictionAlgebra X (U b) V inf_le_right
  letI := restrictionAlgebra X V W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  letI : Module.IsTorsionFree Γ(X, U a) Γ(X, V) :=
    restrictionTorsionFree X (U a) V inf_le_left
  letI : Module.IsTorsionFree Γ(X, U b) Γ(X, V) :=
    restrictionTorsionFree X (U b) V inf_le_right
  letI : Module.IsTorsionFree Γ(X, V) Γ(X, W) :=
    restrictionTorsionFree X V W hWab
  letI : Module.IsTorsionFree Γ(X, U a) Γ(X, W) :=
    restrictionTorsionFree X (U a) W hWa
  letI : Module.IsTorsionFree Γ(X, U b) Γ(X, W) :=
    restrictionTorsionFree X (U b) W hWb
  letI : IsFractionRing Γ(X, U a) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U a) (hU a)
  letI : IsFractionRing Γ(X, U b) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (U b) (hU b)
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsScalarTower Γ(X, U a) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X (U a) V W inf_le_left hWab hWa
  letI : IsScalarTower Γ(X, U b) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X (U b) V W inf_le_right hWab hWb
  letI : IsScalarTower Γ(X, U a) Γ(X, V) X.functionField :=
    restrictionFunctionFieldTower X (U a) V inf_le_left
  letI : IsScalarTower Γ(X, U b) Γ(X, V) X.functionField :=
    restrictionFunctionFieldTower X (U b) V inf_le_right
  letI : IsScalarTower Γ(X, V) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X V W hWab
  letI : IsScalarTower Γ(X, U a) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X (U a) W hWa
  letI : IsScalarTower Γ(X, U b) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X (U b) W hWb
  letI : IsOpenImmersion (extensionMap Γ(X, U a) Γ(X, V)) :=
    restrictionExtensionMapIsOpenImmersion X (U a) V (hU a) hV inf_le_left
  letI : IsOpenImmersion (extensionMap Γ(X, U b) Γ(X, V)) :=
    restrictionExtensionMapIsOpenImmersion X (U b) V (hU b) hV inf_le_right
  letI : IsOpenImmersion (extensionMap Γ(X, V) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X V W hV hW hWab
  letI : IsOpenImmersion (extensionMap Γ(X, U a) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X (U a) W (hU a) hW hWa
  letI : IsOpenImmersion (extensionMap Γ(X, U b) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X (U b) W (hU b) hW hWb
  letI : Algebra.IsEpi Γ(X, V) Γ(X, W) := by
    let g : CommRingCat.of Γ(X, V) ⟶ CommRingCat.of Γ(X, W) :=
      CommRingCat.ofHom (algebraMap Γ(X, V) Γ(X, W))
    letI : Mono (Scheme.Spec.map g.op) := by
      change Mono (Spec.map g)
      infer_instance
    letI : Mono g.op := Scheme.Spec.mono_of_mono_map inferInstance
    letI : Epi g := by
      change Epi g.op.unop
      infer_instance
    exact CommRingCat.epi_iff_epi.mp (inferInstanceAs (Epi g))
  letI : Module.Flat Γ(X, V) Γ(X, W) := by
    let g : CommRingCat.of Γ(X, V) ⟶ CommRingCat.of Γ(X, W) :=
      CommRingCat.ofHom (algebraMap Γ(X, V) Γ(X, W))
    have hg : _root_.AlgebraicGeometry.Flat (Spec.map g) := by
      change _root_.AlgebraicGeometry.Flat
        (extensionMap Γ(X, V) Γ(X, W))
      infer_instance
    exact RingHom.flat_algebraMap_iff.mp
      (_root_.AlgebraicGeometry.Flat.SpecMap_iff.mp hg)
  let hPair := overlapInverseIdealExtensionEq_localDivisor_of_commonMap
    X (U a) (U b) (hU a) (hU b) (h a) (h b) Γ(X, V)
      (restrictionFunctionFieldTower X (U a) V inf_le_left)
      (restrictionFunctionFieldTower X (U b) V inf_le_right)
      hV.fromSpec
      (restrictionExtensionMap_comp_fromSpec X (U a) V (hU a) hV inf_le_left)
      (restrictionExtensionMap_comp_fromSpec X (U b) V (hU b) hV inf_le_right) D
  let hcompₐ := restrictionExtensionMap_comp
    X (U a) V W inf_le_left hWab hWa
  let hcomp_b := restrictionExtensionMap_comp
    X (U b) V W inf_le_right hWab hWb
  let hC := overlapInverseIdealExtensionEq_baseChange
    Γ(X, U a) Γ(X, U b) Γ(X, V) Γ(X, W) X.functionField
      (localDivisor X (U a) (hU a) (h a) D)
      (localDivisor X (U b) (hU b) (h b) D) hPair
  have hPairIso :
      localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b =
        chosenLineBundlePullbackIsoOfOverlapExtensionEq
          Γ(X, U a) Γ(X, U b) Γ(X, V) X.functionField
          (localDivisor X (U a) (hU a) (h a) D)
          (localDivisor X (U b) (hU b) (h b) D) hPair := by
    rfl
  have hDirectIso :
      localLineBundlePullbackIsoViaPairwiseIntersection
          K X f (U a) (U b) W (hU a) (hU b) hW hWa hWb (h a) (h b) D =
        chosenLineBundlePullbackIsoOfOverlapExtensionEq
          Γ(X, U a) Γ(X, U b) Γ(X, W) X.functionField
          (localDivisor X (U a) (hU a) (h a) D)
          (localDivisor X (U b) (hU b) (h b) D) hC := by
    rfl
  unfold PairwiseCommonAffinePullbackCompatibility
  unfold localLineBundlePairwiseModelHomOnCommonAffine
  unfold localLineBundleDirectModelHomOnCommonAffine
  rw [hPairIso]
  dsimp only
  have hp := pullHom_chosenLineBundlePullbackIsoOfOverlapExtensionEq
    Γ(X, U a) Γ(X, U b) Γ(X, V) Γ(X, W) X.functionField
      (localDivisor X (U a) (hU a) (h a) D)
      (localDivisor X (U b) (hU b) (h b) D) hPair hcompₐ hcomp_b
  exact hp.trans (congrArg Iso.hom hDirectIso.symm)

/-- Once the common-affine compatibility law is supplied, the pairwise model pulled along the
composite is the direct common-affine comparison pulled along the same map. -/
theorem pairwiseModelPullHom_eq_directPullHom_of_compatibility
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ (coordinateCover U hcover hU).X a)
    (q_b : Y ⟶ (coordinateCover U hcover hU).X b)
    (hgₐ :
      let hWa : W ≤ U a := hWab.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      let hWb : W ≤ U b := hWab.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hgPairₐ :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b)
    (hcompat : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D a b W hW hWab) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b hgPairₐ hgPair_b =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleDirectModelHomOnCommonAffine
          K X f U hnonempty hcover hU h D a b W hW hWab)
        g qₐ q_b hgₐ hg_b := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U b) W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  have hn := pullHom_localLineBundlePairwiseModelHomOnCommonAffine
    K X f U hnonempty hcover hU h D a b W hWab g qₐ q_b hgₐ hg_b hgPairₐ hgPair_b
  have hc := congrArg
    (fun z ↦ pullHom (F := LineBundleDescent.modulesPseudofunctor)
      z g qₐ q_b hgₐ hg_b) hcompat
  exact hn.symm.trans hc

/-- The pairwise overlap model and the direct common-affine model agree after every further
pullback. -/
theorem pairwiseModelPullHom_eq_directPullHom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ (coordinateCover U hcover hU).X a)
    (q_b : Y ⟶ (coordinateCover U hcover hU).X b)
    (hgₐ :
      let hWa : W ≤ U a := hWab.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      let hWb : W ≤ U b := hWab.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hgPairₐ :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b hgPairₐ hgPair_b =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleDirectModelHomOnCommonAffine
          K X f U hnonempty hcover hU h D a b W hW hWab)
        g qₐ q_b hgₐ hg_b := by
  exact pairwiseModelPullHom_eq_directPullHom_of_compatibility
    K X f U hnonempty hcover hU h D a b W hW hWab
      g qₐ q_b hgₐ hg_b hgPairₐ hgPair_b
      (pairwiseCommonAffinePullbackCompatibility
        K X f U hnonempty hcover hU h D a b W hW hWab)

private theorem pullHom_comp_same_map
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {X₁ X₂ X₃ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {M₃ : F.obj (.mk (.op X₃))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (e₁₂ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (e₂₃ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom e₁₂ g gf₁ gf₂ hgf₁ hgf₂ ≫
      pullHom e₂₃ g gf₂ gf₃ hgf₂ hgf₃ =
      pullHom (e₁₂ ≫ e₂₃) g gf₁ gf₃ hgf₁ hgf₃ := by
  subst gf₁
  subst gf₂
  subst gf₃
  simp [pullHom, Functor.map_comp]

/-- The checked common-affine cocycle remains a cocycle after pullback along any map to that
common affine. -/
theorem pullHom_localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ U₃ W : X.Opens)
    [Nonempty U₁] [Nonempty U₂] [Nonempty U₃] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (hU₃ : IsAffineOpen U₃) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂) (hWU₃ : W ≤ U₃)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (h₃ : AffineChart.DedekindOrderCompatibility X U₃ hU₃)
    (D : WeilDivisor (CodimensionOnePoint X))
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (q₁ : Y ⟶ Spec (.of Γ(X, U₁)))
    (q₂ : Y ⟶ Spec (.of Γ(X, U₂)))
    (q₃ : Y ⟶ Spec (.of Γ(X, U₃)))
    (hg₁ :
      letI := restrictionAlgebra X U₁ W hWU₁
      g ≫ extensionMap Γ(X, U₁) Γ(X, W) = q₁)
    (hg₂ :
      letI := restrictionAlgebra X U₂ W hWU₂
      g ≫ extensionMap Γ(X, U₂) Γ(X, W) = q₂)
    (hg₃ :
      letI := restrictionAlgebra X U₃ W hWU₃
      g ≫ extensionMap Γ(X, U₃) Γ(X, W) = q₃) :
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI := restrictionAlgebra X U₃ W hWU₃
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePullbackIsoViaPairwiseIntersection
            K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D).hom
          g q₁ q₂ hg₁ hg₂ ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePullbackIsoViaPairwiseIntersection
            K X f U₂ U₃ W hU₂ hU₃ hW hWU₂ hWU₃ h₂ h₃ D).hom
          g q₂ q₃ hg₂ hg₃ =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₁ U₃ W hU₁ hU₃ hW hWU₁ hWU₃ h₁ h₃ D).hom
        g q₁ q₃ hg₁ hg₃ := by
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI := restrictionAlgebra X U₃ W hWU₃
  calc
    _ = pullHom (F := LineBundleDescent.modulesPseudofunctor)
        ((localLineBundlePullbackIsoViaPairwiseIntersection
              K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D).hom ≫
          (localLineBundlePullbackIsoViaPairwiseIntersection
              K X f U₂ U₃ W hU₂ hU₃ hW hWU₂ hWU₃ h₂ h₃ D).hom)
        g q₁ q₃ hg₁ hg₃ := by
      exact pullHom_comp_same_map
        (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D).hom
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₂ U₃ W hU₂ hU₃ hW hWU₂ hWU₃ h₂ h₃ D).hom
        g q₁ q₂ q₃ hg₁ hg₂ hg₃
    _ = pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₁ U₃ W hU₁ hU₃ hW hWU₁ hWU₃ h₁ h₃ D).hom
        g q₁ q₃ hg₁ hg₃ := by
      exact congrArg
        (fun z ↦ pullHom (F := LineBundleDescent.modulesPseudofunctor)
          z g q₁ q₃ hg₁ hg₃)
        (localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
          K X f U₁ U₂ U₃ W hU₁ hU₂ hU₃ hW hWU₁ hWU₂ hWU₃ h₁ h₂ h₃ D)

private theorem pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWa : W ≤ U a) (hWb : W ≤ U b) (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ Spec (.of Γ(X, U a)))
    (q_b : Y ⟶ Spec (.of Γ(X, U b)))
    (hgₐ :
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b) :
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleDirectModelHomOnCommonAffine
          K X f U hnonempty hcover hU h D a b W hW hWab)
        g qₐ q_b hgₐ hg_b =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f (U a) (U b) W (hU a) (hU b) hW hWa hWb (h a) (h b) D).hom
        g qₐ q_b hgₐ hg_b := by
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  rfl

/-- Conditional transport of the common-affine cocycle through three supplied pairwise
compatibilities.  The unconditional theorem below discharges these predicates. -/
theorem pairwiseModelPullHom_cocycle_of_compatibilities
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b c : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWa : W ≤ U a) (hWb : W ≤ U b) (hWc : W ≤ U c)
    (hWab : W ≤ U a ⊓ U b) (hWbc : W ≤ U b ⊓ U c)
    (hWac : W ≤ U a ⊓ U c)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ Spec (.of Γ(X, U a)))
    (q_b : Y ⟶ Spec (.of Γ(X, U b)))
    (q_c : Y ⟶ Spec (.of Γ(X, U c)))
    (hgₐ :
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hg_c :
      letI := restrictionAlgebra X (U c) W hWc
      g ≫ extensionMap Γ(X, U c) Γ(X, W) = q_c)
    (hgPair_ab_a :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_ab_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b)
    (hgPair_bc_b :
      letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
      letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
      (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U b ⊓ U c) = q_b)
    (hgPair_bc_c :
      letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
      letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
      (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U c) Γ(X, U b ⊓ U c) = q_c)
    (hgPair_ac_a :
      letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U c) W hWac
      (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U c) = qₐ)
    (hgPair_ac_c :
      letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U c) W hWac
      (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U c) Γ(X, U a ⊓ U c) = q_c)
    (hcompat_ab : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D a b W hW hWab)
    (hcompat_bc : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D b c W hW hWbc)
    (hcompat_ac : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D a c W hW hWac) :
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
    letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
    letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
    letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
    letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U c) W hWac
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    letI := restrictionAlgebra X (U c) W hWc
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D a b).hom
          (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W))
          qₐ q_b hgPair_ab_a hgPair_ab_b ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D b c).hom
          (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W))
          q_b q_c hgPair_bc_b hgPair_bc_c =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a c).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W))
        qₐ q_c hgPair_ac_a hgPair_ac_c := by
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U b) W hWab
  letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
  letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
  letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
  letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
  letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U c) W hWac
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  letI := restrictionAlgebra X (U c) W hWc
  rw [pairwiseModelPullHom_eq_directPullHom_of_compatibility
      K X f U hnonempty hcover hU h D a b W hW hWab
      g qₐ q_b hgₐ hg_b hgPair_ab_a hgPair_ab_b hcompat_ab,
    pairwiseModelPullHom_eq_directPullHom_of_compatibility
      K X f U hnonempty hcover hU h D b c W hW hWbc
      g q_b q_c hg_b hg_c hgPair_bc_b hgPair_bc_c hcompat_bc,
    pairwiseModelPullHom_eq_directPullHom_of_compatibility
      K X f U hnonempty hcover hU h D a c W hW hWac
      g qₐ q_c hgₐ hg_c hgPair_ac_a hgPair_ac_c hcompat_ac]
  rw [pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
      K X f U hnonempty hcover hU h D a b W hW hWa hWb hWab
      g qₐ q_b hgₐ hg_b,
    pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
      K X f U hnonempty hcover hU h D b c W hW hWb hWc hWbc
      g q_b q_c hg_b hg_c,
    pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
      K X f U hnonempty hcover hU h D a c W hW hWa hWc hWac
      g qₐ q_c hgₐ hg_c]
  exact pullHom_localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
    K X f (U a) (U b) (U c) W (hU a) (hU b) (hU c) hW
      hWa hWb hWc (h a) (h b) (h c) D g qₐ q_b q_c hgₐ hg_b hg_c

/-- The three pairwise overlap models satisfy the cocycle law after arbitrary further pullback. -/
theorem pairwiseModelPullHom_cocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b c : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWa : W ≤ U a) (hWb : W ≤ U b) (hWc : W ≤ U c)
    (hWab : W ≤ U a ⊓ U b) (hWbc : W ≤ U b ⊓ U c)
    (hWac : W ≤ U a ⊓ U c)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ Spec (.of Γ(X, U a)))
    (q_b : Y ⟶ Spec (.of Γ(X, U b)))
    (q_c : Y ⟶ Spec (.of Γ(X, U c)))
    (hgₐ :
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hg_c :
      letI := restrictionAlgebra X (U c) W hWc
      g ≫ extensionMap Γ(X, U c) Γ(X, W) = q_c)
    (hgPair_ab_a :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_ab_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b)
    (hgPair_bc_b :
      letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
      letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
      (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U b ⊓ U c) = q_b)
    (hgPair_bc_c :
      letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
      letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
      (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U c) Γ(X, U b ⊓ U c) = q_c)
    (hgPair_ac_a :
      letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U c) W hWac
      (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U c) = qₐ)
    (hgPair_ac_c :
      letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U c) W hWac
      (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U c) Γ(X, U a ⊓ U c) = q_c) :
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
    letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
    letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
    letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
    letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U c) W hWac
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    letI := restrictionAlgebra X (U c) W hWc
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D a b).hom
          (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W))
          qₐ q_b hgPair_ab_a hgPair_ab_b ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D b c).hom
          (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W))
          q_b q_c hgPair_bc_b hgPair_bc_c =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a c).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W))
        qₐ q_c hgPair_ac_a hgPair_ac_c := by
  exact pairwiseModelPullHom_cocycle_of_compatibilities
    K X f U hnonempty hcover hU h D a b c W hW hWa hWb hWc hWab hWbc hWac
      g qₐ q_b q_c hgₐ hg_b hg_c
      hgPair_ab_a hgPair_ab_b hgPair_bc_b hgPair_bc_c hgPair_ac_a hgPair_ac_c
      (pairwiseCommonAffinePullbackCompatibility
        K X f U hnonempty hcover hU h D a b W hW hWab)
      (pairwiseCommonAffinePullbackCompatibility
        K X f U hnonempty hcover hU h D b c W hW hWbc)
      (pairwiseCommonAffinePullbackCompatibility
        K X f U hnonempty hcover hU h D a c W hW hWac)

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
