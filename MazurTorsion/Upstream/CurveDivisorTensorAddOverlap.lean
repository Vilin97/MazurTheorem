/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTildeTensorRestrictionOverlapNaturality
import MazurTorsion.Upstream.CurveLineBundleTripleTower

/-!
# Tensor addition on a curve-chart overlap

The cross-chart naturality square for extended inverse-ideal tilde sheaves is specialized to a
common affine subopen of two curve charts.  The two equality witnesses are obtained by first
comparing on the full pairwise intersection and then applying the checked scalar-tower theorem,
so this is the equality provenance used by the chosen pairwise overlap transition.

Combining that raw square with the two one-leg restriction squares proves tensor/addition
naturality for the actual chosen restriction comparisons between the coordinate-divisor line
bundles.  The final theorem aligns this square with the proof-defined global-divisor addition
and pairwise-intersection transition APIs.  Assembly into a morphism of descent data remains
separate.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open scoped AlgebraicGeometry TensorProduct

universe u

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForDivisorTensorOverlap (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- Tensoring two factorwise conjugacy squares gives the corresponding Hom-level tensor
conjugacy square. -/
private theorem tensorIso_hom_conjugacy
    {C : Type*} [Category C] [MonoidalCategory C]
    {A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : C}
    (q₁D : A₁ ≅ B₁) (eD : B₁ ≅ C₁)
    (tD : A₁ ≅ D₁) (q₂D : D₁ ≅ C₁)
    (q₁E : A₂ ≅ B₂) (eE : B₂ ≅ C₂)
    (tE : A₂ ≅ D₂) (q₂E : D₂ ≅ C₂)
    (hD : q₁D ≪≫ eD = tD ≪≫ q₂D)
    (hE : q₁E ≪≫ eE = tE ≪≫ q₂E) :
    (q₁D ⊗ᵢ q₁E).hom ≫ (eD ⊗ᵢ eE).hom =
      (tD ⊗ᵢ tE).hom ≫ (q₂D ⊗ᵢ q₂E).hom := by
  have hDhom := congrArg (fun z ↦ z.hom) hD
  change q₁D.hom ≫ eD.hom = tD.hom ≫ q₂D.hom at hDhom
  have hEhom := congrArg (fun z ↦ z.hom) hE
  change q₁E.hom ≫ eE.hom = tE.hom ≫ q₂E.hom at hEhom
  calc
    (q₁D ⊗ᵢ q₁E).hom ≫ (eD ⊗ᵢ eE).hom =
        (q₁D.hom ≫ eD.hom) ⊗ₘ (q₁E.hom ≫ eE.hom) :=
      tensorHom_comp_tensorHom q₁D.hom q₁E.hom eD.hom eE.hom
    _ = (tD.hom ≫ q₂D.hom) ⊗ₘ (tE.hom ≫ q₂E.hom) :=
      congrArg₂ (fun a b ↦ a ⊗ₘ b) hDhom hEhom
    _ = (tD ⊗ᵢ tE).hom ≫ (q₂D ⊗ᵢ q₂E).hom :=
      (tensorHom_comp_tensorHom tD.hom tE.hom q₂D.hom q₂E.hom).symm

/-- Restriction tensor comparison cancels a coordinate transport and its inverse on the
two tensor factors. -/
private theorem localLineBundleCoordinateTensorTail
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
    letI := restrictionAlgebra X U W hWU
    letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
      restrictionTorsionFree X U W hWU
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsOpenImmersion (extensionMap Γ(X, U) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
    let d := localDivisor X U hU h D
    let e := localDivisor X U hU h E
    let F := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U) Γ(X, W))
    let qD := localLineBundleCoordinateIso X U hU h D
    let qE := localLineBundleCoordinateIso X U hU h E
    let κ := lineBundleTensorRestrictionIsoViaPullback
      Γ(X, U) Γ(X, W) X.functionField d e
    (F.mapIso (qD.symm ⊗ᵢ qE.symm) ≪≫ κ) ≪≫
        (F.mapIso qD ⊗ᵢ F.mapIso qE) = κ := by
  letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
  letI := restrictionAlgebra X U W hWU
  letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
    restrictionTorsionFree X U W hWU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsOpenImmersion (extensionMap Γ(X, U) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
  let fU := extensionMap Γ(X, U) Γ(X, W)
  let F := Scheme.Modules.restrictFunctor fU
  let PB := Scheme.Modules.pullback fU
  let q := Scheme.Modules.restrictFunctorIsoPullback fU
  let LD := (AffineDedekind.lineBundle Γ(X, U) X.functionField
    (localDivisor X U hU h D)).obj
  let LE := (AffineDedekind.lineBundle Γ(X, U) X.functionField
    (localDivisor X U hU h E)).obj
  let MD := (localLineBundle X U hU h D).obj
  let ME := (localLineBundle X U hU h E).obj
  let qD := localLineBundleCoordinateIso X U hU h D
  let qE := localLineBundleCoordinateIso X U hU h E
  letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal fU
  let qT := (q.app (LD ⊗ LE)).hom
  let δ := Functor.OplaxMonoidal.δ PB LD LE
  let qInvPair := (q.app LD).inv ⊗ₘ (q.app LE).inv
  let qTM := (q.app (MD ⊗ ME)).hom
  let δM := Functor.OplaxMonoidal.δ PB MD ME
  let qInvPairM := (q.app MD).inv ⊗ₘ (q.app ME).inv
  let fInvPair := qD.inv ⊗ₘ qE.inv
  let fHomPair := F.map qD.hom ⊗ₘ F.map qE.hom
  let pbInvPair := PB.map qD.inv ⊗ₘ PB.map qE.inv
  let pbHomPair := PB.map qD.hom ⊗ₘ PB.map qE.hom
  have hq := q.hom.naturality fInvPair
  change F.map fInvPair ≫ qTM = qT ≫ PB.map fInvPair at hq
  have hδ := Functor.OplaxMonoidal.δ_natural PB qD.inv qE.inv
  change δ ≫ pbInvPair = PB.map fInvPair ≫ δM at hδ
  have hqD := q.inv.naturality qD.hom
  change PB.map qD.hom ≫ (q.app LD).inv =
    (q.app MD).inv ≫ F.map qD.hom at hqD
  have hqE := q.inv.naturality qE.hom
  change PB.map qE.hom ≫ (q.app LE).inv =
    (q.app ME).inv ≫ F.map qE.hom at hqE
  have hback₁ : qInvPairM ≫ fHomPair =
      ((q.app MD).inv ≫ F.map qD.hom) ⊗ₘ
        ((q.app ME).inv ≫ F.map qE.hom) :=
    tensorHom_comp_tensorHom (q.app MD).inv (q.app ME).inv
      (F.map qD.hom) (F.map qE.hom)
  have hback₂ :
      ((q.app MD).inv ≫ F.map qD.hom) ⊗ₘ
          ((q.app ME).inv ≫ F.map qE.hom) =
        (PB.map qD.hom ≫ (q.app LD).inv) ⊗ₘ
          (PB.map qE.hom ≫ (q.app LE).inv) :=
    congrArg₂ (fun a b ↦ a ⊗ₘ b) hqD.symm hqE.symm
  have hback₃ :
      (PB.map qD.hom ≫ (q.app LD).inv) ⊗ₘ
          (PB.map qE.hom ≫ (q.app LE).inv) =
        pbHomPair ≫ qInvPair :=
    (tensorHom_comp_tensorHom (PB.map qD.hom) (PB.map qE.hom)
      (q.app LD).inv (q.app LE).inv).symm
  have hback : qInvPairM ≫ fHomPair = pbHomPair ≫ qInvPair :=
    hback₁.trans (hback₂.trans hback₃)
  have hpbD : PB.map qD.inv ≫ PB.map qD.hom = 𝟙 _ := by
    rw [← PB.map_comp, qD.inv_hom_id, PB.map_id]
  have hpbE : PB.map qE.inv ≫ PB.map qE.hom = 𝟙 _ := by
    rw [← PB.map_comp, qE.inv_hom_id, PB.map_id]
  have hpb₁ : pbInvPair ≫ pbHomPair =
      (PB.map qD.inv ≫ PB.map qD.hom) ⊗ₘ
        (PB.map qE.inv ≫ PB.map qE.hom) :=
    tensorHom_comp_tensorHom (PB.map qD.inv) (PB.map qE.inv)
      (PB.map qD.hom) (PB.map qE.hom)
  have hpb₂ :
      (PB.map qD.inv ≫ PB.map qD.hom) ⊗ₘ
          (PB.map qE.inv ≫ PB.map qE.hom) =
        𝟙 (PB.obj LD ⊗ PB.obj LE) :=
    (congrArg₂ (fun a b ↦ a ⊗ₘ b) hpbD hpbE).trans
      (MonoidalCategory.id_tensorHom_id _ _)
  have hpb : pbInvPair ≫ pbHomPair = 𝟙 (PB.obj LD ⊗ PB.obj LE) :=
    hpb₁.trans hpb₂
  apply Iso.ext
  change ((F.map fInvPair ≫ qT ≫ δ ≫ qInvPair) ≫ fHomPair) =
    qT ≫ δ ≫ qInvPair
  calc
    ((F.map fInvPair ≫ qTM ≫ δM ≫ qInvPairM) ≫ fHomPair) =
        ((qT ≫ PB.map fInvPair ≫ δM ≫ qInvPairM) ≫ fHomPair) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ (z ≫ δM ≫ qInvPairM) ≫ fHomPair) hq
    _ = ((qT ≫ δ ≫ pbInvPair ≫ qInvPairM) ≫ fHomPair) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ (qT ≫ z ≫ qInvPairM) ≫ fHomPair) hδ.symm
    _ = qT ≫ δ ≫ pbInvPair ≫ (pbHomPair ≫ qInvPair) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ (qT ≫ δ ≫ pbInvPair) ≫ z) hback
    _ = qT ≫ δ ≫ (pbInvPair ≫ pbHomPair) ≫ qInvPair := by
      simp only [Category.assoc]
    _ = qT ≫ δ ≫ qInvPair := by rw [hpb, Category.id_comp]

/-- Two fixed prefixes may be pasted onto a restriction tensor tail cancellation. -/
private theorem chartAddConjugacy_of_tensorTail
    {C : Type*} [Category C] {A B D E : C}
    (Ag : A ≅ D) (s : A ≅ B) (a : B ≅ D)
    (tail : D ≅ D) (κ : D ≅ E) (q : E ≅ E)
    (hAg : Ag = (s ≪≫ a) ≪≫ tail)
    (htail : (tail ≪≫ κ) ≪≫ q = κ) :
    (Ag ≪≫ κ) ≪≫ q = s ≪≫ (a ≪≫ κ) := by
  calc
    (Ag ≪≫ κ) ≪≫ q = (((s ≪≫ a) ≪≫ tail) ≪≫ κ) ≪≫ q :=
      congrArg (fun z ↦ (z ≪≫ κ) ≪≫ q) hAg
    _ = (s ≪≫ a) ≪≫ ((tail ≪≫ κ) ≪≫ q) := by
      simp only [Iso.trans_assoc]
    _ = (s ≪≫ a) ≪≫ κ := congrArg ((s ≪≫ a) ≪≫ ·) htail
    _ = s ≪≫ (a ≪≫ κ) := Iso.trans_assoc s a κ

/-- Restriction maps the addition-source coordinate transport to the composite of the mapped
bundle coordinate transport and the mapped divisor-addition transport. -/
private theorem localLineBundleAddSourceCoordinateIso_restrict_factor
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
    letI := restrictionAlgebra X U W hWU
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsOpenImmersion (extensionMap Γ(X, U) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
    let F := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U) Γ(X, W))
    let hAdd := localDivisor_add X U hU h D E
    let q := F.mapIso (localLineBundleCoordinateIso X U hU h (D + E))
    let r := F.mapIso (eqToIso (congrArg
      (fun d ↦ (AffineDedekind.lineBundle Γ(X, U) X.functionField d).obj) hAdd))
    let s := F.mapIso (localLineBundleAddSourceCoordinateIso X U hU h D E)
    s = q ≪≫ r := by
  letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
  letI := restrictionAlgebra X U W hWU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsOpenImmersion (extensionMap Γ(X, U) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
  simp only [localLineBundleAddSourceCoordinateIso, Functor.mapIso_trans]

/-- Abstract composition of source decomposition, coordinate reindexing, and factor
conjugacy into a sum conjugacy square. -/
private theorem sum_conjugacy_of_factor_conjugacy
    {C : Type*} [Category C] {A B C' F G H : C}
    (q₁ : A ≅ B) (r₁ : B ≅ C') (s₁ : A ≅ C')
    (eSum eS : C' ≅ H) (eG : B ≅ G)
    (tS : A ≅ F) (q₂ : F ≅ G) (r₂ : G ≅ H) (s₂ : F ≅ H)
    (hs₁ : s₁ = q₁ ≪≫ r₁) (hs₂ : s₂ = q₂ ≪≫ r₂)
    (heSum : eSum = eS) (hReindex : r₁ ≪≫ eSum = eG ≪≫ r₂)
    (hFactor : q₁ ≪≫ eG = tS ≪≫ q₂) :
    s₁ ≪≫ eS = tS ≪≫ s₂ := by
  calc
    s₁ ≪≫ eS = (q₁ ≪≫ r₁) ≪≫ eS := congrArg (· ≪≫ eS) hs₁
    _ = (q₁ ≪≫ r₁) ≪≫ eSum :=
      congrArg ((q₁ ≪≫ r₁) ≪≫ ·) heSum.symm
    _ = q₁ ≪≫ (r₁ ≪≫ eSum) := Iso.trans_assoc q₁ r₁ eSum
    _ = q₁ ≪≫ (eG ≪≫ r₂) := congrArg (q₁ ≪≫ ·) hReindex
    _ = (q₁ ≪≫ eG) ≪≫ r₂ := (Iso.trans_assoc q₁ eG r₂).symm
    _ = (tS ≪≫ q₂) ≪≫ r₂ := congrArg (· ≪≫ r₂) hFactor
    _ = tS ≪≫ (q₂ ≪≫ r₂) := Iso.trans_assoc tS q₂ r₂
    _ = tS ≪≫ s₂ := congrArg (tS ≪≫ ·) hs₂.symm

/-- On a common affine subopen of two proper-smooth curve charts, the equality-induced
inverse-ideal comparison commutes with deterministic divisor addition.  Both factorwise
equalities retain their pairwise-intersection provenance. -/
theorem localExtendedInverseIdealAddIso_naturalityViaPairwiseIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    let d₁ := localDivisor X U₁ hU₁ h₁ D
    let e₁ := localDivisor X U₁ hU₁ h₁ E
    let d₂ := localDivisor X U₂ hU₂ h₂ D
    let e₂ := localDivisor X U₂ hU₂ h₂ E
    let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
    let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE
    extendedInverseIdealTildeIso
          Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
          (d₁ + e₁) (d₂ + e₂) hDE ≪≫
        extendedInverseIdealAddIso Γ(X, U₂) Γ(X, W) X.functionField d₂ e₂ =
      extendedInverseIdealAddIso Γ(X, U₁) Γ(X, W) X.functionField d₁ e₁ ≪≫
        (extendedInverseIdealTildeIso
            Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField d₁ d₂ hD ⊗ᵢ
          extendedInverseIdealTildeIso
            Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField e₁ e₂ hE) := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  let d₁ := localDivisor X U₁ hU₁ h₁ D
  let e₁ := localDivisor X U₁ hU₁ h₁ E
  let d₂ := localDivisor X U₂ hU₂ h₂ D
  let e₂ := localDivisor X U₂ hU₂ h₂ E
  let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  exact extendedInverseIdealAddIso_naturality
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE

/-- On a common affine subopen of two proper-smooth curve charts, deterministic divisor
addition commutes with the chosen restriction comparisons whose equality witnesses come from
the pairwise chart intersection. -/
theorem localLineBundleAddIso_restrictViaPullback_naturalityViaPairwiseIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    let d₁ := localDivisor X U₁ hU₁ h₁ D
    let e₁ := localDivisor X U₁ hU₁ h₁ E
    let d₂ := localDivisor X U₂ hU₂ h₂ D
    let e₂ := localDivisor X U₂ hU₂ h₂ E
    let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
    let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE
    let A₁ :=
      (Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₁) Γ(X, W))).mapIso
          (ExplicitIdeal.lineBundleAddIso Γ(X, U₁) X.functionField d₁ e₁) ≪≫
        lineBundleTensorRestrictionIsoViaPullback
          Γ(X, U₁) Γ(X, W) X.functionField d₁ e₁
    let A₂ :=
      (Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₂) Γ(X, W))).mapIso
          (ExplicitIdeal.lineBundleAddIso Γ(X, U₂) X.functionField d₂ e₂) ≪≫
        lineBundleTensorRestrictionIsoViaPullback
          Γ(X, U₂) Γ(X, W) X.functionField d₂ e₂
    let tD := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField d₁ d₂ hD
    let tE := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField e₁ e₂ hE
    let tDE := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      (d₁ + e₁) (d₂ + e₂) hDE
    A₁ ≪≫ (tD ⊗ᵢ tE) = tDE ≪≫ A₂ := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  let d₁ := localDivisor X U₁ hU₁ h₁ D
  let e₁ := localDivisor X U₁ hU₁ h₁ E
  let d₂ := localDivisor X U₂ hU₂ h₂ D
  let e₂ := localDivisor X U₂ hU₂ h₂ E
  let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  exact lineBundleAddIso_restrict_viaPullback_naturality
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE

/-- Equality-induced chosen restriction transitions are natural under equality transports of
both divisor indices. -/
private theorem chosenLineBundleRestrictionIsoOfOverlapExtensionEq_congr
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [Module.IsTorsionFree R₁ B]
    [Algebra R₂ B] [Module.IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (extensionMap R₁ B)]
    [IsOpenImmersion (extensionMap R₂ B)]
    (d₁ d₁' : WeilDivisor (HeightOneSpectrum R₁))
    (d₂ d₂' : WeilDivisor (HeightOneSpectrum R₂))
    (hd₁ : d₁ = d₁') (hd₂ : d₂ = d₂')
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K d₁ d₂)
    (h' : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K d₁' d₂') :
    let F₁ := Scheme.Modules.restrictFunctor (extensionMap R₁ B)
    let F₂ := Scheme.Modules.restrictFunctor (extensionMap R₂ B)
    let q₁ := F₁.mapIso (eqToIso (congrArg
      (fun d ↦ (AffineDedekind.lineBundle R₁ K d).obj) hd₁))
    let q₂ := F₂.mapIso (eqToIso (congrArg
      (fun d ↦ (AffineDedekind.lineBundle R₂ K d).obj) hd₂))
    q₁ ≪≫ chosenLineBundleRestrictionIsoOfOverlapExtensionEq
        R₁ R₂ B K d₁' d₂' h' =
      chosenLineBundleRestrictionIsoOfOverlapExtensionEq
          R₁ R₂ B K d₁ d₂ h ≪≫ q₂ := by
  subst d₁'
  subst d₂'
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  simp only [eqToIso_refl, Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]

/-- A proof-defined pairwise-intersection transition is the coordinate transition conjugated
by the two local-bundle coordinate transports. -/
private theorem localLineBundleRestrictionIsoViaPairwiseIntersection_factor_conjugacy
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (G : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    let g₁ := localDivisor X U₁ hU₁ h₁ G
    let g₂ := localDivisor X U₂ hU₂ h₂ G
    let hG := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ G
    let F₁ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₁) Γ(X, W))
    let F₂ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₂) Γ(X, W))
    let q₁ := F₁.mapIso (localLineBundleCoordinateIso X U₁ hU₁ h₁ G)
    let q₂ := F₂.mapIso (localLineBundleCoordinateIso X U₂ hU₂ h₂ G)
    let eG := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField g₁ g₂ hG
    let tG := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ G
    q₁ ≪≫ eG = tG ≪≫ q₂ := by
  rfl

/-- After restriction to a smaller affine open, the proof-defined local addition path differs
from the coordinate addition path only by the named source and factor coordinate transports. -/
private theorem localLineBundleAddIso_restrict_coordinate_conjugacy
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
    letI := restrictionAlgebra X U W hWU
    letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
      restrictionTorsionFree X U W hWU
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsOpenImmersion (extensionMap Γ(X, U) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
    let d := localDivisor X U hU h D
    let e := localDivisor X U hU h E
    let F := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U) Γ(X, W))
    let qD := F.mapIso (localLineBundleCoordinateIso X U hU h D)
    let qE := F.mapIso (localLineBundleCoordinateIso X U hU h E)
    let qP := qD ⊗ᵢ qE
    let s := F.mapIso (localLineBundleAddSourceCoordinateIso X U hU h D E)
    let κ := lineBundleTensorRestrictionIsoViaPullback
      Γ(X, U) Γ(X, W) X.functionField d e
    let Ag := F.mapIso (localLineBundleAddIso X U hU h D E) ≪≫ κ
    let Ac := F.mapIso
      (ExplicitIdeal.lineBundleAddIso Γ(X, U) X.functionField d e) ≪≫ κ
    Ag ≪≫ qP = s ≪≫ Ac := by
  letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
  letI := restrictionAlgebra X U W hWU
  letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
    restrictionTorsionFree X U W hWU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsOpenImmersion (extensionMap Γ(X, U) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
  let F := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U) Γ(X, W))
  let qD := localLineBundleCoordinateIso X U hU h D
  let qE := localLineBundleCoordinateIso X U hU h E
  let qP := F.mapIso qD ⊗ᵢ F.mapIso qE
  let s := F.mapIso (localLineBundleAddSourceCoordinateIso X U hU h D E)
  let a := F.mapIso (ExplicitIdeal.lineBundleAddIso Γ(X, U) X.functionField
    (localDivisor X U hU h D) (localDivisor X U hU h E))
  let tail := F.mapIso (qD.symm ⊗ᵢ qE.symm)
  let κ := lineBundleTensorRestrictionIsoViaPullback Γ(X, U) Γ(X, W)
    X.functionField (localDivisor X U hU h D) (localDivisor X U hU h E)
  let Ag := F.mapIso (localLineBundleAddIso X U hU h D E)
  have htail := localLineBundleCoordinateTensorTail X U W hU hW hWU h D E
  dsimp only at htail
  change (tail ≪≫ κ) ≪≫ qP = κ at htail
  have hAg : Ag = (s ≪≫ a) ≪≫ tail := by
    unfold Ag s a tail qD qE
    unfold localLineBundleAddIso
    simp only [Functor.mapIso_trans, Iso.trans_assoc]
  exact chartAddConjugacy_of_tensorTail Ag s a tail κ qP hAg htail

/-- The pairwise-intersection witness for `D + E`, normalized by `localDivisor_add`, is the
canonical witness derived from the factorwise comparisons. -/
private theorem localDivisorOverlapExtensionEq_add_normalized_eq_canonical
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    let d₁ := localDivisor X U₁ hU₁ h₁ D
    let e₁ := localDivisor X U₁ hU₁ h₁ E
    let d₂ := localDivisor X U₂ hU₂ h₂ D
    let e₂ := localDivisor X U₂ hU₂ h₂ E
    let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
    let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
    let hSum : Boundary.OverlapInverseIdealExtensionEq
        Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
        (d₁ + e₁) (d₂ + e₂) := by
      simpa only [localDivisor_add] using
        (localDivisorOverlapExtensionEqViaPairwiseIntersection
          K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ (D + E))
    hSum = Boundary.overlapInverseIdealExtensionEq_add
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE := by
  apply Subsingleton.elim

/-- The proof-defined transition for `D + E` is the canonical coordinate-sum transition
conjugated by the two addition-source coordinate transports. -/
private theorem localLineBundleRestrictionIsoViaPairwiseIntersection_sum_conjugacy
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    let d₁ := localDivisor X U₁ hU₁ h₁ D
    let e₁ := localDivisor X U₁ hU₁ h₁ E
    let d₂ := localDivisor X U₂ hU₂ h₂ D
    let e₂ := localDivisor X U₂ hU₂ h₂ E
    let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
    let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE
    let F₁ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₁) Γ(X, W))
    let F₂ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₂) Γ(X, W))
    let s₁ := F₁.mapIso (localLineBundleAddSourceCoordinateIso X U₁ hU₁ h₁ D E)
    let s₂ := F₂.mapIso (localLineBundleAddSourceCoordinateIso X U₂ hU₂ h₂ D E)
    let eS := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      (d₁ + e₁) (d₂ + e₂) hDE
    let tS := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ (D + E)
    s₁ ≪≫ eS = tS ≪≫ s₂ := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  let d₁ := localDivisor X U₁ hU₁ h₁ D
  let e₁ := localDivisor X U₁ hU₁ h₁ E
  let d₂ := localDivisor X U₂ hU₂ h₂ D
  let e₂ := localDivisor X U₂ hU₂ h₂ E
  let g₁ := localDivisor X U₁ hU₁ h₁ (D + E)
  let g₂ := localDivisor X U₂ hU₂ h₂ (D + E)
  let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  let hDE := Boundary.overlapInverseIdealExtensionEq_add
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
    d₁ e₁ d₂ e₂ hD hE
  let hG := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ (D + E)
  let hAdd₁ := localDivisor_add X U₁ hU₁ h₁ D E
  let hAdd₂ := localDivisor_add X U₂ hU₂ h₂ D E
  let hSum : Boundary.OverlapInverseIdealExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      (d₁ + e₁) (d₂ + e₂) := by
    simpa only [localDivisor_add] using hG
  let F₁ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₁) Γ(X, W))
  let F₂ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₂) Γ(X, W))
  let q₁ := F₁.mapIso (localLineBundleCoordinateIso X U₁ hU₁ h₁ (D + E))
  let q₂ := F₂.mapIso (localLineBundleCoordinateIso X U₂ hU₂ h₂ (D + E))
  let r₁ := F₁.mapIso (eqToIso (congrArg
    (fun d ↦ (AffineDedekind.lineBundle Γ(X, U₁) X.functionField d).obj) hAdd₁))
  let r₂ := F₂.mapIso (eqToIso (congrArg
    (fun d ↦ (AffineDedekind.lineBundle Γ(X, U₂) X.functionField d).obj) hAdd₂))
  let s₁ := F₁.mapIso (localLineBundleAddSourceCoordinateIso X U₁ hU₁ h₁ D E)
  let s₂ := F₂.mapIso (localLineBundleAddSourceCoordinateIso X U₂ hU₂ h₂ D E)
  let eG := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField g₁ g₂ hG
  let eSum := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
    (d₁ + e₁) (d₂ + e₂) hSum
  let eS := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
    (d₁ + e₁) (d₂ + e₂) hDE
  let tS := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ (D + E)
  have hWitness := localDivisorOverlapExtensionEq_add_normalized_eq_canonical
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D E
  change hSum = hDE at hWitness
  have heSum : eSum = eS := congrArg
    (chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      (d₁ + e₁) (d₂ + e₂)) hWitness
  have hReindex := chosenLineBundleRestrictionIsoOfOverlapExtensionEq_congr
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
    g₁ (d₁ + e₁) g₂ (d₂ + e₂) hAdd₁ hAdd₂ hG hSum
  dsimp only at hReindex
  change r₁ ≪≫ eSum = eG ≪≫ r₂ at hReindex
  have hFactor := localLineBundleRestrictionIsoViaPairwiseIntersection_factor_conjugacy
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ (D + E)
  dsimp only at hFactor
  change q₁ ≪≫ eG = tS ≪≫ q₂ at hFactor
  have hs₁ := localLineBundleAddSourceCoordinateIso_restrict_factor
    X U₁ W hU₁ hW hWU₁ h₁ D E
  dsimp only at hs₁
  change s₁ = q₁ ≪≫ r₁ at hs₁
  have hs₂ := localLineBundleAddSourceCoordinateIso_restrict_factor
    X U₂ W hU₂ hW hWU₂ h₂ D E
  dsimp only at hs₂
  change s₂ = q₂ ≪≫ r₂ at hs₂
  exact sum_conjugacy_of_factor_conjugacy
    q₁ r₁ s₁ eSum eS eG tS q₂ r₂ s₂
      hs₁ hs₂ heSum hReindex hFactor

/-- The proof-defined global-divisor local addition maps commute with the proof-defined
pairwise-intersection restriction transitions.  Here `global` records alignment with the
global-divisor APIs; assembly into global descent data is not asserted. -/
theorem localLineBundleAddIso_restrictViaPullback_naturalityViaPairwiseIntersection_global
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    let d₁ := localDivisor X U₁ hU₁ h₁ D
    let e₁ := localDivisor X U₁ hU₁ h₁ E
    let d₂ := localDivisor X U₂ hU₂ h₂ D
    let e₂ := localDivisor X U₂ hU₂ h₂ E
    let A₁ :=
      (Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₁) Γ(X, W))).mapIso
          (localLineBundleAddIso X U₁ hU₁ h₁ D E) ≪≫
        lineBundleTensorRestrictionIsoViaPullback
          Γ(X, U₁) Γ(X, W) X.functionField d₁ e₁
    let A₂ :=
      (Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₂) Γ(X, W))).mapIso
          (localLineBundleAddIso X U₂ hU₂ h₂ D E) ≪≫
        lineBundleTensorRestrictionIsoViaPullback
          Γ(X, U₂) Γ(X, W) X.functionField d₂ e₂
    let tD := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
    let tE := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
    let tDE := localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ (D + E)
    A₁ ≪≫ (tD ⊗ᵢ tE) = tDE ≪≫ A₂ := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  let d₁ := localDivisor X U₁ hU₁ h₁ D
  let e₁ := localDivisor X U₁ hU₁ h₁ E
  let d₂ := localDivisor X U₂ hU₂ h₂ D
  let e₂ := localDivisor X U₂ hU₂ h₂ E
  let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  let hDE := Boundary.overlapInverseIdealExtensionEq_add
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
    d₁ e₁ d₂ e₂ hD hE
  let F₁ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₁) Γ(X, W))
  let F₂ := Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₂) Γ(X, W))
  let q₁D := F₁.mapIso (localLineBundleCoordinateIso X U₁ hU₁ h₁ D)
  let q₁E := F₁.mapIso (localLineBundleCoordinateIso X U₁ hU₁ h₁ E)
  let q₂D := F₂.mapIso (localLineBundleCoordinateIso X U₂ hU₂ h₂ D)
  let q₂E := F₂.mapIso (localLineBundleCoordinateIso X U₂ hU₂ h₂ E)
  let q₁P := q₁D ⊗ᵢ q₁E
  let q₂P := q₂D ⊗ᵢ q₂E
  let s₁ := F₁.mapIso (localLineBundleAddSourceCoordinateIso X U₁ hU₁ h₁ D E)
  let s₂ := F₂.mapIso (localLineBundleAddSourceCoordinateIso X U₂ hU₂ h₂ D E)
  let κ₁ := lineBundleTensorRestrictionIsoViaPullback
    Γ(X, U₁) Γ(X, W) X.functionField d₁ e₁
  let κ₂ := lineBundleTensorRestrictionIsoViaPullback
    Γ(X, U₂) Γ(X, W) X.functionField d₂ e₂
  let Ag₁ := F₁.mapIso (localLineBundleAddIso X U₁ hU₁ h₁ D E) ≪≫ κ₁
  let Ag₂ := F₂.mapIso (localLineBundleAddIso X U₂ hU₂ h₂ D E) ≪≫ κ₂
  let Ac₁ := F₁.mapIso
    (ExplicitIdeal.lineBundleAddIso Γ(X, U₁) X.functionField d₁ e₁) ≪≫ κ₁
  let Ac₂ := F₂.mapIso
    (ExplicitIdeal.lineBundleAddIso Γ(X, U₂) X.functionField d₂ e₂) ≪≫ κ₂
  let eD := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField d₁ d₂ hD
  let eE := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField e₁ e₂ hE
  let eP := eD ⊗ᵢ eE
  let eS := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
    (d₁ + e₁) (d₂ + e₂) hDE
  let tD := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  let tE := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  let tP := tD ⊗ᵢ tE
  let tS := localLineBundleRestrictionIsoViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ (D + E)
  have hFactorD := localLineBundleRestrictionIsoViaPairwiseIntersection_factor_conjugacy
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  dsimp only at hFactorD
  change q₁D ≪≫ eD = tD ≪≫ q₂D at hFactorD
  have hFactorE := localLineBundleRestrictionIsoViaPairwiseIntersection_factor_conjugacy
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  dsimp only at hFactorE
  change q₁E ≪≫ eE = tE ≪≫ q₂E at hFactorE
  have hPair := tensorIso_hom_conjugacy
    q₁D eD tD q₂D q₁E eE tE q₂E hFactorD hFactorE
  change q₁P.hom ≫ eP.hom = tP.hom ≫ q₂P.hom at hPair
  have hAg₁ := localLineBundleAddIso_restrict_coordinate_conjugacy
    X U₁ W hU₁ hW hWU₁ h₁ D E
  dsimp only at hAg₁
  change Ag₁ ≪≫ q₁P = s₁ ≪≫ Ac₁ at hAg₁
  have hA₁ := congrArg (fun z ↦ z.hom) hAg₁
  change Ag₁.hom ≫ q₁P.hom = s₁.hom ≫ Ac₁.hom at hA₁
  have hAg₂ := localLineBundleAddIso_restrict_coordinate_conjugacy
    X U₂ W hU₂ hW hWU₂ h₂ D E
  dsimp only at hAg₂
  change Ag₂ ≪≫ q₂P = s₂ ≪≫ Ac₂ at hAg₂
  have hA₂ := congrArg (fun z ↦ z.hom) hAg₂
  change Ag₂.hom ≫ q₂P.hom = s₂.hom ≫ Ac₂.hom at hA₂
  have hCoordinate :=
    localLineBundleAddIso_restrictViaPullback_naturalityViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D E
  dsimp only at hCoordinate
  change Ac₁ ≪≫ eP = eS ≪≫ Ac₂ at hCoordinate
  have hCoord := congrArg (fun z ↦ z.hom) hCoordinate
  change Ac₁.hom ≫ eP.hom = eS.hom ≫ Ac₂.hom at hCoord
  have hSum := localLineBundleRestrictionIsoViaPairwiseIntersection_sum_conjugacy
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D E
  dsimp only at hSum
  change s₁ ≪≫ eS = tS ≪≫ s₂ at hSum
  have hSumHom := congrArg (fun z ↦ z.hom) hSum
  change s₁.hom ≫ eS.hom = tS.hom ≫ s₂.hom at hSumHom
  apply Iso.ext
  change Ag₁.hom ≫ tP.hom = tS.hom ≫ Ag₂.hom
  apply (cancel_mono q₂P.hom).1
  calc
    (Ag₁.hom ≫ tP.hom) ≫ q₂P.hom =
        Ag₁.hom ≫ (tP.hom ≫ q₂P.hom) := Category.assoc _ _ _
    _ = Ag₁.hom ≫ (q₁P.hom ≫ eP.hom) :=
      congrArg (Ag₁.hom ≫ ·) hPair.symm
    _ = (Ag₁.hom ≫ q₁P.hom) ≫ eP.hom := (Category.assoc _ _ _).symm
    _ = (s₁.hom ≫ Ac₁.hom) ≫ eP.hom := congrArg (· ≫ eP.hom) hA₁
    _ = s₁.hom ≫ (Ac₁.hom ≫ eP.hom) := Category.assoc _ _ _
    _ = s₁.hom ≫ (eS.hom ≫ Ac₂.hom) := congrArg (s₁.hom ≫ ·) hCoord
    _ = (s₁.hom ≫ eS.hom) ≫ Ac₂.hom := (Category.assoc _ _ _).symm
    _ = (tS.hom ≫ s₂.hom) ≫ Ac₂.hom := congrArg (· ≫ Ac₂.hom) hSumHom
    _ = tS.hom ≫ (s₂.hom ≫ Ac₂.hom) := Category.assoc _ _ _
    _ = tS.hom ≫ (Ag₂.hom ≫ q₂P.hom) :=
      congrArg (tS.hom ≫ ·) hA₂.symm
    _ = (tS.hom ≫ Ag₂.hom) ≫ q₂P.hom := (Category.assoc _ _ _).symm

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
