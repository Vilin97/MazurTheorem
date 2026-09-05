/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineModuleBaseChange
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleQuasicoherent
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOpenUnitIso
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleCanonicalSupportThickening

/-!
# Coherent scheme-module pullback

This file builds the pullback-coherence boundary needed by the canonical
finite-support model. The first affine-spectrum layer transports
quasicoherence and finite generation through the checked tilde/base-change
isomorphism.

The named downstream consumers prove that the model module of
`CanonicalSupportThickening` is quasicoherent and of finite type; no
proper-cohomology conclusion is asserted in this interface module.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

private theorem isFiniteType_of_finite_generatingSections
    {X : Scheme.{u}} (M : X.Modules)
    (G : M.GeneratingSections) [G.IsFiniteType] :
    M.IsFiniteType := by
  let qFull := G.localGeneratorsData
  let q : SheafOfModules.LocalGeneratorsData.{u} M := qFull
  have hq : q.IsFiniteType := by
    constructor
    intro i
    exact ⟨by
      change Finite G.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite⟩
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q, hq⟩

/-- Pullback along a map of affine spectra preserves quasicoherence. -/
theorem isQuasicoherent_pullback_specMap
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((pullback (Spec.map f)).obj M).IsQuasicoherent := by
  let P := moduleSpecΓFunctor.obj M
  let Q := (ModuleCat.extendScalars f.hom).obj P
  let eBase :
      (pullback (Spec.map f)).obj ((tilde.functor R).obj P) ≅
        (tilde.functor S).obj Q :=
    (tildePullbackIsoExtendScalars f).app P
  let eM : (tilde.functor R).obj P ≅ M := by
    exact @asIso _ _ _ _ M.fromTildeΓ
      (isIso_fromTildeΓ_of_isQuasicoherent M)
  let ePull :
      (pullback (Spec.map f)).obj ((tilde.functor R).obj P) ≅
        (pullback (Spec.map f)).obj M :=
    (pullback (Spec.map f)).mapIso eM
  have hTilde : ((tilde.functor S).obj Q).IsQuasicoherent := inferInstance
  have hSource :
      ((pullback (Spec.map f)).obj
        ((tilde.functor R).obj P)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso
      eBase.symm hTilde
  exact
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso
      ePull hSource

/-- Pullback along a map of affine spectra preserves finite type for a
quasicoherent module. -/
theorem isFiniteType_pullback_specMap
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback (Spec.map f)).obj M).IsFiniteType := by
  let P := moduleSpecΓFunctor.obj M
  letI : Module.Finite R P := by
    change Module.Finite R Γ(M, ⊤)
    exact globalSections_module_finite_of_isFiniteType M
  letI : Algebra R S := f.hom.toAlgebra
  let Q := (ModuleCat.extendScalars f.hom).obj P
  letI : Module.Finite S Q := by
    change Module.Finite S (TensorProduct R S P)
    infer_instance
  let T := (tilde.functor S).obj Q
  letI : T.IsQuasicoherent := inferInstance
  letI : Module.Finite S Γ(T, ⊤) := by
    let e := tilde.isoTop Q
    exact Module.Finite.equiv e.toLinearEquiv
  obtain ⟨G, hG⟩ :=
    exists_generatingSections_of_moduleSpecΓ_finite T
  letI : G.IsFiniteType := hG
  let eBase :
      (pullback (Spec.map f)).obj ((tilde.functor R).obj P) ≅ T :=
    (tildePullbackIsoExtendScalars f).app P
  let eM : (tilde.functor R).obj P ≅ M := by
    exact @asIso _ _ _ _ M.fromTildeΓ
      (isIso_fromTildeΓ_of_isQuasicoherent M)
  let ePull :
      (pullback (Spec.map f)).obj ((tilde.functor R).obj P) ≅
        (pullback (Spec.map f)).obj M :=
    (pullback (Spec.map f)).mapIso eM
  let GSource := SheafOfModules.GeneratingSections.equivOfIso eBase.symm G
  let GTarget := SheafOfModules.GeneratingSections.equivOfIso ePull GSource
  have hGTarget : GTarget.IsFiniteType := ⟨by
    change Finite G.I
    exact SheafOfModules.GeneratingSections.IsFiniteType.finite⟩
  letI : GTarget.IsFiniteType := hGTarget
  exact isFiniteType_of_finite_generatingSections _ GTarget

/-- Pullback between affine schemes preserves quasicoherence. -/
theorem isQuasicoherent_pullback_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := by
  let a := X.isoSpec.hom
  let g := Spec.map (Hom.appTop f)
  let b := Y.isoSpec.inv
  let Mb := (pullback b).obj M
  have hMbRestrict : (M.restrict b).IsQuasicoherent := by
    infer_instance
  have hMb : Mb.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback b).app M) hMbRestrict
  letI : Mb.IsQuasicoherent := hMb
  let Mg := (pullback g).obj Mb
  have hMg : Mg.IsQuasicoherent :=
    isQuasicoherent_pullback_specMap (Hom.appTop f) Mb
  letI : Mg.IsQuasicoherent := hMg
  let Ma := (pullback a).obj Mg
  have hMaRestrict : (Mg.restrict a).IsQuasicoherent := by
    infer_instance
  have hMa : Ma.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback a).app Mg) hMaRestrict
  let egb : Mg ≅ (pullback (g ≫ b)).obj M :=
    (pullbackComp g b).app M
  let eall : Ma ≅ (pullback (a ≫ (g ≫ b))).obj M :=
    (pullback a).mapIso egb ≪≫ (pullbackComp a (g ≫ b)).app M
  have hcomp : a ≫ (g ≫ b) = f := by
    dsimp only [a, g, b]
    rw [← Category.assoc, isoSpec_hom_naturality]
    simp
  let e : Ma ≅ (pullback f).obj M :=
    eall ≪≫ (pullbackCongr hcomp).app M
  exact
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hMa

/-- Pullback to any source from an affine target preserves finite type for a
finite-type quasicoherent module. -/
theorem isFiniteType_pullback_of_isAffineTarget
    {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  obtain ⟨G, hG⟩ :=
    exists_generatingSections_of_isFiniteType_of_isAffine M
  letI : G.IsFiniteType := hG
  letI :
      PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
        (pullback f) :=
    (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  letI :
      PreservesLimit (Functor.empty.{0} (Opens Y))
        (Opens.map f.base) :=
    preservesTerminal_of_iso _ <| by
      let eY : (⊤_ Opens Y) ≅ (⊤ : Opens Y) :=
        terminalIsTerminal.uniqueUpToIso isTerminalTop
      let eX : (⊤ : Opens X) ≅ (⊤_ Opens X) :=
        isTerminalTop.uniqueUpToIso terminalIsTerminal
      exact (Opens.map f.base).mapIso eY ≪≫ eX
  letI : (Opens.map f.base).Final := inferInstance
  letI :
      (SheafOfModules.pushforward.{u}
        f.toRingCatSheafHom).IsRightAdjoint := by
    change (pushforward f).IsRightAdjoint
    infer_instance
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := Opens.map f.base) f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := Opens.map f.base) f.toRingCatSheafHom
  let eUnit :
      SheafOfModules.unit X.ringCatSheaf ≅
        (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) := by
    exact
      (asIso (SheafOfModules.pullbackObjUnitToUnit
        (F := Opens.map f.base) f.toRingCatSheafHom)).symm
  have hF :
      PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
        (pullback f) := inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G (pullback f) hF eUnit
  letI : G'.IsFiniteType := ⟨by
    change Finite G.I
    exact SheafOfModules.GeneratingSections.IsFiniteType.finite⟩
  exact isFiniteType_of_finite_generatingSections _ G'

/-- Pullback along an affine morphism preserves quasicoherence. -/
theorem isQuasicoherent_pullback_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := by
  have hlocal (U : Y.affineOpens) :
      (((pullback f).obj M).over (f ⁻¹ᵁ U.1)).IsQuasicoherent := by
    let V := f ⁻¹ᵁ U.1
    let fU := f ∣_ U.1
    let MU := (restrictFunctor U.1.ι).obj M
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine V.toScheme := U.2.preimage f
    haveI : MU.IsQuasicoherent := inferInstance
    have hPull : ((pullback fU).obj MU).IsQuasicoherent :=
      isQuasicoherent_pullback_of_isAffine fU MU
    have hRestrict :
        ((restrictFunctor V.ι).obj ((pullback f).obj M)).IsQuasicoherent :=
      (isQuasicoherent V).prop_of_iso
        ((openPullbackSquareExplicitIsoT f U.1).app M) hPull
    letI :
        ((restrictFunctor V.ι).obj ((pullback f).obj M)).IsQuasicoherent :=
      hRestrict
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen
      ((pullback f).obj M) V
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : Y.affineOpens ↦ f ⁻¹ᵁ U.1) := by
    rw [Opens.coversTop_iff, IsOpenCover,
      f.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ((pullback f).obj M) _
      (fun U : Y.affineOpens ↦ f ⁻¹ᵁ U.1) hcover hlocal

/-- Pullback along an affine morphism preserves finite type for a
quasicoherent finite-type module. -/
theorem isFiniteType_pullback_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  let N := (pullback f).obj M
  let V (U : Y.affineOpens) := f ⁻¹ᵁ U.1
  have hlocal (U : Y.affineOpens) :
      ∃ G : (N.restrict (V U).ι).GeneratingSections,
        G.IsFiniteType := by
    let fU := f ∣_ U.1
    let MU := (restrictFunctor U.1.ι).obj M
    let P := (pullback fU).obj MU
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine (V U).toScheme := U.2.preimage f
    haveI : MU.IsQuasicoherent := inferInstance
    obtain ⟨GU, hGU⟩ :=
      exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen M U
    letI : GU.IsFiniteType := hGU
    have hMUFinite : MU.IsFiniteType :=
      isFiniteType_of_finite_generatingSections MU GU
    letI : MU.IsFiniteType := hMUFinite
    have hPQuasicoherent : P.IsQuasicoherent :=
      isQuasicoherent_pullback_of_isAffine fU MU
    letI : P.IsQuasicoherent := hPQuasicoherent
    have hPFinite : P.IsFiniteType :=
      isFiniteType_pullback_of_isAffineTarget fU MU
    letI : P.IsFiniteType := hPFinite
    obtain ⟨GP, hGP⟩ :=
      exists_generatingSections_of_isFiniteType_of_isAffine P
    let e : P ≅ N.restrict (V U).ι :=
      (openPullbackSquareExplicitIsoT f U.1).app M
    let G := SheafOfModules.GeneratingSections.equivOfIso e GP
    refine ⟨G, ⟨?_⟩⟩
    change Finite GP.I
    exact hGP.finite
  choose G hG using hlocal
  let q : N.LocalGeneratorsData :=
    { I := Y.affineOpens
      X := V
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover,
          f.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)]
      generators := fun U ↦
        generatingSectionsOverOfRestrict N (V U) (G U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    letI : (G U).IsFiniteType := hG U
    exact generatingSectionsOverOfRestrict_isFiniteType N (V U) (G U)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩

namespace CanonicalSupportThickening

/-- The canonical support model of a quasicoherent module is
quasicoherent. This is the named downstream consumer of affine-morphism
pullback quasicoherence. -/
theorem modelModule_isQuasicoherent
    {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M) :
    A.modelModule.IsQuasicoherent := by
  change ((pullback A.inclusion).obj M).IsQuasicoherent
  exact isQuasicoherent_pullback_of_isAffineHom A.inclusion M

/-- The canonical support model of a finite-type quasicoherent module is
of finite type. This is the finite-generation input for finite pushforward. -/
theorem modelModule_isFiniteType
    {X : Scheme.{u}} {M : X.Modules}
    [M.IsQuasicoherent] [M.IsFiniteType]
    (A : CanonicalSupportThickening M) :
    A.modelModule.IsFiniteType := by
  change ((pullback A.inclusion).obj M).IsFiniteType
  exact isFiniteType_pullback_of_isAffineHom A.inclusion M

end CanonicalSupportThickening

end AlgebraicGeometry.Scheme.Modules
