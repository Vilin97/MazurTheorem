/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentTilde
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineSectionLocalization
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingBasicOpenExtension
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction

/-!
# Localization of module sections on affine opens over a fixed base

For a quasicoherent module on a scheme over `Spec k`, restriction from an
affine open `U` to the basic open cut out by `r : k` is localization at
`r`.  The proof transports the affine tilde localization theorem along the
canonical open immersion `Spec Γ(X,U) ⟶ X`.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

attribute [local instance] sectionsModule

private noncomputable def affineTopSectionsIso
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≅ Γ(M, U) :=
  let hTop :
      hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  M.restrictAppIso hU.fromSpec ⊤ ≪≫
    M.presheaf.mapIso (eqToIso hTop.symm).op

private noncomputable def affineBasicSectionsIso
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) :
    Γ(M.restrict hU.fromSpec, PrimeSpectrum.basicOpen f) ≅
      Γ(M, X.basicOpen f) :=
  let hBasic :
      hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f =
        X.basicOpen f :=
    hU.fromSpec_image_basicOpen f
  M.restrictAppIso hU.fromSpec (PrimeSpectrum.basicOpen f) ≪≫
    M.presheaf.mapIso (eqToIso hBasic.symm).op

private noncomputable instance affineRestrictedSectionsModule
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (V : (Spec Γ(X, U)).Opens) :
    Module Γ(X, U) Γ(M.restrict hU.fromSpec, V) :=
  Scheme.Modules.instModuleCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecAbPresheafOp
    (R := Γ(X, U)) (M := M.restrict hU.fromSpec) (U := V)

private noncomputable instance affineRestrictedBasicOpenSectionsModule
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) :
    Module Γ(X, U)
      Γ(M.restrict hU.fromSpec, PrimeSpectrum.basicOpen f) :=
  Scheme.Modules.instModuleCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecAbPresheafOp
    (R := Γ(X, U)) (M := M.restrict hU.fromSpec)
    (U := PrimeSpectrum.basicOpen f)

private lemma affineRestrictionSquare
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) :
    let ψ := hU.fromSpec
    let F := M.restrict ψ
    let hTop :
        ψ ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
      ψ.image_top_eq_opensRange.trans hU.opensRange_fromSpec
    let hBasic :
        ψ ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
      by simpa [ψ] using hU.fromSpec_image_basicOpen f
    let eTop : Γ(F, ⊤) ≅ Γ(M, U) :=
      M.restrictAppIso ψ ⊤ ≪≫
        M.presheaf.mapIso (eqToIso hTop.symm).op
    let eBasic :
        Γ(F, PrimeSpectrum.basicOpen f) ≅
          Γ(M, X.basicOpen f) :=
      M.restrictAppIso ψ (PrimeSpectrum.basicOpen f) ≪≫
        M.presheaf.mapIso (eqToIso hBasic.symm).op
    F.presheaf.map
          (homOfLE
            (le_top :
              PrimeSpectrum.basicOpen f ≤
                (⊤ : (Spec Γ(X, U)).Opens))).op ≫
        eBasic.hom =
      eTop.hom ≫
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
  dsimp only
  let ψ := hU.fromSpec
  let hTop :
      ψ ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    ψ.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let hBasic :
      ψ ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
    by simpa [ψ] using hU.fromSpec_image_basicOpen f
  let hImage :
      ψ ''ᵁ PrimeSpectrum.basicOpen f ≤
        ψ ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) :=
    ψ.image_mono le_top
  let qBasic := (eqToIso hBasic.symm).op.hom
  let qTop := (eqToIso hTop.symm).op.hom
  let qImage := (homOfLE hImage).op
  have hopen :
      qImage ≫ qBasic =
        qTop ≫ (homOfLE (X.basicOpen_le f)).op :=
    Subsingleton.elim _ _
  have hmap :
      M.presheaf.map qImage ≫ M.presheaf.map qBasic =
        M.presheaf.map qTop ≫
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
    rw [← M.presheaf.map_comp, ← M.presheaf.map_comp, hopen]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  change
    (M.restrict ψ).presheaf.map
          (homOfLE
            (le_top :
              PrimeSpectrum.basicOpen f ≤
                (⊤ : (Spec Γ(X, U)).Opens))).op ≫
        (M.restrictAppIso ψ
          (PrimeSpectrum.basicOpen f)).hom ≫
        M.presheaf.map qBasic =
      ((M.restrictAppIso ψ ⊤).hom ≫
          M.presheaf.map qTop) ≫
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op
  calc
    _ = ((M.restrictAppIso ψ ⊤).hom ≫
          M.presheaf.map qImage) ≫
        M.presheaf.map qBasic := by
      exact
        (Category.assoc _ _ _).symm.trans
          (CategoryTheory.eq_whisker
            (Scheme.Modules.map_restrictAppIso_hom ψ M
              (homOfLE
                (le_top :
                  PrimeSpectrum.basicOpen f ≤
                    (⊤ : (Spec Γ(X, U)).Opens))).op)
            (M.presheaf.map qBasic))
    _ = (M.restrictAppIso ψ ⊤).hom ≫
        (M.presheaf.map qImage ≫
          M.presheaf.map qBasic) := Category.assoc _ _ _
    _ = (M.restrictAppIso ψ ⊤).hom ≫
        (M.presheaf.map qTop ≫
          M.presheaf.map
            (homOfLE (X.basicOpen_le f)).op) := by
      rw [hmap]
    _ = _ := (Category.assoc _ _ _).symm

private lemma affineBasicSectionsIso_smul
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (f a : Γ(X, U))
    (x : Γ(M.restrict hU.fromSpec,
      PrimeSpectrum.basicOpen f)) :
    (affineBasicSectionsIso M hU f).hom (a • x) =
      (X.presheaf.map
          (homOfLE (X.basicOpen_le f)).op a) •
        (affineBasicSectionsIso M hU f).hom x := by
  have hsmul :=
    Scheme.Modules.smul_Spec_def
      (R := Γ(X, U)) (M := M.restrict hU.fromSpec)
      (U := PrimeSpectrum.basicOpen f) a x
  have hrestrict :=
    Scheme.Modules.smul_restrictAppIso_hom_apply
      hU.fromSpec M (PrimeSpectrum.basicOpen f)
      ((Spec Γ(X, U)).presheaf.map
        (PrimeSpectrum.basicOpen f).leTop.op
        ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a)) x
  rw [hsmul]
  dsimp [affineBasicSectionsIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply]
  rw [hrestrict]
  let hBasic :
      hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f =
        X.basicOpen f :=
    hU.fromSpec_image_basicOpen f
  let q := (eqToIso hBasic.symm).op.hom
  let b :=
    (hU.fromSpec.appIso
      (PrimeSpectrum.basicOpen f)).inv.hom
      ((Spec Γ(X, U)).presheaf.map
        (PrimeSpectrum.basicOpen f).leTop.op
        ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a))
  let z :=
    (M.restrictAppIso hU.fromSpec
      (PrimeSpectrum.basicOpen f)).hom x
  change
    M.presheaf.map q (b • z) =
      X.presheaf.map
          (homOfLE (X.basicOpen_le f)).op a •
        M.presheaf.map q z
  have hsmul :
      M.presheaf.map q (b • z) =
        X.presheaf.map q b • M.presheaf.map q z :=
    M.val.map_smul q b z
  rw [hsmul]
  congr 1
  let V : (Spec Γ(X, U)).Opens :=
    PrimeSpectrum.basicOpen f
  let e : V ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
    exact le_top
  have happ :
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.map V.leTop.op =
        hU.fromSpec.appLE U V e := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 1
  have hscalarMorph :
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.map V.leTop.op ≫
          (hU.fromSpec.appIso V).inv ≫
          X.presheaf.map q =
        X.presheaf.map
          (homOfLE (X.basicOpen_le f)).op := by
    calc
      _ = hU.fromSpec.appLE U V e ≫
            (hU.fromSpec.appIso V).inv ≫
            X.presheaf.map q := by
          simpa only [Category.assoc] using
            congrArg
              (fun p =>
                p ≫ (hU.fromSpec.appIso V).inv ≫
                  X.presheaf.map q) happ
      _ = X.presheaf.map
              (homOfLE
                ((hU.fromSpec.image_mono e).trans
                  (hU.fromSpec.image_preimage_eq_opensRange_inf U ▸
                    inf_le_right))).op ≫
            X.presheaf.map q := by
          simpa only [Category.assoc] using
            congrArg
              (fun p => p ≫ X.presheaf.map q)
              (Scheme.Hom.appLE_appIso_inv hU.fromSpec e)
      _ = X.presheaf.map
            (homOfLE (X.basicOpen_le f)).op := by
          rw [← Functor.map_comp]
          congr 1
  dsimp [q, b]
  exact congrArg
    (fun p : Γ(X, U) ⟶ Γ(X, X.basicOpen f) => p.hom a)
    hscalarMorph

private lemma affineTopSectionsIso_smul
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U))
    (x : Γ(M.restrict hU.fromSpec, ⊤)) :
    (affineTopSectionsIso M hU).hom (a • x) =
      a • (affineTopSectionsIso M hU).hom x := by
  rw [Scheme.Modules.smul_Spec_def]
  dsimp [affineTopSectionsIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply]
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  let hTop :
      hU.fromSpec ''ᵁ
          (⊤ : (Spec Γ(X, U)).Opens) = U :=
    hU.fromSpec.image_top_eq_opensRange.trans
      hU.opensRange_fromSpec
  let q := (eqToIso hTop.symm).op.hom
  let b :=
    (hU.fromSpec.appIso
      (⊤ : (Spec Γ(X, U)).Opens)).inv.hom
      ((Spec Γ(X, U)).presheaf.map
        (⊤ : (Spec Γ(X, U)).Opens).leTop.op
        ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a))
  let z :=
    (M.restrictAppIso hU.fromSpec
      (⊤ : (Spec Γ(X, U)).Opens)).hom x
  change M.presheaf.map q (b • z) =
    a • M.presheaf.map q z
  have hsmul :
      M.presheaf.map q (b • z) =
        X.presheaf.map q b • M.presheaf.map q z :=
    M.val.map_smul q b z
  rw [hsmul]
  congr 1
  let V : (Spec Γ(X, U)).Opens := ⊤
  let e : V ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
  have happ :
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.map V.leTop.op =
        hU.fromSpec.appLE U V e := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 1
  have hscalarMorph :
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.map V.leTop.op ≫
          (hU.fromSpec.appIso V).inv ≫
          X.presheaf.map q =
        𝟙 Γ(X, U) := by
    calc
      _ = hU.fromSpec.appLE U V e ≫
            (hU.fromSpec.appIso V).inv ≫
            X.presheaf.map q := by
          simpa only [Category.assoc] using
            congrArg
              (fun p =>
                p ≫ (hU.fromSpec.appIso V).inv ≫
                  X.presheaf.map q) happ
      _ = X.presheaf.map
              (homOfLE
                ((hU.fromSpec.image_mono e).trans
                  (hU.fromSpec.image_preimage_eq_opensRange_inf U ▸
                    inf_le_right))).op ≫
            X.presheaf.map q := by
          simpa only [Category.assoc] using
            congrArg
              (fun p => p ≫ X.presheaf.map q)
              (Scheme.Hom.appLE_appIso_inv hU.fromSpec e)
      _ = 𝟙 Γ(X, U) := by
          rw [← Functor.map_comp, ← X.presheaf.map_id]
          congr 1
  dsimp [q, b]
  exact congrArg
    (fun p : Γ(X, U) ⟶ Γ(X, U) => p.hom a)
    hscalarMorph

/--
On an affine open, restriction to the basic open cut out by an element of
the fixed base ring is localization at that element.
-/
theorem isLocalizedModule_baseBasicOpen_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (r : k) :
    IsLocalizedModule (Submonoid.powers r)
      (sectionRestrictionLinearMap
        (k := k) M (baseBasicOpen_le (k := k) U r)) := by
  let ψ := hU.fromSpec
  let F : (Spec Γ(X, U)).Modules := M.restrict ψ
  let f : Γ(X, U) := algebraMapOnOpen (k := k) U r
  let a : k →+* Γ(X, U) := algebraMapOnOpen (k := k) U
  letI : Algebra k Γ(X, U) := a.toAlgebra
  letI : Module k Γ(F, (⊤ : (Spec Γ(X, U)).Opens)) :=
    Module.compHom _ a
  letI : Module k
      Γ(F, PrimeSpectrum.basicOpen f) :=
    Module.compHom _ a
  letI : IsScalarTower k Γ(X, U) Γ(F, ⊤) :=
    IsScalarTower.of_compHom k Γ(X, U) Γ(F, ⊤)
  letI : IsScalarTower k Γ(X, U)
      Γ(F, PrimeSpectrum.basicOpen f) :=
    IsScalarTower.of_compHom k Γ(X, U)
      Γ(F, PrimeSpectrum.basicOpen f)
  let eTop : Γ(F, ⊤) ≃ₗ[k] Γ(M, U) :=
    { (affineTopSectionsIso M hU).addCommGroupIsoToAddEquiv with
      map_smul' := by
        intro c x
        change
          (affineTopSectionsIso M hU).hom (a c • x) =
            algebraMapOnOpen (k := k) U c •
              (affineTopSectionsIso M hU).hom x
        exact affineTopSectionsIso_smul M hU (a c) x }
  let eBasic :
      Γ(F, PrimeSpectrum.basicOpen f) ≃ₗ[k]
        Γ(M, baseBasicOpen (k := k) U r) :=
    { (affineBasicSectionsIso M hU f).addCommGroupIsoToAddEquiv with
      map_smul' := by
        intro c x
        change
          (affineBasicSectionsIso M hU f).hom (a c • x) =
            algebraMapOnOpen
                (k := k) (X.basicOpen f) c •
              (affineBasicSectionsIso M hU f).hom x
        rw [affineBasicSectionsIso_smul]
        congr 1
        exact algebraMapOnOpen_apply_restriction
          (k := k)
          (homOfLE
            (baseBasicOpen_le (k := k) U r)).op c }
  let φR :
      Γ(F, ⊤) →ₗ[Γ(X, U)]
        Γ(F, PrimeSpectrum.basicOpen f) :=
    ((modulesSpecToSheaf.obj F).presheaf.map
      (homOfLE
        (le_top :
          PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec Γ(X, U)).Opens))).op).hom
  haveI : F.IsQuasicoherent := by
    dsimp [F, ψ]
    infer_instance
  haveI hφR :
      IsLocalizedModule (Submonoid.powers f) φR := by
    dsimp [φR]
    exact
      AlgebraicGeometry.Scheme.Modules.section_isLocalizedModule_of_isIso_fromTildeΓ
        F f
  let φk : Γ(F, ⊤) →ₗ[k]
      Γ(F, PrimeSpectrum.basicOpen f) :=
    φR.restrictScalars k
  haveI hφk :
      IsLocalizedModule (Submonoid.powers r) φk := by
    dsimp [φk]
    exact IsLocalizedModule.restrictScalars_powers r φR
  let conjugated :
      Γ(M, U) →ₗ[k]
        Γ(M, baseBasicOpen (k := k) U r) :=
    eBasic.toLinearMap ∘ₗ φk ∘ₗ eTop.symm.toLinearMap
  haveI hconjugated :
      IsLocalizedModule (Submonoid.powers r) conjugated := by
    dsimp [conjugated]
    haveI hleft :
        IsLocalizedModule (Submonoid.powers r)
          (eBasic.toLinearMap ∘ₗ φk) :=
      IsLocalizedModule.of_linearEquiv
        (Submonoid.powers r) φk eBasic
    exact IsLocalizedModule.of_linearEquiv_right
      (Submonoid.powers r)
      (eBasic.toLinearMap ∘ₗ φk) eTop.symm
  have hmap :
      conjugated =
        sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r) := by
    apply LinearMap.ext
    intro x
    let t : Γ(F, ⊤) := eTop.symm x
    have hsquare := congrArg
      (fun p :
          F.presheaf.obj
              (op (⊤ : (Spec Γ(X, U)).Opens)) ⟶
            M.presheaf.obj (op (X.basicOpen f)) =>
        p.hom t)
      (affineRestrictionSquare M hU f)
    change eBasic (φk (eTop.symm x)) =
      sectionRestrictionLinearMap
        (k := k) M (baseBasicOpen_le (k := k) U r) x
    change
      (affineBasicSectionsIso M hU f).hom
          (F.presheaf.map
            (homOfLE
              (le_top :
                PrimeSpectrum.basicOpen f ≤
                  (⊤ : (Spec Γ(X, U)).Opens))).op t) =
        M.presheaf.map
          (homOfLE (X.basicOpen_le f)).op x
    have hsquare' :
        (affineBasicSectionsIso M hU f).hom
            (F.presheaf.map
              (homOfLE
                (le_top :
                  PrimeSpectrum.basicOpen f ≤
                    (⊤ : (Spec Γ(X, U)).Opens))).op t) =
          M.presheaf.map
            (homOfLE (X.basicOpen_le f)).op
              ((affineTopSectionsIso M hU).hom t) := by
      exact
        (AddCommGrpCat.comp_apply _ _ t).symm.trans
          (hsquare.trans (AddCommGrpCat.comp_apply _ _ t))
    calc
      _ = M.presheaf.map
          (homOfLE (X.basicOpen_le f)).op
            ((affineTopSectionsIso M hU).hom t) := hsquare'
      _ = _ := by
        rw [show (affineTopSectionsIso M hU).hom t = x by
          exact eTop.apply_symm_apply x]
  rw [← hmap]
  infer_instance

/-- Elementwise extension data supplied by affine localization. -/
theorem affineBasicOpenExtensionData
    (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    BasicOpenExtensionData (k := k) M U :=
  BasicOpenExtensionData.of_isLocalizedModule M U
    (isLocalizedModule_baseBasicOpen_of_isAffineOpen M hU)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
