/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineTildeTensorNaturality
import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineModuleBaseChange
import MazurTorsion.Upstream.AINTLIB.Picard.PullbackTensorSection

/-!
# Tensor coherence for affine tilde base change

This file compares the affine tilde tensor isomorphism with the canonical monoidal structure on
pullback and extension of scalars.  The operational input is the formula for the affine tilde
tensor isomorphism on pure top-level sections.

Implementation lemmas about sheafification remain private.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineTilde

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

private noncomputable local instance affineTildeTensorCoherenceSchemeModulesMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private noncomputable local instance affineTildeTensorCoherenceSheafModulesMonoidal
    (X : Scheme.{u}) : MonoidalCategory (SheafOfModules X.ringCatSheaf) := by
  change MonoidalCategory X.Modules
  exact Scheme.Modules.monoidalCategory X

private noncomputable local instance affineTildeTensorCoherencePresheafModulesMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules := by
  change MonoidalCategory
    (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

/-- The pullback-unit image of a top-level section, transported from the inverse image of the
top open to the top open. -/
private noncomputable def pullbackUnitTop
    {X Y : Scheme.{u}} (f : Y ⟶ X) (P : X.Modules)
    (x : Γ(P, (⊤ : X.Opens))) : Γ((Scheme.Modules.pullback f).obj P, ⊤) :=
  let htop :
      (Opens.map f.base).op.obj (.op (⊤ : X.Opens)) = .op (⊤ : Y.Opens) := by
    simp
  (((Scheme.Modules.pullback f).obj P).presheaf.map (eqToHom htop))
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
      (.op (⊤ : X.Opens)) x)

/-- The transported top-level pullback unit is natural in the module sheaf. -/
private theorem pullbackUnitTop_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) {P Q : X.Modules}
    (q : P ⟶ Q) (x : Γ(P, (⊤ : X.Opens))) :
    ((Scheme.Modules.pullback f).map q).val.app (.op (⊤ : Y.Opens))
        (pullbackUnitTop f P x) =
      pullbackUnitTop f Q (q.val.app (.op (⊤ : X.Opens)) x) := by
  let PB := Scheme.Modules.pullback f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let htop :
      (Opens.map f.base).op.obj (.op (⊤ : X.Opens)) = .op (⊤ : Y.Opens) := by
    simp
  let raw := (adj.unit.app P).val.app (.op (⊤ : X.Opens)) x
  have hrestrict :=
    PresheafOfModules.naturality_apply (PB.map q).val (eqToHom htop) raw
  change (PB.map q).val.app (.op (⊤ : Y.Opens))
      ((PB.obj P).presheaf.map (eqToHom htop) raw) =
    (PB.obj Q).presheaf.map (eqToHom htop)
      ((PB.map q).val.app
        ((Opens.map f.base).op.obj (.op (⊤ : X.Opens))) raw) at hrestrict
  have hunit := congrArg
    (fun k ↦ k.val.app (.op (⊤ : X.Opens)) x) (adj.unit.naturality q)
  conv_lhs at hunit =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at hunit =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change (adj.unit.app Q).val.app (.op (⊤ : X.Opens))
      (q.val.app (.op (⊤ : X.Opens)) x) =
    (PB.map q).val.app
      ((Opens.map f.base).op.obj (.op (⊤ : X.Opens))) raw at hunit
  change (PB.map q).val.app (.op (⊤ : Y.Opens))
      ((PB.obj P).presheaf.map (eqToHom htop) raw) =
    (PB.obj Q).presheaf.map (eqToHom htop)
      ((adj.unit.app Q).val.app (.op (⊤ : X.Opens))
        (q.val.app (.op (⊤ : X.Opens)) x))
  exact hrestrict.trans
    (congrArg ((PB.obj Q).presheaf.map (eqToHom htop)) hunit.symm)

/-- The named affine pullback generator is the transported top-level pullback unit. -/
private theorem tildePullbackGenerator_eq_pullbackUnitTop
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat R) (m : M) :
    Scheme.Modules.tildePullbackGenerator φ M m =
      pullbackUnitTop (Spec.map φ) (_root_.AlgebraicGeometry.tilde M)
        (_root_.AlgebraicGeometry.tilde.toOpen M ⊤ m) := by
  exact Scheme.Modules.tildePullbackGenerator_eq_pullbackUnit_toOpen_top φ M m

/-- Pure tensor sections commute with transport along an equality of opens. -/
private theorem tensorSection_eqToHom
    {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens}
    (h : (.op U : X.Opensᵒᵖ) = .op V) (x : Γ(M, U)) (y : Γ(N, U)) :
    (M ⊗ N).presheaf.map (eqToHom h)
        (ModularCurves.tensorSection M N U x y) =
      ModularCurves.tensorSection M N V
        (M.presheaf.map (eqToHom h) x)
        (N.presheaf.map (eqToHom h) y) := by
  have hUV : U = V := congrArg Opposite.unop h
  subst V
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  let t := ModularCurves.tensorSection M N U x y
  have hT := (CategoryTheory.congr_fun
    ((M ⊗ N).presheaf.map_id (Opposite.op U)) t).trans rfl
  have hM := (CategoryTheory.congr_fun
    (M.presheaf.map_id (Opposite.op U)) x).trans rfl
  have hN := (CategoryTheory.congr_fun
    (N.presheaf.map_id (Opposite.op U)) y).trans rfl
  exact hT.trans (congrArg₂
    (fun a b ↦ ModularCurves.tensorSection M N U a b) hM.symm hN.symm)

/-- The pullback cotensorator sends the transported pullback-unit image of a pure top-level
tensor section to the tensor section of the two transported pullback-unit images. -/
private theorem pullback_δ_pullbackUnitTop_tensorSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    let PB := Scheme.Modules.pullback f
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
    (Functor.OplaxMonoidal.δ PB M N).val.app
        (Opposite.op (⊤ : Y.Opens))
        (pullbackUnitTop f (M ⊗ N)
          (ModularCurves.tensorSection M N ⊤ x y)) =
      ModularCurves.tensorSection (PB.obj M) (PB.obj N) ⊤
        (pullbackUnitTop f M x) (pullbackUnitTop f N y) := by
  dsimp only
  let PB := Scheme.Modules.pullback f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let W := f ⁻¹ᵁ (⊤ : X.Opens)
  let htop : Opposite.op W = Opposite.op (⊤ : Y.Opens) := by
    dsimp only [W]
    simp
  let rawM := (adj.unit.app M).val.app
    (Opposite.op (⊤ : X.Opens)) x
  let rawN := (adj.unit.app N).val.app
    (Opposite.op (⊤ : X.Opens)) y
  let rawT := (adj.unit.app (M ⊗ N)).val.app
    (Opposite.op (⊤ : X.Opens))
    (ModularCurves.tensorSection M N ⊤ x y)
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  let δ := Functor.OplaxMonoidal.δ PB M N
  have hδnat := PresheafOfModules.naturality_apply δ.val (eqToHom htop) rawT
  change δ.val.app (Opposite.op (⊤ : Y.Opens))
      ((PB.obj (M ⊗ N)).presheaf.map (eqToHom htop) rawT) =
    ((PB.obj M ⊗ PB.obj N).presheaf.map (eqToHom htop))
      (δ.val.app (Opposite.op W) rawT) at hδnat
  have hδraw := ModularCurves.pullback_δ_unit_tensorSection f M N ⊤ x y
  dsimp only at hδraw
  change δ.val.app (Opposite.op W) rawT =
    ModularCurves.tensorSection (PB.obj M) (PB.obj N) W rawM rawN at hδraw
  have htransport := tensorSection_eqToHom (PB.obj M) (PB.obj N)
    htop rawM rawN
  change ((PB.obj M ⊗ PB.obj N).presheaf.map (eqToHom htop))
      (ModularCurves.tensorSection (PB.obj M) (PB.obj N) W rawM rawN) =
    ModularCurves.tensorSection (PB.obj M) (PB.obj N) ⊤
      ((PB.obj M).presheaf.map (eqToHom htop) rawM)
      ((PB.obj N).presheaf.map (eqToHom htop) rawN) at htransport
  change δ.val.app (Opposite.op (⊤ : Y.Opens))
      (pullbackUnitTop f (M ⊗ N)
        (ModularCurves.tensorSection M N ⊤ x y)) =
    ModularCurves.tensorSection (PB.obj M) (PB.obj N) ⊤
      (pullbackUnitTop f M x) (pullbackUnitTop f N y)
  exact hδnat.trans
    ((congrArg ((PB.obj M ⊗ PB.obj N).presheaf.map (eqToHom htop))
      hδraw).trans htransport)

/-- The extension-of-scalars tensorator sends a tensor of denominator-one generators to the
denominator-one generator of the tensor. -/
private theorem extendScalars_μ_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M N : ModuleCat R) (m : M) (n : N) :
    let ES := ModuleCat.extendScalars φ.hom
    (Functor.Monoidal.μIso ES M N).hom
        (((1 : S) ⊗ₜ[R, φ.hom] m) ⊗ₜ[S]
          ((1 : S) ⊗ₜ[R, φ.hom] n)) =
      (1 : S) ⊗ₜ[R, φ.hom] (m ⊗ₜ[R] n) := by
  let ES := ModuleCat.extendScalars φ.hom
  let μ := (Functor.Monoidal.μIso ES M N).hom
  let z₀ : ES.obj (M ⊗ N) :=
    (1 : S) ⊗ₜ[R, φ.hom] (m ⊗ₜ[R] n)
  have hδ := ModuleCat.extendScalars_δ_tmul φ.hom M N m n
  have hδμ := ConcreteCategory.congr_hom
    (Functor.Monoidal.δ_μ ES M N) z₀
  change μ ((Functor.OplaxMonoidal.δ ES M N) z₀) = z₀ at hδμ
  change μ
      (((1 : S) ⊗ₜ[R, φ.hom] m) ⊗ₜ[S]
        ((1 : S) ⊗ₜ[R, φ.hom] n)) = z₀
  exact (congrArg μ hδ.symm).trans hδμ

/-- Tilde maps send denominator-one top sections to denominator-one top sections. -/
private theorem tilde_map_toOpen_top
    {R : CommRingCat.{u}} {M N : ModuleCat R}
    (q : M ⟶ N) (m : M) :
    (_root_.AlgebraicGeometry.tilde.map (R := R) q).val.app
        (.op (⊤ : (Spec R).Opens))
        (_root_.AlgebraicGeometry.tilde.toOpen (R := R) M ⊤ m) =
      _root_.AlgebraicGeometry.tilde.toOpen (R := R) N ⊤ (q m) := by
  have h := _root_.AlgebraicGeometry.tilde.toOpen_map_app q
    (⊤ : (Spec R).Opens)
  exact ConcreteCategory.congr_hom h m

/-- An inverse isomorphism carries a section back to a specified preimage whenever the forward
isomorphism carries that preimage to the section. -/
private theorem iso_inv_val_app_of_hom_val_app
    {X : Scheme.{u}} {P Q : X.Modules} (e : P ≅ Q)
    (U : X.Opens) (x : Γ(P, U)) (y : Γ(Q, U))
    (h : e.hom.val.app (.op U) x = y) :
    e.inv.val.app (.op U) y = x := by
  have hid := congrArg (fun q ↦ q.val.app (.op U) x) e.hom_inv_id
  conv_lhs at hid =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change e.inv.val.app (.op U) (e.hom.val.app (.op U) x) = x at hid
  exact (congrArg (e.inv.val.app (.op U)) h.symm).trans hid

/-- The inverse direct affine tilde tensor/base-change comparison sends a denominator-one target
section to the pullback-unit image of the corresponding pure tensor section. -/
private theorem tensorAsSheafification_hom_tensorSection
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)
    (U : (Spec (CommRingCat.of R)).Opens)
    (x : Γ(_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R M), U))
    (y : Γ(_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R N), U)) :
    (tensorAsSheafification R M N).hom.val.app (.op U)
        (ModularCurves.tensorSection
          (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
            (ModuleCat.of R M))
          (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
            (ModuleCat.of R N)) U x y) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app
          ((_root_.AlgebraicGeometry.tilde
              (R := CommRingCat.of R) (ModuleCat.of R M)).val ⊗
            (_root_.AlgebraicGeometry.tilde
              (R := CommRingCat.of R) (ModuleCat.of R N)).val)).app
                (.op U) (x ⊗ₜ y) := by
  let e := tensorAsSheafification R M N
  let z := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app
      ((_root_.AlgebraicGeometry.tilde
          (R := CommRingCat.of R) (ModuleCat.of R M)).val ⊗
        (_root_.AlgebraicGeometry.tilde
          (R := CommRingCat.of R) (ModuleCat.of R N)).val)).app
            (.op U) (x ⊗ₜ y)
  have h := congrArg (fun q ↦ q.val.app (.op U) z) e.inv_hom_id
  conv_lhs at h =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change e.hom.val.app (.op U) (e.inv.val.app (.op U) z) = z at h
  unfold ModularCurves.tensorSection
  change e.hom.val.app (.op U) (e.inv.val.app (.op U) z) = z
  exact h

private theorem sheafification_map_unit_app
    (R : Type u) [CommRing R]
    {A B : (Spec (CommRingCat.of R)).PresheafOfModules}
    (f : A ⟶ B) (U : (Spec (CommRingCat.of R)).Opens)
    (x : A.obj (.op U)) :
    ((PresheafOfModules.sheafification
      (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).map f).val.app
        (.op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app A).app
            (.op U) x) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app B).app
          (.op U) (f.app (.op U) x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)
  have h := congrArg (fun q ↦ q.app (.op U) x) (adj.unit.naturality f)
  conv_lhs at h =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at h =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact h.symm

private theorem sheafifyValIso_hom_unit_app
    (R : Type u) [CommRing R]
    (P : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) (x : P.val.obj (.op U)) :
    (sheafifyValIso R P).hom.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app P.val).app
            (.op U) x) = x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)
  have h := congrArg (fun q ↦ q.app (.op U) x) (adj.right_triangle_components P)
  conv_lhs at h =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (sheafifyValIso R P).hom.val.app (.op U)
    ((adj.unit.app P.val).app (.op U) x) = x at h
  exact h

private theorem tildeTensorUnderlyingHom_tmul_toOpen_top
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (tildeTensorUnderlyingHom R M N).app
        (.op (⊤ : (Spec (CommRingCat.of R)).Opens))
        (_root_.AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R)
            (ModuleCat.of R M) ⊤ m ⊗ₜ
          _root_.AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R)
            (ModuleCat.of R N) ⊤ n) =
      _root_.AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R (M ⊗[R] N)) ⊤
          (m ⊗ₜ[R] n) := by
  change sectionsTensorPure R M N ⊤
      (StructureSheaf.toOpenₗ R M ⊤ m)
      (StructureSheaf.toOpenₗ R N ⊤ n) =
    StructureSheaf.toOpenₗ R (M ⊗[R] N) ⊤ (m ⊗ₜ[R] n)
  apply Subtype.ext
  funext x
  letI := x.1.isPrime
  change localizedTensorEquiv R M N x.1.asIdeal.primeCompl
      (LocalizedModule.mk m 1 ⊗ₜ[StructureSheaf.Localizations R x.1]
        LocalizedModule.mk n 1) =
    LocalizedModule.mk (m ⊗ₜ[R] n) 1
  simpa using localizedTensorEquiv_mk R M N x.1.asIdeal.primeCompl m n
    (1 : x.1.asIdeal.primeCompl) (1 : x.1.asIdeal.primeCompl)

private theorem tildeTensorIso_hom_eq
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) :
    (tildeTensorIso R M N).hom =
      (tensorAsSheafification R M N).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).map
            (tildeTensorUnderlyingHom R M N) ≫
        (sheafifyValIso R
          (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
            (ModuleCat.of R (M ⊗[R] N)))).hom := by
  rfl

/-- On pure top-level sections, the affine tilde tensor comparison is the usual pure-tensor
map. -/
theorem tildeTensorIso_hom_tensorSection_toOpen_top
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (tildeTensorIso R M N).hom.val.app
        (.op (⊤ : (Spec (CommRingCat.of R)).Opens))
        (ModularCurves.tensorSection
          (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
            (ModuleCat.of R M))
          (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
            (ModuleCat.of R N)) ⊤
          (_root_.AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R)
            (ModuleCat.of R M) ⊤ m)
          (_root_.AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R)
            (ModuleCat.of R N) ⊤ n)) =
      _root_.AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R (M ⊗[R] N)) ⊤
          (m ⊗ₜ[R] n) := by
  let TM := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
    (ModuleCat.of R M)
  let TN := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
    (ModuleCat.of R N)
  let TP := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
    (ModuleCat.of R (M ⊗[R] N))
  let L := PresheafOfModules.sheafification
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)
  let e := tensorAsSheafification R M N
  let t := tildeTensorUnderlyingHom R M N
  let c := sheafifyValIso R TP
  let x := _root_.AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R)
    (ModuleCat.of R M) (⊤ : (Spec (CommRingCat.of R)).Opens) m
  let y := _root_.AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R)
    (ModuleCat.of R N) (⊤ : (Spec (CommRingCat.of R)).Opens) n
  let z := (adj.unit.app (TM.val ⊗ TN.val)).app (.op ⊤) (x ⊗ₜ y)
  have he := tensorAsSheafification_hom_tensorSection R M N ⊤ x y
  change e.hom.val.app (.op ⊤)
    (ModularCurves.tensorSection TM TN ⊤ x y) = z at he
  have hmap := sheafification_map_unit_app R t ⊤ (x ⊗ₜ y)
  change (L.map t).val.app (.op ⊤) z =
    (adj.unit.app TP.val).app (.op ⊤) (t.app (.op ⊤) (x ⊗ₜ y)) at hmap
  have hc := sheafifyValIso_hom_unit_app R TP ⊤
    (t.app (.op ⊤) (x ⊗ₜ y))
  change c.hom.val.app (.op ⊤)
    ((adj.unit.app TP.val).app (.op ⊤) (t.app (.op ⊤) (x ⊗ₜ y))) =
      t.app (.op ⊤) (x ⊗ₜ y) at hc
  have ht := tildeTensorUnderlyingHom_tmul_toOpen_top R M N m n
  change t.app (.op ⊤) (x ⊗ₜ y) =
    _root_.AlgebraicGeometry.tilde.toOpen
      (R := CommRingCat.of R) (ModuleCat.of R (M ⊗[R] N)) ⊤
        (m ⊗ₜ[R] n) at ht
  rw [tildeTensorIso_hom_eq R M N]
  change c.hom.val.app (.op ⊤)
      ((L.map t).val.app (.op ⊤)
        (e.hom.val.app (.op ⊤)
          (ModularCurves.tensorSection TM TN ⊤ x y))) = _
  exact (congrArg (fun q ↦ c.hom.val.app (.op ⊤)
    ((L.map t).val.app (.op ⊤) q)) he).trans
      ((congrArg (fun q ↦ c.hom.val.app (.op ⊤) q) hmap).trans
        (hc.trans ht))

private theorem directTensorPullbackIso_inv_toOpen_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (m : M) (n : N) :
    let f := Spec.map φ
    let PB := Scheme.Modules.pullback f
    let ES := ModuleCat.extendScalars φ.hom
    let MR := ModuleCat.of R M
    let NR := ModuleCat.of R N
    let P := ModuleCat.of R (M ⊗[R] N)
    let τR := tildeTensorIso R M N
    let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
    let C := PB.mapIso τR ≪≫ A.app P
    C.inv.val.app (.op (⊤ : (Spec S).Opens))
        (_root_.AlgebraicGeometry.tilde.toOpen (R := S) (ES.obj P) ⊤
          ((1 : S) ⊗ₜ[R, φ.hom] (m ⊗ₜ[R] n))) =
      pullbackUnitTop f
        (_root_.AlgebraicGeometry.tilde (R := R) MR ⊗
          _root_.AlgebraicGeometry.tilde (R := R) NR)
        (ModularCurves.tensorSection
          (_root_.AlgebraicGeometry.tilde (R := R) MR)
          (_root_.AlgebraicGeometry.tilde (R := R) NR) ⊤
          (_root_.AlgebraicGeometry.tilde.toOpen (R := R) MR ⊤ m)
          (_root_.AlgebraicGeometry.tilde.toOpen (R := R) NR ⊤ n)) := by
  dsimp only
  let f := Spec.map φ
  let PB := Scheme.Modules.pullback f
  let ES := ModuleCat.extendScalars φ.hom
  let MR := ModuleCat.of R M
  let NR := ModuleCat.of R N
  let P := ModuleCat.of R (M ⊗[R] N)
  let τR := tildeTensorIso R M N
  let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
  let C := PB.mapIso τR ≪≫ A.app P
  let p : P := m ⊗ₜ[R] n
  let z : ES.obj P := (1 : S) ⊗ₜ[R, φ.hom] p
  let xM := _root_.AlgebraicGeometry.tilde.toOpen (R := R) MR
    (⊤ : (Spec R).Opens) m
  let xN := _root_.AlgebraicGeometry.tilde.toOpen (R := R) NR
    (⊤ : (Spec R).Opens) n
  let t := ModularCurves.tensorSection
    (_root_.AlgebraicGeometry.tilde (R := R) MR)
    (_root_.AlgebraicGeometry.tilde (R := R) NR) ⊤ xM xN
  let xP := _root_.AlgebraicGeometry.tilde.toOpen (R := R) P
    (⊤ : (Spec R).Opens) p
  let yP := _root_.AlgebraicGeometry.tilde.toOpen (R := S) (ES.obj P)
    (⊤ : (Spec S).Opens) z
  let gP := Scheme.Modules.tildePullbackGenerator φ P p
  let eP := A.app P
  have heP := Scheme.Modules.tildePullbackIsoExtendScalars_hom_generator φ P p
  change eP.hom.val.app (.op ⊤) gP = yP at heP
  have hePinv : eP.inv.val.app (.op ⊤) yP = gP :=
    iso_inv_val_app_of_hom_val_app eP ⊤ gP yP heP
  have hbridge := tildePullbackGenerator_eq_pullbackUnitTop φ P p
  change gP = pullbackUnitTop f (_root_.AlgebraicGeometry.tilde (R := R) P) xP
    at hbridge
  let q := PB.map τR.inv
  have hnat := pullbackUnitTop_naturality f τR.inv xP
  change q.val.app (.op ⊤)
      (pullbackUnitTop f (_root_.AlgebraicGeometry.tilde (R := R) P) xP) =
    pullbackUnitTop f
      (_root_.AlgebraicGeometry.tilde (R := R) MR ⊗
        _root_.AlgebraicGeometry.tilde (R := R) NR)
      (τR.inv.val.app (.op ⊤) xP) at hnat
  have hτ := tildeTensorIso_hom_tensorSection_toOpen_top R
    (ModuleCat.of R M) (ModuleCat.of R N) m n
  change τR.hom.val.app (.op ⊤) t = xP at hτ
  have hτinv : τR.inv.val.app (.op ⊤) xP = t :=
    iso_inv_val_app_of_hom_val_app τR ⊤ t xP hτ
  change q.val.app (.op ⊤) (eP.inv.val.app (.op ⊤) yP) =
    pullbackUnitTop f
      (_root_.AlgebraicGeometry.tilde (R := R) MR ⊗
        _root_.AlgebraicGeometry.tilde (R := R) NR) t
  exact (congrArg (q.val.app (.op ⊤)) (hePinv.trans hbridge)).trans
    (hnat.trans (congrArg (pullbackUnitTop f
      (_root_.AlgebraicGeometry.tilde (R := R) MR ⊗
        _root_.AlgebraicGeometry.tilde (R := R) NR)) hτinv))

/-- The canonical cotensorator/factorwise-base-change/tensorator path has the expected value on
the pullback-unit image of a pure top-level tensor section. -/
private theorem canonicalTensorPullbackHom_pullbackUnitTop_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (m : M) (n : N) :
    let f := Spec.map φ
    let PB := Scheme.Modules.pullback f
    let ES := ModuleCat.extendScalars φ.hom
    let MR := ModuleCat.of R M
    let NR := ModuleCat.of R N
    let P := ModuleCat.of R (M ⊗[R] N)
    let EM := ES.obj MR
    let EN := ES.obj NR
    let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
    let τS := tildeTensorIso S EM EN
    let μ := (Functor.Monoidal.μIso ES MR NR).hom
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
    let K := Functor.OplaxMonoidal.δ PB
          (_root_.AlgebraicGeometry.tilde (R := R) MR)
          (_root_.AlgebraicGeometry.tilde (R := R) NR) ≫
        (A.hom.app MR ⊗ₘ A.hom.app NR) ≫ τS.hom ≫
        _root_.AlgebraicGeometry.tilde.map (R := S) μ
    K.val.app (.op (⊤ : (Spec S).Opens))
        (pullbackUnitTop f
          (_root_.AlgebraicGeometry.tilde (R := R) MR ⊗
            _root_.AlgebraicGeometry.tilde (R := R) NR)
          (ModularCurves.tensorSection
            (_root_.AlgebraicGeometry.tilde (R := R) MR)
            (_root_.AlgebraicGeometry.tilde (R := R) NR) ⊤
            (_root_.AlgebraicGeometry.tilde.toOpen (R := R) MR ⊤ m)
            (_root_.AlgebraicGeometry.tilde.toOpen (R := R) NR ⊤ n))) =
      _root_.AlgebraicGeometry.tilde.toOpen (R := S) (ES.obj P) ⊤
        ((1 : S) ⊗ₜ[R, φ.hom] (m ⊗ₜ[R] n)) := by
  dsimp only
  let f := Spec.map φ
  let PB := Scheme.Modules.pullback f
  let ES := ModuleCat.extendScalars φ.hom
  let MR := ModuleCat.of R M
  let NR := ModuleCat.of R N
  let P := ModuleCat.of R (M ⊗[R] N)
  let EM := ES.obj MR
  let EN := ES.obj NR
  let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
  let eM := A.hom.app MR
  let eN := A.hom.app NR
  let τS := tildeTensorIso S EM EN
  let μ := (Functor.Monoidal.μIso ES MR NR).hom
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  let δ := Functor.OplaxMonoidal.δ PB
    (_root_.AlgebraicGeometry.tilde (R := R) MR)
    (_root_.AlgebraicGeometry.tilde (R := R) NR)
  let K := δ ≫ (eM ⊗ₘ eN) ≫ τS.hom ≫
    _root_.AlgebraicGeometry.tilde.map (R := S) μ
  let xM := _root_.AlgebraicGeometry.tilde.toOpen (R := R) MR
    (⊤ : (Spec R).Opens) m
  let xN := _root_.AlgebraicGeometry.tilde.toOpen (R := R) NR
    (⊤ : (Spec R).Opens) n
  let uM := pullbackUnitTop f (_root_.AlgebraicGeometry.tilde (R := R) MR) xM
  let uN := pullbackUnitTop f (_root_.AlgebraicGeometry.tilde (R := R) NR) xN
  let t := ModularCurves.tensorSection
    (_root_.AlgebraicGeometry.tilde (R := R) MR)
    (_root_.AlgebraicGeometry.tilde (R := R) NR) ⊤ xM xN
  let uT := pullbackUnitTop f
    (_root_.AlgebraicGeometry.tilde (R := R) MR ⊗
      _root_.AlgebraicGeometry.tilde (R := R) NR) t
  let gM := Scheme.Modules.tildePullbackGenerator φ MR m
  let gN := Scheme.Modules.tildePullbackGenerator φ NR n
  let zm : EM := (1 : S) ⊗ₜ[R, φ.hom] m
  let zn : EN := (1 : S) ⊗ₜ[R, φ.hom] n
  let zpair := zm ⊗ₜ[S] zn
  let z : ES.obj P := (1 : S) ⊗ₜ[R, φ.hom] (m ⊗ₜ[R] n)
  let yM := _root_.AlgebraicGeometry.tilde.toOpen (R := S) EM
    (⊤ : (Spec S).Opens) zm
  let yN := _root_.AlgebraicGeometry.tilde.toOpen (R := S) EN
    (⊤ : (Spec S).Opens) zn
  let yPair := _root_.AlgebraicGeometry.tilde.toOpen (R := S)
    (ModuleCat.of S (EM ⊗[S] EN)) (⊤ : (Spec S).Opens) zpair
  let y := _root_.AlgebraicGeometry.tilde.toOpen (R := S) (ES.obj P)
    (⊤ : (Spec S).Opens) z
  have hδ := pullback_δ_pullbackUnitTop_tensorSection f
    (_root_.AlgebraicGeometry.tilde (R := R) MR)
    (_root_.AlgebraicGeometry.tilde (R := R) NR) xM xN
  dsimp only at hδ
  change δ.val.app (.op ⊤) uT =
    ModularCurves.tensorSection (PB.obj
      (_root_.AlgebraicGeometry.tilde (R := R) MR))
      (PB.obj (_root_.AlgebraicGeometry.tilde (R := R) NR)) ⊤ uM uN at hδ
  have hbridgeM := tildePullbackGenerator_eq_pullbackUnitTop φ MR m
  have hbridgeN := tildePullbackGenerator_eq_pullbackUnitTop φ NR n
  change gM = uM at hbridgeM
  change gN = uN at hbridgeN
  have heMgen := Scheme.Modules.tildePullbackIsoExtendScalars_hom_generator φ MR m
  have heNgen := Scheme.Modules.tildePullbackIsoExtendScalars_hom_generator φ NR n
  change eM.val.app (.op ⊤) gM = yM at heMgen
  change eN.val.app (.op ⊤) gN = yN at heNgen
  have heM : eM.val.app (.op ⊤) uM = yM :=
    (congrArg (eM.val.app (.op ⊤)) hbridgeM.symm).trans heMgen
  have heN : eN.val.app (.op ⊤) uN = yN :=
    (congrArg (eN.val.app (.op ⊤)) hbridgeN.symm).trans heNgen
  have hmap := ModularCurves.tensorSection_map eM eN ⊤ uM uN
  have hfactor :
      (eM ⊗ₘ eN).val.app (.op ⊤)
          (ModularCurves.tensorSection
            (PB.obj (_root_.AlgebraicGeometry.tilde (R := R) MR))
            (PB.obj (_root_.AlgebraicGeometry.tilde (R := R) NR)) ⊤ uM uN) =
        ModularCurves.tensorSection
          (_root_.AlgebraicGeometry.tilde (R := S) EM)
          (_root_.AlgebraicGeometry.tilde (R := S) EN) ⊤ yM yN :=
    hmap.trans (congrArg₂
      (fun a b ↦ ModularCurves.tensorSection
        (_root_.AlgebraicGeometry.tilde (R := S) EM)
        (_root_.AlgebraicGeometry.tilde (R := S) EN) ⊤ a b) heM heN)
  have hτ := tildeTensorIso_hom_tensorSection_toOpen_top S EM EN zm zn
  change τS.hom.val.app (.op ⊤)
    (ModularCurves.tensorSection
      (_root_.AlgebraicGeometry.tilde (R := S) EM)
      (_root_.AlgebraicGeometry.tilde (R := S) EN) ⊤ yM yN) = yPair at hτ
  have hmapμ := tilde_map_toOpen_top μ zpair
  change (_root_.AlgebraicGeometry.tilde.map (R := S) μ).val.app
    (.op ⊤) yPair =
      _root_.AlgebraicGeometry.tilde.toOpen (R := S) (ES.obj P) ⊤ (μ zpair)
        at hmapμ
  have hμ := extendScalars_μ_tmul φ MR NR m n
  change μ zpair = z at hμ
  have htail :
      (_root_.AlgebraicGeometry.tilde.map (R := S) μ).val.app
          (.op ⊤) yPair = y :=
    hmapμ.trans (congrArg
      (_root_.AlgebraicGeometry.tilde.toOpen (R := S) (ES.obj P) ⊤) hμ)
  change (_root_.AlgebraicGeometry.tilde.map (R := S) μ).val.app (.op ⊤)
    (τS.hom.val.app (.op ⊤)
      ((eM ⊗ₘ eN).val.app (.op ⊤) (δ.val.app (.op ⊤) uT))) = y
  exact (congrArg (fun q ↦
      (_root_.AlgebraicGeometry.tilde.map (R := S) μ).val.app (.op ⊤)
        (τS.hom.val.app (.op ⊤) ((eM ⊗ₘ eN).val.app (.op ⊤) q))) hδ).trans
    ((congrArg (fun q ↦
      (_root_.AlgebraicGeometry.tilde.map (R := S) μ).val.app (.op ⊤)
        (τS.hom.val.app (.op ⊤) q)) hfactor).trans
      ((congrArg
        ((_root_.AlgebraicGeometry.tilde.map (R := S) μ).val.app (.op ⊤)) hτ).trans
        htail))

/-- The direct affine tensor/base-change comparison agrees with the canonical path followed by
the extension-of-scalars tensorator.  This μ-oriented form is an implementation lemma for the
public oplax-δ square below. -/
private theorem directTensorPullbackIso_hom_eq_canonical_μ
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    let f := Spec.map φ
    let PB := Scheme.Modules.pullback f
    let ES := ModuleCat.extendScalars φ.hom
    let MR := ModuleCat.of R M
    let NR := ModuleCat.of R N
    let P := MR ⊗ NR
    let EM := ES.obj MR
    let EN := ES.obj NR
    let τR := tildeTensorIso R M N
    let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
    let C := PB.mapIso τR ≪≫ A.app P
    let τS := tildeTensorIso S EM EN
    let μ := (Functor.Monoidal.μIso ES MR NR).hom
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
    let K := Functor.OplaxMonoidal.δ PB
          (_root_.AlgebraicGeometry.tilde (R := R) MR)
          (_root_.AlgebraicGeometry.tilde (R := R) NR) ≫
        (A.hom.app MR ⊗ₘ A.hom.app NR) ≫ τS.hom ≫
        _root_.AlgebraicGeometry.tilde.map (R := S) μ
    C.hom = K := by
  dsimp only
  let f := Spec.map φ
  let PB := Scheme.Modules.pullback f
  let ES := ModuleCat.extendScalars φ.hom
  let MR := ModuleCat.of R M
  let NR := ModuleCat.of R N
  let P := MR ⊗ NR
  let EM := ES.obj MR
  let EN := ES.obj NR
  let τR := tildeTensorIso R M N
  let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
  let C := PB.mapIso τR ≪≫ A.app P
  let τS := tildeTensorIso S EM EN
  let μ := (Functor.Monoidal.μIso ES MR NR).hom
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  let K := Functor.OplaxMonoidal.δ PB
      (_root_.AlgebraicGeometry.tilde (R := R) MR)
      (_root_.AlgebraicGeometry.tilde (R := R) NR) ≫
    (A.hom.app MR ⊗ₘ A.hom.app NR) ≫ τS.hom ≫
    _root_.AlgebraicGeometry.tilde.map (R := S) μ
  have hpre : C.inv ≫ C.hom = C.inv ≫ K := by
    let adj := _root_.AlgebraicGeometry.tilde.adjunction (R := S)
    apply (adj.homEquiv (ES.obj P)
      (_root_.AlgebraicGeometry.tilde (R := S) (ES.obj P))).injective
    change adj.unit.app (ES.obj P) ≫
        (moduleSpecΓFunctor (R := S)).map (C.inv ≫ C.hom) =
      adj.unit.app (ES.obj P) ≫
        (moduleSpecΓFunctor (R := S)).map (C.inv ≫ K)
    rw [(moduleSpecΓFunctor (R := S)).map_comp,
      (moduleSpecΓFunctor (R := S)).map_comp]
    let L := adj.unit.app (ES.obj P) ≫
      (moduleSpecΓFunctor (R := S)).map C.inv ≫
      (moduleSpecΓFunctor (R := S)).map C.hom
    let G := adj.unit.app (ES.obj P) ≫
      (moduleSpecΓFunctor (R := S)).map C.inv ≫
      (moduleSpecΓFunctor (R := S)).map K
    change L = G
    apply ModuleCat.ExtendScalars.hom_ext
    intro p
    change L ((1 : S) ⊗ₜ[R, φ.hom] p) =
      G ((1 : S) ⊗ₜ[R, φ.hom] p)
    induction p using TensorProduct.induction_on with
    | zero =>
        have hz : ((1 : S) ⊗ₜ[R, φ.hom] (0 : P) : ES.obj P) = 0 :=
          @TensorProduct.tmul_zero R _ S P _ _ (Module.compHom S φ.hom) _ (1 : S)
        have hLzero : L (0 : ES.obj P) = 0 := L.hom.map_zero
        have hGzero : G (0 : ES.obj P) = 0 := G.hom.map_zero
        exact (congrArg L.hom hz).trans
          (hLzero.trans (hGzero.symm.trans (congrArg G.hom hz.symm)))
    | tmul m n =>
        have hCinv := directTensorPullbackIso_inv_toOpen_tmul φ M N m n
        have hK := canonicalTensorPullbackHom_pullbackUnitTop_tmul φ M N m n
        dsimp only at hCinv hK
        let y := _root_.AlgebraicGeometry.tilde.toOpen (R := S) (ES.obj P) ⊤
          ((1 : S) ⊗ₜ[R, φ.hom] (m ⊗ₜ[R] n))
        have hCid := congrArg
          (fun q ↦ q.val.app (.op (⊤ : (Spec S).Opens)) y) C.inv_hom_id
        change C.hom.val.app (.op ⊤) (C.inv.val.app (.op ⊤) y) = y at hCid
        have hright : K.val.app (.op ⊤) (C.inv.val.app (.op ⊤) y) = y :=
          (congrArg (K.val.app (.op ⊤)) hCinv).trans hK
        change C.hom.val.app (.op ⊤) (C.inv.val.app (.op ⊤) y) =
          K.val.app (.op ⊤) (C.inv.val.app (.op ⊤) y)
        exact hCid.trans hright.symm
    | add x y hx hy =>
        have ha : ((1 : S) ⊗ₜ[R, φ.hom] (x + y) : ES.obj P) =
            ((1 : S) ⊗ₜ[R, φ.hom] x) +
              ((1 : S) ⊗ₜ[R, φ.hom] y) :=
          TensorProduct.tmul_add _ _ _
        have hLadd : L (((1 : S) ⊗ₜ[R, φ.hom] x) +
            ((1 : S) ⊗ₜ[R, φ.hom] y)) =
            L ((1 : S) ⊗ₜ[R, φ.hom] x) +
              L ((1 : S) ⊗ₜ[R, φ.hom] y) :=
          L.hom.map_add _ _
        have hGadd : G (((1 : S) ⊗ₜ[R, φ.hom] x) +
            ((1 : S) ⊗ₜ[R, φ.hom] y)) =
            G ((1 : S) ⊗ₜ[R, φ.hom] x) +
              G ((1 : S) ⊗ₜ[R, φ.hom] y) :=
          G.hom.map_add _ _
        exact (congrArg L.hom ha).trans
          (hLadd.trans ((congrArg₂ (fun a b ↦ a + b) hx hy).trans
            (hGadd.symm.trans (congrArg G.hom ha.symm))))
  exact (cancel_epi C.inv).1 hpre

/-- The affine tilde tensor comparison commutes with base change: pull back the tensor
comparison and then apply the oplax tensor map for extension of scalars, or first apply the
oplax tensor map for sheaf pullback and then the two factorwise affine comparisons. -/
theorem tildePullbackIsoExtendScalars_tensor_hom
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M N : ModuleCat R) :
    let f := Spec.map φ
    let PB := Scheme.Modules.pullback f
    let ES := ModuleCat.extendScalars φ.hom
    let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
    PB.map (tildeTensorIso R M N).hom ≫ A.hom.app (M ⊗ N) ≫
        _root_.AlgebraicGeometry.tilde.map (R := S)
          (Functor.OplaxMonoidal.δ ES M N) =
      Functor.OplaxMonoidal.δ PB
          (_root_.AlgebraicGeometry.tilde (R := R) M)
          (_root_.AlgebraicGeometry.tilde (R := R) N) ≫
        (A.hom.app M ⊗ₘ A.hom.app N) ≫
        (tildeTensorIso S (ES.obj M) (ES.obj N)).hom := by
  dsimp only
  let f := Spec.map φ
  let PB := Scheme.Modules.pullback f
  let ES := ModuleCat.extendScalars φ.hom
  let MR := ModuleCat.of R M
  let NR := ModuleCat.of R N
  let P := ModuleCat.of R (M ⊗[R] N)
  let EM := ES.obj MR
  let EN := ES.obj NR
  let τR := tildeTensorIso R M N
  let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
  let C := PB.mapIso τR ≪≫ A.app P
  let τS := tildeTensorIso S EM EN
  let μ := (Functor.Monoidal.μIso ES MR NR).hom
  let δES := Functor.OplaxMonoidal.δ ES MR NR
  let T := _root_.AlgebraicGeometry.tilde.functor S
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  let B := Functor.OplaxMonoidal.δ PB
      (_root_.AlgebraicGeometry.tilde (R := R) MR)
      (_root_.AlgebraicGeometry.tilde (R := R) NR) ≫
    (A.hom.app MR ⊗ₘ A.hom.app NR) ≫ τS.hom
  have hCK := directTensorPullbackIso_hom_eq_canonical_μ φ M N
  dsimp only at hCK
  change C.hom = B ≫ T.map μ at hCK
  have hμδ := Functor.Monoidal.map_μ_δ ES T MR NR
  change T.map μ ≫ T.map δES = 𝟙 _ at hμδ
  change C.hom ≫ T.map δES = B
  have hpost : C.hom ≫ T.map δES =
      (B ≫ T.map μ) ≫ T.map δES :=
    congrArg (fun q ↦ q ≫ T.map δES) hCK
  have hassoc : (B ≫ T.map μ) ≫ T.map δES =
      B ≫ (T.map μ ≫ T.map δES) :=
    Category.assoc _ _ _
  have hcancel : B ≫ (T.map μ ≫ T.map δES) = B ≫ 𝟙 _ :=
    congrArg (fun q ↦ B ≫ q) hμδ
  have hid : B ≫ 𝟙 _ = B := Category.comp_id _
  exact hpost.trans (hassoc.trans (hcancel.trans hid))


end

end MazurTorsion.AlgebraicGeometry.AffineTilde
