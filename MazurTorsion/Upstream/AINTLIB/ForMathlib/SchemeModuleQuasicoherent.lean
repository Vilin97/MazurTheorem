/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Localization.Finiteness
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechBasic
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleRestrictLimits
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleRestrictPushforward
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SpecBasicOpen

/-!
# Quasicoherent modules on affine schemes

This file records the exact closure and global-section properties of quasicoherent scheme modules
needed for affine sheaf-cohomology vanishing. The proofs use the equivalence between modules and
quasicoherent modules on an affine scheme supplied by `tilde`.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Scheme

open Modules

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}

variable (X) in
/-- Quasicoherence as an object property on scheme modules. -/
abbrev Modules.isQuasicoherent : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

@[simp]
lemma Modules.isQuasicoherent_def {M : X.Modules} :
    Modules.isQuasicoherent X M ↔ M.IsQuasicoherent := by
  rfl

instance : (Modules.isQuasicoherent X).IsClosedUnderIsomorphisms :=
  inferInstanceAs
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms

variable {J : Type w} [Category.{v} J] [HasColimitsOfShape J AddCommGrpCat]

instance : (Modules.isQuasicoherent (Spec R)).IsClosedUnderColimitsOfShape J := by
  change
    (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf).IsClosedUnderColimitsOfShape J
  rw [← AlgebraicGeometry.essImage_tilde]
  let F := tilde.functor R
  letI : F.Full := tilde.fullyFaithfulFunctor.full
  letI : F.Faithful := tilde.fullyFaithfulFunctor.faithful
  letI : PreservesColimitsOfShape J F := inferInstance
  letI : F.essImage.IsClosedUnderIsomorphisms := inferInstance
  change F.essImage.IsClosedUnderColimitsOfShape J
  exact .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨colimit (Functor.essImage.liftFunctor G F hG),
      ⟨IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves F (colimit.isColimit _))
        (colimit.isColimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

instance [Finite J] :
    (Modules.isQuasicoherent (Spec R)).IsClosedUnderLimitsOfShape (Discrete J) := by
  change (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderLimitsOfShape
    (Discrete J)
  rw [← AlgebraicGeometry.essImage_tilde]
  exact
    instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsOfShapeOfPreservesLimitsOfShapeOfFullOfFaithful
      (tilde.functor R)

namespace Modules

noncomputable section

private noncomputable def kernelAppLinearEquiv
    {M N : (Spec R).Modules} (f : M ⟶ N) (U : (Spec R).Opens) :
    Γ(kernel f, U) ≃ₗ[R]
      ((modulesSpecToSheaf.map f).hom.app (op U)).hom.ker :=
  let e := (PreservesKernel.iso
    (SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)) f).trans
      (ModuleCat.kernelIsoKer _)
  let fU : Γ(M, U) →ₗ[Γ(Spec R, U)] Γ(N, U) :=
    (f.val.app (op U)).hom
  letI : Module R fU.ker :=
    Module.compHom (R := Γ(Spec R, U)) fU.ker
      (algebraMap R Γ(Spec R, U))
  letI : IsScalarTower R Γ(Spec R, U) fU.ker :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let eΓ : Γ(kernel f, U) ≃ₗ[Γ(Spec R, U)] fU.ker :=
    e.toLinearEquiv
  let eR : Γ(kernel f, U) ≃ₗ[R] fU.ker :=
    { toEquiv := eΓ.toEquiv
      map_add' := eΓ.map_add
      map_smul' := by
        intro r x
        change eΓ ((algebraMap R Γ(Spec R, U)) r • x) =
          (algebraMap R Γ(Spec R, U)) r • eΓ x
        exact eΓ.map_smul _ _ }
  let eKer : fU.ker ≃ₗ[R]
      ((modulesSpecToSheaf.map f).hom.app (op U)).hom.ker :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        apply Subtype.ext
        change (algebraMap R Γ(Spec R, U)) r • (x : Γ(M, U)) = _
        rfl }
  eR.trans eKer

private theorem kernelAppLinearEquiv_coe
    {M N : (Spec R).Modules} (f : M ⟶ N) (U : (Spec R).Opens)
    (x : Γ(kernel f, U)) :
    (kernelAppLinearEquiv f U x).1 =
      (kernel.ι f).val.app (op U) x := by
  change (((ModuleCat.kernelIsoKer
      ((SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)).map f)).hom
        ((PreservesKernel.iso
          (SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)) f).hom x)).1) =
      (kernel.ι f).val.app (op U) x
  let F := SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)
  have hsub := ConcreteCategory.congr_hom
    (ModuleCat.kernelIsoKer_hom_ker_subtype (F.map f))
    ((PreservesKernel.iso F f).hom x)
  have hcomparison := ConcreteCategory.congr_hom
    (PreservesKernel.iso_inv_ι (G := F) (f := f))
    ((PreservesKernel.iso F f).hom x)
  change F.map (kernel.ι f)
      ((PreservesKernel.iso F f).inv ((PreservesKernel.iso F f).hom x)) =
    (kernel.ι (F.map f)) ((PreservesKernel.iso F f).hom x) at hcomparison
  have hinv : (PreservesKernel.iso F f).inv
      ((PreservesKernel.iso F f).hom x) = x :=
    ConcreteCategory.congr_hom (PreservesKernel.iso F f).hom_inv_id x
  rw [hinv] at hcomparison
  symm at hcomparison
  exact hsub.trans hcomparison

private theorem isLocalizedModuleAway_of_linearEquiv_square
    {A : Type u} [CommRing A] {M N M' N' : Type u}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module A M] [Module A N] [Module A M'] [Module A N']
    (r : A) (f : M →ₗ[A] N) (g : M' →ₗ[A] N')
    (eM : M' ≃ₗ[A] M) (eN : N' ≃ₗ[A] N)
    (hsquare : eN.toLinearMap.comp g = f.comp eM.toLinearMap)
    (hf : IsLocalizedModule.Away r f) :
    IsLocalizedModule.Away r g := by
  letI : IsLocalizedModule.Away r f := hf
  let f' := f.comp eM.toLinearMap
  letI : IsLocalizedModule.Away r f' :=
    IsLocalizedModule.of_linearEquiv_right
      (Submonoid.powers r) f eM
  let g' := eN.symm.toLinearMap.comp f'
  letI : IsLocalizedModule.Away r g' :=
    IsLocalizedModule.of_linearEquiv
      (Submonoid.powers r) f' eN.symm
  have hg' : IsLocalizedModule.Away r g' := inferInstance
  convert hg' using 1
  ext x
  have hx := LinearMap.congr_fun hsquare x
  change eN (g x) = f (eM x) at hx
  change g x = eN.symm (f (eM x))
  rw [← hx]
  exact (eN.symm_apply_apply (g x)).symm

private theorem isQuasicoherent_kernel_spec
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) : (kernel f).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  rw [isIso_fromTildeΓ_iff_isLocalizing]
  intro r
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let m := ((modulesSpecToSheaf.obj M).obj.map U.leTop.op).hom
  let n := ((modulesSpecToSheaf.obj N).obj.map U.leTop.op).hom
  have hm : IsLocalizedModule.Away r m :=
    ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance) r
  have hn : IsLocalizedModule.Away r n :=
    ((isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance) r
  letI : IsLocalizedModule.Away r m := hm
  letI : IsLocalizedModule.Away r n := hn
  let g := ((modulesSpecToSheaf.map f).hom.app (op ⊤)).hom
  let gU := ((modulesSpecToSheaf.map f).hom.app (op U)).hom
  have hmap : IsLocalizedModule.map (Submonoid.powers r) m n g = gU := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r) m n
    rw [IsLocalizedModule.map_comp]
    ext x
    change N.presheaf.map U.leTop.op (f.val.app (op ⊤) x) =
      f.val.app (op U) (M.presheaf.map U.leTop.op x)
    exact (ConcreteCategory.congr_hom (f.val.naturality U.leTop.op) x).symm
  let k := LinearMap.toKerIsLocalized (Submonoid.powers r) m n g
  let eTop := kernelAppLinearEquiv f ⊤
  let eMap : gU.ker ≃ₗ[R]
      (IsLocalizedModule.map (Submonoid.powers r) m n g).ker :=
    LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hmap.symm)
  let eU := kernelAppLinearEquiv f U ≪≫ₗ eMap
  let a : Γ(kernel f, ⊤) →ₗ[R] Γ(kernel f, U) :=
    ((modulesSpecToSheaf.obj (kernel f)).obj.map U.leTop.op).hom
  have hsquare : eU.toLinearMap.comp a = k.comp eTop.toLinearMap := by
    ext x
    change (eMap (kernelAppLinearEquiv f U (a x))).1 =
      m (kernelAppLinearEquiv f ⊤ x).1
    change (kernelAppLinearEquiv f U (a x)).1 =
      m (kernelAppLinearEquiv f ⊤ x).1
    rw [kernelAppLinearEquiv_coe, kernelAppLinearEquiv_coe]
    exact ConcreteCategory.congr_hom
      ((kernel.ι f).val.naturality U.leTop.op) x
  letI : Module Γ(Spec R, U)
      ((modulesSpecToSheaf.obj M).obj.obj (op U)) :=
    (inferInstance : Module Γ(Spec R, U) Γ(M, U))
  letI : IsScalarTower R Γ(Spec R, U)
      ((modulesSpecToSheaf.obj M).obj.obj (op U)) :=
    (inferInstance : IsScalarTower R Γ(Spec R, U) Γ(M, U))
  letI : Module Γ(Spec R, U)
      ((modulesSpecToSheaf.obj N).obj.obj (op U)) :=
    (inferInstance : Module Γ(Spec R, U) Γ(N, U))
  letI : IsScalarTower R Γ(Spec R, U)
      ((modulesSpecToSheaf.obj N).obj.obj (op U)) :=
    (inferInstance : IsScalarTower R Γ(Spec R, U) Γ(N, U))
  exact isLocalizedModuleAway_of_linearEquiv_square r k a eTop eU hsquare
    (LinearMap.toKerLocalized_isLocalizedModule
      (S := Γ(Spec R, U))
      (Submonoid.powers r) m n g)

private noncomputable def presentationOfIsQuasicoherentSpec
    (M : (Spec R).Modules) [M.IsQuasicoherent] : M.Presentation := by
  have hIso : IsIso M.fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  let P : (tilde (moduleSpecΓFunctor.obj M)).Presentation :=
    presentationTilde (moduleSpecΓFunctor.obj M) Set.univ (by simp) _
      (Submodule.span_eq _)
  let e : tilde (moduleSpecΓFunctor.obj M) ≅ M :=
    @asIso _ _ _ _ M.fromTildeΓ hIso
  let f : tilde (moduleSpecΓFunctor.obj M) ⟶ M := e.hom
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    f e.isIso_hom P

end

end Modules

/-- On an affine spectrum, global sections send epimorphisms of quasicoherent modules to
epimorphisms of modules. -/
lemma Modules.moduleSpecΓ_epi_of_epi {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Epi (moduleSpecΓFunctor.map f) := by
  haveI : IsIso M.fromTildeΓ := inferInstance
  haveI : IsIso N.fromTildeΓ := inferInstance
  have hnat : tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := by
    have h := Scheme.Modules.fromTildeΓNatTrans.naturality f
    change tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f at h
    exact h
  have hright : Epi (M.fromTildeΓ ≫ f) :=
    epi_comp' (by infer_instance) (by infer_instance)
  have hcomp : Epi (tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ) :=
    hnat.symm ▸ hright
  have hmapped : Epi (tilde.map (moduleSpecΓFunctor.map f)) :=
    (epi_comp_iff_of_isIso _ N.fromTildeΓ).mp hcomp
  exact (tilde.functor R).epi_of_epi_map hmapped

/-- On an affine spectrum, an epimorphism of quasicoherent modules is surjective on global
sections. -/
theorem Modules.isQuasicoherent_spec_surjective_of_epi
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom :=
  (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f)).mp
    (Modules.moduleSpecΓ_epi_of_epi f)

noncomputable section

/-- A section of a quasicoherent module on `D(f)` extends globally after multiplication by a
power of `f`. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s : Γ(M, specBasicOpen R f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (specBasicOpen R f).leTop.op t = f ^ n • s := by
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  letI : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj M).obj.map (specBasicOpen R f).leTop.op).hom :=
    hlocal f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    ((modulesSpecToSheaf.obj M).obj.map (specBasicOpen R f).leTop.op).hom f s
  exact ⟨n, t, ht.symm⟩

/-- Finitely many sections of a quasicoherent module on `D(f)` extend globally after
multiplication by one common power of `f`. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_finite
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    {ι : Type*} [Finite ι] (s : ι → Γ(M, specBasicOpen R f)) :
    ∃ (n : ℕ) (t : ι → Γ(M, ⊤)), ∀ i,
      M.presheaf.map (specBasicOpen R f).leTop.op (t i) = f ^ n • s i := by
  choose n t ht using fun i ↦
    Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent M f (s i)
  have hle (i : ι) : n i ≤ ⨆ i, n i :=
    le_ciSup (Finite.bddAbove_range n) i
  refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t i, fun i ↦ ?_⟩
  rw [M.map_smul_Spec, ht i, ← mul_smul, ← pow_add,
    Nat.sub_add_cancel (hle i)]

/-- A quasicoherent module on an affine spectrum with finitely many global generators has a
finite module of global sections. -/
theorem Modules.globalSections_module_finite_of_generatingSections
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite R Γ(M, ⊤) := by
  haveI : Finite G.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let f : SheafOfModules.free G.I ⟶ M := G.π
  letI : Epi f := G.epi
  haveI : Module.Finite R (G.I →₀ R) :=
    Module.finite_finsupp_self_iff.mpr (.inr inferInstance)
  letI : (SheafOfModules.free G.I (R := (Spec R).ringCatSheaf)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeFinsupp G.I) (by infer_instance)
  let e : ModuleCat.of R (G.I →₀ R) ≅
      moduleSpecΓFunctor.obj (SheafOfModules.free G.I) :=
    tilde.isoTop (ModuleCat.of R (G.I →₀ R)) ≪≫
      moduleSpecΓFunctor.mapIso (tildeFinsupp G.I)
  haveI : Module.Finite R
      (moduleSpecΓFunctor.obj (SheafOfModules.free G.I)) :=
    Module.Finite.equiv e.toLinearEquiv
  have hf : Epi f := inferInstance
  have hsurj : Function.Surjective (moduleSpecΓFunctor.map f).hom := by
    have h := @Modules.isQuasicoherent_spec_surjective_of_epi R
      (SheafOfModules.free G.I) M f inferInstance inferInstance hf
    exact h
  exact Module.Finite.of_surjective
    (moduleSpecΓFunctor.map f).hom hsurj

namespace Modules

variable (φ : X ≅ Y)

/-- Pullback of scheme modules along a scheme isomorphism is an equivalence. -/
theorem pullback_isEquivalence_of_iso :
    (pullback φ.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' (pullback φ.inv)
    ((pullbackComp φ.inv φ.hom ≪≫ pullbackCongr φ.inv_hom_id ≪≫ pullbackId Y).symm)
    (pullbackComp φ.hom φ.inv ≪≫ pullbackCongr φ.hom_inv_id ≪≫ pullbackId X)

/-- Restricting along an isomorphism and then along its inverse is naturally the identity. -/
def restrictFunctor_inv_restrictFunctor_hom_id :
    restrictFunctor φ.inv ⋙ restrictFunctor φ.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp φ.hom φ.inv).symm ≪≫
    restrictFunctorCongr φ.hom_inv_id ≪≫ restrictFunctorId

instance : (restrictFunctor φ.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' _
    (restrictFunctor_inv_restrictFunctor_hom_id φ.symm).symm
    (restrictFunctor_inv_restrictFunctor_hom_id φ)

/-- Quasicoherence is invariant under restriction along a scheme isomorphism. -/
theorem isQuasicoherent_restrictFunctor_iff {M : Y.Modules} :
    (M.restrict φ.hom).IsQuasicoherent ↔ M.IsQuasicoherent := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  apply ObjectProperty.prop_of_iso _
    ((restrictFunctor_inv_restrictFunctor_hom_id φ.symm).app M)
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.comp_obj]
  infer_instance

/-- Under a scheme isomorphism, quasicoherence is the inverse image of quasicoherence. -/
theorem isQuasicoherent_inverseImage_iso :
    (isQuasicoherent X).inverseImage (restrictFunctor φ.hom) = isQuasicoherent Y := by
  ext M
  simp [isQuasicoherent_restrictFunctor_iff]

instance isQuasicoherent_pushforward_of_iso {φ : X ⟶ Y} [IsIso φ]
    {M : X.Modules} [M.IsQuasicoherent] :
    ((pushforward φ).obj M).IsQuasicoherent := by
  apply (isQuasicoherent_restrictFunctor_iff (asIso φ)).mp
  apply (isQuasicoherent X).prop_of_iso
    ((restrictFunctorAdjCounitIso φ).app M).symm
  change M.IsQuasicoherent
  infer_instance

instance {S T : CommRingCat.{u}} (ψ : S ⟶ T) {M : (Spec T).Modules}
    [M.IsQuasicoherent] :
    ((pushforward (Spec.map ψ)).obj M).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ] at ⊢
  exact isIso_fromTildeΓ_pushforward ψ M

instance isQuasicoherent_of_pushforward [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  rw [show f = (X.isoSpec.hom ≫ Spec.map (Hom.appTop f)) ≫ Y.isoSpec.inv by
    simp [isoSpec_hom_naturality f]]
  let e := (pushforward X.isoSpec.hom).isoWhiskerLeft
      (pushforwardComp (Spec.map (Hom.appTop f)) Y.isoSpec.inv) ≪≫
    pushforwardComp X.isoSpec.hom (Spec.map (Hom.appTop f) ≫ Y.isoSpec.inv)
  have : ((pushforward X.isoSpec.hom ⋙ pushforward (Spec.map (Hom.appTop f)) ⋙
      pushforward Y.isoSpec.inv).obj M).IsQuasicoherent := by
    simp only [Functor.comp_obj]
    infer_instance
  exact (isQuasicoherent Y).prop_of_iso (e.app M) this

private noncomputable def presentationOfIsQuasicoherentOfIsAffine
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    M.Presentation := by
  let F := restrictFunctor (isoSpec X).inv
  let M' := F.obj M
  let P' : M'.Presentation := presentationOfIsQuasicoherentSpec M'
  let P : ((M.restrict (isoSpec X).inv).restrict (isoSpec X).hom).Presentation :=
    presentationRestrict (isoSpec X).hom P'
  let e := (restrictFunctor_inv_restrictFunctor_hom_id (isoSpec X)).app M
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    e.hom e.isIso_hom P

/-- On an affine open, quasicoherence after scheme-module restriction implies
quasicoherence of the corresponding module on the over-site. -/
theorem isQuasicoherent_over_of_restrict_of_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) [IsAffine U]
    [(M.restrict U.ι).IsQuasicoherent] : (M.over U).IsQuasicoherent := by
  let N := M.restrict U.ι
  let P : N.Presentation := presentationOfIsQuasicoherentOfIsAffine N
  letI : (overEquiv U).inverse.IsEquivalence := by
    infer_instance
  let hPres : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse := by
    infer_instance
  let Q : ((overEquiv U).inverse.obj N).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _
      P (overEquiv U).inverse hPres
        (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e : M.over U ≅ (overEquiv U).inverse.obj N :=
    (overEquiv U).unitIso.app (M.over U) ≪≫
      (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M)
  let Q' : (M.over U).Presentation :=
    @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
      e.inv e.isIso_inv Q
  exact Q'.isQuasicoherent

/-- Pushforward along an affine morphism preserves quasicoherent modules. -/
theorem isQuasicoherent_pushforward_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {M : X.Modules} [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  have hlocal (U : Y.affineOpens) :
      (((pushforward f).obj M).over (U : Y.Opens)).IsQuasicoherent := by
    let V := f ⁻¹ᵁ U.1
    let fU := f ∣_ U.1
    let MU := (restrictFunctor V.ι).obj M
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine V.toScheme := U.2.preimage f
    haveI : MU.IsQuasicoherent := inferInstance
    have hPush : ((pushforward fU).obj MU).IsQuasicoherent :=
      isQuasicoherent_of_pushforward fU MU
    have hRestrict :
        ((restrictFunctor U.1.ι).obj ((pushforward f).obj M)).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_of_iso
        (restrictPushforwardIsoOfIsPullbackApp f fU V.ι U.1.ι
          (isPullback_morphismRestrict f U.1) M).symm
        hPush
    letI :
        ((restrictFunctor U.1.ι).obj ((pushforward f).obj M)).IsQuasicoherent :=
      hRestrict
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen ((pushforward f).obj M) U.1
  have hcover : (Opens.grothendieckTopology Y).CoversTop
      (fun U : Y.affineOpens ↦ (U : Y.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top Y]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ((pushforward f).obj M) _
      (fun U : Y.affineOpens ↦ (U : Y.Opens)) hcover hlocal

/-- On an affine scheme, the kernel of a morphism between quasicoherent modules is
quasicoherent. -/
theorem isQuasicoherent_kernel_of_isAffine
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let F := restrictFunctor (isoSpec X).inv
  letI : F.IsEquivalence := by
    exact Functor.IsEquivalence.mk' _
      (restrictFunctor_inv_restrictFunctor_hom_id (isoSpec X)).symm
      (restrictFunctor_inv_restrictFunctor_hom_id (isoSpec X).symm)
  have hKernel : (kernel (F.map f)).IsQuasicoherent :=
    isQuasicoherent_kernel_spec (F.map f)
  have hRestrict : (F.obj (kernel f)).IsQuasicoherent :=
    (isQuasicoherent (Spec Γ(X, ⊤))).prop_of_iso
      (PreservesKernel.iso F f).symm hKernel
  exact (isQuasicoherent_restrictFunctor_iff (isoSpec X).symm).mp hRestrict

/-- The kernel of a morphism between quasicoherent modules on a scheme is quasicoherent. -/
theorem isQuasicoherent_kernel
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  have hlocal (U : X.affineOpens) :
      ((kernel f).over (U : X.Opens)).IsQuasicoherent := by
    let F := restrictFunctor U.1.ι
    letI : PreservesLimits F := restrictFunctor_preservesLimits U.1.ι
    have hKernel : (kernel (F.map f)).IsQuasicoherent :=
      isQuasicoherent_kernel_of_isAffine (F.map f)
    have hRestrict : (F.obj (kernel f)).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_of_iso (PreservesKernel.iso F f).symm hKernel
    letI : (F.obj (kernel f)).IsQuasicoherent := hRestrict
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen (kernel f) U.1
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : X.affineOpens ↦ (U : X.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ (kernel f) _
      (fun U : X.affineOpens ↦ (U : X.Opens)) hcover hlocal

/-- The cokernel of a morphism between quasicoherent modules on a scheme is
quasicoherent. -/
theorem isQuasicoherent_cokernel
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent := by
  have hlocal (U : X.affineOpens) :
      ((cokernel f).over (U : X.Opens)).IsQuasicoherent := by
    let F := restrictFunctor U.1.ι
    letI : IsAffine U.1 := U.2
    letI : PreservesColimitsOfSize.{u, u} F := by
      dsimp [F]
      infer_instance
    let P := isQuasicoherent U.1
    letI : P.IsClosedUnderColimitsOfShape WalkingParallelPair := by
      dsimp [P]
      rw [← isQuasicoherent_inverseImage_iso (isoSpec U.1).symm]
      exact ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage ..
    let c := CokernelCofork.ofπ
      (cokernel.π (F.map f)) (cokernel.condition (F.map f))
    have hCokernel : (cokernel (F.map f)).IsQuasicoherent := by
      change P c.pt
      apply P.prop_of_isColimit (cokernelIsCokernel (F.map f))
      rintro (_ | _)
      · change (F.obj M).IsQuasicoherent
        infer_instance
      · change (F.obj N).IsQuasicoherent
        infer_instance
    have hRestrict : (F.obj (cokernel f)).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_of_iso
        (PreservesCokernel.iso F f).symm hCokernel
    letI : (F.obj (cokernel f)).IsQuasicoherent := hRestrict
    exact
      isQuasicoherent_over_of_restrict_of_isAffineOpen
        (cokernel f) U.1
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : X.affineOpens ↦ (U : X.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ (cokernel f) _
      (fun U : X.affineOpens ↦ (U : X.Opens)) hcover hlocal

/-- The image of a morphism between quasicoherent modules on a scheme is
quasicoherent. -/
theorem isQuasicoherent_image
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (Abelian.image f).IsQuasicoherent := by
  letI : (cokernel f).IsQuasicoherent :=
    isQuasicoherent_cokernel f
  exact isQuasicoherent_kernel (cokernel.π f)

variable [IsAffine X] (F : J ⥤ X.Modules)

instance : (isQuasicoherent X).IsClosedUnderColimitsOfShape J := by
  rw [← isQuasicoherent_inverseImage_iso (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage ..

/-- A coproduct of quasicoherent modules on a scheme is quasicoherent. -/
theorem isQuasicoherent_coproduct
    {X : Scheme.{u}} {ι : Type} (M : ι → X.Modules)
    (hM : ∀ i, (M i).IsQuasicoherent) : (∐ M).IsQuasicoherent := by
  have hlocal (U : X.affineOpens) :
      ((∐ M).over (U : X.Opens)).IsQuasicoherent := by
    let F := restrictFunctor U.1.ι
    let D := Discrete.functor M
    have hObj (i : Discrete ι) : ((D ⋙ F).obj i).IsQuasicoherent := by
      dsimp [D, F]
      letI : (M i.as).IsQuasicoherent := hM i.as
      infer_instance
    have hColimit : (colimit (D ⋙ F)).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_colimit (D ⋙ F) hObj
    have hRestrict : (F.obj (∐ M)).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_of_iso
        (preservesColimitIso F D).symm hColimit
    letI : (F.obj (∐ M)).IsQuasicoherent := hRestrict
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen (∐ M) U.1
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : X.affineOpens ↦ (U : X.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ (∐ M) _
      (fun U : X.affineOpens ↦ (U : X.Opens)) hcover hlocal

instance [Finite J] :
    (isQuasicoherent X).IsClosedUnderLimitsOfShape (Discrete J) := by
  rw [← isQuasicoherent_inverseImage_iso (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage ..

end Modules

/-- On an affine scheme, an epimorphism of quasicoherent modules is surjective on global
sections. -/
theorem Modules.isQuasicoherent_surjective_of_epi [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom := by
  rw [← (isoSpec X).inv.opensRange_of_isIso,
    ← (isoSpec X).inv.image_top_eq_opensRange]
  change Function.Surjective
    (((restrictFunctor (isoSpec X).inv).map f).val.app (op ⊤))
  exact Modules.isQuasicoherent_spec_surjective_of_epi
    ((restrictFunctor (isoSpec X).inv).map f)

/-- The global sections of a finite free sheaf form a finite module. -/
theorem Modules.free_globalSections_module_finite
    (X : Scheme.{u}) (I : Type u) [Finite I] :
    Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free I (R := X.ringCatSheaf))) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let U := fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf
  letI : HasBiproduct U := HasBiproduct.of_hasCoproduct U
  letI : F.Additive := by
    change (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).Additive
    unfold SheafOfModules.evaluation
    infer_instance
  letI : PreservesLimit (Discrete.functor U) F := by
    dsimp [F]
    infer_instance
  letI : PreservesBiproduct U F :=
    preservesBiproduct_of_preservesProduct F
  let e : F.obj (SheafOfModules.free I) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op ⊤))
        (∀ i, F.obj (U i)) :=
    F.mapIso (biproduct.isoCoproduct U).symm ≪≫
      F.mapBiproduct U ≪≫
      biproduct.isoProduct (F.obj ∘ U) ≪≫
      ModuleCat.piIsoPi (F.obj ∘ U)
  have hfinite (i : I) :
      Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (F.obj (U i)) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      (X.ringCatSheaf.obj.obj (op ⊤))
    infer_instance
  haveI : Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (∀ i, F.obj (U i)) :=
    @Module.Finite.pi _ _ I (fun i ↦ F.obj (U i)) inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) hfinite
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- A quasicoherent module on an affine scheme with finitely many global generators has a
finite module of global sections. -/
theorem Modules.globalSections_module_finite_of_generatingSections_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  haveI : Finite G.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let L : X.Modules := SheafOfModules.free G.I
  let f : L ⟶ M := G.π
  letI : Epi f := G.epi
  letI : L.IsQuasicoherent := inferInstance
  have hL : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free G.I (R := X.ringCatSheaf)))
    exact Modules.free_globalSections_module_finite X G.I
  letI : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := hL
  have hf : Epi f := inferInstance
  have hsurj : Function.Surjective (f.val.app (op ⊤)).hom := by
    exact @Modules.isQuasicoherent_surjective_of_epi X inferInstance
      L M f inferInstance inferInstance hf
  exact @Module.Finite.of_surjective
    _ _ _ _ _ _ _ _ _ _ _ RingHomSurjective.ids hL
    (f.val.app (op ⊤)).hom hsurj

private theorem Modules.module_finite_restrict_of_over_generators
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) := by
  letI : IsAffine U.toScheme := hU
  let F := (Modules.overEquiv U).functor
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (Modules.overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF (Iso.refl _)
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((Modules.overFunctorEquiv U).app M) G'
  haveI : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact Modules.globalSections_module_finite_of_generatingSections_of_isAffine
    (M.restrict U.ι) G''

private theorem Modules.module_finite_app_of_over_generators
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have hfinite : Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) :=
    Modules.module_finite_restrict_of_over_generators M U hU G
  let eR' := U.ι.appIso (⊤ : U.toScheme.Opens)
  let eR : Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) ≃+* Γ(U.toScheme, ⊤) :=
    eR'.commRingCatIsoToRingEquiv
  let eM' := M.restrictAppIso U.ι ⊤
  let σ : Γ(U.toScheme, ⊤) →+*
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := eR'.inv.hom
  let eM : Γ(M.restrict U.ι, ⊤) →ₛₗ[σ]
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := by
        intro r x
        change eM'.hom (r • x) = eR'.inv.hom r • eM'.hom x
        exact Modules.smul_restrictAppIso_hom_apply U.ι M ⊤ r x }
  have hσ : Function.Surjective σ := by
    change Function.Surjective
      (eR.symm : Γ(U.toScheme, ⊤) →+*
        Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)))
    exact eR.symm.surjective
  letI : RingHomSurjective σ := ⟨hσ⟩
  have heM : Function.Bijective eM := by
    change Function.Bijective eM'.hom
    exact ConcreteCategory.bijective_of_isIso eM'.hom
  have htarget : Module.Finite
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens))
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    (eM.finite_iff_of_bijective heM).mp hfinite
  rw [U.ι_image_top] at htarget
  exact htarget

private theorem Modules.module_finite_app_of_over_generators_of_le
    (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hVU : V ≤ U) (hV : IsAffineOpen V)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, V) Γ(M, V) := by
  let i : V ⟶ U := homOfLE hVU
  let F := SheafOfModules.overMap X.ringCatSheaf i
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (SheafOfModules.overMapPushforwardAdj X.ringCatSheaf i).leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF
      (SheafOfModules.overMapUnitIso i).symm
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M) G'
  haveI : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact Modules.module_finite_app_of_over_generators M V hV G''

/-- A finite-type quasicoherent module on an affine spectrum has finite global sections. -/
theorem Modules.globalSections_module_finite_of_isFiniteType
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R Γ(M, ⊤) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  letI : q.IsFiniteType := hq
  let t : Set R := { f | ∃ i, specBasicOpen R f ≤ q.X i }
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := Spec R) q.X).mp q.coversTop
  have hopen : ⨆ f ∈ t, specBasicOpen R f = ⊤ := by
    apply top_unique
    rw [← hqcover]
    refine iSup_le fun i ↦ ?_
    rintro x hx
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx (q.X i).2
    have hle : specBasicOpen R f ≤ ⨆ f ∈ t, specBasicOpen R f :=
      le_iSup_of_le f (le_iSup_of_le (show f ∈ t from ⟨i, hf⟩) le_rfl)
    exact hle hxf
  have ht : Ideal.span t = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hopen
  let φ : (g : t) → Γ(M, ⊤) →ₗ[R] Γ(M, specBasicOpen R g.1) :=
    fun g ↦ ((modulesSpecToSheaf.obj M).obj.map
      (specBasicOpen R g.1).leTop.op).hom
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  letI (g : t) : Algebra R Γ(Spec R, specBasicOpen R g.1) :=
    inferInstance
  letI (g : t) : IsLocalization.Away g.1
      Γ(Spec R, specBasicOpen R g.1) := inferInstance
  letI (g : t) : IsScalarTower R
      Γ(Spec R, specBasicOpen R g.1) Γ(M, specBasicOpen R g.1) :=
    inferInstance
  letI : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) :=
    fun g ↦ hlocal g.1
  refine Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t ↦ Γ(M, specBasicOpen R g.1))
    (Rₚ := fun g : t ↦ Γ(Spec R, specBasicOpen R g.1))
    t ht φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  letI : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact Modules.module_finite_app_of_over_generators_of_le M hi
    (IsAffineOpen.Spec_basicOpen g.1) (q.generators i)

private theorem Modules.isLocalizedModuleAway_of_iso_square
    {A : Type u} [CommRing A] {M N M' N' : ModuleCat.{u} A}
    (r : A) (f : M ⟶ N) (g : M' ⟶ N') (eM : M ≅ M') (eN : N ≅ N')
    (hsquare : f ≫ eN.hom = eM.hom ≫ g)
    (hf : IsLocalizedModule.Away r f.hom) :
    IsLocalizedModule.Away r g.hom := by
  have hconj : eM.inv ≫ f ≫ eN.hom = g := by
    rw [hsquare, ← Category.assoc, eM.inv_hom_id, Category.id_comp]
  let f' := f.hom.comp eM.symm.toLinearEquiv.toLinearMap
  letI : IsLocalizedModule.Away r f.hom := hf
  letI : IsLocalizedModule.Away r f' :=
    IsLocalizedModule.of_linearEquiv_right
      (Submonoid.powers r) f.hom eM.symm.toLinearEquiv
  let g' := eN.toLinearEquiv.toLinearMap.comp f'
  letI : IsLocalizedModule.Away r g' :=
    IsLocalizedModule.of_linearEquiv
      (Submonoid.powers r) f' eN.toLinearEquiv
  have hg' : IsLocalizedModule.Away r g' := inferInstance
  convert hg' using 1
  ext x
  exact (ConcreteCategory.congr_hom hconj x).symm

private theorem Modules.baseModulePresheaf_isLocalized_image_of_restrict
    {Y S Z : Scheme.{u}} (π : Y ⟶ S) (j : Z ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) {U V : Z.Opens} (i : op V ⟶ op U)
    (r : Γ(S, ⊤))
    (h : IsLocalizedModule.Away r
      ((baseModulePresheaf (j ≫ π) (M.restrict j)).map i).hom) :
    IsLocalizedModule.Away r
      ((baseModulePresheaf π M).map
        (homOfLE (j.image_mono (leOfHom i.unop))).op).hom := by
  exact Modules.isLocalizedModuleAway_of_iso_square r
    ((baseModulePresheaf (j ≫ π) (M.restrict j)).map i)
    ((baseModulePresheaf π M).map
      (homOfLE (j.image_mono (leOfHom i.unop))).op)
    (Modules.baseModulePresheafRestrictAppIso π j M V)
    (Modules.baseModulePresheafRestrictAppIso π j M U)
    (Modules.baseModulePresheafRestrictAppIso_hom_naturality π j M i)
    h

private noncomputable def Modules.isoSpecInvBaseModuleIso
    [IsAffine X] (M : X.Modules)
    (V : (Spec Γ(X, (⊤ : X.Opens))).Opens) :
    (baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X)
        (M.restrict X.isoSpec.inv)).obj (op V) ≅
      (modulesSpecToSheaf.obj (M.restrict X.isoSpec.inv)).obj.obj (op V) := by
  have happ : X.isoSpec.inv.appTop =
      (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv := by
    have hhom : X.isoSpec.hom.appTop =
        (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom := by
      simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop]
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom]
    rw [← hhom]
    rw [← Scheme.Hom.comp_appTop]
    rw [X.isoSpec.hom_inv_id]
    rw [hhom]
    simp
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext (x : Γ(M.restrict X.isoSpec.inv, V))
  change
    (Spec Γ(X, (⊤ : X.Opens))).presheaf.map V.leTop.op
          ((Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv r) • x =
      (Spec Γ(X, (⊤ : X.Opens))).presheaf.map V.leTop.op
          (X.isoSpec.inv.appTop r) • x
  rw [happ]

private theorem Modules.modulesSpec_isLocalized_basicOpen_of_isoSpecInv
    [IsAffine X] (M : X.Modules) (f : Γ(X, ⊤))
    (h : IsLocalizedModule.Away f
      ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X)
        (M.restrict X.isoSpec.inv)).map
          (PrimeSpectrum.basicOpen f).leTop.op).hom) :
    IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj (M.restrict X.isoSpec.inv)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom := by
  let N : (Spec Γ(X, ⊤)).Modules := M.restrict X.isoSpec.inv
  let U : (Spec Γ(X, ⊤)).Opens := PrimeSpectrum.basicOpen f
  let i := U.leTop.op
  let ψ := ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X) N).map i).hom
  let φ := ((modulesSpecToSheaf.obj N).obj.map i).hom
  let eTop := (Modules.isoSpecInvBaseModuleIso M
    (⊤ : (Spec Γ(X, ⊤)).Opens)).toLinearEquiv
  let eBasic := (Modules.isoSpecInvBaseModuleIso M U).toLinearEquiv
  have hsquare :
      eBasic.symm.toLinearMap.comp φ = ψ.comp eTop.symm.toLinearMap := by
    ext x
    rfl
  exact isLocalizedModuleAway_of_linearEquiv_square f ψ φ
    eTop.symm eBasic.symm hsquare h

private theorem Modules.isoSpecInv_isLocalized_basicOpen
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) :
    IsLocalizedModule.Away f
      ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X)
        (M.restrict X.isoSpec.inv)).map
          (PrimeSpectrum.basicOpen f).leTop.op).hom := by
  let N : (Spec Γ(X, ⊤)).Modules := M.restrict X.isoSpec.inv
  haveI : N.IsQuasicoherent := inferInstance
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  let φ := ((modulesSpecToSheaf.obj N).obj.map
    (PrimeSpectrum.basicOpen f).leTop.op).hom
  let ψ := ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X) N).map
    (PrimeSpectrum.basicOpen f).leTop.op).hom
  let eTop := (Modules.isoSpecInvBaseModuleIso M
    (⊤ : (Spec Γ(X, ⊤)).Opens)).toLinearEquiv
  let eBasic := (Modules.isoSpecInvBaseModuleIso M
    (PrimeSpectrum.basicOpen f)).toLinearEquiv
  have hsquare : eBasic.toLinearMap.comp ψ = φ.comp eTop.toLinearMap := by
    ext x
    rfl
  exact isLocalizedModuleAway_of_linearEquiv_square f φ ψ
    eTop eBasic hsquare (hlocal f)

private lemma Modules.isoSpecInv_image_top [IsAffine X] :
    X.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) = ⊤ := by
  rw [Scheme.Hom.inv_image]
  simp

private lemma Modules.isoSpecInv_image_basic [IsAffine X]
    (f : Γ(X, ⊤)) :
    X.isoSpec.inv ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  (Scheme.Hom.inv_image X.isoSpec (PrimeSpectrum.basicOpen f)).trans
    (Scheme.map_PrimeSpectrum_basicOpen_of_affine X f)

private theorem Modules.isLocalizedModuleAway_map_of_eq
    {A T : Type u} [CommRing A] [TopologicalSpace T]
    (F : (TopologicalSpace.Opens T)ᵒᵖ ⥤ ModuleCat.{u} A)
    {U V U' V' : TopologicalSpace.Opens T}
    (i : op V ⟶ op U) (i' : op V' ⟶ op U')
    (hU : U = U') (hV : V = V') (r : A)
    (h : IsLocalizedModule.Away r (F.map i).hom) :
    IsLocalizedModule.Away r (F.map i').hom := by
  subst U'
  subst V'
  have hi : i' = i := Subsingleton.elim _ _
  subst i'
  exact h

/-- On an affine scheme, restriction of a quasicoherent module to a basic open is localization at
the function defining that open. -/
theorem Modules.baseModulePresheaf_isLocalized_basicOpen
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) :
    IsLocalizedModule.Away f
      ((baseModulePresheaf (𝟙 X) M).map
        (X.basicOpen f).leTop.op).hom := by
  let U : (Spec Γ(X, ⊤)).Opens := PrimeSpectrum.basicOpen f
  let i := U.leTop.op
  have hsource : IsLocalizedModule.Away f
      ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X)
        (M.restrict X.isoSpec.inv)).map i).hom := by
    simpa only [i, U] using Modules.isoSpecInv_isLocalized_basicOpen M f
  have himage :=
    Modules.baseModulePresheaf_isLocalized_image_of_restrict
      (π := 𝟙 X) (j := X.isoSpec.inv) (M := M)
      (i := i) (r := f) hsource
  exact Modules.isLocalizedModuleAway_map_of_eq
    (baseModulePresheaf (𝟙 X) M)
    (homOfLE (X.isoSpec.inv.image_mono (leOfHom i.unop))).op
    (X.basicOpen f).leTop.op
    (show X.isoSpec.inv ''ᵁ U = X.basicOpen f by
      simpa only [U] using Modules.isoSpecInv_image_basic f)
    Modules.isoSpecInv_image_top f himage

private theorem Modules.isoSpecInv_isLocalized_basicOpen_of_isLocalized_basicOpen
    [IsAffine X] (M : X.Modules) (f : Γ(X, ⊤))
    (h : IsLocalizedModule.Away f
      ((baseModulePresheaf (𝟙 X) M).map
        (X.basicOpen f).leTop.op).hom) :
    IsLocalizedModule.Away f
      ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X)
        (M.restrict X.isoSpec.inv)).map
          (PrimeSpectrum.basicOpen f).leTop.op).hom := by
  let N : (Spec Γ(X, ⊤)).Modules := M.restrict X.isoSpec.inv
  let U : (Spec Γ(X, ⊤)).Opens := PrimeSpectrum.basicOpen f
  let i := U.leTop.op
  let target := ((baseModulePresheaf (𝟙 X) M).map
    (homOfLE (X.isoSpec.inv.image_mono (leOfHom i.unop))).op).hom
  have htarget : IsLocalizedModule.Away f target := by
    exact Modules.isLocalizedModuleAway_map_of_eq
      (baseModulePresheaf (𝟙 X) M)
      (X.basicOpen f).leTop.op
      (homOfLE (X.isoSpec.inv.image_mono (leOfHom i.unop))).op
      (Modules.isoSpecInv_image_basic (X := X) f).symm
      (Modules.isoSpecInv_image_top (X := X)).symm f h
  let eTop := Modules.baseModulePresheafRestrictAppIso
    (𝟙 X) X.isoSpec.inv M (⊤ : (Spec Γ(X, ⊤)).Opens)
  let eBasic := Modules.baseModulePresheafRestrictAppIso
    (𝟙 X) X.isoSpec.inv M U
  have hsquare :
      ((baseModulePresheaf (𝟙 X) M).map
          (homOfLE (X.isoSpec.inv.image_mono (leOfHom i.unop))).op) ≫
          eBasic.inv =
        eTop.inv ≫
          (baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X) N).map i := by
    have hnat := Modules.baseModulePresheafRestrictAppIso_hom_naturality
      (𝟙 X) X.isoSpec.inv M i
    calc
      _ = eTop.inv ≫
          (eTop.hom ≫
            (baseModulePresheaf (𝟙 X) M).map
              (homOfLE (X.isoSpec.inv.image_mono (leOfHom i.unop))).op) ≫
            eBasic.inv := by simp
      _ = eTop.inv ≫
          ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X) N).map i ≫
            eBasic.hom) ≫ eBasic.inv := by rw [hnat]
      _ = _ := by simp
  exact Modules.isLocalizedModuleAway_of_iso_square f
    ((baseModulePresheaf (𝟙 X) M).map
      (homOfLE (X.isoSpec.inv.image_mono (leOfHom i.unop))).op)
    ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X) N).map i)
    eTop.symm eBasic.symm hsquare htarget

/-- On an affine scheme, a module whose restriction to every intrinsic basic
open is localization of its global sections is quasicoherent. -/
theorem Modules.isQuasicoherent_of_isLocalized_basicOpen
    [IsAffine X] (M : X.Modules)
    (h : ∀ f : Γ(X, ⊤), IsLocalizedModule.Away f
      ((baseModulePresheaf (𝟙 X) M).map
        (X.basicOpen f).leTop.op).hom) :
    M.IsQuasicoherent := by
  apply (Modules.isQuasicoherent_restrictFunctor_iff X.isoSpec.symm).mp
  let N : (Spec Γ(X, ⊤)).Modules := M.restrict X.isoSpec.inv
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  rw [isIso_fromTildeΓ_iff_isLocalizing]
  intro f
  exact Modules.modulesSpec_isLocalized_basicOpen_of_isoSpecInv M f
    (Modules.isoSpecInv_isLocalized_basicOpen_of_isLocalized_basicOpen
      M f (h f))

/-- A morphism between quasicoherent modules on an affine scheme is an
isomorphism if it is an isomorphism on global sections. -/
theorem Modules.isIso_of_isQuasicoherent_of_isIso_app_top
    [IsAffine X] {M N : X.Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (h : IsIso (φ.val.app (.op (⊤ : X.Opens)))) : IsIso φ := by
  let F := baseModulePresheafFunctor (𝟙 X)
  let φB := F.map φ
  letI : IsIso (φ.val.app (.op (⊤ : X.Opens))) := h
  haveI hφBTop : IsIso (φB.app (.op (⊤ : X.Opens))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso
      (φ.val.app (.op (⊤ : X.Opens)))
  letI hreflect : (SheafOfModules.toSheaf.{u}
      X.ringCatSheaf).ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  haveI hmap : IsIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_basicOpen X)
    intro r
    let V := X.basicOpen r
    let i := V.leTop.op
    let sourceRestriction := (F.obj M).map i
    let targetRestriction := (F.obj N).map i
    have hSource : IsLocalizedModule.Away r sourceRestriction.hom := by
      dsimp only [sourceRestriction, F, i, V]
      exact Modules.baseModulePresheaf_isLocalized_basicOpen M r
    have hTarget : IsLocalizedModule.Away r targetRestriction.hom := by
      dsimp only [targetRestriction, F, i, V]
      exact Modules.baseModulePresheaf_isLocalized_basicOpen N r
    haveI hφBOpen : IsIso (φB.app (.op V)) := by
      refine ModuleCat.isIso_of_isLocalizedModule_comp hSource ?_
      change IsLocalizedModule.Away r
        (sourceRestriction ≫ φB.app (.op V)).hom
      rw [φB.naturality i]
      change IsLocalizedModule.Away r
        (φB.app (.op (⊤ : X.Opens)) ≫ targetRestriction).hom
      exact IsLocalizedModule.of_linearEquiv_right
        (Submonoid.powers r) targetRestriction.hom
        (asIso (φB.app (.op (⊤ : X.Opens)))).toLinearEquiv
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (φB.app (.op V))
  exact @Functor.ReflectsIsomorphisms.reflects _ _ _ _
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) hreflect _ _ φ hmap

/-- On an affine scheme, if a global section of a quasicoherent module vanishes on a basic open,
then some power of the function defining that open annihilates the section. -/
theorem Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) (t : Γ(M, ⊤))
    (ht : M.presheaf.map (X.basicOpen f).leTop.op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  let B := baseModulePresheaf (𝟙 X) M
  let ψ := (B.map (X.basicOpen f).leTop.op).hom
  letI : IsLocalizedModule.Away f ψ :=
    Modules.baseModulePresheaf_isLocalized_basicOpen M f
  change ψ t = 0 at ht
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) ψ).mp ht
  refine ⟨n, ?_⟩
  change X.presheaf.map (homOfLE le_rfl).op
      ((Scheme.Hom.appTop (𝟙 X)) (f ^ n)) • t = 0 at hn
  rw [Scheme.Hom.id_appTop] at hn
  simpa using hn

/-- If a section of a quasicoherent module over an affine open vanishes on an intrinsic basic
open, then some power of the function defining that basic open annihilates the section. -/
theorem Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) (t : Γ(M, U.1))
    (ht : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  let N := M.restrict U.1.ι
  let g : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := U.1.topIso.inv f
  have hTop : U.1 = U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) :=
    U.1.ι_image_top.symm
  have hBasic : X.basicOpen f =
      U.1.ι ''ᵁ U.1.toScheme.basicOpen g := by
    exact (U.1.ι_image_basicOpen_topIso_inv f).symm
  let eTop : Γ(N, (⊤ : U.1.toScheme.Opens)) ≅ Γ(M, U.1) :=
    M.restrictAppIso U.1.ι ⊤ ≪≫
      M.presheaf.mapIso (eqToIso hTop).op
  let eBasic : Γ(N, U.1.toScheme.basicOpen g) ≅ Γ(M, X.basicOpen f) :=
    M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g) ≪≫
      M.presheaf.mapIso (eqToIso hBasic).op
  let s : Γ(N, (⊤ : U.1.toScheme.Opens)) := eTop.inv t
  have hs : N.presheaf.map (U.1.toScheme.basicOpen g).leTop.op s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso eBasic.hom).1
    rw [map_zero]
    simp only [N, s, eTop, eBasic, Iso.trans_hom,
      ConcreteCategory.comp_apply, Scheme.Modules.map_restrictAppIso_hom_apply,
      Iso.trans_inv, Iso.inv_hom_id_apply, Functor.mapIso_hom,
      Functor.mapIso_inv, ← M.presheaf.map_comp_apply]
    rw [show (((eqToIso hTop).op.inv ≫
          (homOfLE (U.1.ι.image_mono
            (show U.1.toScheme.basicOpen g ≤ ⊤ from le_top))).op) ≫
          (eqToIso hBasic).op.hom) =
        (homOfLE (X.basicOpen_le f)).op by
      apply Subsingleton.elim]
    exact ht
  obtain ⟨n, hn⟩ :=
    Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffine
      N g s hs
  refine ⟨n, ?_⟩
  have hn' := congr(eTop.hom $hn)
  rw [map_zero] at hn'
  have hscalarOne :
      X.presheaf.map (eqToIso hTop).hom.op
          ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv g) = f := by
    dsimp [g]
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso]
    change X.presheaf.map (eqToIso hTop).hom.op
      (X.presheaf.map (eqToIso hTop).op.inv f) = f
    rw [← X.presheaf.map_comp_apply]
    simp
  have hscalar :
      X.presheaf.map (eqToIso hTop).hom.op
          ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv
            (g ^ n)) = f ^ n := by
    rw [map_pow, map_pow, hscalarOne]
  simp only [eTop, Iso.trans_hom, ConcreteCategory.comp_apply] at hn'
  rw [smul_restrictAppIso_hom_apply] at hn'
  simp only [Functor.mapIso_hom] at hn'
  rw [show (eqToIso hTop).op.hom = (eqToIso hTop).hom.op by
    apply Subsingleton.elim] at hn'
  rw [M.map_smul, hscalar] at hn'
  have hsection :
      M.presheaf.map (eqToIso hTop).hom.op
          ((M.restrictAppIso U.1.ι ⊤).hom s) = t := by
    change eTop.hom s = t
    exact eTop.inv_hom_id_apply t
  rw [hsection] at hn'
  exact hn'

/-- On an affine scheme, a section of a quasicoherent module over `D(f)` extends globally after
multiplication by a power of the restriction of `f`. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (X.basicOpen f).leTop.op t =
        X.presheaf.map (X.basicOpen f).leTop.op (f ^ n) • s := by
  let B := baseModulePresheaf (𝟙 X) M
  let ψ := (B.map (X.basicOpen f).leTop.op).hom
  letI : IsLocalizedModule.Away f ψ :=
    Modules.baseModulePresheaf_isLocalized_basicOpen M f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj ψ f s
  exact ⟨n, t, ht.symm⟩

/-- A section of a quasicoherent module on an intrinsic basic open of an affine open extends
to the affine open after multiplication by a power of the restricted function. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U.1)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s := by
  let N := M.restrict U.1.ι
  let g : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := U.1.topIso.inv f
  have hTop : U.1 = U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) :=
    U.1.ι_image_top.symm
  have hBasic : X.basicOpen f =
      U.1.ι ''ᵁ U.1.toScheme.basicOpen g := by
    exact (U.1.ι_image_basicOpen_topIso_inv f).symm
  let eTop : Γ(N, (⊤ : U.1.toScheme.Opens)) ≅ Γ(M, U.1) :=
    M.restrictAppIso U.1.ι ⊤ ≪≫
      M.presheaf.mapIso (eqToIso hTop).op
  let eBasic : Γ(N, U.1.toScheme.basicOpen g) ≅ Γ(M, X.basicOpen f) :=
    M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g) ≪≫
      M.presheaf.mapIso (eqToIso hBasic).op
  let r : Γ(N, U.1.toScheme.basicOpen g) := eBasic.inv s
  obtain ⟨n, t, ht⟩ :=
    Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffine
      N g r
  refine ⟨n, eTop.hom t, ?_⟩
  have hleft :
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op (eTop.hom t) =
        eBasic.hom
          (N.presheaf.map (U.1.toScheme.basicOpen g).leTop.op t) := by
    simp only [N, eTop, eBasic, Iso.trans_hom,
      ConcreteCategory.comp_apply, Functor.mapIso_hom,
      Modules.map_restrictAppIso_hom_apply,
      ← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) _
  have hright :
      eBasic.hom
          (U.1.toScheme.presheaf.map
              (U.1.toScheme.basicOpen g).leTop.op (g ^ n) • r) =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s := by
    change M.presheaf.map (eqToIso hBasic).op.hom
        ((M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g)).hom
          (U.1.toScheme.presheaf.map
              (U.1.toScheme.basicOpen g).leTop.op (g ^ n) • r)) = _
    rw [Modules.smul_restrictAppIso_hom_apply]
    have hmap := M.val.map_smul (eqToIso hBasic).op.hom
      ((U.1.ι.appIso (U.1.toScheme.basicOpen g)).inv
        (U.1.toScheme.presheaf.map
          (U.1.toScheme.basicOpen g).leTop.op (g ^ n)))
      ((M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g)).hom r)
    refine hmap.trans ?_
    have hr :
        M.val.map (eqToIso hBasic).op.hom
            ((M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g)).hom r) = s := by
      dsimp only [r]
      change eBasic.hom r = s
      exact eBasic.inv_hom_id_apply s
    rw [hr]
    let i : Opposite.op (⊤ : U.1.toScheme.Opens) ⟶
        Opposite.op (U.1.toScheme.basicOpen g) :=
      (U.1.toScheme.basicOpen g).leTop.op
    have hnat := ConcreteCategory.congr_hom
      (U.1.ι.appIso_inv_naturality i) (g ^ n)
    have hscalarOne :
        X.presheaf.map (eqToIso hTop).hom.op
            ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv g) = f := by
      dsimp only [g]
      rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso]
      change X.presheaf.map (eqToIso hTop).hom.op
        (X.presheaf.map (eqToIso hTop).op.inv f) = f
      rw [← X.presheaf.map_comp_apply]
      simp
    have hscalarTop :
        X.presheaf.map (eqToIso hTop).hom.op
            ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv (g ^ n)) =
          f ^ n := by
      rw [map_pow, map_pow, hscalarOne]
    have hscalar :
        X.presheaf.map (eqToIso hBasic).op.hom
            ((U.1.ι.appIso (U.1.toScheme.basicOpen g)).inv
              (U.1.toScheme.presheaf.map i (g ^ n))) =
          X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) := by
      calc
        X.presheaf.map (eqToIso hBasic).op.hom
            ((U.1.ι.appIso (U.1.toScheme.basicOpen g)).inv
              (U.1.toScheme.presheaf.map i (g ^ n))) =
            X.presheaf.map (eqToIso hBasic).op.hom
              (X.presheaf.map (U.1.ι.opensFunctor.op.map i)
                ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv (g ^ n))) := by
              exact congrArg
                (fun y ↦ X.presheaf.map (eqToIso hBasic).op.hom y) hnat
        _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op
            (X.presheaf.map (eqToIso hTop).hom.op
              ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv (g ^ n))) := by
              rw [← X.presheaf.map_comp_apply, ← X.presheaf.map_comp_apply]
              exact ConcreteCategory.congr_hom
                (X.presheaf.congr_map (Subsingleton.elim _ _)) _
        _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) := by
              rw [hscalarTop]
    exact congrArg (fun z : Γ(X, X.basicOpen f) ↦ z • s) hscalar
  exact hleft.trans ((congrArg eBasic.hom ht).trans hright)

/-- Restriction of a quasicoherent module from an affine open to an intrinsic basic open is
localization away from the function defining that basic open. -/
theorem Modules.isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    letI : Module Γ(X, U.1) Γ(M, X.basicOpen f) :=
      Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))
    IsLocalizedModule.Away f
      ({
          toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
          map_add' :=
            (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.map_add
          map_smul' := fun r x ↦
            M.map_smul (homOfLE (X.basicOpen_le f)) r x
        } : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen f)) := by
  letI : Module Γ(X, U.1) Γ(M, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))
  letI : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    U.2.isLocalization_basicOpen f
  let ψ : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen f) :=
    {
      toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
      map_add' :=
        (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.map_add
      map_smul' := fun r x ↦
        M.map_smul (homOfLE (X.basicOpen_le f)) r x
    }
  change IsLocalizedModule.Away f ψ
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · have hunit : IsUnit
        (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) f) :=
      IsLocalization.Away.algebraMap_isUnit _
    have hunitEnd := hunit.map
      (algebraMap Γ(X, X.basicOpen f)
        (Module.End Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)))
    rw [Module.End.isUnit_iff] at hunitEnd ⊢
    convert hunitEnd using 1
    ext x
    rfl
  · intro s
    obtain ⟨n, t, ht⟩ :=
      Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffineOpen
        M U f s
    exact ⟨n, t, ht.symm⟩
  · intro t ht
    exact
      Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
        M U f t ht

/-- Finitely many sections on an intrinsic basic open of an affine open extend to the affine
open after multiplication by one common power of the restricted function. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_finite_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) {I : Type*} [Finite I]
    (s : I → Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : I → Γ(M, U.1)), ∀ i,
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op (t i) =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s i := by
  choose n t ht using fun i ↦
    Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffineOpen
      M U f (s i)
  have hle (i : I) : n i ≤ ⨆ i, n i :=
    le_ciSup (Finite.bddAbove_range n) i
  refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t i, fun i ↦ ?_⟩
  rw [M.map_smul, ht i, ← mul_smul, ← map_mul, ← pow_add,
    Nat.sub_add_cancel (hle i)]

/-- On an affine scheme, finitely many sections of a quasicoherent module over `D(f)` extend
globally after multiplication by one common power of the restriction of `f`. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_finite_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) {ι : Type*} [Finite ι]
    (s : ι → Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : ι → Γ(M, ⊤)), ∀ i,
      M.presheaf.map (X.basicOpen f).leTop.op (t i) =
        X.presheaf.map (X.basicOpen f).leTop.op (f ^ n) • s i := by
  choose n t ht using fun i ↦
    Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_of_isAffine
      M f (s i)
  have hle (i : ι) : n i ≤ ⨆ i, n i :=
    le_ciSup (Finite.bddAbove_range n) i
  refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t i,
    fun i ↦ ?_⟩
  rw [M.map_smul, ht i, ← mul_smul, ← map_mul, ← pow_add,
    Nat.sub_add_cancel (hle i)]

/-- A finite-type quasicoherent module has a finite module of sections on every affine open. -/
theorem Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  letI : q.IsFiniteType := hq
  let t : Set Γ(X, U.1) :=
    { f | ∃ i, X.basicOpen f ≤ q.X i }
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := X) q.X).mp q.coversTop
  have hopen : ⨆ f : t, X.basicOpen f.1 = U.1 := by
    apply le_antisymm
    · exact iSup_le fun f ↦ X.basicOpen_le f.1
    · calc
        U.1 = U.1 ⊓ ⊤ := by simp
        _ = U.1 ⊓ ⨆ i, q.X i := by rw [hqcover]
        _ = ⨆ i, U.1 ⊓ q.X i := by rw [inf_iSup_eq]
        _ ≤ ⨆ f : t, X.basicOpen f.1 := by
          refine iSup_le fun i ↦ ?_
          rintro x hx
          obtain ⟨f, hf, hxf⟩ :=
            U.2.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
          have hle : X.basicOpen f ≤
              ⨆ f : t, X.basicOpen f.1 :=
            le_iSup_of_le ⟨f, i, hf⟩ le_rfl
          exact hle hxf
  have ht : Ideal.span t = ⊤ :=
    U.2.iSup_basicOpen_eq_self_iff.mp hopen
  letI (g : t) : Algebra Γ(X, U.1) Γ(X, X.basicOpen g.1) :=
    inferInstance
  letI (g : t) : Module Γ(X, U.1) Γ(M, X.basicOpen g.1) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen g.1))
  letI (g : t) : IsLocalization.Away g.1
      Γ(X, X.basicOpen g.1) :=
    U.2.isLocalization_basicOpen g.1
  letI (g : t) : IsScalarTower Γ(X, U.1)
      Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : (g : t) →
      Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen g.1) :=
    fun g ↦
      {
        toFun := M.presheaf.map (homOfLE (X.basicOpen_le g.1)).op
        map_add' :=
          (M.presheaf.map (homOfLE (X.basicOpen_le g.1)).op).hom.map_add
        map_smul' := fun r x ↦
          M.map_smul (homOfLE (X.basicOpen_le g.1)) r x
      }
  letI : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) :=
    fun g ↦
      Modules.isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen
        M U g.1
  refine Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t ↦ Γ(M, X.basicOpen g.1))
    (Rₚ := fun g : t ↦ Γ(X, X.basicOpen g.1))
    t ht φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  letI : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact Modules.module_finite_app_of_over_generators_of_le M hi
    (U.2.basicOpen g.1) (q.generators i)

/-- A finite-type quasicoherent module on an affine scheme has finite global sections. -/
theorem Modules.globalSections_module_finite_of_isFiniteType_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  letI : q.IsFiniteType := hq
  let t : Set Γ(X, ⊤) := { f | ∃ i, X.basicOpen f ≤ q.X i }
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := X) q.X).mp q.coversTop
  have hopen : ⨆ f : t, X.basicOpen f.1 = ⊤ := by
    apply top_unique
    calc
      ⊤ = ⨆ i, q.X i := hqcover.symm
      _ ≤ ⨆ f : t, X.basicOpen f.1 := by
        refine iSup_le fun i ↦ ?_
        rintro x hx
        obtain ⟨f, hf, hxf⟩ :=
          (isAffineOpen_top X).exists_basicOpen_le ⟨x, hx⟩ (by simp)
        have hle : X.basicOpen f ≤ ⨆ f : t, X.basicOpen f.1 :=
          le_iSup_of_le ⟨f, i, hf⟩ le_rfl
        exact hle hxf
  have ht : Ideal.span t = ⊤ :=
    (isAffineOpen_top X).iSup_basicOpen_eq_self_iff.mp hopen
  let B := baseModulePresheaf (𝟙 X) M
  letI (g : t) : Algebra Γ(X, ⊤) Γ(X, X.basicOpen g.1) :=
    inferInstance
  letI (g : t) : Module Γ(X, ⊤) Γ(M, X.basicOpen g.1) :=
    Module.compHom _ (algebraMap _ Γ(X, X.basicOpen g.1))
  letI (g : t) : IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) :=
    inferInstance
  letI (g : t) : IsScalarTower Γ(X, ⊤)
      Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eTop : B.obj (op ⊤) ≅ ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, ⊤))
    change r • x =
      X.presheaf.map
        ((initialOpOfTerminal isTerminalTop).to (op (⊤ : X.Opens)))
          (Scheme.Hom.appTop (𝟙 X) r) • x
    rw [Scheme.Hom.id_appTop]
    rw [Subsingleton.elim
      ((initialOpOfTerminal isTerminalTop).to (op (⊤ : X.Opens))) (𝟙 _)]
    simp
  let eBasic (g : t) :
      B.obj (op (X.basicOpen g.1)) ≅
        ModuleCat.of Γ(X, ⊤) Γ(M, X.basicOpen g.1) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, X.basicOpen g.1))
    change
      algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g.1) r • x =
        X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to
            (op (X.basicOpen g.1)))
            (Scheme.Hom.appTop (𝟙 X) r) • x
    rw [Scheme.Hom.id_appTop]
    rfl
  let φCat (g : t) :
      ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) ⟶
        ModuleCat.of Γ(X, ⊤) Γ(M, X.basicOpen g.1) :=
    eTop.inv ≫ B.map (X.basicOpen g.1).leTop.op ≫ (eBasic g).hom
  let φ : (g : t) → Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(M, X.basicOpen g.1) :=
    fun g ↦ (φCat g).hom
  letI : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) := fun g ↦ by
    exact Modules.isLocalizedModuleAway_of_iso_square g.1
      (B.map (X.basicOpen g.1).leTop.op) (φCat g)
      eTop (eBasic g) (by simp [φCat])
      (Modules.baseModulePresheaf_isLocalized_basicOpen M g.1)
  refine Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t ↦ Γ(M, X.basicOpen g.1))
    (Rₚ := fun g : t ↦ Γ(X, X.basicOpen g.1))
    t ht φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  letI : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact Modules.module_finite_app_of_over_generators_of_le M hi
    ((isAffineOpen_top X).basicOpen g.1) (q.generators i)

/-- A quasicoherent module on an affine spectrum whose global sections are finite has finitely
many global generating sections. -/
theorem Modules.exists_generatingSections_of_moduleSpecΓ_finite
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R Γ(M, ⊤)] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) := by
    change Module.Finite R Γ(M, ⊤)
    infer_instance
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin
    (R := R) (M := moduleSpecΓFunctor.obj M)
  let ι := ULift.{u} (Fin n)
  let v : ι → moduleSpecΓFunctor.obj M := fun i ↦ s i.down
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    have hrange : Set.range v = Set.range s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
    rw [hrange, hs]
  let p' : ModuleCat.of R (ι →₀ R) ⟶ moduleSpecΓFunctor.obj M := by
    change ModuleCat.of R (ι →₀ R) ⟶
      ModuleCat.of R (moduleSpecΓFunctor.obj M)
    exact ModuleCat.ofHom (Finsupp.linearCombination R v)
  letI : Epi p' := (ModuleCat.epi_iff_surjective p').mpr
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hv)
  letI : (tilde.functor R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction tilde.adjunction
  have hmap : Epi ((tilde.functor R).map p') :=
    Functor.map_epi (tilde.functor R) p'
  letI : IsIso M.fromTildeΓ := inferInstance
  have hfrom : Epi M.fromTildeΓ := IsIso.epi_of_iso M.fromTildeΓ
  let e := tildeFinsupp (R := R) ι
  letI : IsIso e.inv := e.isIso_inv
  have he : Epi e.inv := IsIso.epi_of_iso e.inv
  let f : SheafOfModules.free (R := (Spec R).ringCatSheaf) ι ⟶ M :=
    e.inv ≫ (tilde.functor R).map p' ≫ M.fromTildeΓ
  haveI : Epi f := by
    have hleft : Epi (e.inv ≫ (tilde.functor R).map p') :=
      epi_comp' he hmap
    have hfull : Epi ((e.inv ≫ (tilde.functor R).map p') ≫ M.fromTildeΓ) :=
      epi_comp' hleft hfrom
    exact hfull
  let G : M.GeneratingSections :=
    { I := ι
      s := M.freeHomEquiv f
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }
  haveI : G.IsFiniteType := ⟨inferInstance⟩
  exact ⟨G, inferInstance⟩

private theorem Modules.moduleSpecΓ_finite_of_globalSections_module_finite_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)] :
    Module.Finite Γ(X, ⊤)
      (moduleSpecΓFunctor.obj (M.restrict (isoSpec X).inv)) := by
  let M' := M.restrict (isoSpec X).inv
  have hM : Module.Finite Γ(X, ⊤) Γ(M, ⊤) :=
    inferInstance
  let eRight : ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) ≅
      (baseModulePresheaf (𝟙 X) M).obj (op (⊤ : X.Opens)) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, ⊤))
    change X.presheaf.map (homOfLE le_rfl).op
        ((Scheme.Hom.appTop (𝟙 X)) r) • x = r • x
    rw [Scheme.Hom.id_appTop]
    simp
  letI : Module.Finite Γ(X, ⊤)
      ((baseModulePresheaf (𝟙 X) M).obj (op (⊤ : X.Opens))) :=
    Module.Finite.equiv eRight.toLinearEquiv
  have hright : Module.Finite Γ(X, ⊤)
      ((baseModulePresheaf (𝟙 X) M).obj
        (op ((isoSpec X).inv ''ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens)))) := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_of_isIso]
    infer_instance
  let e := baseModulePresheafRestrictAppIso
    (𝟙 X) (isoSpec X).inv M (⊤ : (Spec Γ(X, ⊤)).Opens)
  letI : Module.Finite Γ(X, ⊤)
      ((baseModulePresheaf (𝟙 X) M).obj
        (op ((isoSpec X).inv ''ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens)))) := hright
  have hleft : Module.Finite Γ(X, ⊤)
      ((baseModulePresheaf ((isoSpec X).inv ≫ 𝟙 X) M').obj
        (op (⊤ : (Spec Γ(X, ⊤)).Opens))) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have happ : X.isoSpec.inv.appTop =
      (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv := by
    have hhom : X.isoSpec.hom.appTop =
        (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom := by
      simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop]
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom]
    rw [← hhom]
    rw [← Scheme.Hom.comp_appTop]
    rw [X.isoSpec.hom_inv_id]
    rw [hhom]
    simp
  let eLeft :
      (baseModulePresheaf ((isoSpec X).inv ≫ 𝟙 X) M').obj
          (op (⊤ : (Spec Γ(X, ⊤)).Opens)) ≅
        moduleSpecΓFunctor.obj M' := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M', ⊤))
    change
      (Spec Γ(X, ⊤)).presheaf.map (homOfLE le_rfl).op
          ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) • x =
        (Spec Γ(X, ⊤)).presheaf.map (homOfLE le_rfl).op
          ((X.isoSpec.inv ≫ 𝟙 X).appTop r) • x
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, Category.id_comp,
      happ]
  letI : Module.Finite Γ(X, ⊤)
      ((baseModulePresheaf ((isoSpec X).inv ≫ 𝟙 X) M').obj
        (op (⊤ : (Spec Γ(X, ⊤)).Opens))) := hleft
  change Module.Finite Γ(X, ⊤)
    (moduleSpecΓFunctor.obj (M.restrict (isoSpec X).inv))
  exact Module.Finite.equiv eLeft.toLinearEquiv

/-- A quasicoherent module with finite global sections on an affine scheme has finitely many
global generating sections. -/
theorem Modules.exists_generatingSections_of_globalSections_module_finite_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let M' : (Spec Γ(X, ⊤)).Modules := M.restrict (isoSpec X).inv
  have hfinite : Module.Finite Γ(X, ⊤) (moduleSpecΓFunctor.obj M') :=
    Modules.moduleSpecΓ_finite_of_globalSections_module_finite_of_isAffine M
  letI : Module.Finite Γ(X, ⊤) Γ(M', ⊤) := by
    change Module.Finite Γ(X, ⊤) (moduleSpecΓFunctor.obj M')
    exact hfinite
  obtain ⟨G', hG'⟩ :=
    Modules.exists_generatingSections_of_moduleSpecΓ_finite M'
  letI : G'.IsFiniteType := hG'
  let F := Scheme.Modules.restrictFunctor (isoSpec X).hom
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F := by
    dsimp [F]
    infer_instance
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G'' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G' F hF
      (restrictUnitIso (isoSpec X).hom).symm
  let G := SheafOfModules.GeneratingSections.equivOfIso
    ((Scheme.Modules.restrictFunctor_inv_restrictFunctor_hom_id
      (isoSpec X)).app M) G''
  haveI : G.IsFiniteType := ⟨by
    change Finite G'.I
    exact hG'.finite⟩
  exact ⟨G, inferInstance⟩

/-- A finite-type quasicoherent module on an affine scheme has finitely many global generating
sections. -/
theorem Modules.exists_generatingSections_of_isFiniteType_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    [M.IsFiniteType] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  letI : Module.Finite Γ(X, ⊤) Γ(M, ⊤) :=
    Modules.globalSections_module_finite_of_isFiniteType_of_isAffine M
  exact
    Modules.exists_generatingSections_of_globalSections_module_finite_of_isAffine M

/-- If the sections of a quasicoherent module on an affine open are finite, then its restriction
has finitely many global generating sections. -/
theorem Modules.exists_generatingSections_restrict_of_sections_module_finite_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) [Module.Finite Γ(X, U.1) Γ(M, U.1)] :
    ∃ G : (M.restrict U.1.ι).GeneratingSections, G.IsFiniteType := by
  let N := M.restrict U.1.ι
  letI : IsAffine U.1.toScheme := U.2
  have hfinite : Module.Finite Γ(X, U.1) Γ(M, U.1) := inferInstance
  let eR' := U.1.ι.appIso (⊤ : U.1.toScheme.Opens)
  let eR : Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) ≃+*
      Γ(U.1.toScheme, ⊤) :=
    eR'.commRingCatIsoToRingEquiv
  let eM' := M.restrictAppIso U.1.ι ⊤
  let σ : Γ(U.1.toScheme, ⊤) →+*
      Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    eR'.inv.hom
  let eM : Γ(N, ⊤) →ₛₗ[σ]
      Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    {
      toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := by
        intro r x
        change eM'.hom (r • x) = eR'.inv.hom r • eM'.hom x
        exact Modules.smul_restrictAppIso_hom_apply U.1.ι M ⊤ r x
    }
  have hσ : Function.Surjective σ := by
    change Function.Surjective
      (eR.symm : Γ(U.1.toScheme, ⊤) →+*
        Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
    exact eR.symm.surjective
  letI : RingHomSurjective σ := ⟨hσ⟩
  have heM : Function.Bijective eM := by
    change Function.Bijective eM'.hom
    exact ConcreteCategory.bijective_of_isIso eM'.hom
  have htarget : Module.Finite
      Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))
      Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) := by
    rw [U.1.ι_image_top]
    exact hfinite
  have hsource : Module.Finite Γ(U.1.toScheme, ⊤) Γ(N, ⊤) :=
    (eM.finite_iff_of_bijective heM).mpr htarget
  letI : Module.Finite Γ(U.1.toScheme, ⊤) Γ(N, ⊤) :=
    hsource
  exact
    Modules.exists_generatingSections_of_globalSections_module_finite_of_isAffine N

/-- Restriction of a finite-type quasicoherent module to an affine open has finitely many global
generating sections. -/
theorem Modules.exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) :
    ∃ G : (M.restrict U.1.ι).GeneratingSections, G.IsFiniteType := by
  letI : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M U
  exact Modules.exists_generatingSections_restrict_of_sections_module_finite_of_isAffineOpen
    M U

namespace Modules

private noncomputable def kernelAppLinearEquivOverOpen
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    Γ(kernel f, U) ≃ₗ[Γ(X, U)]
      (show Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) from
        (f.val.app (op U)).hom).ker := by
  let e := (PreservesKernel.iso
    (SheafOfModules.evaluation X.ringCatSheaf (op U)) f).trans
      (ModuleCat.kernelIsoKer _)
  let fU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    (f.val.app (op U)).hom
  let eΓ : Γ(kernel f, U) ≃ₗ[Γ(X, U)] fU.ker :=
    e.toLinearEquiv
  exact eΓ

private theorem kernel_sections_module_finite_of_isAffineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (f : M ⟶ N) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(kernel f, U.1) := by
  letI : IsNoetherianRing Γ(X, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  letI : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M U
  let fU : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1) :=
    (f.val.app (op U.1)).hom
  letI : _root_.IsNoetherian Γ(X, U.1) Γ(M, U.1) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  letI : _root_.IsNoetherian Γ(X, U.1) fU.ker :=
    isNoetherian_of_submodule_of_noetherian _ _ fU.ker inferInstance
  letI : Module.Finite Γ(X, U.1) fU.ker :=
    Module.IsNoetherian.finite _ _
  exact Module.Finite.equiv (kernelAppLinearEquivOverOpen f U.1).symm

/-- Generating sections of a restriction give generating sections of the corresponding
over-site module. -/
noncomputable def generatingSectionsOverOfRestrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.restrict U.ι).GeneratingSections) :
    (M.over U).GeneratingSections := by
  let N := M.restrict U.ι
  letI : (overEquiv U).inverse.IsEquivalence := by
    infer_instance
  let hPres : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse := by
    infer_instance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G (overEquiv U).inverse hPres
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e : M.over U ≅ (overEquiv U).inverse.obj N :=
    (overEquiv U).unitIso.app (M.over U) ≪≫
      (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M)
  exact (SheafOfModules.GeneratingSections.equivOfIso e).symm G'

/-- The over-site generating sections induced from finite generating sections of a restriction
are finite. -/
theorem generatingSectionsOverOfRestrict_isFiniteType
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.restrict U.ι).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsOverOfRestrict M U G).IsFiniteType where
  finite := by
    change Finite G.I
    exact SheafOfModules.GeneratingSections.IsFiniteType.finite

/-- A quasicoherent module whose sections on every affine open are finite is of finite type. -/
theorem isFiniteType_of_sections_module_finite
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (hfinite : ∀ U : X.affineOpens,
      Module.Finite Γ(X, U.1) Γ(M, U.1)) :
    M.IsFiniteType := by
  choose G hG using fun U : X.affineOpens ↦ by
    letI : Module.Finite Γ(X, U.1) Γ(M, U.1) := hfinite U
    exact exists_generatingSections_restrict_of_sections_module_finite_of_isAffineOpen M U
  let q : M.LocalGeneratorsData :=
    { I := X.affineOpens
      X := fun U ↦ (U : X.Opens)
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
      generators := fun U ↦ generatingSectionsOverOfRestrict M U.1 (G U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    letI : (G U).IsFiniteType := hG U
    exact generatingSectionsOverOfRestrict_isFiniteType M U.1 (G U)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩

private theorem pushforward_sections_module_finite_of_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {M : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (U : Y.affineOpens) :
    Module.Finite Γ(Y, U.1) Γ((pushforward f).obj M, U.1) := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hM : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M V
  letI : Module.Finite Γ(X, V.1) Γ(M, V.1) := hM
  letI : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.app U.1).hom.toAlgebra
  letI : Module Γ(Y, U.1) Γ(M, V.1) :=
    Module.compHom Γ(M, V.1) (f.app U.1).hom
  letI : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(M, V.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rw [Module.finite_def]
  change (⊤ : Submodule Γ(Y, U.1) Γ(M, V.1)).FG
  rw [← Submodule.restrictScalars_top (S := Γ(Y, U.1))
    (R := Γ(X, V.1)) (M := Γ(M, V.1))]
  exact hM.fg_top.restrictScalars_of_surjective (f.app_surjective U.1 U.2)

/-- Pushforward along a closed immersion preserves finite-type quasicoherent modules. -/
theorem isFiniteType_pushforward_of_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {M : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pushforward f).obj M).IsFiniteType := by
  let N := (pushforward f).obj M
  letI : N.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom f
  exact isFiniteType_of_sections_module_finite N
    (pushforward_sections_module_finite_of_isClosedImmersion f)

/-- On a locally Noetherian scheme, the kernel of a morphism from a finite-type quasicoherent
module to a quasicoherent module is of finite type. -/
theorem isFiniteType_kernel
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType]
    (f : M ⟶ N) : (kernel f).IsFiniteType := by
  let K := kernel f
  letI : K.IsQuasicoherent := isQuasicoherent_kernel f
  exact isFiniteType_of_sections_module_finite K
    (kernel_sections_module_finite_of_isAffineOpen f)

private theorem fin_coproduct_sections_module_finite
    {X : Scheme.{u}} {r : ℕ} (M : Fin r → X.Modules)
    (hqc : ∀ i, (M i).IsQuasicoherent)
    (hft : ∀ i, (M i).IsFiniteType) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(∐ M, U.1) := by
  letI : HasZeroMorphisms X.Modules :=
    CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  letI : HasZeroMorphisms
      (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U.1))) :=
    CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  letI : HasFiniteBiproducts X.Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  letI : HasFiniteBiproducts
      (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U.1))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : F.Additive := by
    dsimp only [F, SheafOfModules.evaluation]
    infer_instance
  let hPresZero : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  letI : F.PreservesZeroMorphisms := hPresZero
  let hFinite : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  letI (i : Fin r) : (M i).IsQuasicoherent := hqc i
  letI (i : Fin r) : (M i).IsFiniteType := hft i
  letI (i : Fin r) : Module.Finite Γ(X, U.1) Γ(M i, U.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen (M i) U
  letI : Module.Finite Γ(X, U.1) (∀ i : Fin r, Γ(M i, U.1)) :=
    Module.Finite.pi
  let hBM : HasBiproduct M := HasBiproduct.of_hasCoproduct M
  letI : HasBiproduct M := hBM
  let hBF : HasBiproduct (F.obj ∘ M) :=
    HasBiproduct.of_hasProduct (F.obj ∘ M)
  letI : HasBiproduct (F.obj ∘ M) := hBF
  let hShape : PreservesBiproductsOfShape (Fin r) F :=
    @PreservesFiniteBiproducts.preserves
      X.Modules _
      (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U.1))) _
      CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
      CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
      F hPresZero hFinite (Fin r) inferInstance
  let hPres :=
    @PreservesBiproductsOfShape.preserves
      X.Modules _
      (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U.1))) _
      CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
      CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
      (Fin r) F hPresZero hShape M
  let e₀ := F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ := @Functor.mapBiproduct
    X.Modules _
    (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U.1))) _
    CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
    CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
    (Fin r) F M hBM hPresZero hPres
  let e₂ := biproduct.isoProduct (F.obj ∘ M)
  let e₃ := ModuleCat.piIsoPi (F.obj ∘ M)
  let e : ModuleCat.of Γ(X, U.1) Γ(∐ M, U.1) ≅
      ModuleCat.of Γ(X, U.1) (∀ i : Fin r, Γ(M i, U.1)) :=
    e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- A finite coproduct of finite-type quasicoherent modules is of finite type. -/
theorem isFiniteType_fin_coproduct
    {X : Scheme.{u}} {r : ℕ} (M : Fin r → X.Modules)
    (hqc : ∀ i, (M i).IsQuasicoherent)
    (hft : ∀ i, (M i).IsFiniteType) :
    (∐ M).IsFiniteType := by
  letI : (∐ M).IsQuasicoherent := isQuasicoherent_coproduct M hqc
  exact isFiniteType_of_sections_module_finite (∐ M)
    (fin_coproduct_sections_module_finite M hqc hft)

end Modules

/-- An epimorphism of quasicoherent modules is surjective on sections over an affine open. -/
theorem Modules.isQuasicoherent_app_surjective_of_epi
    (U : X.Opens) (hU : IsAffineOpen U)
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op U)).hom := by
  letI : IsAffine U.toScheme := hU
  have h := Modules.isQuasicoherent_surjective_of_epi
    ((restrictFunctor U.ι).map f)
  change Function.Surjective
    (f.val.app (op (U.ι ''ᵁ (⊤ : U.toScheme.Opens)))).hom at h
  rw [U.ι_image_top] at h
  exact h

end

end AlgebraicGeometry.Scheme
