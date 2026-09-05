/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechHomology
import MazurTorsion.Upstream.SchemeModuleCohomologyHZero

/-!
# Base-linear Cech degree zero and global sections

This file closes the degree-zero side of the low-degree Cech comparison.
For an arbitrary open cover, native Cech homology in degree zero is the
kernel of the first differential, and the sheaf axiom identifies that kernel
with global sections.  The comparison is then transported through the
base-module forgetful isomorphism.

The design boundary is deliberately narrower than proper cohomology: this
file proves only the cover comparison and makes no finiteness or properness
claim.  Its named downstream consumer is the coherent-support finiteness
theorem in `SchemeModuleBaseCechHZeroFinite`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- For an open cover, degree-zero native Cech homology is canonically the
global-sections object. -/
noncomputable def cechHomologyZeroIsoGlobalSectionsOfOpenCover
    (F : Sheaf AddCommGrpCat.{u} X) {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) :
    ((cechComplexFunctor U).obj F.obj).homology 0 ≅
      (globalSectionsFunctor X).obj F := by
  let C := (cechComplexFunctor U).obj F.obj
  let S := cechGlobalSectionsNativeShortComplex U F
  have hS : S.Exact :=
    cechGlobalSectionsNativeShortComplex_exact U F hU
  letI : Mono S.f := cechGlobalSectionsAugmentation_mono U F hU
  exact C.isoHomologyπ₀.symm ≪≫
    KernelFork.mapIsoOfIsLimit
      (C.cyclesIsKernel 0 1 (by simp)) hS.fIsKernel (Iso.refl _)

/-- The degree-zero comparison followed by the Cech augmentation is the
canonical inclusion of degree-zero homology into degree-zero cochains. -/
@[reassoc]
theorem cechHomologyZeroIsoGlobalSectionsOfOpenCover_hom_comp_augmentation
    (F : Sheaf AddCommGrpCat.{u} X) {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) :
    (cechHomologyZeroIsoGlobalSectionsOfOpenCover F U hU).hom ≫
        cechGlobalSectionsAugmentation F U =
      (((cechComplexFunctor U).obj F.obj).isoHomologyπ₀).inv ≫
        ((cechComplexFunctor U).obj F.obj).iCycles 0 := by
  simp only [cechHomologyZeroIsoGlobalSectionsOfOpenCover,
    cechGlobalSectionsNativeShortComplex, Iso.trans_hom, Iso.symm_hom,
    KernelFork.mapIsoOfIsLimit_hom, Iso.refl_hom, Category.assoc,
    Iso.cancel_iso_inv_left]
  apply KernelFork.mapOfIsLimit_ι

/-- The degree-zero native Cech/global-sections comparison is natural in the
coefficient sheaf. -/
@[reassoc]
theorem cechHomologyZeroIsoGlobalSectionsOfOpenCover_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) :
    HomologicalComplex.homologyMap
          ((cechComplexFunctor U).map f.hom) 0 ≫
        (cechHomologyZeroIsoGlobalSectionsOfOpenCover G U hU).hom =
      (cechHomologyZeroIsoGlobalSectionsOfOpenCover F U hU).hom ≫
        (globalSectionsFunctor X).map f := by
  let φ := (cechComplexFunctor U).map f.hom
  letI : Mono (cechGlobalSectionsAugmentation G U) :=
    cechGlobalSectionsAugmentation_mono U G hU
  apply (cancel_mono (cechGlobalSectionsAugmentation G U)).1
  simp only [Category.assoc]
  rw [cechHomologyZeroIsoGlobalSectionsOfOpenCover_hom_comp_augmentation]
  rw [← cechGlobalSectionsAugmentation_naturality]
  rw [cechHomologyZeroIsoGlobalSectionsOfOpenCover_hom_comp_augmentation_assoc]
  have hπ := CochainComplex.isoHomologyπ₀_inv_naturality
    (K := (cechComplexFunctor U).obj F.obj)
    (L := (cechComplexFunctor U).obj G.obj) φ
  rw [← Category.assoc, hπ, Category.assoc,
    HomologicalComplex.cyclesMap_i]

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- After forgetting the base action, degree-zero base-linear Cech homology
on an open cover is canonically the additive group of global sections. -/
noncomputable def baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    (baseModuleForget S).obj ((baseCechComplex π M U).homology 0) ≅
      AddCommGrpCat.of Γ(M, (⊤ : X.Opens)) :=
  baseCechComplexHomologyForgetIso π M U 0 ≪≫
    TopCat.Sheaf.cechHomologyZeroIsoGlobalSectionsOfOpenCover
      M.sheaf U (by simpa only [IsOpenCover] using hU) ≪≫
    (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).app M.sheaf

/-- The forgotten base-linear degree-zero Cech/global-sections comparison is
natural in morphisms of scheme modules. -/
@[reassoc]
theorem baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    (baseModuleForget S).map
          (HomologicalComplex.homologyMap
            ((baseCechComplexFunctor π U).map f) 0) ≫
        (baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
          π N U hU).hom =
      (baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
          π M U hU).hom ≫
        f.sheafHom.hom.app (op (⊤ : X.Opens)) := by
  let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  let a := (baseModuleForget S).map
    (HomologicalComplex.homologyMap
      ((baseCechComplexFunctor π U).map f) 0)
  let bM := (baseCechComplexHomologyForgetIso π M U 0).hom
  let bN := (baseCechComplexHomologyForgetIso π N U 0).hom
  let cM :=
    (TopCat.Sheaf.cechHomologyZeroIsoGlobalSectionsOfOpenCover
      M.sheaf U (by simpa only [IsOpenCover] using hU)).hom
  let cN :=
    (TopCat.Sheaf.cechHomologyZeroIsoGlobalSectionsOfOpenCover
      N.sheaf U (by simpa only [IsOpenCover] using hU)).hom
  let cMap := HomologicalComplex.homologyMap
    ((cechComplexFunctor U).map f.sheafHom.hom) 0
  let dM := eΓ.hom.app M.sheaf
  let dN := eΓ.hom.app N.sheaf
  let g := (TopCat.Sheaf.globalSectionsFunctor X).map f.sheafHom
  let k := f.sheafHom.hom.app (op (⊤ : X.Opens))
  have hab : a ≫ bN = bM ≫ cMap :=
    baseCechComplexHomologyForgetIso_naturality π f U 0
  have hcc : cMap ≫ cN = cM ≫ g :=
    TopCat.Sheaf.cechHomologyZeroIsoGlobalSectionsOfOpenCover_naturality
      f.sheafHom U (by simpa only [IsOpenCover] using hU)
  have hdd : g ≫ dN = dM ≫ k := eΓ.hom.naturality f.sheafHom
  have hleft :
      ((a ≫ bN) ≫ cN) ≫ dN = ((bM ≫ cMap) ≫ cN) ≫ dN :=
    congrArg (fun q => (q ≫ cN) ≫ dN) hab
  have hmiddle :
      ((bM ≫ cMap) ≫ cN) ≫ dN = ((bM ≫ cM) ≫ g) ≫ dN := by
    simpa only [Category.assoc] using
      congrArg (fun q => (bM ≫ q) ≫ dN) hcc
  have hright :
      ((bM ≫ cM) ≫ g) ≫ dN = (bM ≫ (cM ≫ dM)) ≫ k := by
    rw [Category.assoc, hdd]
    exact congrArg (fun q => q ≫ k) (Category.assoc bM cM dM)
  change a ≫ (bN ≫ (cN ≫ dN)) = (bM ≫ (cM ≫ dM)) ≫ k
  rw [← Category.assoc a bN (cN ≫ dN),
    ← Category.assoc (a ≫ bN) cN dN]
  exact hleft.trans (hmiddle.trans hright)

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

private theorem baseModulePresheafFunctor_map_globalSmulHom_app_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    (r : Γ(S, ⊤)) (V : X.Opensᵒᵖ) :
    ((baseModulePresheafFunctor π).map
        (globalSmulHom M (π.appTop r))).app V =
      r • 𝟙 ((baseModulePresheaf π M).obj V) := by
  ext x
  rfl

private theorem baseCechComplexFunctor_map_globalSmulHom_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤)) :
    (baseCechComplexFunctor π U).map
        (globalSmulHom M (π.appTop r)) =
      r • 𝟙 (baseCechComplex π M U) := by
  apply baseCechComplexFunctor_map_eq_smul_id
  exact baseModulePresheafFunctor_map_globalSmulHom_app_zero π M r

private theorem baseCechHomologyZeroMap_smul_id
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤)) :
    HomologicalComplex.homologyMap
        (r • 𝟙 (baseCechComplex π M U)) 0 =
      r • 𝟙 ((baseCechComplex π M U).homology 0) := by
  calc
    HomologicalComplex.homologyMap
        (r • 𝟙 (baseCechComplex π M U)) 0 =
      r • HomologicalComplex.homologyMap
        (𝟙 (baseCechComplex π M U)) 0 := by
        dsimp only [HomologicalComplex.homologyMap]
        rw [show
          (HomologicalComplex.shortComplexFunctor
              (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) (.up ℕ) 0).map
                (r • 𝟙 (baseCechComplex π M U)) =
            r • (HomologicalComplex.shortComplexFunctor
              (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) (.up ℕ) 0).map
                (𝟙 (baseCechComplex π M U)) by
          ext <;> rfl]
        exact ShortComplex.homologyMap_smul _ _
    _ = r • 𝟙 ((baseCechComplex π M U).homology 0) := by
      rw [HomologicalComplex.homologyMap_id]

/-- The canonical action of base global functions on genuine `H⁰`, obtained
by restricting the global-functions action along the base morphism. -/
@[reducible]
noncomputable def baseSectionsHZeroModule
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    Module Γ(S, ⊤) (H M 0) := by
  letI := globalSectionsCohomologyModule M 0
  exact Module.compHom (H M 0) π.appTop.hom

private theorem
    baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover_map_globalSmulHom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (r : Γ(S, ⊤)) (x : (baseCechComplex π M U).homology 0) :
    (baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
        π M U hU).hom (r • x) =
      (globalSmulHom M (π.appTop r)).app ⊤
        ((baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
          π M U hU).hom x) := by
  have hnat :=
    baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover_naturality
      π (globalSmulHom M (π.appTop r)) U hU
  rw [baseCechComplexFunctor_map_globalSmulHom_zero] at hnat
  have hhom := ConcreteCategory.congr_hom
    (baseCechHomologyZeroMap_smul_id π M U r) x
  change (HomologicalComplex.homologyMap
      (r • 𝟙 (baseCechComplex π M U)) 0).hom x = r • x at hhom
  have hx := ConcreteCategory.congr_hom hnat x
  change (baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
      π M U hU).hom.hom
        ((HomologicalComplex.homologyMap
          (r • 𝟙 (baseCechComplex π M U)) 0).hom x) =
    (globalSmulHom M (π.appTop r)).app ⊤
      ((baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
        π M U hU).hom.hom x) at hx
  rw [← hhom]
  exact hx

/-- Native base-Cech `H⁰` on any open cover is linearly equivalent to
genuine `H⁰` with the canonical global-functions action restricted along
the base morphism. -/
noncomputable def nativeBaseCechHZeroLinearEquivCanonicalOfOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    letI := baseSectionsHZeroModule π M
    (baseCechComplex π M U).homology 0 ≃ₗ[Γ(S, ⊤)] H M 0 := by
  letI := globalSectionsCohomologyModule M 0
  letI := baseSectionsHZeroModule π M
  let eΓ : (baseCechComplex π M U).homology 0 ≃+ Γ(M, ⊤) :=
    (baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
      π M U hU).addCommGroupIsoToAddEquiv
  let e : (baseCechComplex π M U).homology 0 ≃+ H M 0 :=
    eΓ.trans (hZeroEquivGlobalSections M).symm
  exact
    { e with
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        change e (r • x) = π.appTop r • e x
        rw [globalSectionsCohomologyModule_smul]
        apply (hZeroEquivGlobalSections M).injective
        rw [← hZeroEquivGlobalSections_naturality]
        have he (y : (baseCechComplex π M U).homology 0) :
            hZeroEquivGlobalSections M (e y) = eΓ y := by
          simp only [e, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
        rw [he, he]
        change (baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
            π M U hU).hom.hom (r • x) =
          (globalSmulHom M (π.appTop r)).app ⊤
            ((baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover
              π M U hU).hom.hom x)
        exact
          baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover_map_globalSmulHom
            π M U hU r x }

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
