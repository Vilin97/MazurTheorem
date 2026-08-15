/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechHomology
import MazurTorsion.Upstream.SchemeModuleCohomologyHZero

/-!
# Base-linear Cech degree one and genuine sheaf cohomology

This is the project-facing boundary for the affine-cover Cech comparison. It
identifies the additive group obtained by forgetting the base-module structure
on degree-one base-Cech homology with genuine Ext-based sheaf `H¹`.

The general comparison is additive and is compatible with the action induced
by global functions on the base.  Finite generation, properness, base change,
and semicontinuity remain separate results.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- On an affine open cover, forgetting the base action on native base-Cech
degree-one homology gives genuine Ext-based sheaf `H¹` as an additive group. -/
noncomputable def nativeBaseCechHOneForgetIso_of_affineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    (baseModuleForget S).obj ((baseCechComplex π M U).homology 1) ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj M.sheaf :=
  baseCechHomologyOneIso_of_affine_openCover π M U hU hUaff

/-- The project-facing affine-cover comparison is natural in an actual
morphism of quasicoherent coefficient modules. -/
private theorem nativeBaseCechHOneForgetIso_of_affineOpenCover_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    (baseModuleForget S).map
          (HomologicalComplex.homologyMap
            ((baseCechComplexFunctor π U).map f) 1) ≫
        (nativeBaseCechHOneForgetIso_of_affineOpenCover
          π N U hU hUaff).hom =
      (nativeBaseCechHOneForgetIso_of_affineOpenCover
          π M U hU hUaff).hom ≫
        (zariskiFunctor X 1).map f := by
  exact baseCechHomologyOneIso_of_affine_openCover_naturality
    π f U hU hUaff

private theorem baseModulePresheafFunctor_map_globalSmulHom_app
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    (r : Γ(S, ⊤))
    (V : X.Opensᵒᵖ) :
    ((baseModulePresheafFunctor π).map
        (globalSmulHom M (π.appTop r))).app V =
      r • 𝟙 ((baseModulePresheaf π M).obj V) := by
  ext x
  rfl

private theorem baseCechComplexFunctor_map_globalSmulHom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤)) :
    (baseCechComplexFunctor π U).map
        (globalSmulHom M (π.appTop r)) =
      r • 𝟙 (baseCechComplex π M U) := by
  apply baseCechComplexFunctor_map_eq_smul_id
  exact baseModulePresheafFunctor_map_globalSmulHom_app π M r

private theorem baseCechHomologyMap_smul_id
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤)) :
    HomologicalComplex.homologyMap
        (r • 𝟙 (baseCechComplex π M U)) 1 =
      r • 𝟙 ((baseCechComplex π M U).homology 1) := by
  calc
    HomologicalComplex.homologyMap
        (r • 𝟙 (baseCechComplex π M U)) 1 =
      r • HomologicalComplex.homologyMap
        (𝟙 (baseCechComplex π M U)) 1 := by
        dsimp only [HomologicalComplex.homologyMap]
        rw [show
          (HomologicalComplex.shortComplexFunctor
              (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) (.up ℕ) 1).map
                (r • 𝟙 (baseCechComplex π M U)) =
            r • (HomologicalComplex.shortComplexFunctor
              (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) (.up ℕ) 1).map
                (𝟙 (baseCechComplex π M U)) by
          ext <;> rfl]
        exact ShortComplex.homologyMap_smul _ _
    _ = r • 𝟙 ((baseCechComplex π M U).homology 1) := by
      rw [HomologicalComplex.homologyMap_id]

/-- The canonical action of base global functions on genuine `H¹`, obtained
by restricting the global-functions action along the base morphism. -/
@[reducible]
noncomputable def baseSectionsHOneModule
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    Module Γ(S, ⊤) (H M 1) := by
  letI := globalSectionsCohomologyModule M 1
  exact Module.compHom (H M 1) π.appTop.hom

/-- The affine-cover comparison intertwines native base-Cech scalar
multiplication with the canonical action induced from global functions on
the source scheme. -/
private theorem nativeBaseCechHOneForgetIso_of_affineOpenCover_map_globalSmulHom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (r : Γ(S, ⊤))
    (x : (baseCechComplex π M U).homology 1) :
    (nativeBaseCechHOneForgetIso_of_affineOpenCover
        π M U hU hUaff).hom (r • x) =
      (zariskiFunctor X 1).map (globalSmulHom M (π.appTop r))
        ((nativeBaseCechHOneForgetIso_of_affineOpenCover
          π M U hU hUaff).hom x) := by
  have hnat :=
    nativeBaseCechHOneForgetIso_of_affineOpenCover_naturality
      π (globalSmulHom M (π.appTop r)) U hU hUaff
  rw [baseCechComplexFunctor_map_globalSmulHom] at hnat
  have hhom := ConcreteCategory.congr_hom
    (baseCechHomologyMap_smul_id π M U r) x
  change (HomologicalComplex.homologyMap
      (r • 𝟙 (baseCechComplex π M U)) 1).hom x = r • x at hhom
  have hx := ConcreteCategory.congr_hom hnat x
  change (nativeBaseCechHOneForgetIso_of_affineOpenCover
      π M U hU hUaff).hom.hom
        ((HomologicalComplex.homologyMap
          (r • 𝟙 (baseCechComplex π M U)) 1).hom x) =
    ((zariskiFunctor X 1).map (globalSmulHom M (π.appTop r))).hom
      ((nativeBaseCechHOneForgetIso_of_affineOpenCover
        π M U hU hUaff).hom.hom x) at hx
  rw [← hhom]
  exact hx

/-- Native base-Cech `H¹` is linearly equivalent to genuine `H¹` with the
canonical global-functions action restricted along the base morphism. -/
noncomputable def nativeBaseCechHOneLinearEquivCanonical_of_affineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    letI := baseSectionsHOneModule π M
    (baseCechComplex π M U).homology 1 ≃ₗ[Γ(S, ⊤)] H M 1 := by
  letI := globalSectionsCohomologyModule M 1
  letI := baseSectionsHOneModule π M
  let e : (baseCechComplex π M U).homology 1 ≃+ H M 1 :=
    (nativeBaseCechHOneForgetIso_of_affineOpenCover
      π M U hU hUaff).addCommGroupIsoToAddEquiv
  exact
    { e with
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        change e (r • x) = π.appTop r • e x
        rw [globalSectionsCohomologyModule_smul]
        exact
          nativeBaseCechHOneForgetIso_of_affineOpenCover_map_globalSmulHom
            π M U hU hUaff r x }

/-- Every genuine sheaf `H¹` class has a representative in the underlying
additive group of native base-Cech degree-one homology. -/
theorem exists_nativeBaseCechHOne_class_of_sheafHOne_class
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (ξ : (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 1).obj M.sheaf) :
    ∃ η : (baseModuleForget S).obj ((baseCechComplex π M U).homology 1),
      (nativeBaseCechHOneForgetIso_of_affineOpenCover
        π M U hU hUaff).hom η = ξ :=
  (ConcreteCategory.bijective_of_isIso
    (nativeBaseCechHOneForgetIso_of_affineOpenCover
      π M U hU hUaff).hom).2 ξ

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
