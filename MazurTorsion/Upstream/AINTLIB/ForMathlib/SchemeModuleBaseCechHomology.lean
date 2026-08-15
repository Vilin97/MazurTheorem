/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import MazurTorsion.Upstream.AINTLIB.ForMathlib.AcyclicAffineCechComparison
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCech

/-!
# Degree-one homology of base-linear Cech complexes

This is the isomorphism-only slice of AINTLIB's base-Cech homology module.
It transports homology through the reviewed forgetful complex isomorphism and
then applies the affine-cover native-Cech comparison.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Forgetting the base-module structure on Cech homology recovers the
homology of the native additive Cech complex. -/
private noncomputable def baseCechComplexHomologyForgetIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseModuleForget S).obj ((baseCechComplex π M U).homology n) ≅
      ((cechComplexFunctor U).obj M.sheaf.obj).homology n :=
  (((baseCechComplex π M U).sc n).mapHomologyIso
    (baseModuleForget S)).symm ≪≫
      HomologicalComplex.homologyMapIso
        (baseCechComplexForgetIso π M U) n

@[simp]
private theorem baseCechComplexHomologyForgetIso_hom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplexHomologyForgetIso π M U n).hom =
      (((baseCechComplex π M U).sc n).mapHomologyIso
          (baseModuleForget S)).inv ≫
        HomologicalComplex.homologyMap
          (baseCechComplexForgetIso π M U).hom n :=
  rfl

/-- The comparison between forgotten base-linear Cech homology and native
additive Cech homology is natural in the coefficient module. -/
@[reassoc]
private theorem baseCechComplexHomologyForgetIso_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseModuleForget S).map
          (HomologicalComplex.homologyMap
            ((baseCechComplexFunctor π U).map f) n) ≫
        (baseCechComplexHomologyForgetIso π N U n).hom =
      (baseCechComplexHomologyForgetIso π M U n).hom ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor U).map f.sheafHom.hom) n := by
  let a := (((baseModuleForget S).mapHomologicalComplex (.up ℕ)).map
    ((baseCechComplexFunctor π U).map f))
  let b := (baseCechComplexForgetIso π N U).hom
  let c := (baseCechComplexForgetIso π M U).hom
  let d := (cechComplexFunctor U).map f.sheafHom.hom
  have hcomp : a ≫ b = c ≫ d :=
    baseCechComplexForgetIso_naturality π f U
  have hcomplex :
      HomologicalComplex.homologyMap a n ≫
          HomologicalComplex.homologyMap b n =
        HomologicalComplex.homologyMap c n ≫
          HomologicalComplex.homologyMap d n :=
    (HomologicalComplex.homologyMap_comp a b n).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g n) hcomp).trans
        (HomologicalComplex.homologyMap_comp c d n))
  let φ := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) (.up ℕ) n).map
      ((baseCechComplexFunctor π U).map f)
  let β := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      (baseCechComplexForgetIso π N U).hom
  let γ := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      (baseCechComplexForgetIso π M U).hom
  let δ := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      ((cechComplexFunctor U).map f.sheafHom.hom)
  let iN := ((((baseCechComplexFunctor π U).obj N).sc n).mapHomologyIso
    (baseModuleForget S)).inv
  let iM := ((((baseCechComplexFunctor π U).obj M).sc n).mapHomologyIso
    (baseModuleForget S)).inv
  dsimp only [a, b, c, d, HomologicalComplex.homologyMap] at hcomplex
  change ShortComplex.homologyMap
        ((baseModuleForget S).mapShortComplex.map φ) ≫
      ShortComplex.homologyMap β =
    ShortComplex.homologyMap γ ≫
      ShortComplex.homologyMap δ at hcomplex
  rw [baseCechComplexHomologyForgetIso_hom,
    baseCechComplexHomologyForgetIso_hom]
  dsimp only [HomologicalComplex.homologyMap]
  change (baseModuleForget S).map (ShortComplex.homologyMap φ) ≫
      (iN ≫ ShortComplex.homologyMap β) =
    iM ≫ (ShortComplex.homologyMap γ ≫
      ShortComplex.homologyMap δ)
  have hnat :
      (baseModuleForget S).map (ShortComplex.homologyMap φ) ≫ iN =
        iM ≫ ShortComplex.homologyMap
          ((baseModuleForget S).mapShortComplex.map φ) :=
    ShortComplex.mapHomologyIso_inv_naturality φ (baseModuleForget S)
  calc
    _ = ((baseModuleForget S).map (ShortComplex.homologyMap φ) ≫ iN) ≫
        ShortComplex.homologyMap β :=
      (Category.assoc _ _ _).symm
    _ = (iM ≫ ShortComplex.homologyMap
          ((baseModuleForget S).mapShortComplex.map φ)) ≫
        ShortComplex.homologyMap β :=
      congrArg (fun q => q ≫ ShortComplex.homologyMap β) hnat
    _ = iM ≫
        (ShortComplex.homologyMap
            ((baseModuleForget S).mapShortComplex.map φ) ≫
          ShortComplex.homologyMap β) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun q => iM ≫ q) hcomplex

/-- On an affine open cover, the underlying additive group of base-linear
Cech homology in degree one is genuine sheaf `H¹`. -/
noncomputable def baseCechHomologyOneIsoOfAffineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    (baseModuleForget S).obj ((baseCechComplex π M U).homology 1) ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj M.sheaf :=
  baseCechComplexHomologyForgetIso π M U 1 ≪≫
    cechHomologyOneIsoOfAffineOpenCover M U hU hUaff

@[simp]
private theorem baseCechHomologyOneIsoOfAffineOpenCover_hom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    (baseCechHomologyOneIsoOfAffineOpenCover
      π M U hU hUaff).hom =
      (baseCechComplexHomologyForgetIso π M U 1).hom ≫
        (cechHomologyOneIsoOfAffineOpenCover M U hU hUaff).hom :=
  rfl

/-- The affine-cover comparison from base-linear Cech homology to genuine
degree-one sheaf cohomology is natural in the coefficient module. -/
theorem baseCechHomologyOneIsoOfAffineOpenCover_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    (baseModuleForget S).map
          (HomologicalComplex.homologyMap
            ((baseCechComplexFunctor π U).map f) 1) ≫
        (baseCechHomologyOneIsoOfAffineOpenCover
          π N U hU hUaff).hom =
      (baseCechHomologyOneIsoOfAffineOpenCover
          π M U hU hUaff).hom ≫
        (CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology X) 1).map f.sheafHom := by
  let a := (baseModuleForget S).map
    (HomologicalComplex.homologyMap
      ((baseCechComplexFunctor π U).map f) 1)
  let b := (baseCechComplexHomologyForgetIso π N U 1).hom
  let c := (baseCechComplexHomologyForgetIso π M U 1).hom
  let d := HomologicalComplex.homologyMap
    ((cechComplexFunctor U).map f.sheafHom.hom) 1
  let e := (cechHomologyOneIsoOfAffineOpenCover N U hU hUaff).hom
  let g := (cechHomologyOneIsoOfAffineOpenCover M U hU hUaff).hom
  let k := (CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) 1).map f.sheafHom
  have hab : a ≫ b = c ≫ d := by
    exact baseCechComplexHomologyForgetIso_naturality π f U 1
  have hde : d ≫ e = g ≫ k := by
    exact cechHomologyOneIsoOfAffineOpenCover_naturality f U hU hUaff
  rw [baseCechHomologyOneIsoOfAffineOpenCover_hom,
    baseCechHomologyOneIsoOfAffineOpenCover_hom]
  change a ≫ (b ≫ e) = c ≫ (g ≫ k)
  exact (Category.assoc a b e).symm.trans
    ((congrArg (fun q => q ≫ e) hab).trans
      ((Category.assoc c d e).trans
        (congrArg (fun q => c ≫ q) hde)))

end

end AlgebraicGeometry.Scheme.Modules
