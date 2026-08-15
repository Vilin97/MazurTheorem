/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechInjectiveComparison
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineHThree

/-!
# Degree-one Cech comparison for affine covers

This is the degree-one slice of AINTLIB's affine-cover comparison. The source
`AffineVanishing` dependency is replaced by the project's existing
option-free positive-degree affine quasicoherent acyclicity theorem.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

private theorem restrict_subsingleton_H_of_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj M.sheaf)
      (n + 1)) := by
  change Subsingleton
    (MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.H
      (M.restrict U.ι) (n + 1))
  letI : IsAffine U := hU
  exact MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.moduleAffineHSucc_subsingleton
    (M.restrict U.ι) n

/-- The native Cech complex of a quasicoherent module on an affine open cover
computes its genuine degree-one sheaf cohomology. -/
noncomputable def cechHomologyOneIso_of_affine_openCover
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    ((cechComplexFunctor U).obj M.sheaf.obj).homology 1 ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj M.sheaf := by
  apply cechHomologyOneIso_of_subsingleton_H U M.sheaf
  · simpa only [IsOpenCover] using hU
  · intro i
    simpa using restrict_subsingleton_H_of_isAffineOpen M (U i) (hUaff i) 0

/-- The affine-cover degree-one Cech comparison is natural in a morphism of
quasicoherent coefficient modules. -/
@[reassoc]
theorem cechHomologyOneIso_of_affine_openCover_naturality
    {X : Scheme.{u}} {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (f : M ⟶ N) {ι : Type u}
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map f.sheafHom.hom) 1 ≫
      (cechHomologyOneIso_of_affine_openCover N U hU hUaff).hom =
    (cechHomologyOneIso_of_affine_openCover M U hU hUaff).hom ≫
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).map f.sheafHom := by
  apply cechHomologyOneIso_of_subsingleton_H_naturality U f.sheafHom

end AlgebraicGeometry.Scheme.Modules
