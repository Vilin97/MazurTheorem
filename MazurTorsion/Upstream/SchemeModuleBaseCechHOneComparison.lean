/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechHomology

/-!
# Base-linear Cech degree one and genuine sheaf cohomology

This is the project-facing boundary for the affine-cover Cech comparison. It
identifies the additive group obtained by forgetting the base-module structure
on degree-one base-Cech homology with genuine Ext-based sheaf `H¹`.

The comparison does not assert compatibility with the scalar action of global
functions, finite generation, properness, base change, or semicontinuity.
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
