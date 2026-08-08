/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
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

/-- On an affine open cover, the underlying additive group of base-linear
Cech homology in degree one is genuine sheaf `H¹`. -/
noncomputable def baseCechHomologyOneIso_of_affine_openCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    (baseModuleForget S).obj ((baseCechComplex π M U).homology 1) ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj M.sheaf :=
  baseCechComplexHomologyForgetIso π M U 1 ≪≫
    cechHomologyOneIso_of_affine_openCover M U hU hUaff

end

end AlgebraicGeometry.Scheme.Modules
