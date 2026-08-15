/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarTransport

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

variable (k : Type) [CommRing k] (d : ℕ)

theorem projectiveIntegerSecondOverlapToGlued_eq_raw
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerSecondOverlapToGlued k d m i j =
      (Scheme.Modules.pullbackComp
        (((glueData k d).t i j ≫
            (glueData k d).f j i) ≫
          (cover k d).f j)
        (inv (cover k d).fromGlued)).hom.app
        (effectiveGluedIntegerModule k d m) ≫
      (Scheme.Modules.pullbackCongr
        (show
          ((((glueData k d).t i j ≫
                (glueData k d).f j i) ≫
                (cover k d).f j) ≫
              inv (cover k d).fromGlued) =
            ((glueData k d).t i j ≫
              (glueData k d).f j i) ≫
              (glueData k d).ι j by
          exact
            (Category.assoc _ _ _).trans
              (congrArg
                (fun q =>
                  ((glueData k d).t i j ≫
                    (glueData k d).f j i) ≫ q)
                (chart_comp_fromGlued_inv k d j)))).hom.app
        (effectiveGluedIntegerModule k d m) := by
  rfl

theorem gluedIntegerSecondChartLegCore_eq_raw
    (m : ℤ) (i j : Fin (d + 1)) :
    gluedIntegerSecondChartLegCore k d m i j =
      (Scheme.Modules.pullbackComp
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        ((glueData k d).ι j)).inv.app
          (glueObject
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)) ≫
        (Scheme.Modules.pullback
          ((glueData k d).t i j ≫
            (glueData k d).f j i)).map
            (restrictionIso
              (glueData k d)
              (integerChartModules k d)
              (integerTransitionFamily k d m)
              (integerIdentityFamily k d m)
              (integerCocycleFamily k d m)
              j).hom := by
  rfl

/-- Reassociate the literal second-chart restriction through the transition,
then replace it by the named second-chart core.  Keeping this normalization
separate avoids unfolding the effective-descent object in the final pointwise
overlap chain. -/
theorem gluedIntegerSecondChartLegCoreTransition_eq_raw
    (m : ℤ) (i j : Fin (d + 1)) :
    (Scheme.Modules.pullbackComp
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        ((glueData k d).ι j)).inv.app
          (glueObject
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)) ≫
      (Scheme.Modules.pullback
        ((glueData k d).t i j ≫
          (glueData k d).f j i)).map
          (restrictionIso
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)
            j).hom ≫
        (integerTransitionFamily k d m i j).inv =
      gluedIntegerSecondChartLegCore k d m i j ≫
        (integerTransitionFamily k d m i j).inv := by
  rw [← Category.assoc]
  exact congrArg
    (fun q => q ≫ (integerTransitionFamily k d m i j).inv)
    (gluedIntegerSecondChartLegCore_eq_raw k d m i j).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
