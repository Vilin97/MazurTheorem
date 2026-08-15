/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerProjectiveOverlap

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- The first projective scalar route, factored to the literal first raw
descent route. -/
theorem projectiveIntegerFirstScalarLeg_factor_raw
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerFirstScalarLeg k d m i j =
      projectiveIntegerOverlapToGlued k d m i j ≫
        (((Scheme.Modules.pullbackComp
              ((glueData k d).f i j) ((glueData k d).ι i)).inv.app
              (glueObject
                (glueData k d)
                (integerChartModules k d)
                (integerTransitionFamily k d m)
                (integerIdentityFamily k d m)
                (integerCocycleFamily k d m)) ≫
            (Scheme.Modules.pullback ((glueData k d).f i j)).map
              (restrictionIso
                (glueData k d)
                (integerChartModules k d)
                (integerTransitionFamily k d m)
                (integerIdentityFamily k d m)
                (integerCocycleFamily k d m)
                i).hom) ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom) := by
  unfold projectiveIntegerFirstScalarLeg
  rw [projectiveIntegerFirstChartLeg_factor]
  simp only [Category.assoc]
  rfl

/-- Raw descent compatibility after prefixing both routes by the
projective-to-glued comparison. -/
theorem projectiveIntegerRawDescentScalarCompatibility
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerOverlapToGlued k d m i j ≫
        (((Scheme.Modules.pullbackComp
              ((glueData k d).f i j) ((glueData k d).ι i)).inv.app
              (glueObject
                (glueData k d)
                (integerChartModules k d)
                (integerTransitionFamily k d m)
                (integerIdentityFamily k d m)
                (integerCocycleFamily k d m)) ≫
            (Scheme.Modules.pullback ((glueData k d).f i j)).map
              (restrictionIso
                (glueData k d)
                (integerChartModules k d)
                (integerTransitionFamily k d m)
                (integerIdentityFamily k d m)
                (integerCocycleFamily k d m)
                i).hom) ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom) =
      projectiveIntegerOverlapToGlued k d m i j ≫
        (((Scheme.Modules.pullbackCongr
              (integerCompatibilityGluedOverlapEquation k d i j)).inv.app
                (glueObject
                  (glueData k d)
                  (integerChartModules k d)
                  (integerTransitionFamily k d m)
                  (integerIdentityFamily k d m)
                  (integerCocycleFamily k d m)) ≫
              (Scheme.Modules.pullbackComp
                ((glueData k d).t i j ≫
                  (glueData k d).f j i)
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
                  (integerTransitionFamily k d m i j).inv) ≫
            (pullbackUnitIso ((glueData k d).f i j)).hom) := by
  exact congrArg
    (fun q => projectiveIntegerOverlapToGlued k d m i j ≫ q)
    (gluedIntegerScalarLegOverlapCompatibilityRaw k d m i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
