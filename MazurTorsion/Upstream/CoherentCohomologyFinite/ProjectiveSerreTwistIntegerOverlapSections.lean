/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerProjectiveOverlap

/-!
# Pointwise integer-twist overlap steps

These declarations evaluate the four morphism equalities in the
projective/effective-descent comparison at an arbitrary open and section.
Their inferred proposition types deliberately preserve the parenthesization
of the underlying pseudofunctor comparison maps.  This keeps each reusable
step within the default heartbeat budget.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- Sections of the integer twist pulled back to a projective chart
overlap. -/
abbrev IntegerOverlapSection (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens) :=
  Γ((Scheme.Modules.pullback
    ((glueData k d).f i j ≫ (cover k d).f i)).obj
      (OInt k d m), W)

/-- Pointwise form of the first projective-chart factorization. -/
def projectiveFirstChartLegAppFactorRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerFirstChartLeg_factor k d m i j)

/-- Pointwise effective-descent overlap compatibility after inserting the
projective-to-glued comparison section. -/
def gluedIntegerChartLegOverlapAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg
    (fun q => q.app W
      ((projectiveIntegerOverlapToGlued k d m i j).app W x))
    (gluedIntegerChartLegOverlapCompatibilityRaw k d m i j)

/-- Pointwise form of the projective/glued overlap-transport square. -/
def projectiveOverlapTransportAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerOverlapTransportSquareRaw k d m i j).symm

/-- Pointwise form of the second projective-chart factorization, evaluated
after the overlap cast. -/
def projectiveSecondChartCoreAppFactorRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg
    (fun q => q.app W
      ((projectiveIntegerOverlapCast k d m i j).app W x))
    (projectiveIntegerSecondChartCore_factor k d m i j).symm

/-- Pointwise descent overlap compatibility already composed with the
unit-module trivialization.  The proposition is written explicitly so
the proof remains opaque to downstream section calculations. -/
theorem gluedIntegerScalarLegOverlapAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :
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
      (pullbackUnitIso ((glueData k d).f i j)).hom).app W
        ((projectiveIntegerOverlapToGlued k d m i j).app W x) =
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
        (pullbackUnitIso ((glueData k d).f i j)).hom).app W
          ((projectiveIntegerOverlapToGlued k d m i j).app W x) :=
  congrArg
    (fun q => q.app W
      ((projectiveIntegerOverlapToGlued k d m i j).app W x))
    (gluedIntegerScalarLegOverlapCompatibilityRaw k d m i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
