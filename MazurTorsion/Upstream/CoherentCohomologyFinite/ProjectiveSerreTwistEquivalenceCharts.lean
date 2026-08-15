/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModuleSerreTwistEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerDescentShift
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLocalTrivialization
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedCharts

/-!
# Chart restrictions of the projective scalar-twist equivalence

Scalar twisting changes only overlap transitions.  Consequently the
projective autoequivalence obtained by descent is locally the identity on
every member of the standard affine cover.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

/-- Restricting the inverse projective-to-glued equivalence to a standard
chart is the same as restricting its glued input to the corresponding
glued chart. -/
noncomputable def inverseGluedStandardChartIso
    (Z : (glueData k d).glued.Modules)
    (i : Fin (d + 1)) :
    (pullback ((cover k d).f i)).obj
        ((projectiveToGluedModules k d).inverse.obj Z) ≅
      (pullback ((glueData k d).ι i)).obj Z :=
  (pullback ((cover k d).f i)).mapIso
      ((gluedToProjectiveModulesFunctorIso k d).app Z) ≪≫
    (pullbackComp
      ((cover k d).f i)
      (inv (cover k d).fromGlued)).app Z ≪≫
    (pullbackCongr
      (chart_comp_fromGlued_inv k d i)).app Z

/-- Restriction of the named integer glued scalar twist is its named
descent scalar twist. -/
noncomputable def gluedIntegerScalarTwistRestrictionIso
    (W : (glueData k d).glued.Modules) (n : ℤ) :
    (restrictionFunctor (D := glueData k d)).obj
        ((gluedIntegerScalarTwistEquivalence
          k d n).functor.obj W) ≅
      (integerScalarTwistDescentFunctor k d n).obj
        ((restrictionFunctor (D := glueData k d)).obj W) :=
  descentGlueRestrictionIso
    (D := glueData k d)
    ((integerScalarTwistDescentFunctor k d n).obj
      ((restrictionFunctor
        (D := glueData k d)).obj W))

/-- The component of the restriction comparison on one standard glued
chart. -/
noncomputable def gluedIntegerScalarTwistDescentChartIso
    (W : (glueData k d).glued.Modules)
    (n : ℤ) (i : Fin (d + 1)) :
    ((restrictionFunctor (D := glueData k d)).obj
        ((gluedIntegerScalarTwistEquivalence
          k d n).functor.obj W)).chart i ≅
      ((integerScalarTwistDescentFunctor k d n).obj
        ((restrictionFunctor (D := glueData k d)).obj W)).chart i :=
  isoApp
    (gluedIntegerScalarTwistRestrictionIso k d W n)
    i

/-- Scalar twisting leaves the chart object of an integer-twisted descent
datum unchanged. -/
lemma integerScalarTwistDescentChart_eq
    (W : (glueData k d).glued.Modules)
    (n : ℤ) (i : Fin (d + 1)) :
    ((integerScalarTwistDescentFunctor k d n).obj
        ((restrictionFunctor
          (D := glueData k d)).obj W)).chart i =
      ((restrictionFunctor
        (D := glueData k d)).obj W).chart i :=
  rfl

/-- On a glued standard chart, integer scalar twisting leaves the
underlying chart module unchanged. -/
noncomputable def gluedIntegerScalarTwistChartIso
    (W : (glueData k d).glued.Modules)
    (n : ℤ) (i : Fin (d + 1)) :
    (pullback ((glueData k d).ι i)).obj
        ((gluedIntegerScalarTwistEquivalence
          k d n).functor.obj W) ≅
      (pullback ((glueData k d).ι i)).obj W :=
  gluedIntegerScalarTwistDescentChartIso
      k d W n i ≪≫
    eqToIso (integerScalarTwistDescentChart_eq
      k d W n i)

/-- Restricting the projective-to-glued equivalence to a glued chart
recovers restriction to the corresponding standard projective chart. -/
noncomputable def projectiveToGluedStandardChartIso
    (E : (scheme k d).Modules)
    (i : Fin (d + 1)) :
    (pullback ((glueData k d).ι i)).obj
        ((projectiveToGluedModules k d).functor.obj E) ≅
      (pullback ((cover k d).f i)).obj E :=
  (pullback ((glueData k d).ι i)).mapIso
      ((projectiveToGluedModulesFunctorIso k d).app E) ≪≫
    (pullbackComp
      ((glueData k d).ι i)
      (cover k d).fromGlued).app E ≪≫
    (pullbackCongr
      ((cover k d).ι_fromGlued i)).app E

/-- Every standard-chart restriction of the projective integer
scalar-twist functor is isomorphic to the original chart restriction. -/
noncomputable def projectiveIntegerScalarTwistChartIso
    (E : (scheme k d).Modules)
    (n : ℤ) (i : Fin (d + 1)) :
    (pullback ((cover k d).f i)).obj
        ((projectiveIntegerScalarTwistEquivalence
          k d n).functor.obj E) ≅
      (pullback ((cover k d).f i)).obj E :=
  inverseGluedStandardChartIso k d
      ((gluedIntegerScalarTwistEquivalence
        k d n).functor.obj
          ((projectiveToGluedModules k d).functor.obj E))
      i ≪≫
    gluedIntegerScalarTwistChartIso k d
      ((projectiveToGluedModules k d).functor.obj E)
      n i ≪≫
    projectiveToGluedStandardChartIso k d E i

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
