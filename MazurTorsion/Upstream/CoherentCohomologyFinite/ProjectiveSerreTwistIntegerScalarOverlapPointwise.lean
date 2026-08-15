/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarTrivialization
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerOverlapSections

/-!
# Pointwise assembly of the projective integer scalar overlap

The morphisms in the effective-descent comparison have large dependent
types.  Evaluating each already-proved morphism equality on a fixed open
and section before composing the equalities keeps kernel conversion within
the default heartbeat budget.

The raw proof declarations below intentionally have inferred proposition
types.  This preserves the literal endpoints of adjacent comparison
theorems, so their equality proofs compose without unfolding the effective
descent object.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

local macro "integerRawOverlapCast%(" k:term "," d:term "," m:term ","
    i:term "," j:term ")" : term =>
  `((Scheme.Modules.pullbackCongr
      (integerCompatibilityGluedOverlapEquation $k $d $i $j)).inv.app
      (glueObject
        (glueData $k $d)
        (integerChartModules $k $d)
        (integerTransitionFamily $k $d $m)
        (integerIdentityFamily $k $d $m)
        (integerCocycleFamily $k $d $m)))

/-- Pointwise form of the first scalar-leg factorization. -/
def projectiveIntegerFirstScalarFactorAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerFirstScalarLeg_factor_raw k d m i j)

/-- Pointwise form of raw effective-descent scalar compatibility. -/
def projectiveIntegerDescentScalarCompatibilityAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerRawDescentScalarCompatibility k d m i j)

/-- Pointwise replacement of the literal second-chart restriction and its
transition by the named second-chart core. -/
def projectiveIntegerSecondChartCoreNormalizeAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg
    (fun q =>
      (projectiveIntegerOverlapToGlued k d m i j ≫
        ((integerRawOverlapCast%(k, d, m, i, j) ≫ q) ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom)).app W x)
    (gluedIntegerSecondChartLegCoreTransition_eq_raw k d m i j)

/-- Pointwise normalization to the right endpoint of the transport square. -/
def projectiveIntegerSecondScalarTransportRightAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerRawSecondScalar_to_transportRight k d m i j)

/-- Pointwise replacement of the named transport endpoint by its exact raw
presentation. -/
def projectiveIntegerSecondScalarTransportEndpointAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerRawSecondScalar_to_transportEndpoint k d m i j)

/-- Pointwise reassociation of the exact raw transport endpoint. -/
def projectiveIntegerSecondScalarTransportEndpointReassocAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerRawSecondScalar_transportEndpoint_reassoc
      k d m i j)

/-- Pointwise form of the whiskered projective/glued transport square. -/
def projectiveIntegerSecondScalarTransportAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerRawSecondScalar_transport k d m i j)

/-- Pointwise replacement of the literal second comparison by its name. -/
def projectiveIntegerSecondComparisonNormalizeAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerRawSecondComparison_normalize k d m i j)

/-- Pointwise replacement of the raw suffix by the named second-chart core. -/
def projectiveIntegerSecondComparisonSuffixAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerNamedSecondComparison_suffix k d m i j)

/-- Pointwise reassociation of the named second scalar route. -/
def projectiveIntegerSecondComparisonReassocAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerNamedSecondComparison_reassoc k d m i j)

/-- Pointwise factorization through the direct second projective chart core. -/
def projectiveIntegerSecondChartCoreFactorAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerNamedSecondChartCore_factor k d m i j)

/-- Pointwise trivialization of the inverse integer transition on the
fully raw second-chart route. -/
def projectiveIntegerRawSecondScalarTrivializeAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  congrArg (fun q => q.app W x)
    (projectiveIntegerRawSecondScalar_trivialize k d m i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
