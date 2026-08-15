/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInteger
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCategory

/-!
# The integer Serre twist as cover descent data

This file packages the chart modules and transition maps already used to
construct `gluedIntegerModule` as an object of the cover-descent category.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

/-- The standard cover descent datum whose gluing is the integer Serre
twist of degree `m`. -/
noncomputable def integerCoverDescentData (m : ℤ) :
    CoverDescentData (glueData k d) where
  chart := integerChartModules k d
  transition := integerTransitionFamily k d m
  identity := integerIdentityFamily k d m
  cocycle := integerCocycleFamily k d m

/-- Gluing the named integer cover descent datum recovers the original
glued integer module. -/
noncomputable def glueIntegerCoverDescentIso (m : ℤ) :
    (glueFunctor (D := glueData k d)).obj
        (integerCoverDescentData k d m) ≅
      gluedIntegerModule k d m :=
  Iso.refl _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
