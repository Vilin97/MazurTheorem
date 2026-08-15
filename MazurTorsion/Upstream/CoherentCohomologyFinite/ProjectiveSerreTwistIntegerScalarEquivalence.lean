/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoverUnits
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedEquivalence

/-!
# Integer scalar-twist equivalences on projective cover descent

This file gives short names to the descent functor, descent equivalence,
and glued equivalence defined by an integer power of the standard
projective overlap cocycle.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

/-- Scalar twisting by the integer degree-`n` projective cocycle as an
endofunctor of cover descent data. -/
noncomputable def integerScalarTwistDescentFunctor
    (n : ℤ) :
    CoverDescentData (glueData k d) ⥤
      CoverDescentData (glueData k d) :=
  scalarTwistFunctor
    (integerCoverUnit k d n)
    (integerCoverUnit_self k d n)
    (integerCoverUnit_cocycle k d n)

/-- Scalar twisting by the integer degree-`n` cocycle is an equivalence
of the cover-descent category. -/
noncomputable def integerScalarTwistDescentEquivalence
    (n : ℤ) :
    CoverDescentData (glueData k d) ≌
      CoverDescentData (glueData k d) :=
  scalarTwistEquivalence
    (integerCoverUnit k d n)
    (integerCoverUnit_self k d n)
    (integerCoverUnit_cocycle k d n)

/-- The named descent equivalence has the named integer scalar-twist
functor as its forward functor. -/
@[simp]
theorem integerScalarTwistDescentEquivalence_functor
    (n : ℤ) :
    (integerScalarTwistDescentEquivalence
      k d n).functor =
        integerScalarTwistDescentFunctor k d n :=
  rfl

/-- Scalar twisting on the glued standard cover by the integer Serre
cocycle. -/
noncomputable def gluedIntegerScalarTwistEquivalence
    (n : ℤ) :
    (glueData k d).glued.Modules ≌
      (glueData k d).glued.Modules :=
  (restrictionEquivalence
      (D := glueData k d)).trans
    ((integerScalarTwistDescentEquivalence
      k d n).trans
        (restrictionEquivalence
          (D := glueData k d)).symm)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
