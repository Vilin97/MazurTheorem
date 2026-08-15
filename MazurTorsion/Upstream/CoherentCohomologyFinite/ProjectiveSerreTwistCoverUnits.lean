/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistedCoverDescent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCategory

/-!
# Serre-twist units as a cover cocycle

The integer powers of the standard projective overlap ratios form a
unit-valued cocycle for the standard affine cover.  Consequently they may
be used to scalar-twist the canonical cover descent datum of any global
module sheaf.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules

variable (k : Type) [CommRing k] (d : ℕ)

/-- The unit on the `ij` overlap defining the integer Serre twist `m`. -/
def integerCoverUnit (m : ℤ) (i j : Fin (d + 1)) :
    Γ((glueData k d).V (i, j), ⊤)ˣ :=
  (overlapUnit k d i j) ^ m

/-- Integer Serre-twist cover units are one on diagonal overlaps. -/
lemma integerCoverUnit_self (m : ℤ) (i : Fin (d + 1)) :
    integerCoverUnit k d m i i = 1 := by
  simp [integerCoverUnit, overlapUnit_self]
  rfl

/-- Integer Serre-twist cover units satisfy the pulled-back triple-overlap
cocycle used by scalar-twisted module descent. -/
lemma integerCoverUnit_cocycle (m : ℤ) :
    CoverUnitCocycleCondition (glueData k d)
      (integerCoverUnit k d m) := by
  intro i j l
  apply Units.ext
  exact overlapUnit_cocycle_transport_zpow k d m i j l

/-- Scalar-twist the canonical cover descent datum of a global module by
the projective Serre unit cocycle of exponent `m`. -/
def integerScalarTwistedCoverDescentData
    (W : (glueData k d).glued.Modules) (m : ℤ) :
    CoverDescentData (glueData k d) where
  chart := coverRestriction (glueData k d) W
  transition :=
    scalarTwistedCoverTransition
      (glueData k d) W (integerCoverUnit k d m)
  identity :=
    scalarTwistedCoverTransition_self
      (glueData k d) W (integerCoverUnit k d m)
      (integerCoverUnit_self k d m)
  cocycle :=
    scalarTwistedCoverTransition_cocycle
      (glueData k d) W (integerCoverUnit k d m)
      (integerCoverUnit_cocycle k d m)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
