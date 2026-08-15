/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeScalarSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCoordinateCoverCompatibility
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseChangeCoverUnits

/-!
# Projective coordinate functions after base change

The functions `(Xᵣ / Xⱼ)^N` pull back to the charts of the standard
projective cover after an arbitrary base change.
-/


open AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Cover
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)
  {T : Scheme.{0}} (g : T ⟶ scheme k d)

/-- Pullback of the coordinate chart functions to the base-changed
standard projective cover. -/
def baseChangedCoordinateChartFunction
    (N : ℕ) (r : Fin (d + 1)) :
    ∀ j,
      Γ((Scheme.Cover.gluedCover
        ((cover k d).pullback₁ g)).U j, ⊤) :=
  baseChangeCoverSection
    (cover k d) g
    (coordinateChartFunction k d N r)

/-- On the pulled-back chart selected by `r`, the coordinate function
is still one. -/
@[simp]
theorem baseChangedCoordinateChartFunction_self
    (N : ℕ) (r : Fin (d + 1)) :
    baseChangedCoordinateChartFunction
      k d g N r r = 1 := by
  change
    ((cover k d).pullbackHom g r).appTop
        (coordinateChartFunction k d N r r) =
      1
  rw [coordinateChartFunction_self]
  exact map_one _

/--
The pulled-back coordinate functions transform by the pulled-back
degree-`N` Serre unit cocycle.
-/
theorem baseChangedCoordinateChartFunction_coverCompatible
    (N : ℕ) (r : Fin (d + 1)) :
    CoverScalarSectionCompatibility
      (D := Scheme.Cover.gluedCover
        ((cover k d).pullback₁ g))
      (baseChangedIntegerCoverUnit
        k d g (N : ℤ))
      (baseChangedCoordinateChartFunction
        k d g N r) := by
  exact
    baseChangeCoverSection_compatible
      (cover k d) g
      (integerCoverUnit k d (N : ℤ))
      (coordinateChartFunction k d N r)
      (coordinateChartFunction_coverCompatible
        k d N r)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
