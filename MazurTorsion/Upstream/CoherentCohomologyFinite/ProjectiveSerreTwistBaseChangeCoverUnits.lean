/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeUnitCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoverUnits

/-!
# Serre-twist cover units after base change

The integer Serre overlap cocycle on the standard projective cover pulls
back along any morphism into projective space.  This is the unit cocycle
used by relative or fiberwise scalar-twist descent constructions.
-/


open AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Cover
open AlgebraicGeometry.Scheme.Modules

variable (k : Type) [CommRing k] (d : ℕ)
  {T : Scheme.{0}} (f : T ⟶ scheme k d)

/-- The integer Serre unit cocycle pulled to the standard cover after base
change along `f`. -/
def baseChangedIntegerCoverUnit (m : ℤ) :
    ∀ i j,
      Γ((Scheme.Cover.gluedCover
        ((cover k d).pullback₁ f)).V (i, j), ⊤)ˣ :=
  baseChangeCoverUnit (cover k d) f
    (integerCoverUnit k d m)

/-- The base-changed integer Serre units are one on diagonal overlaps. -/
theorem baseChangedIntegerCoverUnit_self (m : ℤ) :
    ∀ i, baseChangedIntegerCoverUnit k d f m i i = 1 :=
  baseChangeCoverUnit_self
    (cover k d) f (integerCoverUnit k d m)
    (integerCoverUnit_self k d m)

/-- The base-changed integer Serre units satisfy the triple-overlap
cocycle. -/
theorem baseChangedIntegerCoverUnit_cocycle (m : ℤ) :
    CoverUnitCocycleCondition
      (Scheme.Cover.gluedCover
        ((cover k d).pullback₁ f))
      (baseChangedIntegerCoverUnit k d f m) :=
  baseChangeCoverUnit_cocycle
    (cover k d) f (integerCoverUnit k d m)
    (integerCoverUnit_cocycle k d m)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
