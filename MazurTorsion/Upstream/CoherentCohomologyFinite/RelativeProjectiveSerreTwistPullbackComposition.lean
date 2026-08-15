/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverPullbackCompositionUnits
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistCoverIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistIteratedPullback

/-!
# Relative projective Serre twists and composite pullback

Canonical open-cover base change first produces the scalar twist on the
literal iterated pullback of the standard projective cover.  The
pullback-pasting isomorphism identifies that cover, together with its
unit cocycle, with the cover pulled back along the composite morphism.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Cover
open AlgebraicGeometry.Scheme.Modules

variable (k : Type) [CommRing k] (d : ℕ)
  {X Y : Scheme.{0}} (p : Y ⟶ scheme k d) (j : X ⟶ Y)

/-- The scalar twist on the literal iterated pullback cover agrees with
the relative twist attached to the composite morphism. -/
noncomputable def
    iteratedRelativeProjectiveSerreTwistCoverIsoNatIso
    (m : ℤ) :
    (iteratedRelativeProjectiveSerreTwistEquivalence
        k d p j m).functor ≅
      (relativeProjectiveSerreTwistEquivalence
        k d (j ≫ p) m).functor :=
  (openCoverScalarTwistCoverIsoNatIso
    (pullbackPullbackIso (cover k d) p j)
    (baseChangeCoverUnit
      ((cover k d).pullback₁ p) j
      (baseChangedIntegerCoverUnit k d p m))
    (baseChangedIntegerCoverUnit k d (j ≫ p) m)
    (baseChangeCoverUnit_self
      ((cover k d).pullback₁ p) j
      (baseChangedIntegerCoverUnit k d p m)
      (baseChangedIntegerCoverUnit_self k d p m))
    (baseChangeCoverUnit_cocycle
      ((cover k d).pullback₁ p) j
      (baseChangedIntegerCoverUnit k d p m)
      (baseChangedIntegerCoverUnit_cocycle k d p m))
    (baseChangedIntegerCoverUnit_self k d (j ≫ p) m)
    (baseChangedIntegerCoverUnit_cocycle k d (j ≫ p) m)
    (pullbackCoverUnitAlongIso_pullbackPullbackIso
      (cover k d) p j (integerCoverUnit k d m))).symm

/-- Relative projective Serre twisting commutes naturally with
pullback, with the target relative twist formed along the composite
morphism. -/
noncomputable def relativeProjectiveSerreTwistPullbackCompositionNatIso
    (m : ℤ) :
    (relativeProjectiveSerreTwistEquivalence
        k d p m).functor ⋙
        pullback j ≅
      pullback j ⋙
        (relativeProjectiveSerreTwistEquivalence
          k d (j ≫ p) m).functor :=
  relativeProjectiveSerreTwistIteratedPullbackNatIso
      k d p j m ≪≫
    Functor.isoWhiskerLeft
      (pullback j)
      (iteratedRelativeProjectiveSerreTwistCoverIsoNatIso
        k d p j m)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
