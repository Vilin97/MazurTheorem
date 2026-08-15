/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistCanonicalBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistEquivalence

/-!
# Iterated pullback of relative projective Serre twists

Pulling the relative integer cocycle first to a scheme `Y` and then
along `j : X ⟶ Y` gives a literal iterated-cover twist on `X`.
Canonical open-cover base change identifies restriction of the twist on
`Y` with this iterated twist.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Cover
open AlgebraicGeometry.Scheme.Modules

variable (k : Type) [CommRing k] (d : ℕ)
  {X Y : Scheme.{0}} (p : Y ⟶ scheme k d) (j : X ⟶ Y)

/-- The relative scalar twist on `X` obtained by pulling the standard
projective cover and cocycle first along `p` and then along `j`. -/
noncomputable def iteratedRelativeProjectiveSerreTwistEquivalence
    (m : ℤ) :
    X.Modules ≌ X.Modules :=
  openCoverScalarTwistEquivalence
    (((cover k d).pullback₁ p).pullback₁ j)
    (baseChangeCoverUnit
      ((cover k d).pullback₁ p) j
      (baseChangedIntegerCoverUnit k d p m))
    (baseChangeCoverUnit_self
      ((cover k d).pullback₁ p) j
      (baseChangedIntegerCoverUnit k d p m)
      (baseChangedIntegerCoverUnit_self k d p m))
    (baseChangeCoverUnit_cocycle
      ((cover k d).pullback₁ p) j
      (baseChangedIntegerCoverUnit k d p m)
      (baseChangedIntegerCoverUnit_cocycle k d p m))

/-- Restriction of a relative projective scalar twist is canonically
the twist constructed on the literal iterated pulled-back cover. -/
noncomputable def relativeProjectiveSerreTwistIteratedPullbackNatIso
    (m : ℤ) :
    (relativeProjectiveSerreTwistEquivalence
        k d p m).functor ⋙
        pullback j ≅
      pullback j ⋙
        (iteratedRelativeProjectiveSerreTwistEquivalence
          k d p j m).functor :=
  openCoverScalarTwistCanonicalBaseChangeNatIso
    ((cover k d).pullback₁ p) j
    (baseChangedIntegerCoverUnit k d p m)
    (baseChangedIntegerCoverUnit_self k d p m)
    (baseChangedIntegerCoverUnit_cocycle k d p m)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
