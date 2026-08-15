/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistEquivalence

/-!
# Congruence for relative projective Serre twists

Equal morphisms into projective space define equal relative
scalar-twist functors.  This file packages the resulting transport as a
natural isomorphism so downstream geometric comparisons do not expose
raw equality casts.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)
  {T : Scheme.{0}} {f g : T ⟶ scheme k d}

/-- Relative projective Serre-twist functors depend only on the
morphism into projective space, up to equality. -/
noncomputable def relativeProjectiveSerreTwistFunctorCongr
    (h : f = g) (m : ℤ) :
    (relativeProjectiveSerreTwistEquivalence
        k d f m).functor ≅
      (relativeProjectiveSerreTwistEquivalence
        k d g m).functor :=
  eqToIso
    (congrArg
      (fun q =>
        (relativeProjectiveSerreTwistEquivalence
          k d q m).functor)
      h)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
