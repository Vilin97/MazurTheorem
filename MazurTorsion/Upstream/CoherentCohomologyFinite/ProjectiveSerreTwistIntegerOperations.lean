/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInteger

/-!
# Finite sums of integer Serre twists
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/-- A finite direct sum of integer Serre twists. -/
def finiteIntegerSum {ι : Type} [Fintype ι] (degree : ι → ℤ) :
    (scheme k d).Modules :=
  ∐ fun i => OInt k d (degree i)

/-- A finite direct sum of negative Serre twists. -/
def finiteNegativeSum {ι : Type} [Fintype ι] (degree : ι → ℕ) :
    (scheme k d).Modules :=
  ∐ fun i => ONeg k d (degree i)

/-- A finite direct sum containing `multiplicity n` copies of each listed
negative twist. -/
def finiteNegativeMultiplicitySum {ι : Type} [Fintype ι]
    (degree multiplicity : ι → ℕ) :
    (scheme k d).Modules :=
  ∐ fun p : Σ i, Fin (multiplicity i) =>
    ONeg k d (degree p.1)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
