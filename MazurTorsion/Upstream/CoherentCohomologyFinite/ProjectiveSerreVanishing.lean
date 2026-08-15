/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreVanishingResolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseCoordinateNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenOverlapTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistPositiveEquivalence

/-!
# Positive-degree Serre vanishing on projective space

The integer overlap cocycle supplies an exact family of projective
scalar-twist autoequivalences.  Its chart transition law, coordinate
naturality, degree-shift property, and preservation of quasicoherence
discharge every hypothesis of the abstract resolution theorem.
-/


open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open SerreTwist

local instance projectiveSpaceOverBaseForPositiveSerreVanishing
    (R : Type) [CommRing R] (d : ℕ) :
    (scheme R d).Over (Spec (CommRingCat.of R)) :=
  ⟨toSpec R d⟩

/-- Unconditional positive-degree Serre vanishing for the projective
integer scalar-twist family over a Noetherian base ring flat over
`ℤ`. -/
theorem eventually_positiveScalarTwist_moduleSheafExt_subsingleton
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    [IsNoetherianRing R]
    (d : ℕ)
    (M : (scheme R d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ q : ℕ, 0 < q →
        Subsingleton
          (Abelian.Ext
            (constantRankOneSheaf
              (R := R) (scheme R d))
            (moduleSheaf (k := R)
              ((positiveScalarTwistFunctor
                R d n).obj M))
            q) :=
  eventually_moduleSheafExt_subsingleton_of_twistFamily
    (R := R) (d := d)
    (fun N =>
      integerOverChartCoordinateTransition R d N)
    (fun m =>
      baseStandardCoverCoordinatesNatural R d m)
    (positiveScalarTwistFunctor R d)
    (fun E hE =>
      eventually_isBaseFiniteNonnegativeTwistSum_positiveScalarTwist
        R d E hE)
    (fun n E hE =>
      positiveScalarTwistFunctor_isQuasicoherent
        R d n E hE)
    M

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
