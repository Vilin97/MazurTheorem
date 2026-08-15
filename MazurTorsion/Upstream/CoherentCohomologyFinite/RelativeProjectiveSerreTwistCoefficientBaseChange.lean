/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoefficientCoverUnits
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistCoverIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistEquivalence

/-!
# Relative Serre twists under extension of coefficients

After extension of coefficients `k → R`, the relative Serre twist formed
from a morphism to projective space over `R` agrees with the relative
Serre twist formed from its composite with `ℙ^d_R ⟶ ℙ^d_k`.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable (d : ℕ) {Y : Scheme} (g : Y ⟶ scheme R d)

/--
Relative projective Serre twisting is invariant under extension of the
coefficient ring, naturally in the sheaf being twisted.
-/
noncomputable def
    relativeProjectiveSerreTwistCoefficientBaseChangeNatIso
    (m : ℤ) :
    (relativeProjectiveSerreTwistEquivalence
        k d (g ≫ coefficientMap (algebraMap k R) d) m).functor ≅
      (relativeProjectiveSerreTwistEquivalence
        R d g m).functor :=
  (openCoverScalarTwistCoverIsoNatIso
    (coefficientBaseChangeStandardCoverIso d g)
    (baseChangedIntegerCoverUnit k d
      (g ≫ coefficientMap (algebraMap k R) d) m)
    (baseChangedIntegerCoverUnit R d g m)
    (baseChangedIntegerCoverUnit_self k d
      (g ≫ coefficientMap (algebraMap k R) d) m)
    (baseChangedIntegerCoverUnit_cocycle k d
      (g ≫ coefficientMap (algebraMap k R) d) m)
    (baseChangedIntegerCoverUnit_self R d g m)
    (baseChangedIntegerCoverUnit_cocycle R d g m)
    (pullbackCoverUnitAlongIso_coefficientBaseChangeStandardCoverIso
      d g m)).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
