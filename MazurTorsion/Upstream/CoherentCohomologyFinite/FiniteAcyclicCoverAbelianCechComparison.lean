/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AbelianSheafFiniteSubsetCech
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Additive Čech comparison for finite acyclic covers

This file combines the free-sheaf resolution comparison for a finite
acyclic cover with the canonical integer-linear Čech complex of an
abelian sheaf.  The result is stated entirely in terms of the original
abelian section groups.
-/

open CategoryTheory TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverAbelianCechComparison

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.AbelianSheafFiniteSubsetCech
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverSectionCechComparison

variable {T : TopCat}
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- On a finite acyclic cover, sheaf cohomology is the homology of the
normalized finite-subset complex of the original abelian section
groups. -/
noncomputable def globalHAddEquivAbelianSectionCechHomology
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T)
    (hU : ⨆ i, U i = ⊤)
    (hacyclic :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison.IsAcyclicOnIntersections
        G U Finset.univ)
    (n : ℕ) :
    CategoryTheory.Sheaf.H G n ≃+
      (abelianSectionCechComplex G U).homology n := by
  let complexIso :=
    integerLiftSectionPiCechComplexIsoAbelian G U
  let eHomology :=
    isoOfQuasiIsoAt complexIso.hom n
  exact
    (globalHAddEquivSectionPiHomology
      G U hU hacyclic n).trans <|
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso
        eHomology).addCommGroupIsoToAddEquiv

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverAbelianCechComparison
