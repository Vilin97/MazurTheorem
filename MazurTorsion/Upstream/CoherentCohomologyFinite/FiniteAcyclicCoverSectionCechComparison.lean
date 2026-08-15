/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafExtLinearComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.FreeIntegerModuleSheafOpenCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafCechComparison

/-!
# A normalized section Čech comparison for finite acyclic covers

For an abelian sheaf on a universe-zero space, lift the coefficients
along the equivalence between abelian groups and integer modules.  The
normalized finite-subset free-sheaf resolution then identifies global
cohomology with the homology of the target-oriented section Čech complex,
provided all nonempty intersections are acyclic.

This supplies a concrete comparison at the exact benchmark pin without
using an unnormalised Čech-to-derived comparison theorem.
-/

open CategoryTheory TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverSectionCechComparison

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeIntegerModuleSheafOpenCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {T : TopCat}
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- An abelian sheaf regarded as a sheaf of integer modules. -/
noncomputable abbrev integerLiftSheaf
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat) :
    ModuleSheaf (R := ℤ) T :=
  (sheafLiftAbToZ
    (Opens.grothendieckTopology T)).obj G

/-- Acyclicity of the nonempty intersections makes every represented
free term Ext-acyclic against the integer lift. -/
theorem freeIntegerIntersection_ext_subsingleton
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T)
    (hacyclic :
      IsAcyclicOnIntersections G U Finset.univ)
    (q r : ℕ) (I : Simplex (ι := ι) q) :
    Subsingleton
      (Abelian.Ext
        (freeModuleSheaf (R := ℤ)
          (intersection U I.1))
        (integerLiftSheaf G) (r + 1)) := by
  have hI : I.1.Nonempty := by
    rw [← Finset.card_pos, I.2]
    omega
  have h :=
    hacyclic I.1 hI (Finset.subset_univ I.1)
      (r + 1) (Nat.succ_pos r)
  change
    Subsingleton
      (CategoryTheory.Sheaf.H' G
        (r + 1) (intersection U I.1)) at h
  let e :=
    freeIntegerModuleSheafExtAddEquivHPrime
      (intersection U I.1) G (r + 1)
  exact
    ⟨fun x y =>
      e.injective (h.elim (e x) (e y))⟩

/-- For a finite acyclic cover, global cohomology is additively
equivalent to homology of the normalized integer-linear section complex. -/
noncomputable def globalHAddEquivSectionPiHomology
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T)
    (hU : ⨆ i, U i = ⊤)
    (hacyclic :
      IsAcyclicOnIntersections G U Finset.univ)
    (n : ℕ) :
    CategoryTheory.Sheaf.H G n ≃+
      (sectionPiCechComplex U
        (integerLiftSheaf G)).homology n := by
  let F := integerLiftSheaf G
  let eExt :=
    finiteSubsetFreeSheafExtIsoLinearResolutionHomology
      (R := ℤ) U hU F
      (freeIntegerIntersection_ext_subsingleton
        G U hacyclic) n
  let eSection :=
    (HomologicalComplex.homologyFunctor
      (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
        (contravariantHomCocomplexIsoSectionPiCech U F)
  exact
    (constantIntegerModuleSheafExtAddEquivH G n).symm.trans <|
      eExt.addCommGroupIsoToAddEquiv.trans <|
        ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso
          eSection).addCommGroupIsoToAddEquiv

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverSectionCechComparison
