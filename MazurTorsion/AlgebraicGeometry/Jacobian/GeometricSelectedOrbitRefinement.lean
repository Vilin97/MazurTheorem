/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedRefinedSupportQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteActionSheets

/-!
# Refining an incidence graph chart to one selected orbit sheet

The block-invariant quotient chart is defined on the stable union of the
orbit of a chosen split sheet.  The graph-product calculation, meanwhile,
starts from an affine neighbourhood of one exact refinement point.  This
file intersects those two constructions: the graph neighbourhood can be
chosen inside the selected sheet locus, and its map to the selected target
is the already constructed tuple-sheet map to the actual component chart.

The named downstream consumer is `PointedIncidenceDescent`, where this
shrinking is applied to an ordered-incidence point before comparison with
the local block-monic coefficient chart.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricSelectedOrbitRefinement

open EquivariantFpqcRefinement
open EquivariantSplitRefinement
open FiniteEtaleCoproductPower
open FiniteSupportEtaleCoordinates
open GeometricAssignedAffineChart
open GeometricAssignedAffineRootCoordinates
open GeometricAssignedAffineSimultaneousNeighborhood
open GeometricAssignedAffineSupportCoproduct
open SplitFiniteActionSheets
open SplitFiniteBaseChange
open SmoothCurveEtaleCoordinate

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K))) [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
variable {V : (commonAffineBase K C d z).left.Opens}
variable (hVs : (action K C d z).IsStableOpen V)
variable (hpre : (componentAction K C d z).IsStableOpen
  ((componentToBasePower K C d z).left ⁻¹ᵁ V))
variable {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
variable (m : ℕ)
variable (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
  Spec (.of (Fin m → T)))
variable (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
  pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
variable {hmem : exactCommonAffineBasePoint K C d z ∈ V}
variable {s : (componentFpqcBlockRefinement K C d z hVs q).left}
variable {j : Fin m}
variable {hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
  commonAffineComponentPointInPreimage K C d z hmem}

/-- The selected orbit-sheet open, written with the exact generic action
terms used by `SplitFiniteActionSheets`. -/
noncomputable abbrev selectedOrbitSheetOpenExact :=
  selectedOrbitSheetOpen
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (splitAction ((action K C d z).restrict hVs)
      ((componentToBasePower K C d z).left ∣_ V) q
      (componentPreimageAction K C d z hpre)
      (componentToBasePower_restrict_equivariant
        K C d z hVs hpre) m E hE)
    (refinementAction ((action K C d z).restrict hVs) q) s j

/-- The locus of refinement-base points whose `j`-th split sheet lies in
the stable selected orbit-sheet open. -/
noncomputable def selectedOrbitSheetBaseOpen :
    (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
  (sheetInclusion
      (componentFpqcBlockRefinement K C d z hVs q).left m j).left ⁻¹ᵁ
    selectedOrbitSheetOpenExact
      K C d z hVs hpre q m E hE (s := s) (j := j)

include E hE in
/-- The exact refinement point belongs to the selected sheet-base locus. -/
theorem exact_mem_selectedOrbitSheetBaseOpen :
    s ∈ selectedOrbitSheetBaseOpen
      K C d z hVs hpre q m E hE (s := s) (j := j) := by
  let S := (componentFpqcBlockRefinement K C d z hVs q).left
  let α := componentFpqcBlockSplitAction K C d z hVs hpre q m E hE
  let β := refinementAction ((action K C d z).restrict hVs) q
  change sheetPoint S m j s ∈ selectedOrbitSheetSet S m α β s j
  have h := orbit_sheetPoint_mem_selectedOrbitSheetSet
    S m α β s j (1 : geometricAssignedStabilizer K C d z)
  rw [β.hom_one, sheetTransition_one S m α β
    (componentFpqcBlockSplitAction_equivariant
      K C d z hVs hpre q m E hE)] at h
  exact h

/-- Simultaneous affine graph neighborhoods may be chosen inside the stable
selected orbit-sheet locus. -/
theorem exists_selectedOrbit_simultaneousAffineGraphNeighborhood :
    ∃ N : SimultaneousAffineGraphNeighborhood
        K C d z hVs q m E hE hmem s j hj,
      N.baseOpen ≤ selectedOrbitSheetBaseOpen
        K C d z hVs hpre q m E hE (s := s) (j := j) := by
  classical
  let N₀ := Classical.choice
    (nonempty_simultaneousAffineGraphNeighborhood_of_exact
      K C d z hVs q m E hE hmem s j hj)
  let A : (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
    N₀.baseOpen ⊓
      selectedOrbitSheetBaseOpen K C d z hVs hpre q m E hE
        (s := s) (j := j)
  have hsA : s ∈ A :=
    ⟨N₀.exact_mem_base,
      exact_mem_selectedOrbitSheetBaseOpen
        K C d z hVs hpre q m E hE (s := s) (j := j)⟩
  have hb :=
    (componentFpqcBlockRefinement K C d z hVs q).left.isBasis_affineOpens
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, hWA⟩ :=
    hb.exists_subset_of_mem_open hsA A.isOpen
  change W ≤ A at hWA
  let N : SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj := {
    baseOpen := W
    base_isAffine := hW
    exact_mem_base := hsW
    base_le_simultaneous :=
      (hWA.trans inf_le_left).trans N₀.base_le_simultaneous
    supportOpen := N₀.supportOpen
    support_isAffine := N₀.support_isAffine
    support_le_intersection := N₀.support_le_intersection
    base_le_graph_preimage := fun a i ↦
      (hWA.trans inf_le_left).trans (N₀.base_le_graph_preimage a i) }
  exact ⟨N, hWA.trans inf_le_right⟩

/-- A selected simultaneous graph base maps through the chosen stable
orbit-sheet open. -/
noncomputable def SimultaneousAffineGraphNeighborhood.toSelectedOrbitSheet
    (N : SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj)
    (hN : N.baseOpen ≤ selectedOrbitSheetBaseOpen
      K C d z hVs hpre q m E hE (s := s) (j := j)) :
    N.baseOpen.toScheme ⟶
      (selectedOrbitSheetOpenExact
        K C d z hVs hpre q m E hE (s := s) (j := j)).toScheme :=
  IsOpenImmersion.lift
    (selectedOrbitSheetOpenExact
      K C d z hVs hpre q m E hE (s := s) (j := j)).ι
    (N.baseOpen.ι ≫
      (sheetInclusion
        (componentFpqcBlockRefinement K C d z hVs q).left m j).left)
    (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨_, hN x.property⟩, rfl⟩)

@[reassoc]
theorem SimultaneousAffineGraphNeighborhood.toSelectedOrbitSheet_comp_inclusion
    (N : SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj)
    (hN : N.baseOpen ≤ selectedOrbitSheetBaseOpen
      K C d z hVs hpre q m E hE (s := s) (j := j)) :
    SimultaneousAffineGraphNeighborhood.toSelectedOrbitSheet
        K C d z hVs hpre q m E hE N hN ≫
        (selectedOrbitSheetOpenExact
          K C d z hVs hpre q m E hE (s := s) (j := j)).ι =
      N.baseOpen.ι ≫
        (sheetInclusion
          (componentFpqcBlockRefinement K C d z hVs q).left m j).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The map through the selected sheet and target opens is the restriction
of the tuple-sheet map to the actual component chart. -/
@[reassoc]
theorem SimultaneousAffineGraphNeighborhood.toSelectedOrbitSheet_comp_target
    (N : SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj)
    (hN : N.baseOpen ≤ selectedOrbitSheetBaseOpen
      K C d z hVs hpre q m E hE (s := s) (j := j))
    [IsFinite q] [Etale q] :
    SimultaneousAffineGraphNeighborhood.toSelectedOrbitSheet
        K C d z hVs hpre q m E hE N hN ≫
        selectedOrbitSheetToTargetOpen
          ((action K C d z).restrict hVs)
          ((componentToBasePower K C d z).left ∣_ V) q
          (componentPreimageAction K C d z hpre)
          (componentToBasePower_restrict_equivariant
            K C d z hVs hpre) m E hE s j ≫
        (selectedOrbitTargetOpen
          ((action K C d z).restrict hVs)
          ((componentToBasePower K C d z).left ∣_ V) q
          (componentPreimageAction K C d z hpre)
          (componentToBasePower_restrict_equivariant
            K C d z hVs hpre) m E hE s j).ι =
      N.baseOpen.ι ≫
        tupleSheetToComponentPreimage K C d z hVs q m E hE j := by
  rw [selectedOrbitSheetToTargetOpen_comp_inclusion]
  rw [selectedOrbitSheetToOriginal]
  rw [← Category.assoc]
  rw [SimultaneousAffineGraphNeighborhood.toSelectedOrbitSheet_comp_inclusion]
  simp only [Category.assoc]
  change N.baseOpen.ι ≫
      (sheetInclusion
        (componentFpqcBlockRefinement K C d z hVs q).left m j).left ≫
        componentFpqcBlockSplitToComponentPreimage
          K C d z hVs q m E hE =
    N.baseOpen.ι ≫
      tupleSheetToComponentPreimage K C d z hVs q m E hE j
  rw [← tupleSheetToComponentPreimage_eq_direct]

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricSelectedOrbitRefinement
