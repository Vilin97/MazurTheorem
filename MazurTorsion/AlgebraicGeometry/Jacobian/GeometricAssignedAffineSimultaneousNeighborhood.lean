/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedSimultaneousGraphNeighborhood

/-!
# Affine simultaneous graph neighbourhoods

At an exact tuple-sheet lift, the simultaneous graph locus contains the
base point and every support-owned graph has the same value within its
support block.  Since affine opens form a basis on every scheme, one may
choose an affine open around each support value inside its graph-isolating
intersection.  Intersecting their inverse images gives a common open on the
refinement base; choosing an affine basis member there produces one affine
base on which every occurrence graph lands in its assigned affine support
piece.

The named downstream consumer is `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSimultaneousNeighborhood

open AssignedProductStabilizer
open FiniteSupportEtaleCoordinates
open FiniteSupportIndex
open GeometricAssignedAffineChart
open GeometricAssignedAffineRootCoordinates
open GeometricAssignedSimultaneousGraphNeighborhood
open SplitFiniteBaseChange

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K))) [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
variable {V : (commonAffineBase K C d z).left.Opens}
variable (hVs : (action K C d z).IsStableOpen V)
variable {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
variable (m : ℕ)
variable (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
  Spec (.of (Fin m → T)))
variable (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
  pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)

/-- Choose one occurrence owned by each enumerated geometric support member.
Surjectivity of the geometric support index makes this choice total, even
though no representative occurrence is part of the public interface. -/
private noncomputable def representativeOccurrence
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    OccurrencesAtSupport K C d z a := by
  let h := coordinateSupportIndex_surjective
    (Spec (.of K)) d C z a
  refine ⟨Classical.choose h, ?_⟩
  change coordinateSupportIndex (Spec (.of K)) d C z
      (Classical.choose h) = a
  exact Classical.choose_spec h

/-- Every exact support-graph value has an affine neighbourhood contained in
the full intersection of its occurrence-isolating opens. -/
theorem exists_affineSupportOpen_of_exact
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem)
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    ∃ U : (supportAmbient K C d z hVs q a).Opens,
      IsAffineOpen U ∧
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a
            (representativeOccurrence K C d z a) s ∈ U ∧
          U ≤ supportIntersectionOpen K C d z hVs q m E hE j a := by
  have hs :=
    graphToSupportAmbientAtSupport_apply_mem_supportIntersection_of_exact
      K C d z hVs q m E hE hmem s j hj a
        (representativeOccurrence K C d z a)
  have hb := (supportAmbient K C d z hVs q a).isBasis_affineOpens
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, hUle⟩ :=
    hb.exists_subset_of_mem_open hs
      (supportIntersectionOpen K C d z hVs q m E hE j a).isOpen
  exact ⟨U, hU, hsU, hUle⟩

/-- Affine local data simultaneously adapted to every occurrence graph at
one exact tuple-sheet lift.  The base open is contained in the simultaneous
graph locus, every support open is contained in its isolating intersection,
and every graph maps the base open into the corresponding support open. -/
structure SimultaneousAffineGraphNeighborhood
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem) where
  baseOpen : (componentFpqcBlockRefinement K C d z hVs q).left.Opens
  base_isAffine : IsAffineOpen baseOpen
  exact_mem_base : s ∈ baseOpen
  base_le_simultaneous :
    baseOpen ≤ simultaneousBaseOpen K C d z hVs q m E hE j
  supportOpen : (a : Fin (geometricDistinctSupportCard K C d z)) →
    (supportAmbient K C d z hVs q a).Opens
  support_isAffine : ∀ a, IsAffineOpen (supportOpen a)
  support_le_intersection : ∀ a,
    supportOpen a ≤ supportIntersectionOpen K C d z hVs q m E hE j a
  base_le_graph_preimage : ∀ a (i : OccurrencesAtSupport K C d z a),
    baseOpen ≤ graphToSupportAmbientAtSupport
      K C d z hVs q m E hE j a i ⁻¹ᵁ supportOpen a

/-- The exact lift admits simultaneous affine graph data.  The second affine
shrinking is performed only after all affine support pieces have been
chosen, so the final base is affine and every occurrence graph factors
through its assigned support piece. -/
theorem nonempty_simultaneousAffineGraphNeighborhood_of_exact
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem) :
    Nonempty (SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj) := by
  classical
  choose U hUaff hsU hUle using fun a ↦
    exists_affineSupportOpen_of_exact
      K C d z hVs q m E hE hmem s j hj a
  let A : (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
    simultaneousBaseOpen K C d z hVs q m E hE j ⊓
      ⨅ a : Fin (geometricDistinctSupportCard K C d z),
        ⨅ i : OccurrencesAtSupport K C d z a,
          graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ⁻¹ᵁ
            U a
  have hsA : s ∈ A := by
    refine ⟨mem_simultaneousBaseOpen_of_exact
      K C d z hVs q m E hE hmem s j hj, ?_⟩
    apply mem_iInf_opens_of_forall_mem
    intro a
    apply mem_iInf_opens_of_forall_mem
    intro i
    apply mem_preimageOpen_of_apply_mem
    rw [graphToSupportAmbientAtSupport_apply_eq_of_exact
      K C d z hVs q m E hE hmem s j hj a i
        (representativeOccurrence K C d z a)]
    exact hsU a
  have hb :=
    (componentFpqcBlockRefinement K C d z hVs q).left.isBasis_affineOpens
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, hWA⟩ :=
    hb.exists_subset_of_mem_open hsA A.isOpen
  change W ≤ A at hWA
  refine ⟨{
    baseOpen := W
    base_isAffine := hW
    exact_mem_base := hsW
    base_le_simultaneous := hWA.trans inf_le_left
    supportOpen := U
    support_isAffine := hUaff
    support_le_intersection := hUle
    base_le_graph_preimage := ?_ }⟩
  intro a i
  exact hWA.trans <| inf_le_right.trans <|
    iInf_le_of_le a <| iInf_le_of_le i le_rfl

/-- Restrict an occurrence graph to the affine base and affine support piece
chosen by simultaneous affine graph data. -/
noncomputable def SimultaneousAffineGraphNeighborhood.graph
    {hmem : exactCommonAffineBasePoint K C d z ∈ V}
    {s : (componentFpqcBlockRefinement K C d z hVs q).left}
    {j : Fin m}
    {hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem}
    (N : SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    N.baseOpen.toScheme ⟶ (N.supportOpen a).toScheme :=
  (componentFpqcBlockRefinement K C d z hVs q).left.homOfLE
      (N.base_le_graph_preimage a i) ≫
    (graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ∣_
      N.supportOpen a)

@[reassoc]
theorem SimultaneousAffineGraphNeighborhood.graph_comp_ι
    {hmem : exactCommonAffineBasePoint K C d z ∈ V}
    {s : (componentFpqcBlockRefinement K C d z hVs q).left}
    {j : Fin m}
    {hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem}
    (N : SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    N.graph K C d z hVs q m E hE a i ≫ (N.supportOpen a).ι =
      N.baseOpen.ι ≫
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i := by
  rw [SimultaneousAffineGraphNeighborhood.graph, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- The restricted graph remains a section over the affine base open. -/
@[reassoc]
theorem SimultaneousAffineGraphNeighborhood.graph_comp_base
    {hmem : exactCommonAffineBasePoint K C d z ∈ V}
    {s : (componentFpqcBlockRefinement K C d z hVs q).left}
    {j : Fin m}
    {hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem}
    (N : SimultaneousAffineGraphNeighborhood
      K C d z hVs q m E hE hmem s j hj)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    N.graph K C d z hVs q m E hE a i ≫
        (N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a =
      N.baseOpen.ι := by
  rw [← Category.assoc,
    SimultaneousAffineGraphNeighborhood.graph_comp_ι,
    Category.assoc, graphToSupportAmbientAtSupport_comp_base,
    Category.comp_id]

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSimultaneousNeighborhood
