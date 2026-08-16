/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineRootCoordinates

/-!
# Simultaneous graph neighbourhoods on an assigned affine chart

For one split tuple sheet, every occurrence graph has an open neighbourhood
that removes the other étale sheets.  A union of those opens contains all
the selected graphs, but does not preserve every graph-ideal identity on the
whole union.  The correct common neighbourhood is their finite intersection,
after restricting the refinement base to the locus where every selected
graph lands in that intersection.

This file carries out that simultaneous restriction support by support.  It
then base changes each support intersection to the common base open and
exhibits every selected occurrence graph as a section there.  The named
downstream consumer is `PointedIncidenceDescent`, where this is the topology
needed before comparing the restricted incidence ideal with the full
independent-root graph product.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedSimultaneousGraphNeighborhood

open GeometricAssignedAffineChart
open GeometricAssignedAffineRootCoordinates
open AssignedProductStabilizer
open EqualCoordinateClosedImmersion
open EtaleGraphNeighborhood
open FiniteSupportEtaleCoordinates
open SplitFiniteBaseChange
open SmoothCurveEtaleCoordinate

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

/-- Projection from a support-indexed curve-family ambient to the common
block-refinement base. -/
noncomputable def supportAmbientToBase
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportAmbient K C d z hVs q a ⟶
      (componentFpqcBlockRefinement K C d z hVs q).left :=
  pullback.snd
    ((affineComponentToCoordinateLine K C d z a).left ≫
      (coordinateLine K).hom)
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom)

@[reassoc]
theorem occurrenceAmbientIsoSupportAmbient_hom_fst (i : Fin d) :
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
        pullback.fst
          ((affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left ≫
              (coordinateLine K).hom)
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      pullback.fst
        ((affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left ≫
            (coordinateLine K).hom)
        (occurrenceCoordinate K C d z hVs q i ≫
          (coordinateLine K).hom) := by
  simp only [occurrenceAmbientIsoSupportAmbient,
    pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem occurrenceAmbientIsoSupportAmbient_hom_snd (i : Fin d) :
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i) =
      pullback.snd
        ((affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left ≫
            (coordinateLine K).hom)
        (occurrenceCoordinate K C d z hVs q i ≫
          (coordinateLine K).hom) := by
  simp only [occurrenceAmbientIsoSupportAmbient,
    supportAmbientToBase, pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem supportEqualCoordinateInclusion_comp_base (i : Fin d) :
    (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom) ≫
      supportAmbientToBase K C d z hVs q
        (geometricPointSupportIndex K C d z i) =
    pullback.snd
      (affineComponentToCoordinateLine K C d z
        (geometricPointSupportIndex K C d z i)).left
      (occurrenceCoordinate K C d z hVs q i) := by
  rw [Category.assoc,
    occurrenceAmbientIsoSupportAmbient_hom_snd]
  exact equalCoordinateInclusion_snd
    (coordinateLine K).hom
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCoordinate K C d z hVs q i)

@[reassoc]
theorem occurrenceGraph_comp_snd (j : Fin m) (i : Fin d) :
    occurrenceGraph K C d z hVs q m E hE j i ≫
        pullback.snd
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left :=
  pullback.lift_snd _ _ _

/-- The selected occurrence graph, viewed directly in its common support
ambient. -/
noncomputable def graphToSupportAmbient (j : Fin m) (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      supportAmbient K C d z hVs q
        (geometricPointSupportIndex K C d z i) :=
  occurrenceGraph K C d z hVs q m E hE j i ≫
    occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
      (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom

@[reassoc]
theorem graphToSupportAmbient_comp_fst (j : Fin m) (i : Fin d) :
    graphToSupportAmbient K C d z hVs q m E hE j i ≫
        pullback.fst
          ((affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left ≫
              (coordinateLine K).hom)
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i := by
  simp only [graphToSupportAmbient, Category.assoc,
    occurrenceAmbientIsoSupportAmbient_hom_fst,
    occurrenceGraph, pullback.lift_fst]

@[reassoc]
theorem graphToSupportAmbient_comp_base (j : Fin m) (i : Fin d) :
    graphToSupportAmbient K C d z hVs q m E hE j i ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i) =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left := by
  calc
    graphToSupportAmbient K C d z hVs q m E hE j i ≫
          supportAmbientToBase K C d z hVs q
            (geometricPointSupportIndex K C d z i) =
        occurrenceGraph K C d z hVs q m E hE j i ≫
          ((occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
              (occurrenceAmbientIsoSupportAmbient
                K C d z hVs q i).hom) ≫
            supportAmbientToBase K C d z hVs q
              (geometricPointSupportIndex K C d z i)) := by
      simp only [graphToSupportAmbient, Category.assoc]
    _ = occurrenceGraph K C d z hVs q m E hE j i ≫
        pullback.snd
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) := by
      rw [supportEqualCoordinateInclusion_comp_base]
    _ = 𝟙 (componentFpqcBlockRefinement K C d z hVs q).left :=
      occurrenceGraph_comp_snd K C d z hVs q m E hE j i

/-- The simultaneous support neighbourhood is the intersection of all
chosen occurrence-isolating opens in the one curve-family ambient. -/
noncomputable def supportIntersectionOpen (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (supportAmbient K C d z hVs q a).Opens :=
  ⨅ i : OccurrencesAtSupport K C d z a,
    occurrenceOpenAtSupport K C d z hVs q m E hE j a i

theorem supportIntersectionOpen_le_occurrenceOpenAtSupport (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    supportIntersectionOpen K C d z hVs q m E hE j a ≤
      occurrenceOpenAtSupport K C d z hVs q m E hE j a i :=
  iInf_le (fun i : OccurrencesAtSupport K C d z a ↦
    occurrenceOpenAtSupport K C d z hVs q m E hE j a i) i

/-- A support-owned occurrence graph with its codomain rewritten using the
proof that its owner is `a`. -/
noncomputable def graphToSupportAmbientAtSupport (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      supportAmbient K C d z hVs q a :=
  graphToSupportAmbient K C d z hVs q m E hE j i.1 ≫
    eqToHom (congrArg (supportAmbient K C d z hVs q) i.2)

@[reassoc]
theorem graphToOccurrenceOpenAtSupport_comp_ι (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToOccurrenceOpenAtSupport K C d z hVs q m E hE j a i ≫
        (occurrenceOpenAtSupport K C d z hVs q m E hE j a i).ι =
      graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i := by
  rcases i with ⟨i, rfl⟩
  change (chosenOccurrenceGraphNeighborhood
      K C d z hVs q m E hE j i).graphToOpen ≫
        (chosenOccurrenceGraphNeighborhood
          K C d z hVs q m E hE j i).occurrenceOpen.ι =
    graphToSupportAmbient K C d z hVs q m E hE j i
  exact (chosenOccurrenceGraphNeighborhood
    K C d z hVs q m E hE j i).graph_isPullback.w

/-- The tuple-sheet curve component of a support-owned occurrence, with its
codomain transported to the fixed support member. -/
noncomputable def tupleSheetToOccurrenceComponentAtSupport (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (affineComponentFamily K C d z a).left :=
  tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i.1 ≫
    (eqToHom (congrArg (affineComponentFamily K C d z) i.2)).left

@[reassoc]
theorem graphToSupportAmbientAtSupport_comp_fst (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ≫
        pullback.fst
          ((affineComponentToCoordinateLine K C d z a).left ≫
            (coordinateLine K).hom)
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      tupleSheetToOccurrenceComponentAtSupport
        K C d z hVs q m E hE j a i := by
  rcases i with ⟨i, rfl⟩
  change graphToSupportAmbient K C d z hVs q m E hE j i ≫
      pullback.fst
        ((affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left ≫
            (coordinateLine K).hom)
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) =
    tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i
  exact graphToSupportAmbient_comp_fst K C d z hVs q m E hE j i

@[reassoc]
theorem graphToSupportAmbientAtSupport_comp_base (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ≫
        supportAmbientToBase K C d z hVs q a =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left := by
  rcases i with ⟨i, rfl⟩
  simp only [graphToSupportAmbientAtSupport, eqToHom_refl,
    Category.comp_id, graphToSupportAmbient_comp_base]

/-- The exact repeated-product value makes the residue-field maps of two
support-owned tuple-sheet projections equal. -/
theorem residue_tupleSheetToOccurrenceComponentAtSupport_eq_of_exact
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hs : tupleSheetToComponent K C d z hVs q m E hE j s =
      commonAffineComponentPoint K C d z)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i k : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left.fromSpecResidueField s ≫
        tupleSheetToOccurrenceComponentAtSupport
          K C d z hVs q m E hE j a i =
      (componentFpqcBlockRefinement K C d z hVs q).left.fromSpecResidueField s ≫
        tupleSheetToOccurrenceComponentAtSupport
          K C d z hVs q m E hE j a k := by
  unfold tupleSheetToOccurrenceComponentAtSupport
    tupleSheetToOccurrenceComponent
  simp only [Category.assoc]
  exact residuePoint_map_toCommonAffineComponent_projection_eq_to_support
    K C d z
    (componentFpqcBlockRefinement K C d z hVs q).left
    (tupleSheetToComponent K C d z hVs q m E hE j) s
    hs a i.1 k.1 i.2 k.2

/-- At an exact correlated tuple-sheet lift, occurrence graphs belonging to
the same geometric support agree after restriction to the lift's residue
field.  Unlike equality of underlying projections, this controls the prime
of the curve/base tensor product and is therefore strong enough for open
neighbourhood membership. -/
theorem residue_graphToSupportAmbientAtSupport_eq_of_exact
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i k : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left.fromSpecResidueField s ≫
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i =
      (componentFpqcBlockRefinement K C d z hVs q).left.fromSpecResidueField s ≫
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a k := by
  have hs : tupleSheetToComponent K C d z hVs q m E hE j s =
      commonAffineComponentPoint K C d z := by
    change ((componentToBasePower K C d z).left ⁻¹ᵁ V).ι
        (tupleSheetToComponentPreimage K C d z hVs q m E hE j s) = _
    rw [hj]
    rfl
  apply pullback.hom_ext
  · simp only [Category.assoc, graphToSupportAmbientAtSupport_comp_fst]
    exact residue_tupleSheetToOccurrenceComponentAtSupport_eq_of_exact
      K C d z hVs q m E hE s j hs a i k
  · change
      ((componentFpqcBlockRefinement K C d z hVs q).left.fromSpecResidueField s ≫
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i) ≫
          supportAmbientToBase K C d z hVs q a =
      ((componentFpqcBlockRefinement K C d z hVs q).left.fromSpecResidueField s ≫
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a k) ≫
          supportAmbientToBase K C d z hVs q a
    rw [Category.assoc, graphToSupportAmbientAtSupport_comp_base,
      Category.comp_id, Category.assoc,
      graphToSupportAmbientAtSupport_comp_base, Category.comp_id]

/-- Hence the support-owned graphs have the same underlying value at the
exact refinement point. -/
theorem graphToSupportAmbientAtSupport_apply_eq_of_exact
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i k : OccurrencesAtSupport K C d z a) :
    graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i s =
      graphToSupportAmbientAtSupport K C d z hVs q m E hE j a k s := by
  have hres := residue_graphToSupportAmbientAtSupport_eq_of_exact
    K C d z hVs q m E hE hmem s j hj a i k
  exact apply_eq_of_fromSpecResidueField_comp_eq s
    (graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i)
    (graphToSupportAmbientAtSupport K C d z hVs q m E hE j a k) hres

/-- At the exact lift, every support-owned graph value lies in every chosen
isolating open for that same support. -/
theorem graphToSupportAmbientAtSupport_apply_mem_occurrenceOpen_of_exact
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i k : OccurrencesAtSupport K C d z a) :
    graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i s ∈
      occurrenceOpenAtSupport K C d z hVs q m E hE j a k := by
  have hfac := congrArg (fun f ↦ f s)
    (graphToOccurrenceOpenAtSupport_comp_ι
      K C d z hVs q m E hE j a k)
  change (occurrenceOpenAtSupport K C d z hVs q m E hE j a k).ι
      (graphToOccurrenceOpenAtSupport K C d z hVs q m E hE j a k s) =
    graphToSupportAmbientAtSupport K C d z hVs q m E hE j a k s at hfac
  rw [graphToSupportAmbientAtSupport_apply_eq_of_exact
    K C d z hVs q m E hE hmem s j hj a i k]
  rw [← hfac]
  exact (graphToOccurrenceOpenAtSupport
    K C d z hVs q m E hE j a k s).property

/-- Consequently every support-owned graph value at the exact lift lies in
the full intersection of the isolating opens for that support. -/
theorem graphToSupportAmbientAtSupport_apply_mem_supportIntersection_of_exact
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i s ∈
      supportIntersectionOpen K C d z hVs q m E hE j a := by
  change graphToSupportAmbientAtSupport
      K C d z hVs q m E hE j a i s ∈
    ((supportIntersectionOpen K C d z hVs q m E hE j a :
      (supportAmbient K C d z hVs q a).Opens) : Set _)
  rw [supportIntersectionOpen, TopologicalSpace.Opens.coe_iInf,
    Set.mem_iInter]
  intro k
  exact graphToSupportAmbientAtSupport_apply_mem_occurrenceOpen_of_exact
    K C d z hVs q m E hE hmem s j hj a i k

/-- The base locus on which one occurrence graph lands in the common
intersection for its support owner. -/
noncomputable abbrev supportAdmissibleBaseOpen (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
  graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ⁻¹ᵁ
    supportIntersectionOpen K C d z hVs q m E hE j a

/-- Restrict the refinement base until every occurrence graph lands in the
common intersection belonging to every support owner. -/
noncomputable def simultaneousBaseOpen (j : Fin m) :
    (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
  ⨅ a : Fin (geometricDistinctSupportCard K C d z),
    ⨅ i : OccurrencesAtSupport K C d z a,
      supportAdmissibleBaseOpen K C d z hVs q m E hE j a i

/-- The simultaneous graph neighbourhood is nonempty at the geometrically
correct point: the exact tuple-sheet lift belongs to every support and
occurrence admissibility condition. -/
theorem mem_simultaneousBaseOpen_of_exact
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    (hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
      commonAffineComponentPointInPreimage K C d z hmem) :
    s ∈ simultaneousBaseOpen K C d z hVs q m E hE j := by
  unfold simultaneousBaseOpen
  apply mem_iInf_opens_of_forall_mem
  intro a
  apply mem_iInf_opens_of_forall_mem
  intro i
  exact mem_preimageOpen_of_apply_mem
    (graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i)
    (supportIntersectionOpen K C d z hVs q m E hE j a) s
    (graphToSupportAmbientAtSupport_apply_mem_supportIntersection_of_exact
      K C d z hVs q m E hE hmem s j hj a i)

theorem simultaneousBaseOpen_le_supportAdmissibleBaseOpen (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    simultaneousBaseOpen K C d z hVs q m E hE j ≤
      supportAdmissibleBaseOpen K C d z hVs q m E hE j a i :=
  iInf_le_of_le a (iInf_le_of_le i le_rfl)

/-- After the common base restriction, every selected graph factors through
the intersection of all isolating opens belonging to its support owner. -/
noncomputable def graphToSupportIntersection (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (simultaneousBaseOpen K C d z hVs q m E hE j).toScheme ⟶
      (supportIntersectionOpen K C d z hVs q m E hE j a).toScheme :=
  (componentFpqcBlockRefinement K C d z hVs q).left.homOfLE
      (simultaneousBaseOpen_le_supportAdmissibleBaseOpen
        K C d z hVs q m E hE j a i) ≫
    (graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ∣_
      supportIntersectionOpen K C d z hVs q m E hE j a)

@[reassoc]
theorem graphToSupportIntersection_comp_ι (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportIntersection K C d z hVs q m E hE j a i ≫
        (supportIntersectionOpen K C d z hVs q m E hE j a).ι =
      (simultaneousBaseOpen K C d z hVs q m E hE j).ι ≫
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i := by
  rw [graphToSupportIntersection, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- Every restricted occurrence graph is a section over the simultaneous
base open. -/
@[reassoc]
theorem graphToSupportIntersection_comp_base (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportIntersection K C d z hVs q m E hE j a i ≫
        (supportIntersectionOpen K C d z hVs q m E hE j a).ι ≫
          supportAmbientToBase K C d z hVs q a =
      (simultaneousBaseOpen K C d z hVs q m E hE j).ι := by
  rw [← Category.assoc, graphToSupportIntersection_comp_ι,
    Category.assoc]
  rcases i with ⟨i, rfl⟩
  change (simultaneousBaseOpen K C d z hVs q m E hE j).ι ≫
      graphToSupportAmbient K C d z hVs q m E hE j i ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i) =
    (simultaneousBaseOpen K C d z hVs q m E hE j).ι
  rw [graphToSupportAmbient_comp_base, Category.comp_id]

/-- Base change the simultaneous support intersection to the common base
open on which all selected graphs land in it. -/
noncomputable abbrev supportIntersectionBaseChange (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z)) : Scheme.{u} :=
  pullback
    ((supportIntersectionOpen K C d z hVs q m E hE j a).ι ≫
      supportAmbientToBase K C d z hVs q a)
    (simultaneousBaseOpen K C d z hVs q m E hE j).ι

/-- The selected occurrence graph as a genuine section of the base-changed
simultaneous support neighbourhood. -/
noncomputable def graphToSupportIntersectionBaseChange (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (simultaneousBaseOpen K C d z hVs q m E hE j).toScheme ⟶
      supportIntersectionBaseChange K C d z hVs q m E hE j a :=
  pullback.lift
    (graphToSupportIntersection K C d z hVs q m E hE j a i)
    (𝟙 _)
    (by
      simpa only [Category.id_comp] using
        (graphToSupportIntersection_comp_base
          K C d z hVs q m E hE j a i))

@[reassoc]
theorem graphToSupportIntersectionBaseChange_comp_snd (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportIntersectionBaseChange
        K C d z hVs q m E hE j a i ≫
      pullback.snd
        ((supportIntersectionOpen K C d z hVs q m E hE j a).ι ≫
          supportAmbientToBase K C d z hVs q a)
        (simultaneousBaseOpen K C d z hVs q m E hE j).ι =
      𝟙 (simultaneousBaseOpen K C d z hVs q m E hE j).toScheme :=
  pullback.lift_snd _ _ _

/-- Include the simultaneous support intersection in the chosen isolating
open for one occurrence. -/
noncomputable def supportIntersectionToOccurrenceOpen
    (j : Fin m) (i : Fin d) :
    (supportIntersectionOpen K C d z hVs q m E hE j
      (geometricPointSupportIndex K C d z i)).toScheme ⟶
    (occurrenceOpenAtSupport K C d z hVs q m E hE j
      (geometricPointSupportIndex K C d z i) ⟨i, rfl⟩).toScheme :=
  (supportAmbient K C d z hVs q
    (geometricPointSupportIndex K C d z i)).homOfLE
      (supportIntersectionOpen_le_occurrenceOpenAtSupport
        K C d z hVs q m E hE j
          (geometricPointSupportIndex K C d z i) ⟨i, rfl⟩)

/-- Pull back one chosen graph along the simultaneous support
intersection. -/
noncomputable abbrev supportIntersectionGraph (j : Fin m) (i : Fin d) :
    Scheme.{u} :=
  pullback
    (supportIntersectionToOccurrenceOpen K C d z hVs q m E hE j i)
    (graphToOccurrenceOpenAtSupport K C d z hVs q m E hE j
      (geometricPointSupportIndex K C d z i) ⟨i, rfl⟩)

/-- The restricted graph maps into the simultaneous support intersection. -/
noncomputable def supportIntersectionGraphι (j : Fin m) (i : Fin d) :
    supportIntersectionGraph K C d z hVs q m E hE j i ⟶
      (supportIntersectionOpen K C d z hVs q m E hE j
        (geometricPointSupportIndex K C d z i)).toScheme :=
  pullback.fst
    (supportIntersectionToOccurrenceOpen K C d z hVs q m E hE j i)
    (graphToOccurrenceOpenAtSupport K C d z hVs q m E hE j
      (geometricPointSupportIndex K C d z i) ⟨i, rfl⟩)

/-- The restricted graph maps to the occurrence equal-coordinate locus. -/
noncomputable def supportIntersectionGraphToEqualCoordinate
    (j : Fin m) (i : Fin d) :
    supportIntersectionGraph K C d z hVs q m E hE j i ⟶
      pullback
        (affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left
        (occurrenceCoordinate K C d z hVs q i) :=
  pullback.snd
      (supportIntersectionToOccurrenceOpen K C d z hVs q m E hE j i)
      (graphToOccurrenceOpenAtSupport K C d z hVs q m E hE j
        (geometricPointSupportIndex K C d z i) ⟨i, rfl⟩) ≫
    occurrenceGraph K C d z hVs q m E hE j i

/-- Intersecting the occurrence open preserves the cartesian graph square. -/
theorem supportIntersectionGraph_isPullback (j : Fin m) (i : Fin d) :
    IsPullback
      (supportIntersectionGraphι K C d z hVs q m E hE j i)
      (supportIntersectionGraphToEqualCoordinate
        K C d z hVs q m E hE j i)
      (supportIntersectionOpen K C d z hVs q m E hE j
        (geometricPointSupportIndex K C d z i)).ι
      (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom) := by
  let U := occurrenceOpenAtSupport K C d z hVs q m E hE j
    (geometricPointSupportIndex K C d z i) ⟨i, rfl⟩
  let g := graphToOccurrenceOpenAtSupport K C d z hVs q m E hE j
    (geometricPointSupportIndex K C d z i) ⟨i, rfl⟩
  let hsmall := IsPullback.of_hasPullback
    (supportIntersectionToOccurrenceOpen K C d z hVs q m E hE j i) g
  have hbig : IsPullback g
      (occurrenceGraph K C d z hVs q m E hE j i) U.ι
      (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom) := by
    exact (chosenOccurrenceGraphNeighborhood
      K C d z hVs q m E hE j i).graph_isPullback
  dsimp only [U, g] at hsmall hbig
  simpa only [supportIntersectionGraph, supportIntersectionGraphι,
    supportIntersectionGraphToEqualCoordinate,
    supportIntersectionToOccurrenceOpen, Scheme.homOfLE_ι] using
      hsmall.paste_vert hbig

/-- On the simultaneous support intersection, the pulled-back
equal-coordinate ideal is exactly the restricted selected graph ideal. -/
theorem supportIntersection_equalCoordinateIdeal (j : Fin m) (i : Fin d) :
    (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom).ker.comap
        (supportIntersectionOpen K C d z hVs q m E hE j
          (geometricPointSupportIndex K C d z i)).ι =
      (supportIntersectionGraphι K C d z hVs q m E hE j i).ker := by
  let inclusion := occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom
  let openι := (supportIntersectionOpen K C d z hVs q m E hE j
    (geometricPointSupportIndex K C d z i)).ι
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  letI : IsClosedImmersion
      (occurrenceEqualCoordinateInclusion K C d z hVs q i) := by
    exact EqualCoordinateClosedImmersion.equalCoordinateInclusion_closed
      (coordinateLine K).hom
      (affineComponentToCoordinateLine K C d z
        (geometricPointSupportIndex K C d z i)).left
      (occurrenceCoordinate K C d z hVs q i)
  letI : IsClosedImmersion inclusion := by
    dsimp only [inclusion]
    rw [MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
      (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom]
    infer_instance
  calc
    inclusion.ker.comap openι = (pullback.fst openι inclusion).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
        inclusion openι).symm
    _ = ((supportIntersectionGraph_isPullback
          K C d z hVs q m E hE j i).isoPullback.hom ≫
        pullback.fst openι inclusion).ker :=
      (Scheme.Hom.ker_comp_of_isIso
        (supportIntersectionGraph_isPullback
          K C d z hVs q m E hE j i).isoPullback.hom
        (pullback.fst openι inclusion)).symm
    _ = (supportIntersectionGraphι
        K C d z hVs q m E hE j i).ker := by
      rw [(supportIntersectionGraph_isPullback
        K C d z hVs q m E hE j i).isoPullback_hom_fst]

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedSimultaneousGraphNeighborhood
