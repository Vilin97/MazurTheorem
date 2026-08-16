/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphNeighborhood
import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedRootCoordinates

/-!
# Incidence neighbourhoods on a geometric assigned split chart

For every ordered occurrence in the exact coherent support chart, isolate
the genuine split sheet selected by that occurrence.  The resulting open
neighbourhood in the relative curve-chart product has the property that the
whole equal-affine-coordinate closed locus is precisely the selected graph.

This is the geometric counterpart of the evaluated linear graph equation in
`GeometricAssignedRootCoordinates`.  The named downstream consumer is the
full product-ideal transport in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedIncidenceNeighborhood

open EqualCoordinateClosedImmersion
open EtaleGraphNeighborhood
open FiniteEtaleCoproductPower
open FiniteSupportCoordinateMaps
open FiniteSupportEtaleCoordinates
open GeometricAssignedRootCoordinates
open GeometricSupportAssignedSplitChart
open SmoothCurveEtaleCoordinate
open SplitFiniteBaseChange

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K))) [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
variable (V : (geometricDistinctCommonBase K C d z).left.Opens)
variable (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
variable (r : Fin (geometricDistinctSupportCard K C d z) → ℕ)
variable
  (E : ∀ j, pullback
      (restrictedPulledComponentToBase K C
        (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z)
        (geometricDistinctCharts K C d z)
        (geometricDistinctNeighborhoods K C d z) V j) q ≅
    Spec (.of (Fin (r j) → T)))
variable
  (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
    pullback.snd
      (restrictedPulledComponentToBase K C
        (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z)
        (geometricDistinctCharts K C d z)
        (geometricDistinctNeighborhoods K C d z) V j) q)
variable
  (w : (assignedComponentProductOverGround K C d z V
    (Spec (.of T)) q).left)

/-- The relative curve-chart ambient for one ordered occurrence before
imposing equality with its actual coherent root coordinate. -/
noncomputable abbrev occurrenceAmbient (i : Fin d) : Scheme.{u} :=
  ambient (coordinateLine K).hom
    ((geometricDistinctCharts K C d z)
      (geometricPointSupportIndex K C d z i)).schemeMap
    (baseCoordinate K C d z V T q i)

/-- The equal-coordinate closed subscheme inside the occurrence ambient. -/
noncomputable abbrev occurrenceEqualCoordinateInclusion (i : Fin d) :
    pullback
        ((geometricDistinctCharts K C d z)
          (geometricPointSupportIndex K C d z i)).schemeMap
        (baseCoordinate K C d z V T q i) ⟶
      occurrenceAmbient K C d z V T q i :=
  equalCoordinateInclusion (coordinateLine K).hom
    ((geometricDistinctCharts K C d z)
      (geometricPointSupportIndex K C d z i)).schemeMap
    (baseCoordinate K C d z V T q i)

/-- The actual selected split sheet as a graph in the occurrence's
equal-coordinate fiber product. -/
noncomputable abbrev occurrenceGraph (i : Fin d) :
    base K C d z V T q ⟶
      pullback
        ((geometricDistinctCharts K C d z)
          (geometricPointSupportIndex K C d z i)).schemeMap
        (baseCoordinate K C d z V T q i) :=
  graph
    ((geometricDistinctCharts K C d z)
      (geometricPointSupportIndex K C d z i)).schemeMap
    (baseCoordinate K C d z V T q i)
    (rootSheetToChart K C d z V T q r E hE w i)
    (rootSheetToChart_comp_schemeMap K C d z V T q r E hE w i)

/-- Around the actual selected sheet, the curve-chart incidence equation has
no complementary equal-coordinate sheets: its closed locus is exactly that
graph. -/
theorem exists_occurrenceOpen_graph_isPullback (i : Fin d) :
    ∃ (W : Scheme.{u})
      (F : pullback
          ((geometricDistinctCharts K C d z)
            (geometricPointSupportIndex K C d z i)).schemeMap
          (baseCoordinate K C d z V T q i) ≅
        base K C d z V T q ⨿ W)
      (U : (occurrenceAmbient K C d z V T q i).Opens)
      (graphToU : base K C d z V T q ⟶ U.toScheme),
      occurrenceGraph K C d z V T q r E hE w i ≫ F.hom = coprod.inl ∧
      IsPullback graphToU
        (occurrenceGraph K C d z V T q r E hE w i) U.ι
        (occurrenceEqualCoordinateInclusion K C d z V T q i) := by
  letI : Etale
      ((geometricDistinctCharts K C d z)
        (geometricPointSupportIndex K C d z i)).schemeMap :=
    PointChart.schemeMap_etale _
  letI : IsSeparated
      ((geometricDistinctCharts K C d z)
        (geometricPointSupportIndex K C d z i)).schemeMap :=
    PointChart.schemeMap_isSeparated _
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  exact @exists_open_graph_isPullback _ _ _ _
    (coordinateLine K).hom
    ((geometricDistinctCharts K C d z)
      (geometricPointSupportIndex K C d z i)).schemeMap
    (PointChart.schemeMap_etale _)
    (PointChart.schemeMap_isSeparated _)
    (baseCoordinate K C d z V T q i)
    (rootSheetToChart K C d z V T q r E hE w i)
    (rootSheetToChart_comp_schemeMap K C d z V T q r E hE w i)
    (show IsSeparated (coordinateLine K).hom from inferInstance)

/-- The isolating occurrence neighbourhood also identifies ideal sheaves:
the selected graph ideal is the pullback of the equal-coordinate ideal. -/
theorem exists_occurrenceOpen_graphIdeal (i : Fin d) :
    ∃ (W : Scheme.{u})
      (F : pullback
          ((geometricDistinctCharts K C d z)
            (geometricPointSupportIndex K C d z i)).schemeMap
          (baseCoordinate K C d z V T q i) ≅
        base K C d z V T q ⨿ W)
      (U : (occurrenceAmbient K C d z V T q i).Opens)
      (graphToU : base K C d z V T q ⟶ U.toScheme),
      occurrenceGraph K C d z V T q r E hE w i ≫ F.hom = coprod.inl ∧
      IsPullback graphToU
        (occurrenceGraph K C d z V T q r E hE w i) U.ι
        (occurrenceEqualCoordinateInclusion K C d z V T q i) ∧
      (occurrenceEqualCoordinateInclusion K C d z V T q i).ker.comap U.ι =
        graphToU.ker := by
  obtain ⟨W, F, U, graphToU, hF, hU⟩ :=
    exists_occurrenceOpen_graph_isPullback
      K C d z V T q r E hE w i
  refine ⟨W, F, U, graphToU, hF, hU, ?_⟩
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  exact equalCoordinateIdeal_comap_eq_graphToOpen_ker
    (coordinateLine K).hom
    ((geometricDistinctCharts K C d z)
      (geometricPointSupportIndex K C d z i)).schemeMap
    (baseCoordinate K C d z V T q i)
    (rootSheetToChart K C d z V T q r E hE w i)
    (rootSheetToChart_comp_schemeMap K C d z V T q r E hE w i) hU

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedIncidenceNeighborhood
