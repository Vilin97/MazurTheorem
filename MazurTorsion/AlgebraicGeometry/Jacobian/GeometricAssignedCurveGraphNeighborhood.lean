/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedSimultaneousGraphNeighborhood

/-!
# Curve-level graph neighbourhoods on an assigned affine chart

The affine-coordinate graph neighbourhood separates the sheets of an étale
coordinate map, but the selected affine component need not inject into the
original curve.  This file applies the same étale graph-neighbourhood theorem
directly to the component-to-curve map.  After transport, both constructions
live in the common support ambient, so their opens can be intersected in the
owner-graph refinement.

The named downstream consumer is
`GeometricAssignedAffineSupportCoproduct.CrossSupportAffineGraphRefinement`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedCurveGraphNeighborhood

open EqualCoordinateClosedImmersion
open EtaleGraphNeighborhood
open FiniteSupportEtaleCoordinates
open GeometricAssignedAffineChart
open GeometricAssignedAffineRootCoordinates
open GeometricAssignedSimultaneousGraphNeighborhood
open SmoothCurveEtaleCoordinate
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

/-- The selected tuple-sheet occurrence mapped to the original curve over
the coordinate copy of the ground field. -/
noncomputable def occurrenceCurveCoordinate (j : Fin m) (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (PointChart.curveOverCoordinateBase K C.left C.hom).left :=
  tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i ≫
    (affineComponentToCurve K C d z
      (geometricPointSupportIndex K C d z i)).left

/-- Every curve-valued tuple-sheet occurrence has the common structural map
from the block-refinement base to the coordinate ground scheme. -/
theorem occurrenceCurveCoordinate_comp_curve (j : Fin m) (i : Fin d) :
    occurrenceCurveCoordinate K C d z hVs q m E hE j i ≫
        (PointChart.curveOverCoordinateBase K C.left C.hom).hom =
      refinementToBase K C d z hVs q ≫
        (commonAffineBase K C d z).hom := by
  calc
    occurrenceCurveCoordinate K C d z hVs q m E hE j i ≫
          (PointChart.curveOverCoordinateBase K C.left C.hom).hom =
        tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i ≫
          ((affineComponentToCurve K C d z
              (geometricPointSupportIndex K C d z i)).left ≫
            (PointChart.curveOverCoordinateBase K C.left C.hom).hom) := by
      simp only [occurrenceCurveCoordinate, Category.assoc]
    _ = tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i ≫
        (affineComponentFamily K C d z
          (geometricPointSupportIndex K C d z i)).hom := by
      rw [(affineComponentToCurve K C d z
        (geometricPointSupportIndex K C d z i)).w]
    _ = tupleSheetToComponent K C d z hVs q m E hE j ≫
        (commonAffineComponent K C d z).hom := by
      rw [tupleSheetToOccurrenceComponent, Category.assoc,
        (Pi.π (fun k : Fin d ↦ affineComponentFamily K C d z
          (geometricPointSupportIndex K C d z k)) i).w]
    _ = tupleSheetToComponent K C d z hVs q m E hE j ≫
        (componentToBasePower K C d z).left ≫
          (commonAffineBase K C d z).hom := by
      rw [← (componentToBasePower K C d z).w]
    _ = refinementToBase K C d z hVs q ≫
        (commonAffineBase K C d z).hom := by
      rw [← Category.assoc, tupleSheetToComponent_comp_base]

/-- The curve and affine-line presentations of a selected component have
the same structural composite to the coordinate ground scheme. -/
theorem affineComponentToCurve_comp_curve_eq_coordinate
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (affineComponentToCurve K C d z a).left ≫
        (PointChart.curveOverCoordinateBase K C.left C.hom).hom =
      (affineComponentToCoordinateLine K C d z a).left ≫
        (coordinateLine K).hom :=
  (affineComponentToCurve K C d z a).w.trans
    (affineComponentToCoordinateLine K C d z a).w.symm

/-- The relative component/tuple-sheet ambient formed over the original
curve. -/
noncomputable abbrev occurrenceCurveAmbient (j : Fin m) (i : Fin d) :
    Scheme.{u} :=
  ambient (PointChart.curveOverCoordinateBase K C.left C.hom).hom
    (affineComponentToCurve K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCurveCoordinate K C d z hVs q m E hE j i)

/-- The curve-level occurrence ambient is canonically the same common
support ambient used by the affine-coordinate construction. -/
noncomputable def occurrenceCurveAmbientIsoSupportAmbient
    (j : Fin m) (i : Fin d) :
    occurrenceCurveAmbient K C d z hVs q m E hE j i ≅
      supportAmbient K C d z hVs q
        (geometricPointSupportIndex K C d z i) :=
  pullback.congrHom
    (affineComponentToCurve_comp_curve_eq_coordinate K C d z
      (geometricPointSupportIndex K C d z i))
    (occurrenceCurveCoordinate_comp_curve K C d z hVs q m E hE j i)

/-- Transport a curve-level isolating open to the common support ambient. -/
noncomputable abbrev curveOpenOnSupportAmbient (j : Fin m) (i : Fin d)
    (U : (occurrenceCurveAmbient K C d z hVs q m E hE j i).Opens) :
    (supportAmbient K C d z hVs q
      (geometricPointSupportIndex K C d z i)).Opens :=
  (occurrenceCurveAmbientIsoSupportAmbient
    K C d z hVs q m E hE j i).inv ⁻¹ᵁ U

/-- Transport identifies the schemes carried by the curve-level occurrence
open and its common-support presentation. -/
noncomputable def curveOpenIso (j : Fin m) (i : Fin d)
    (U : (occurrenceCurveAmbient K C d z hVs q m E hE j i).Opens) :
    U.toScheme ≅ (curveOpenOnSupportAmbient
      K C d z hVs q m E hE j i U).toScheme :=
  (Scheme.Hom.preimageIso
    (occurrenceCurveAmbientIsoSupportAmbient
      K C d z hVs q m E hE j i).inv U).symm

@[reassoc]
theorem curveOpenIso_hom_comp_ι (j : Fin m) (i : Fin d)
    (U : (occurrenceCurveAmbient K C d z hVs q m E hE j i).Opens) :
    (curveOpenIso K C d z hVs q m E hE j i U).hom ≫
        (curveOpenOnSupportAmbient K C d z hVs q m E hE j i U).ι =
      U.ι ≫ (occurrenceCurveAmbientIsoSupportAmbient
        K C d z hVs q m E hE j i).hom := by
  apply (cancel_mono (occurrenceCurveAmbientIsoSupportAmbient
    K C d z hVs q m E hE j i).inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (Scheme.Hom.preimageIso
      (occurrenceCurveAmbientIsoSupportAmbient
        K C d z hVs q m E hE j i).inv U).inv ≫
      ((occurrenceCurveAmbientIsoSupportAmbient
        K C d z hVs q m E hE j i).inv ⁻¹ᵁ U).ι ≫
      (occurrenceCurveAmbientIsoSupportAmbient
        K C d z hVs q m E hE j i).inv = U.ι
  exact Scheme.Hom.preimageIso_inv_ι
    (occurrenceCurveAmbientIsoSupportAmbient
      K C d z hVs q m E hE j i).inv U

/-- The closed locus where a varying selected component and the tuple-sheet
occurrence have equal images in the original curve. -/
noncomputable abbrev occurrenceCurveEqualCoordinateInclusion
    (j : Fin m) (i : Fin d) :
    pullback
        (affineComponentToCurve K C d z
          (geometricPointSupportIndex K C d z i)).left
        (occurrenceCurveCoordinate K C d z hVs q m E hE j i) ⟶
      occurrenceCurveAmbient K C d z hVs q m E hE j i :=
  equalCoordinateInclusion
    (PointChart.curveOverCoordinateBase K C.left C.hom).hom
    (affineComponentToCurve K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCurveCoordinate K C d z hVs q m E hE j i)

/-- The selected tuple-sheet occurrence as a graph in the curve-level
equal-coordinate fiber product. -/
noncomputable abbrev occurrenceCurveGraph (j : Fin m) (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      pullback
        (affineComponentToCurve K C d z
          (geometricPointSupportIndex K C d z i)).left
        (occurrenceCurveCoordinate K C d z hVs q m E hE j i) :=
  graph
    (affineComponentToCurve K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCurveCoordinate K C d z hVs q m E hE j i)
    (tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i) rfl

/-- Transport a curve-level graph factorization to the common support
ambient. -/
noncomputable def curveGraphToSupportOpen (j : Fin m) (i : Fin d)
    (U : (occurrenceCurveAmbient K C d z hVs q m E hE j i).Opens)
    (graphToU :
      (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (curveOpenOnSupportAmbient K C d z hVs q m E hE j i U).toScheme :=
  graphToU ≫ (curveOpenIso K C d z hVs q m E hE j i U).hom

/-- A curve-level graph-isolating pullback remains a pullback after
transport to the common support ambient. -/
theorem transport_curve_isPullback (j : Fin m) (i : Fin d)
    (U : (occurrenceCurveAmbient K C d z hVs q m E hE j i).Opens)
    (graphToU :
      (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme)
    (h : IsPullback graphToU
      (occurrenceCurveGraph K C d z hVs q m E hE j i) U.ι
      (occurrenceCurveEqualCoordinateInclusion
        K C d z hVs q m E hE j i)) :
    IsPullback
      (curveGraphToSupportOpen K C d z hVs q m E hE j i U graphToU)
      (occurrenceCurveGraph K C d z hVs q m E hE j i)
      (curveOpenOnSupportAmbient K C d z hVs q m E hE j i U).ι
      (occurrenceCurveEqualCoordinateInclusion
          K C d z hVs q m E hE j i ≫
        (occurrenceCurveAmbientIsoSupportAmbient
          K C d z hVs q m E hE j i).hom) := by
  exact h.of_iso (Iso.refl _)
    (curveOpenIso K C d z hVs q m E hE j i U)
    (Iso.refl _)
    (occurrenceCurveAmbientIsoSupportAmbient
      K C d z hVs q m E hE j i)
    rfl (by simp) (curveOpenIso_hom_comp_ι
      K C d z hVs q m E hE j i U).symm (by simp)

/-- Every tuple-sheet occurrence has a common-support open in which curve
equality is exactly that selected graph. -/
theorem exists_curveSupportOpen_graph_isPullback [IsSeparated C.hom]
    (j : Fin m) (i : Fin d) :
    ∃ (W : Scheme.{u})
      (F : pullback
          (affineComponentToCurve K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCurveCoordinate K C d z hVs q m E hE j i) ≅
        (componentFpqcBlockRefinement K C d z hVs q).left ⨿ W)
      (U : (supportAmbient K C d z hVs q
        (geometricPointSupportIndex K C d z i)).Opens)
      (graphToU :
        (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme),
      occurrenceCurveGraph K C d z hVs q m E hE j i ≫ F.hom =
        coprod.inl ∧
      IsPullback graphToU
        (occurrenceCurveGraph K C d z hVs q m E hE j i) U.ι
        (occurrenceCurveEqualCoordinateInclusion
            K C d z hVs q m E hE j i ≫
          (occurrenceCurveAmbientIsoSupportAmbient
            K C d z hVs q m E hE j i).hom) := by
  letI : IsSeparated
      (affineComponentToCurve K C d z
        (geometricPointSupportIndex K C d z i)).left := by
    infer_instance
  letI : IsSeparated
      (PointChart.curveOverCoordinateBase K C.left C.hom).hom := by
    change IsSeparated (C.hom ≫ (coordinateBaseIso K).inv)
    infer_instance
  obtain ⟨W, F, U, graphToU, hF, hU⟩ :=
    @exists_open_graph_isPullback _ _ _ _
      (PointChart.curveOverCoordinateBase K C.left C.hom).hom
      (affineComponentToCurve K C d z
        (geometricPointSupportIndex K C d z i)).left
      (affineComponentToCurve_etale K C d z
        (geometricPointSupportIndex K C d z i))
      (show IsSeparated
        (affineComponentToCurve K C d z
          (geometricPointSupportIndex K C d z i)).left from inferInstance)
      (occurrenceCurveCoordinate K C d z hVs q m E hE j i)
      (tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i)
      rfl
      (show IsSeparated
        (PointChart.curveOverCoordinateBase K C.left C.hom).hom from
          inferInstance)
  refine ⟨W, F, curveOpenOnSupportAmbient
    K C d z hVs q m E hE j i U,
    curveGraphToSupportOpen K C d z hVs q m E hE j i U graphToU,
    hF, ?_⟩
  exact transport_curve_isPullback
    K C d z hVs q m E hE j i U graphToU hU

/-- The transported curve graph, regarded directly in the common support
ambient. -/
noncomputable def curveGraphToSupportAmbient (j : Fin m) (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      supportAmbient K C d z hVs q
        (geometricPointSupportIndex K C d z i) :=
  occurrenceCurveGraph K C d z hVs q m E hE j i ≫
    occurrenceCurveEqualCoordinateInclusion
      K C d z hVs q m E hE j i ≫
    (occurrenceCurveAmbientIsoSupportAmbient
      K C d z hVs q m E hE j i).hom

/-- The curve-level and affine-coordinate graph constructions give the same
map to the common support ambient. -/
theorem curveGraphToSupportAmbient_eq_graphToSupportAmbient
    (j : Fin m) (i : Fin d) :
    curveGraphToSupportAmbient K C d z hVs q m E hE j i =
      graphToSupportAmbient K C d z hVs q m E hE j i := by
  apply pullback.hom_ext
  · rw [graphToSupportAmbient_comp_fst]
    simp only [curveGraphToSupportAmbient, Category.assoc,
      occurrenceCurveAmbientIsoSupportAmbient, pullback.congrHom_hom]
    dsimp only [pullback.map]
    simp only [pullback.lift_fst, Category.comp_id,
      occurrenceCurveEqualCoordinateInclusion, equalCoordinateInclusion,
      occurrenceCurveGraph, graph, pullback.lift_fst]
  · change curveGraphToSupportAmbient
        K C d z hVs q m E hE j i ≫
          supportAmbientToBase K C d z hVs q
            (geometricPointSupportIndex K C d z i) =
      graphToSupportAmbient K C d z hVs q m E hE j i ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i)
    rw [graphToSupportAmbient_comp_base]
    unfold supportAmbientToBase
    simp only [curveGraphToSupportAmbient, Category.assoc,
      occurrenceCurveAmbientIsoSupportAmbient, pullback.congrHom_hom]
    dsimp only [pullback.map]
    simp only [pullback.lift_snd, Category.comp_id,
      occurrenceCurveEqualCoordinateInclusion, equalCoordinateInclusion,
      occurrenceCurveGraph, graph, pullback.lift_snd]

/-- Curve-level isolating data for one ordered occurrence, packaged for a
finite common-intersection construction. -/
structure CurveOccurrenceGraphNeighborhood [IsSeparated C.hom]
    (j : Fin m) (i : Fin d) where
  occurrenceOpen : (supportAmbient K C d z hVs q
    (geometricPointSupportIndex K C d z i)).Opens
  graphToOpen :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      occurrenceOpen.toScheme
  graph_isPullback : IsPullback graphToOpen
    (occurrenceCurveGraph K C d z hVs q m E hE j i)
    occurrenceOpen.ι
    (occurrenceCurveEqualCoordinateInclusion
        K C d z hVs q m E hE j i ≫
      (occurrenceCurveAmbientIsoSupportAmbient
        K C d z hVs q m E hE j i).hom)

/-- Every ordered occurrence admits curve-level isolating data. -/
theorem nonempty_curveOccurrenceGraphNeighborhood [IsSeparated C.hom]
    (j : Fin m) (i : Fin d) :
    Nonempty (CurveOccurrenceGraphNeighborhood
      K C d z hVs q m E hE j i) := by
  obtain ⟨_, _, U, graphToU, _, hU⟩ :=
    exists_curveSupportOpen_graph_isPullback
      K C d z hVs q m E hE j i
  exact ⟨⟨U, graphToU, hU⟩⟩

/-- Choose one curve-level isolating neighbourhood for every occurrence. -/
noncomputable def chosenCurveOccurrenceGraphNeighborhood
    [IsSeparated C.hom] (j : Fin m) (i : Fin d) :
    CurveOccurrenceGraphNeighborhood K C d z hVs q m E hE j i :=
  Classical.choice
    (nonempty_curveOccurrenceGraphNeighborhood
      K C d z hVs q m E hE j i)

/-- The chosen curve-level isolating open, with its support owner fixed by a
proof. -/
noncomputable def curveOccurrenceOpenAtSupport [IsSeparated C.hom]
    (j : Fin m) (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (supportAmbient K C d z hVs q a).Opens := by
  rcases i with ⟨i, rfl⟩
  exact (chosenCurveOccurrenceGraphNeighborhood
    K C d z hVs q m E hE j i).occurrenceOpen

/-- The chosen curve graph factors through its owner-indexed support
ambient open. -/
noncomputable def curveGraphToOccurrenceOpenAtSupport [IsSeparated C.hom]
    (j : Fin m) (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (curveOccurrenceOpenAtSupport
        K C d z hVs q m E hE j a i).toScheme := by
  rcases i with ⟨i, rfl⟩
  exact (chosenCurveOccurrenceGraphNeighborhood
    K C d z hVs q m E hE j i).graphToOpen

/-- Factoring through the chosen curve-level open does not change the graph
map to the common support ambient. -/
@[reassoc]
theorem curveGraphToOccurrenceOpenAtSupport_comp_ι [IsSeparated C.hom]
    (j : Fin m) (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    curveGraphToOccurrenceOpenAtSupport
        K C d z hVs q m E hE j a i ≫
      (curveOccurrenceOpenAtSupport
        K C d z hVs q m E hE j a i).ι =
      graphToSupportAmbientAtSupport
        K C d z hVs q m E hE j a i := by
  rcases i with ⟨i, rfl⟩
  change (chosenCurveOccurrenceGraphNeighborhood
      K C d z hVs q m E hE j i).graphToOpen ≫
      (chosenCurveOccurrenceGraphNeighborhood
        K C d z hVs q m E hE j i).occurrenceOpen.ι =
    graphToSupportAmbient K C d z hVs q m E hE j i
  rw [(chosenCurveOccurrenceGraphNeighborhood
    K C d z hVs q m E hE j i).graph_isPullback.w]
  exact curveGraphToSupportAmbient_eq_graphToSupportAmbient
    K C d z hVs q m E hE j i

/-- Every value of the chosen curve graph belongs to its transported
owner-isolating open. -/
theorem graphToSupportAmbientAtSupport_apply_mem_curveOccurrenceOpenAtSupport
    [IsSeparated C.hom]
    (j : Fin m) (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a)
    (x : (componentFpqcBlockRefinement K C d z hVs q).left) :
    graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i x ∈
      curveOccurrenceOpenAtSupport K C d z hVs q m E hE j a i := by
  have h := congrArg (fun f ↦ f x)
    (curveGraphToOccurrenceOpenAtSupport_comp_ι
      K C d z hVs q m E hE j a i)
  rw [← h]
  exact (curveGraphToOccurrenceOpenAtSupport
    K C d z hVs q m E hE j a i x).property

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedCurveGraphNeighborhood
