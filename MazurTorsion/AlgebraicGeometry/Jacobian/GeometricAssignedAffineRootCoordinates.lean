/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphNeighborhood
import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineChart

/-!
# Independent root coordinates on a geometric assigned affine chart

The affine assigned chart retains one independently varying coordinate for
every ordered occurrence.  After its finite étale selected-component product
is split over the common block-refinement cover, every tuple sheet projects
to a genuine curve sheet for each occurrence.  This file proves that the
affine-line coordinate of that curve sheet is exactly the corresponding
independent occurrence coordinate on the refinement base.

Unlike specialization to the coherent support point, this construction does
not identify repeated occurrences.  It is therefore the dimension-preserving
geometric input for the local incidence calculation in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineRootCoordinates

open GeometricAssignedAffineChart
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

/-- The block-refinement cover, viewed as a morphism to the unrestricted
occurrence-wise affine coordinate base. -/
noncomputable def refinementToBase :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (commonAffineBase K C d z).left :=
  (componentFpqcBlockRefinement K C d z hVs q).hom ≫ V.ι

/-- The `j`-th tuple sheet as a section of the transported split source. -/
noncomputable def tupleSheetSection (j : Fin m) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (componentFpqcBlockSplitSource K C d z hVs q).left :=
  (sheetInclusion
      (componentFpqcBlockRefinement K C d z hVs q).left m j).left ≫
    (componentFpqcBlockSplitIso K C d z hVs q m E hE).inv.left

/-- A tuple sheet is a section over the block-refinement base. -/
@[reassoc]
theorem tupleSheetSection_comp_structure (j : Fin m) :
    tupleSheetSection K C d z hVs q m E hE j ≫
        (componentFpqcBlockSplitSource K C d z hVs q).hom =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left := by
  rw [tupleSheetSection, Category.assoc,
    (componentFpqcBlockSplitIso K C d z hVs q m E hE).inv.w]
  exact (sheetInclusion
    (componentFpqcBlockRefinement K C d z hVs q).left m j).w

/-- Map a tuple sheet back to the restricted occurrence-wise selected
component product. -/
noncomputable def tupleSheetToComponentPreimage (j : Fin m) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme :=
  tupleSheetSection K C d z hVs q m E hE j ≫
    componentFpqcBlockSplitSourceToComponentPreimage K C d z hVs q

/-- The tuple sheet lies over the refinement cover of the restricted affine
base. -/
@[reassoc]
theorem tupleSheetToComponentPreimage_comp_restrictedBase (j : Fin m) :
    tupleSheetToComponentPreimage K C d z hVs q m E hE j ≫
        ((componentToBasePower K C d z).left ∣_ V) =
      (componentFpqcBlockRefinement K C d z hVs q).hom := by
  rw [tupleSheetToComponentPreimage, Category.assoc,
    componentFpqcBlockSplitSourceToComponentPreimage_comp]
  rw [← Category.assoc, tupleSheetSection_comp_structure,
    Category.id_comp]

/-- Map a tuple sheet into the unrestricted occurrence-wise selected
component product. -/
noncomputable def tupleSheetToComponent (j : Fin m) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (commonAffineComponent K C d z).left :=
  tupleSheetToComponentPreimage K C d z hVs q m E hE j ≫
    ((componentToBasePower K C d z).left ⁻¹ᵁ V).ι

/-- The tuple sheet maps to its occurrence-wise affine base through the
block-refinement cover. -/
@[reassoc]
theorem tupleSheetToComponent_comp_base (j : Fin m) :
    tupleSheetToComponent K C d z hVs q m E hE j ≫
        (componentToBasePower K C d z).left =
      refinementToBase K C d z hVs q := by
  let sheet := tupleSheetToComponentPreimage K C d z hVs q m E hE j
  let f := (componentToBasePower K C d z).left
  let fV := f ∣_ V
  calc
    tupleSheetToComponent K C d z hVs q m E hE j ≫ f =
        (sheet ≫ (f ⁻¹ᵁ V).ι) ≫ f := rfl
    _ = sheet ≫ ((f ⁻¹ᵁ V).ι ≫ f) := Category.assoc _ _ _
    _ = sheet ≫ (fV ≫ V.ι) :=
      congrArg (fun g ↦ sheet ≫ g) (morphismRestrict_ι f V).symm
    _ = (sheet ≫ fV) ≫ V.ι := (Category.assoc _ _ _).symm
    _ = (componentFpqcBlockRefinement K C d z hVs q).hom ≫ V.ι :=
      congrArg (fun g ↦ g ≫ V.ι)
        (tupleSheetToComponentPreimage_comp_restrictedBase
          K C d z hVs q m E hE j)
    _ = refinementToBase K C d z hVs q := rfl

/-- The independent affine-line coordinate of occurrence `i` on the
block-refinement base. -/
noncomputable def occurrenceCoordinate (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (coordinateLine K).left :=
  refinementToBase K C d z hVs q ≫
    (toCoordinatePower K C d z).left ≫
      (Pi.π (fun _ : Fin d ↦ coordinateLine K) i).left

/-- Project a tuple sheet to the selected affine curve component belonging
to occurrence `i`. -/
noncomputable def tupleSheetToOccurrenceComponent (j : Fin m) (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (affineComponentFamily K C d z
        (geometricPointSupportIndex K C d z i)).left :=
  tupleSheetToComponent K C d z hVs q m E hE j ≫
    (Pi.π (fun i : Fin d ↦ affineComponentFamily K C d z
      (geometricPointSupportIndex K C d z i)) i).left

/-- On every tuple sheet, the selected curve component at occurrence `i`
has exactly the independently varying occurrence coordinate. -/
theorem tupleSheetToOccurrenceComponent_comp_coordinate
    (j : Fin m) (i : Fin d) :
    tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i ≫
        (affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left =
      occurrenceCoordinate K C d z hVs q i := by
  have hcomponent :
      (componentToCoordinatePower K C d z).left ≫
          (Pi.π (fun _ : Fin d ↦ coordinateLine K) i).left =
        (Pi.π (fun i : Fin d ↦ affineComponentFamily K C d z
          (geometricPointSupportIndex K C d z i)) i).left ≫
            (affineComponentToCoordinateLine K C d z
              (geometricPointSupportIndex K C d z i)).left := by
    exact congrArg Over.Hom.left
      (componentToCoordinatePower_comp_projection K C d z i)
  have hfactor :
      (componentToBasePower K C d z).left ≫
          (toCoordinatePower K C d z).left =
        (componentToCoordinatePower K C d z).left := by
    exact congrArg Over.Hom.left
      (componentToBasePower_comp_toCoordinatePower K C d z)
  calc
    tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i ≫
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left =
        tupleSheetToComponent K C d z hVs q m E hE j ≫
          ((componentToCoordinatePower K C d z).left ≫
            (Pi.π (fun _ : Fin d ↦ coordinateLine K) i).left) := by
      rw [tupleSheetToOccurrenceComponent, Category.assoc, ← hcomponent]
    _ = tupleSheetToComponent K C d z hVs q m E hE j ≫
          (((componentToBasePower K C d z).left ≫
            (toCoordinatePower K C d z).left) ≫
              (Pi.π (fun _ : Fin d ↦ coordinateLine K) i).left) := by
      rw [hfactor]
    _ = (tupleSheetToComponent K C d z hVs q m E hE j ≫
          (componentToBasePower K C d z).left) ≫
            (toCoordinatePower K C d z).left ≫
              (Pi.π (fun _ : Fin d ↦ coordinateLine K) i).left := by
      simp only [Category.assoc]
    _ = occurrenceCoordinate K C d z hVs q i := by
      rw [tupleSheetToComponent_comp_base]
      rfl

/-- Every independent occurrence coordinate has the common structural
composite from the block-refinement base to the coordinate ground scheme. -/
theorem occurrenceCoordinate_comp_coordinateLine (i : Fin d) :
    occurrenceCoordinate K C d z hVs q i ≫ (coordinateLine K).hom =
      refinementToBase K C d z hVs q ≫
        (commonAffineBase K C d z).hom := by
  have h :
      ((toCoordinatePower K C d z).left ≫
          (Pi.π (fun _ : Fin d ↦ coordinateLine K) i).left) ≫
        (coordinateLine K).hom = (commonAffineBase K C d z).hom := by
    exact (toCoordinatePower K C d z ≫
      Pi.π (fun _ : Fin d ↦ coordinateLine K) i).w
  calc
    occurrenceCoordinate K C d z hVs q i ≫ (coordinateLine K).hom =
        refinementToBase K C d z hVs q ≫
          (((toCoordinatePower K C d z).left ≫
            (Pi.π (fun _ : Fin d ↦ coordinateLine K) i).left) ≫
              (coordinateLine K).hom) := by
      simp only [occurrenceCoordinate, Category.assoc]
    _ = refinementToBase K C d z hVs q ≫
        (commonAffineBase K C d z).hom := congrArg _ h

/-- The relative affine curve-component ambient for occurrence `i`, before
imposing equality with its independent root coordinate.  Occurrences with
the same support owner use the same curve-family factor and differ only in
their coordinate map from the refinement base. -/
noncomputable abbrev occurrenceAmbient (i : Fin d) : Scheme.{u} :=
  ambient (coordinateLine K).hom
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCoordinate K C d z hVs q i)

/-- The common affine curve-family ambient for one geometric support owner.
All occurrence coordinates with this owner have canonically isomorphic
ambients of this form. -/
noncomputable abbrev supportAmbient
    (a : Fin (geometricDistinctSupportCard K C d z)) : Scheme.{u} :=
  pullback
    ((affineComponentToCoordinateLine K C d z a).left ≫
      (coordinateLine K).hom)
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom)

/-- The occurrence-specific ambient is canonically the common affine
curve-family ambient of its geometric support owner. -/
noncomputable def occurrenceAmbientIsoSupportAmbient (i : Fin d) :
    occurrenceAmbient K C d z hVs q i ≅
      supportAmbient K C d z hVs q
        (geometricPointSupportIndex K C d z i) :=
  pullback.congrHom rfl
    (occurrenceCoordinate_comp_coordinateLine K C d z hVs q i)

/-- Transport an isolating occurrence open into its support-indexed affine
curve-family ambient. -/
noncomputable abbrev occurrenceOpenOnSupportAmbient (i : Fin d)
    (U : (occurrenceAmbient K C d z hVs q i).Opens) :
    (supportAmbient K C d z hVs q
      (geometricPointSupportIndex K C d z i)).Opens :=
  (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).inv ⁻¹ᵁ U

/-- Transport identifies the schemes carried by the two occurrence-open
presentations. -/
noncomputable def occurrenceOpenIso (i : Fin d)
    (U : (occurrenceAmbient K C d z hVs q i).Opens) :
    U.toScheme ≅
      (occurrenceOpenOnSupportAmbient K C d z hVs q i U).toScheme :=
  (Scheme.Hom.preimageIso
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).inv U).symm

@[reassoc]
theorem occurrenceOpenIso_hom_comp_ι (i : Fin d)
    (U : (occurrenceAmbient K C d z hVs q i).Opens) :
    (occurrenceOpenIso K C d z hVs q i U).hom ≫
        (occurrenceOpenOnSupportAmbient K C d z hVs q i U).ι =
      U.ι ≫ (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom := by
  apply (cancel_mono
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (Scheme.Hom.preimageIso
      (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).inv U).inv ≫
      ((occurrenceAmbientIsoSupportAmbient K C d z hVs q i).inv
        ⁻¹ᵁ U).ι ≫
      (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).inv = U.ι
  exact Scheme.Hom.preimageIso_inv_ι
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).inv U

/-- The equal-coordinate closed locus for one independently varying ordered
occurrence. -/
noncomputable abbrev occurrenceEqualCoordinateInclusion (i : Fin d) :
    pullback
        (affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left
        (occurrenceCoordinate K C d z hVs q i) ⟶
      occurrenceAmbient K C d z hVs q i :=
  equalCoordinateInclusion (coordinateLine K).hom
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCoordinate K C d z hVs q i)

/-- The occurrence projection of a split tuple sheet, embedded as a graph
in its equal-coordinate locus. -/
noncomputable abbrev occurrenceGraph (j : Fin m) (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      pullback
        (affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left
        (occurrenceCoordinate K C d z hVs q i) :=
  graph
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCoordinate K C d z hVs q i)
    (tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i)
    (tupleSheetToOccurrenceComponent_comp_coordinate
      K C d z hVs q m E hE j i)

/-- Transport the selected tuple-sheet graph factorization into the common
support-indexed affine curve-family ambient. -/
noncomputable def graphToSupportOpen (i : Fin d)
    (U : (occurrenceAmbient K C d z hVs q i).Opens)
    (graphToU :
      (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      (occurrenceOpenOnSupportAmbient K C d z hVs q i U).toScheme :=
  graphToU ≫ (occurrenceOpenIso K C d z hVs q i U).hom

/-- A graph-isolating pullback square remains a pullback square after
transport to the common support-indexed affine curve-family ambient. -/
theorem transport_isPullback (j : Fin m) (i : Fin d)
    (U : (occurrenceAmbient K C d z hVs q i).Opens)
    (graphToU :
      (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme)
    (h : IsPullback graphToU
      (occurrenceGraph K C d z hVs q m E hE j i) U.ι
      (occurrenceEqualCoordinateInclusion K C d z hVs q i)) :
    IsPullback
      (graphToSupportOpen K C d z hVs q i U graphToU)
      (occurrenceGraph K C d z hVs q m E hE j i)
      (occurrenceOpenOnSupportAmbient K C d z hVs q i U).ι
      (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom) := by
  exact h.of_iso (Iso.refl _)
    (occurrenceOpenIso K C d z hVs q i U)
    (Iso.refl _)
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i)
    rfl (by simp) (occurrenceOpenIso_hom_comp_ι K C d z hVs q i U).symm
    (by simp)

/-- On a transported support-ambient open, the equal-coordinate ideal is
still exactly the selected tuple-sheet graph ideal. -/
theorem transport_ideal (j : Fin m) (i : Fin d)
    (U : (occurrenceAmbient K C d z hVs q i).Opens)
    (graphToU :
      (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme)
    (h : IsPullback
      (graphToSupportOpen K C d z hVs q i U graphToU)
      (occurrenceGraph K C d z hVs q m E hE j i)
      (occurrenceOpenOnSupportAmbient K C d z hVs q i U).ι
      (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom)) :
    (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom).ker.comap
        (occurrenceOpenOnSupportAmbient K C d z hVs q i U).ι =
      (graphToSupportOpen K C d z hVs q i U graphToU).ker := by
  let inclusion := occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom
  let openι := (occurrenceOpenOnSupportAmbient K C d z hVs q i U).ι
  let graphToOpen := graphToSupportOpen K C d z hVs q i U graphToU
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  letI : IsClosedImmersion
      (occurrenceEqualCoordinateInclusion K C d z hVs q i) := by
    exact equalCoordinateInclusion_closed
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
    _ = (h.isoPullback.hom ≫ pullback.fst openι inclusion).ker :=
      (Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom
        (pullback.fst openι inclusion)).symm
    _ = graphToOpen.ker := by
      rw [h.isoPullback_hom_fst]

/-- Around every occurrence projection of a split tuple sheet, there is an
open affine-curve-family neighbourhood in which the whole equal-coordinate
locus is exactly that graph. -/
theorem exists_occurrenceOpen_graph_isPullback (j : Fin m) (i : Fin d) :
    ∃ (W : Scheme.{u})
      (F : pullback
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) ≅
        (componentFpqcBlockRefinement K C d z hVs q).left ⨿ W)
      (U : (occurrenceAmbient K C d z hVs q i).Opens)
      (graphToU :
        (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme),
      occurrenceGraph K C d z hVs q m E hE j i ≫ F.hom = coprod.inl ∧
      IsPullback graphToU
        (occurrenceGraph K C d z hVs q m E hE j i) U.ι
        (occurrenceEqualCoordinateInclusion K C d z hVs q i) := by
  letI : IsSeparated
      (affineComponentToCoordinateLine K C d z
        (geometricPointSupportIndex K C d z i)).left := by
    infer_instance
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  exact @exists_open_graph_isPullback _ _ _ _
    (coordinateLine K).hom
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (affineComponentToCoordinateLine_etale K C d z
      (geometricPointSupportIndex K C d z i))
    (show IsSeparated
      (affineComponentToCoordinateLine K C d z
        (geometricPointSupportIndex K C d z i)).left from inferInstance)
    (occurrenceCoordinate K C d z hVs q i)
    (tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i)
    (tupleSheetToOccurrenceComponent_comp_coordinate
      K C d z hVs q m E hE j i)
    (show IsSeparated (coordinateLine K).hom from inferInstance)

/-- The isolating occurrence neighbourhood identifies ideal sheaves: the
selected tuple-sheet graph ideal is the pullback of the equal-coordinate
ideal, with no specialization of the other ordered root coordinates. -/
theorem exists_occurrenceOpen_graphIdeal (j : Fin m) (i : Fin d) :
    ∃ (W : Scheme.{u})
      (F : pullback
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) ≅
        (componentFpqcBlockRefinement K C d z hVs q).left ⨿ W)
      (U : (occurrenceAmbient K C d z hVs q i).Opens)
      (graphToU :
        (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme),
      occurrenceGraph K C d z hVs q m E hE j i ≫ F.hom = coprod.inl ∧
      IsPullback graphToU
        (occurrenceGraph K C d z hVs q m E hE j i) U.ι
        (occurrenceEqualCoordinateInclusion K C d z hVs q i) ∧
      (occurrenceEqualCoordinateInclusion K C d z hVs q i).ker.comap U.ι =
        graphToU.ker := by
  obtain ⟨W, F, U, graphToU, hF, hU⟩ :=
    exists_occurrenceOpen_graph_isPullback
      K C d z hVs q m E hE j i
  refine ⟨W, F, U, graphToU, hF, hU, ?_⟩
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  exact equalCoordinateIdeal_comap_eq_graphToOpen_ker
    (coordinateLine K).hom
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCoordinate K C d z hVs q i)
    (tupleSheetToOccurrenceComponent K C d z hVs q m E hE j i)
    (tupleSheetToOccurrenceComponent_comp_coordinate
      K C d z hVs q m E hE j i) hU

/-- Every independently varying occurrence graph admits an isolating open
inside the one common affine curve-family ambient attached to its geometric
support owner.  Both the cartesian graph square and the exact ideal-sheaf
identity survive this transport. -/
theorem exists_supportOpen_graphIdeal (j : Fin m) (i : Fin d) :
    ∃ (W : Scheme.{u})
      (F : pullback
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) ≅
        (componentFpqcBlockRefinement K C d z hVs q).left ⨿ W)
      (U : (supportAmbient K C d z hVs q
        (geometricPointSupportIndex K C d z i)).Opens)
      (graphToU :
        (componentFpqcBlockRefinement K C d z hVs q).left ⟶ U.toScheme),
      occurrenceGraph K C d z hVs q m E hE j i ≫ F.hom = coprod.inl ∧
      IsPullback graphToU
        (occurrenceGraph K C d z hVs q m E hE j i) U.ι
        (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
          (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom) ∧
      (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
          (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom).ker.comap
          U.ι = graphToU.ker := by
  obtain ⟨W, F, U, graphToU, hF, hU, _⟩ :=
    exists_occurrenceOpen_graphIdeal K C d z hVs q m E hE j i
  let U' := occurrenceOpenOnSupportAmbient K C d z hVs q i U
  let graphToU' := graphToSupportOpen K C d z hVs q i U graphToU
  have hU' := transport_isPullback
    K C d z hVs q m E hE j i U graphToU hU
  refine ⟨W, F, U', graphToU', hF, hU', ?_⟩
  exact transport_ideal K C d z hVs q m E hE j i U graphToU hU'

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineRootCoordinates
