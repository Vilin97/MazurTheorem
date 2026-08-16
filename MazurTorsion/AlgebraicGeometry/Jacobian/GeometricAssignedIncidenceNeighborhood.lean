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
  pullback
    ((geometricDistinctCharts K C d z
      (geometricPointSupportIndex K C d z i)).sourceOver.hom)
    (baseCoordinate K C d z V T q i ≫ (coordinateLine K).hom)

/-- The common ambient for all occurrences assigned to one geometric
support member.  Its right structural morphism is written directly through
the coherent base's ground-field map and therefore does not depend on an
ordered occurrence. -/
noncomputable abbrev supportAmbient
    (j : Fin (geometricDistinctSupportCard K C d z)) : Scheme.{u} :=
  pullback
    ((geometricDistinctCharts K C d z) j).sourceOver.hom
    (coherentBaseToGround K C d z V (Spec (.of T)) q ≫
      (coordinateBaseIso K).inv)

/-- The support-indexed ambient retains its projection to the coherent
splitting base. -/
noncomputable def supportAmbientToBase
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    supportAmbient K C d z V T q j ⟶ base K C d z V T q :=
  pullback.snd
    ((geometricDistinctCharts K C d z) j).sourceOver.hom
    (coherentBaseToGround K C d z V (Spec (.of T)) q ≫
      (coordinateBaseIso K).inv)

/-- The occurrence-specific ambient is canonically the common ambient of
its assigned geometric support member. -/
noncomputable def occurrenceAmbientIsoSupportAmbient (i : Fin d) :
    occurrenceAmbient K C d z V T q i ≅
      supportAmbient K C d z V T q
        (geometricPointSupportIndex K C d z i) :=
  pullback.congrHom rfl
    (baseCoordinate_comp_coordinateLine K C d z V T q i)

@[reassoc]
theorem occurrenceAmbientIsoSupportAmbient_hom_snd (i : Fin d) :
    (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom ≫
        supportAmbientToBase K C d z V T q
          (geometricPointSupportIndex K C d z i) =
      pullback.snd
        ((geometricDistinctCharts K C d z
          (geometricPointSupportIndex K C d z i)).sourceOver.hom)
        (baseCoordinate K C d z V T q i ≫ (coordinateLine K).hom) := by
  simp only [occurrenceAmbientIsoSupportAmbient,
    supportAmbientToBase, pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_snd, Category.comp_id]

/-- Transport an occurrence neighbourhood to the common ambient of its
geometric support member. -/
noncomputable abbrev occurrenceOpenOnSupportAmbient (i : Fin d)
    (U : (occurrenceAmbient K C d z V T q i).Opens) :
    (supportAmbient K C d z V T q
      (geometricPointSupportIndex K C d z i)).Opens :=
  (occurrenceAmbientIsoSupportAmbient K C d z V T q i).inv ⁻¹ᵁ U

/-- The scheme carried by an occurrence neighbourhood is isomorphic to the
scheme carried by its transported support-ambient neighbourhood. -/
noncomputable def occurrenceOpenIso (i : Fin d)
    (U : (occurrenceAmbient K C d z V T q i).Opens) :
    U.toScheme ≅
      (occurrenceOpenOnSupportAmbient K C d z V T q i U).toScheme :=
  (Scheme.Hom.preimageIso
    (occurrenceAmbientIsoSupportAmbient K C d z V T q i).inv U).symm

@[reassoc]
theorem occurrenceOpenIso_hom_comp_ι (i : Fin d)
    (U : (occurrenceAmbient K C d z V T q i).Opens) :
    (occurrenceOpenIso K C d z V T q i U).hom ≫
        (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι =
      U.ι ≫
        (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom := by
  apply (cancel_mono
    (occurrenceAmbientIsoSupportAmbient K C d z V T q i).inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (Scheme.Hom.preimageIso
      (occurrenceAmbientIsoSupportAmbient K C d z V T q i).inv U).inv ≫
      ((occurrenceAmbientIsoSupportAmbient K C d z V T q i).inv
        ⁻¹ᵁ U).ι ≫
      (occurrenceAmbientIsoSupportAmbient K C d z V T q i).inv = U.ι
  exact Scheme.Hom.preimageIso_inv_ι
    (occurrenceAmbientIsoSupportAmbient K C d z V T q i).inv U

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

/-- After transport to the support-indexed ambient, the equal-coordinate
inclusion still projects to the coherent base through the second projection
of its defining fiber product. -/
@[reassoc]
theorem supportEqualCoordinateInclusion_comp_base (i : Fin d) :
    (occurrenceEqualCoordinateInclusion K C d z V T q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom) ≫
      supportAmbientToBase K C d z V T q
        (geometricPointSupportIndex K C d z i) =
    pullback.snd
      ((geometricDistinctCharts K C d z)
        (geometricPointSupportIndex K C d z i)).schemeMap
      (baseCoordinate K C d z V T q i) := by
  rw [Category.assoc,
    occurrenceAmbientIsoSupportAmbient_hom_snd]
  exact equalCoordinateInclusion_snd
    (coordinateLine K).hom
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

@[reassoc]
theorem occurrenceGraph_comp_snd (i : Fin d) :
    occurrenceGraph K C d z V T q r E hE w i ≫
        pullback.snd
          ((geometricDistinctCharts K C d z)
            (geometricPointSupportIndex K C d z i)).schemeMap
          (baseCoordinate K C d z V T q i) =
      𝟙 (base K C d z V T q) :=
  pullback.lift_snd _ _ _

/-- Transport a factorization of the selected graph through an occurrence
neighbourhood into the common support ambient. -/
noncomputable def graphToSupportOpen (i : Fin d)
    (U : (occurrenceAmbient K C d z V T q i).Opens)
    (graphToU : base K C d z V T q ⟶ U.toScheme) :
    base K C d z V T q ⟶
      (occurrenceOpenOnSupportAmbient K C d z V T q i U).toScheme :=
  graphToU ≫ (occurrenceOpenIso K C d z V T q i U).hom

/-- Any transported graph neighbourhood supplied by the public existence
theorem is a neighbourhood over the coherent base with the selected graph
as a section. -/
theorem supportGraphToOpen_comp_base (i : Fin d)
    (U : (supportAmbient K C d z V T q
      (geometricPointSupportIndex K C d z i)).Opens)
    (graphToU : base K C d z V T q ⟶ U.toScheme)
    (h : IsPullback graphToU
      (occurrenceGraph K C d z V T q r E hE w i) U.ι
      (occurrenceEqualCoordinateInclusion K C d z V T q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom)) :
    graphToU ≫ U.ι ≫
        supportAmbientToBase K C d z V T q
          (geometricPointSupportIndex K C d z i) =
      𝟙 (base K C d z V T q) := by
  let b := supportAmbientToBase K C d z V T q
    (geometricPointSupportIndex K C d z i)
  let inclusion := occurrenceEqualCoordinateInclusion K C d z V T q i ≫
    (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom
  let graph := occurrenceGraph K C d z V T q r E hE w i
  have hpullPost := congrArg (fun f ↦ f ≫ b) h.w
  have hsupp := supportEqualCoordinateInclusion_comp_base
    K C d z V T q i
  have hsuppPre := congrArg (fun f ↦ graph ≫ f) hsupp
  calc
    graphToU ≫ U.ι ≫ b = (graphToU ≫ U.ι) ≫ b :=
      (Category.assoc _ _ _).symm
    _ = (graph ≫ inclusion) ≫ b := hpullPost
    _ = graph ≫ (inclusion ≫ b) := Category.assoc _ _ _
    _ = graph ≫ pullback.snd
        ((geometricDistinctCharts K C d z)
          (geometricPointSupportIndex K C d z i)).schemeMap
        (baseCoordinate K C d z V T q i) := hsuppPre
    _ = 𝟙 (base K C d z V T q) :=
      occurrenceGraph_comp_snd K C d z V T q r E hE w i

/-- The selected graph is a section of its transported neighbourhood over
the coherent base.  This is the input needed to compare all occurrence
neighbourhoods inside the common support-indexed curve ambient. -/
theorem graphToSupportOpen_comp_base (i : Fin d)
    (U : (occurrenceAmbient K C d z V T q i).Opens)
    (graphToU : base K C d z V T q ⟶ U.toScheme)
    (h : IsPullback graphToU
      (occurrenceGraph K C d z V T q r E hE w i) U.ι
      (occurrenceEqualCoordinateInclusion K C d z V T q i)) :
    graphToSupportOpen K C d z V T q i U graphToU ≫
        (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι ≫
          supportAmbientToBase K C d z V T q
            (geometricPointSupportIndex K C d z i) =
      𝟙 (base K C d z V T q) := by
  let e := occurrenceAmbientIsoSupportAmbient K C d z V T q i
  let b := supportAmbientToBase K C d z V T q
    (geometricPointSupportIndex K C d z i)
  let inclusion := occurrenceEqualCoordinateInclusion K C d z V T q i
  let graph := occurrenceGraph K C d z V T q r E hE w i
  have hopen := occurrenceOpenIso_hom_comp_ι_assoc
    K C d z V T q i U b
  have hopenPre := congrArg (fun f ↦ graphToU ≫ f) hopen
  have hpullPost := congrArg (fun f ↦ f ≫ e.hom ≫ b) h.w
  have hsupp := supportEqualCoordinateInclusion_comp_base
    K C d z V T q i
  have hsuppPre := congrArg (fun f ↦ graph ≫ f) hsupp
  calc
    graphToSupportOpen K C d z V T q i U graphToU ≫
          (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι ≫ b =
        graphToU ≫
          ((occurrenceOpenIso K C d z V T q i U).hom ≫
            (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι ≫ b) := by
      simp only [graphToSupportOpen, Category.assoc]
    _ = graphToU ≫ (U.ι ≫ e.hom ≫ b) := hopenPre
    _ = (graphToU ≫ U.ι) ≫ e.hom ≫ b := by
      simp only [Category.assoc]
    _ = (graph ≫ inclusion) ≫ e.hom ≫ b := hpullPost
    _ = graph ≫ ((inclusion ≫ e.hom) ≫ b) := by
      simp only [Category.assoc]
    _ = graph ≫ pullback.snd
        ((geometricDistinctCharts K C d z)
          (geometricPointSupportIndex K C d z i)).schemeMap
        (baseCoordinate K C d z V T q i) := hsuppPre
    _ = 𝟙 (base K C d z V T q) :=
      occurrenceGraph_comp_snd K C d z V T q r E hE w i

/-- Pullback squares isolating a selected graph remain pullback squares
after transporting the ambient and its open neighbourhood by the canonical
occurrence-to-support isomorphism. -/
theorem transport_isPullback (i : Fin d)
    (U : (occurrenceAmbient K C d z V T q i).Opens)
    (graphToU : base K C d z V T q ⟶ U.toScheme)
    (h : IsPullback graphToU
      (occurrenceGraph K C d z V T q r E hE w i) U.ι
      (occurrenceEqualCoordinateInclusion K C d z V T q i)) :
    IsPullback
      (graphToSupportOpen K C d z V T q i U graphToU)
      (occurrenceGraph K C d z V T q r E hE w i)
      (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι
      (occurrenceEqualCoordinateInclusion K C d z V T q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom) := by
  exact h.of_iso (Iso.refl _)
    (occurrenceOpenIso K C d z V T q i U)
    (Iso.refl _)
    (occurrenceAmbientIsoSupportAmbient K C d z V T q i)
    rfl (by simp) (occurrenceOpenIso_hom_comp_ι K C d z V T q i U).symm
    (by simp)

/-- On a transported support-ambient neighbourhood, the transported
equal-coordinate ideal is still exactly the selected graph ideal. -/
theorem transport_ideal (i : Fin d)
    (U : (occurrenceAmbient K C d z V T q i).Opens)
    (graphToU : base K C d z V T q ⟶ U.toScheme)
    (h : IsPullback
      (graphToSupportOpen K C d z V T q i U graphToU)
      (occurrenceGraph K C d z V T q r E hE w i)
      (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι
      (occurrenceEqualCoordinateInclusion K C d z V T q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom)) :
    (occurrenceEqualCoordinateInclusion K C d z V T q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom).ker.comap
        (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι =
      (graphToSupportOpen K C d z V T q i U graphToU).ker := by
  let inclusion := occurrenceEqualCoordinateInclusion K C d z V T q i ≫
    (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom
  let openι := (occurrenceOpenOnSupportAmbient K C d z V T q i U).ι
  let graphToOpen := graphToSupportOpen K C d z V T q i U graphToU
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  letI : IsClosedImmersion
      (occurrenceEqualCoordinateInclusion K C d z V T q i) := by
    change IsClosedImmersion
      (equalCoordinateInclusion
        (coordinateLine K).hom
        ((geometricDistinctCharts K C d z)
          (geometricPointSupportIndex K C d z i)).schemeMap
        (baseCoordinate K C d z V T q i))
    exact equalCoordinateInclusion_closed
      (coordinateLine K).hom
      ((geometricDistinctCharts K C d z)
        (geometricPointSupportIndex K C d z i)).schemeMap
      (baseCoordinate K C d z V T q i)
  letI : IsClosedImmersion inclusion := by
    dsimp only [inclusion]
    rw [MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
      (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom]
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

/-- Every occurrence-level isolating neighbourhood can be expressed in the
single ambient attached to its geometric support member.  Both the pullback
square and the scheme-theoretic graph-ideal identity survive transport.
This is the interface used by the subsequent finite common-refinement step. -/
theorem exists_supportOpen_graphIdeal (i : Fin d) :
    ∃ (W : Scheme.{u})
      (F : pullback
          ((geometricDistinctCharts K C d z)
            (geometricPointSupportIndex K C d z i)).schemeMap
          (baseCoordinate K C d z V T q i) ≅
        base K C d z V T q ⨿ W)
      (U : (supportAmbient K C d z V T q
        (geometricPointSupportIndex K C d z i)).Opens)
      (graphToU : base K C d z V T q ⟶ U.toScheme),
      occurrenceGraph K C d z V T q r E hE w i ≫ F.hom = coprod.inl ∧
      IsPullback graphToU
        (occurrenceGraph K C d z V T q r E hE w i) U.ι
        (occurrenceEqualCoordinateInclusion K C d z V T q i ≫
          (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom) ∧
      (occurrenceEqualCoordinateInclusion K C d z V T q i ≫
          (occurrenceAmbientIsoSupportAmbient K C d z V T q i).hom).ker.comap
          U.ι = graphToU.ker := by
  obtain ⟨W, F, U, graphToU, hF, hU, _⟩ :=
    exists_occurrenceOpen_graphIdeal K C d z V T q r E hE w i
  let U' := occurrenceOpenOnSupportAmbient K C d z V T q i U
  let graphToU' := graphToSupportOpen K C d z V T q i U graphToU
  have hU' := transport_isPullback
    K C d z V T q r E hE w i U graphToU hU
  refine ⟨W, F, U', graphToU', hF, hU', ?_⟩
  exact transport_ideal
    K C d z V T q r E hE w i U graphToU hU'

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedIncidenceNeighborhood
