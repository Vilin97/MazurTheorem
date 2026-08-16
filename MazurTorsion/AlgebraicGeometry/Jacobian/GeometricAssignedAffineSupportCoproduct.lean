/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSimultaneousNeighborhood
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleCoproductPower
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineIdealSheafPullback
import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleQuotientProduct

/-!
# The affine support coproduct for an assigned graph chart

Simultaneous affine graph data gives one affine base open and one affine
support open for every geometric support member.  This file pulls every
support open to that common base and forms their finite disjoint union.
Every ordered occurrence graph becomes a section of the appropriate pulled
back support piece and hence a morphism into its assigned coproduct summand.
The whole coproduct also maps canonically to the original disjoint family of
selected affine curve components.

The named downstream consumer is `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSupportCoproduct

open FiniteEtaleCoproductPower
open AffineIdealSheafPullback
open EtaleQuotientProduct
open EqualCoordinateClosedImmersion
open FiniteSupportEtaleCoordinates
open GeometricAssignedAffineChart
open GeometricAssignedAffineRootCoordinates
open GeometricAssignedSimultaneousGraphNeighborhood
open GeometricAssignedAffineSimultaneousNeighborhood
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
variable {hmem : exactCommonAffineBasePoint K C d z ∈ V}
variable {s : (componentFpqcBlockRefinement K C d z hVs q).left}
variable {j : Fin m}
variable {hj : tupleSheetToComponentPreimage K C d z hVs q m E hE j s =
  commonAffineComponentPointInPreimage K C d z hmem}
variable (N : SimultaneousAffineGraphNeighborhood
  K C d z hVs q m E hE hmem s j hj)

/-- The affine chart base mapped back to the common coordinate ground
scheme. -/
noncomputable def baseToCoordinateBase :
    N.baseOpen.toScheme ⟶ coordinateBase K :=
  N.baseOpen.ι ≫ refinementToBase K C d z hVs q ≫
    (commonAffineBase K C d z).hom

/-- Pull one chosen affine support open to the common affine chart base. -/
noncomputable abbrev supportPiece
    (a : Fin (geometricDistinctSupportCard K C d z)) : Scheme.{u} :=
  pullback
    ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
    N.baseOpen.ι

/-- A pulled-back support piece, regarded over the common affine base. -/
noncomputable abbrev supportPieceFamily
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Over N.baseOpen.toScheme :=
  Over.mk (pullback.snd
    ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
    N.baseOpen.ι)

/-- When the block-refinement ambient is affine—as it is on the finite
étale fpqc chart used downstream—every pulled-back support piece is affine. -/
theorem supportPiece_isAffine
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    IsAffine (supportPiece K C d z hVs q m E hE N a) := by
  letI : IsAffine N.baseOpen.toScheme := N.base_isAffine
  letI : IsAffine (N.supportOpen a).toScheme := N.support_isAffine a
  infer_instance

/-- The restricted occurrence graph lifted into its support piece over the
common affine base. -/
noncomputable def graphToSupportPiece
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    N.baseOpen.toScheme ⟶ supportPiece K C d z hVs q m E hE N a :=
  pullback.lift
    (N.graph K C d z hVs q m E hE a i)
    (𝟙 _)
    (by
      simpa only [Category.id_comp] using
        N.graph_comp_base K C d z hVs q m E hE a i)

@[reassoc]
theorem graphToSupportPiece_comp_fst
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportPiece K C d z hVs q m E hE N a i ≫
        pullback.fst
          ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι =
      N.graph K C d z hVs q m E hE a i :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem graphToSupportPiece_comp_snd
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportPiece K C d z hVs q m E hE N a i ≫
        (supportPieceFamily K C d z hVs q m E hE N a).hom =
      𝟙 N.baseOpen.toScheme :=
  pullback.lift_snd _ _ _

/-- Include a chosen affine support open in the simultaneous isolating
intersection from which it was selected. -/
noncomputable def supportOpenToIntersection
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (N.supportOpen a).toScheme ⟶
      (supportIntersectionOpen K C d z hVs q m E hE j a).toScheme :=
  (supportAmbient K C d z hVs q a).homOfLE
    (N.support_le_intersection a)

@[reassoc]
theorem supportOpenToIntersection_comp_ι
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportOpenToIntersection K C d z hVs q m E hE N a ≫
      (supportIntersectionOpen K C d z hVs q m E hE j a).ι =
      (N.supportOpen a).ι :=
  Scheme.homOfLE_ι (supportAmbient K C d z hVs q a)
    (N.support_le_intersection a)

/-- The graph ideal for one occurrence, restricted from the simultaneous
support intersection to its chosen affine support open. -/
noncomputable def supportOpenGraphIdeal
    (i : Fin d) :
    Scheme.IdealSheafData
      (N.supportOpen (geometricPointSupportIndex K C d z i)).toScheme :=
  (supportIntersectionGraphι K C d z hVs q m E hE j i).ker.comap
    (supportOpenToIntersection K C d z hVs q m E hE N
      (geometricPointSupportIndex K C d z i))

/-- On every chosen affine support open, the occurrence equal-coordinate
ideal remains exactly the selected graph ideal restricted from the
simultaneous intersection. -/
theorem supportOpen_equalCoordinateIdeal
    (i : Fin d) :
    (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom).ker.comap
        (N.supportOpen (geometricPointSupportIndex K C d z i)).ι =
      supportOpenGraphIdeal K C d z hVs q m E hE N i := by
  rw [← supportOpenToIntersection_comp_ι
    K C d z hVs q m E hE N
      (geometricPointSupportIndex K C d z i),
    Scheme.IdealSheafData.comap_comp,
    supportIntersection_equalCoordinateIdeal]
  rfl

/-- The same graph ideal after pulling the affine support open to the final
common affine base. -/
noncomputable def supportPieceGraphIdeal
    (i : Fin d) :
    Scheme.IdealSheafData
      (supportPiece K C d z hVs q m E hE N
        (geometricPointSupportIndex K C d z i)) :=
  (supportOpenGraphIdeal K C d z hVs q m E hE N i).comap
    (pullback.fst
      ((N.supportOpen (geometricPointSupportIndex K C d z i)).ι ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i))
      N.baseOpen.ι)

/-- Pulling to the common affine base preserves the exact occurrence graph
ideal equality. -/
theorem supportPiece_equalCoordinateIdeal
    (i : Fin d) :
    (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom).ker.comap
        (pullback.fst
            ((N.supportOpen
                (geometricPointSupportIndex K C d z i)).ι ≫
              supportAmbientToBase K C d z hVs q
                (geometricPointSupportIndex K C d z i))
            N.baseOpen.ι ≫
          (N.supportOpen
            (geometricPointSupportIndex K C d z i)).ι) =
      supportPieceGraphIdeal K C d z hVs q m E hE N i := by
  rw [Scheme.IdealSheafData.comap_comp,
    supportOpen_equalCoordinateIdeal]
  rfl

/-- On global sections of an affine support piece, its occurrence graph
ideal is the extension of the graph ideal on the chosen affine support open.
This is the section-ring bridge consumed by the later graph-product
comparison. -/
theorem supportPieceGraphIdeal_top_eq_map
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (i : Fin d) :
    (supportPieceGraphIdeal K C d z hVs q m E hE N i).ideal
        ⟨⊤, @isAffineOpen_top _
          (supportPiece_isAffine K C d z hVs q m E hE N _)⟩ =
      Ideal.map
        (pullback.fst
          ((N.supportOpen
              (geometricPointSupportIndex K C d z i)).ι ≫
            supportAmbientToBase K C d z hVs q
              (geometricPointSupportIndex K C d z i))
          N.baseOpen.ι).appTop.hom
        ((supportOpenGraphIdeal K C d z hVs q m E hE N i).ideal
          ⟨⊤, @isAffineOpen_top _ (N.support_isAffine _)⟩) := by
  letI : IsAffine
      (supportPiece K C d z hVs q m E hE N
        (geometricPointSupportIndex K C d z i)) :=
    supportPiece_isAffine K C d z hVs q m E hE N _
  letI : IsAffine
      (N.supportOpen
        (geometricPointSupportIndex K C d z i)).toScheme :=
    N.support_isAffine _
  exact ideal_comap_top_eq_map_of_isAffine
    (supportOpenGraphIdeal K C d z hVs q m E hE N i)
    (pullback.fst
      ((N.supportOpen
          (geometricPointSupportIndex K C d z i)).ι ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i))
      N.baseOpen.ι)

/-- The restricted graph ideal of an occurrence, transported along the
proof that the occurrence is owned by a fixed support member. -/
noncomputable def supportOpenGraphIdealAt
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    Scheme.IdealSheafData (N.supportOpen a).toScheme := by
  rcases i with ⟨i, rfl⟩
  exact supportOpenGraphIdeal K C d z hVs q m E hE N i

/-- The corresponding graph ideal on the pulled-back affine support piece. -/
noncomputable def supportPieceGraphIdealAt
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    Scheme.IdealSheafData
      (supportPiece K C d z hVs q m E hE N a) := by
  rcases i with ⟨i, rfl⟩
  exact supportPieceGraphIdeal K C d z hVs q m E hE N i

/-- The fixed-owner form of an occurrence graph ideal is still its affine
support-open ideal pulled to the common base. -/
theorem supportPieceGraphIdealAt_eq_comap
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    supportPieceGraphIdealAt K C d z hVs q m E hE N a i =
      (supportOpenGraphIdealAt K C d z hVs q m E hE N a i).comap
        (pullback.fst
          ((N.supportOpen a).ι ≫
            supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι) := by
  rcases i with ⟨i, rfl⟩
  rfl

/-- The multiplicity-sensitive product of all occurrence graph ideals owned
by one chosen affine support open. -/
noncomputable def supportOpenGraphProductIdeal
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Scheme.IdealSheafData (N.supportOpen a).toScheme :=
  ∏ i : OccurrencesAtSupport K C d z a,
    supportOpenGraphIdealAt K C d z hVs q m E hE N a i

/-- The multiplicity-sensitive product of all occurrence graph ideals on
one pulled-back affine support piece. -/
noncomputable def supportPieceGraphProductIdeal
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Scheme.IdealSheafData
      (supportPiece K C d z hVs q m E hE N a) :=
  ∏ i : OccurrencesAtSupport K C d z a,
    supportPieceGraphIdealAt K C d z hVs q m E hE N a i

/-- Pulling a complete owner block to the common affine base preserves the
product of occurrence graph ideals, including every repeated occurrence. -/
theorem supportPieceGraphProductIdeal_eq_comap
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceGraphProductIdeal K C d z hVs q m E hE N a =
      (supportOpenGraphProductIdeal K C d z hVs q m E hE N a).comap
        (pullback.fst
          ((N.supportOpen a).ι ≫
            supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι) := by
  letI : IsAffine
      (supportPiece K C d z hVs q m E hE N a) :=
    supportPiece_isAffine K C d z hVs q m E hE N a
  letI : IsAffine (N.supportOpen a).toScheme := N.support_isAffine a
  rw [supportPieceGraphProductIdeal, supportOpenGraphProductIdeal,
    idealSheaf_comap_finsetProd_of_isAffine]
  apply Finset.prod_congr rfl
  intro i _
  exact supportPieceGraphIdealAt_eq_comap
    K C d z hVs q m E hE N a i

/-- On global sections, the complete occurrence product on an affine support
piece is extension of the complete product on its chosen affine support
open. -/
theorem supportPieceGraphProductIdeal_top_eq_map
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (supportPieceGraphProductIdeal K C d z hVs q m E hE N a).ideal
        ⟨⊤, @isAffineOpen_top _
          (supportPiece_isAffine K C d z hVs q m E hE N a)⟩ =
      Ideal.map
        (pullback.fst
          ((N.supportOpen a).ι ≫
            supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι).appTop.hom
        ((supportOpenGraphProductIdeal K C d z hVs q m E hE N a).ideal
          ⟨⊤, @isAffineOpen_top _ (N.support_isAffine a)⟩) := by
  letI : IsAffine
      (supportPiece K C d z hVs q m E hE N a) :=
    supportPiece_isAffine K C d z hVs q m E hE N a
  letI : IsAffine (N.supportOpen a).toScheme := N.support_isAffine a
  rw [supportPieceGraphProductIdeal_eq_comap]
  exact ideal_comap_top_eq_map_of_isAffine
    (supportOpenGraphProductIdeal K C d z hVs q m E hE N a)
    (pullback.fst
      ((N.supportOpen a).ι ≫
        supportAmbientToBase K C d z hVs q a)
      N.baseOpen.ι)

/-- Forget a pulled-back support piece to its original selected affine curve
component. -/
noncomputable def supportPieceToAffineComponent
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPiece K C d z hVs q m E hE N a ⟶
      (affineComponentFamily K C d z a).left :=
  pullback.fst
      ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
      N.baseOpen.ι ≫
    (N.supportOpen a).ι ≫
      pullback.fst
        ((affineComponentToCoordinateLine K C d z a).left ≫
          (coordinateLine K).hom)
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom)

/-- Forgetting a support piece to its selected affine component is compatible
with the common coordinate-base morphism. -/
@[reassoc]
theorem supportPieceToAffineComponent_comp_structure
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceToAffineComponent K C d z hVs q m E hE N a ≫
        (affineComponentFamily K C d z a).hom =
      (supportPieceFamily K C d z hVs q m E hE N a).hom ≫
        baseToCoordinateBase K C d z hVs q m E hE N := by
  have hAmbient :
      pullback.fst
          ((affineComponentToCoordinateLine K C d z a).left ≫
            (coordinateLine K).hom)
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) ≫
        ((affineComponentToCoordinateLine K C d z a).left ≫
          (coordinateLine K).hom) =
      pullback.snd
          ((affineComponentToCoordinateLine K C d z a).left ≫
            (coordinateLine K).hom)
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) ≫
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) :=
    pullback.condition
  have hPiece :
      pullback.fst
          ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι ≫
        ((N.supportOpen a).ι ≫
          supportAmbientToBase K C d z hVs q a) =
      pullback.snd
          ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι ≫ N.baseOpen.ι :=
    pullback.condition
  unfold supportPieceToAffineComponent baseToCoordinateBase
  rw [← (affineComponentToCoordinateLine K C d z a).w]
  simp only [Category.assoc]
  rw [hAmbient]
  change
    pullback.fst
          ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι ≫
        ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a) ≫
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      pullback.snd
          ((N.supportOpen a).ι ≫ supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι ≫
        N.baseOpen.ι ≫ refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom
  rw [← Category.assoc, hPiece]
  simp only [Category.assoc]

/-- The common affine line after base change to the block-refinement base,
before the final simultaneous affine shrinking. -/
noncomputable abbrev refinementAffineLine : Scheme.{u} :=
  pullback (coordinateLine K).hom
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom)

/-- The block-refinement affine line regarded over the refinement base. -/
noncomputable abbrev refinementAffineLineFamily :
    Over (componentFpqcBlockRefinement K C d z hVs q).left :=
  Over.mk (pullback.snd (coordinateLine K).hom
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom))

/-- Rewrite the occurrence-specific base change of the affine line using
the common structural map of the block-refinement base. -/
noncomputable def occurrenceRelativeTargetIsoRefinementAffineLine
    (i : Fin d) :
    relativeTarget (coordinateLine K).hom
        (occurrenceCoordinate K C d z hVs q i) ≅
      refinementAffineLine K C d z hVs q :=
  pullback.congrHom rfl
    (occurrenceCoordinate_comp_coordinateLine K C d z hVs q i)

@[reassoc]
theorem occurrenceRelativeTargetIsoRefinementAffineLine_hom_fst
    (i : Fin d) :
    (occurrenceRelativeTargetIsoRefinementAffineLine
        K C d z hVs q i).hom ≫
      pullback.fst (coordinateLine K).hom
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) =
    pullback.fst (coordinateLine K).hom
      (occurrenceCoordinate K C d z hVs q i ≫
        (coordinateLine K).hom) := by
  simp only [occurrenceRelativeTargetIsoRefinementAffineLine,
    pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem occurrenceRelativeTargetIsoRefinementAffineLine_hom_snd
    (i : Fin d) :
    (occurrenceRelativeTargetIsoRefinementAffineLine
        K C d z hVs q i).hom ≫
      pullback.snd (coordinateLine K).hom
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) =
    pullback.snd (coordinateLine K).hom
      (occurrenceCoordinate K C d z hVs q i ≫
        (coordinateLine K).hom) := by
  simp only [occurrenceRelativeTargetIsoRefinementAffineLine,
    pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem occurrenceRelativeTargetIsoRefinementAffineLine_hom_base
    (i : Fin d) :
    (occurrenceRelativeTargetIsoRefinementAffineLine
        K C d z hVs q i).hom ≫
      (refinementAffineLineFamily K C d z hVs q).hom =
    pullback.snd (coordinateLine K).hom
      (occurrenceCoordinate K C d z hVs q i ≫
        (coordinateLine K).hom) :=
  occurrenceRelativeTargetIsoRefinementAffineLine_hom_snd
    K C d z hVs q i

/-- The independently varying occurrence coordinate as a section of the
affine line over the block-refinement base. -/
noncomputable def refinementAffineLineGraph (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      refinementAffineLine K C d z hVs q :=
  relativeSection (coordinateLine K).hom
      (occurrenceCoordinate K C d z hVs q i) ≫
    (occurrenceRelativeTargetIsoRefinementAffineLine
      K C d z hVs q i).hom

@[reassoc]
theorem refinementAffineLineGraph_comp_fst (i : Fin d) :
    refinementAffineLineGraph K C d z hVs q i ≫
        pullback.fst (coordinateLine K).hom
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      occurrenceCoordinate K C d z hVs q i := by
  rw [refinementAffineLineGraph, Category.assoc,
    occurrenceRelativeTargetIsoRefinementAffineLine_hom_fst,
    relativeSection_fst]

@[reassoc]
theorem refinementAffineLineGraph_comp_base (i : Fin d) :
    refinementAffineLineGraph K C d z hVs q i ≫
        (refinementAffineLineFamily K C d z hVs q).hom =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left := by
  rw [refinementAffineLineGraph, Category.assoc,
    occurrenceRelativeTargetIsoRefinementAffineLine_hom_base,
    relativeSection_snd]

@[reassoc]
theorem refinementAffineLineGraph_comp_snd (i : Fin d) :
    refinementAffineLineGraph K C d z hVs q i ≫
        pullback.snd (coordinateLine K).hom
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left :=
  refinementAffineLineGraph_comp_base K C d z hVs q i

/-- The selected affine-component coordinate after base change to the
block-refinement base. -/
noncomputable def supportAmbientToRefinementAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportAmbient K C d z hVs q a ⟶
      refinementAffineLine K C d z hVs q :=
  pullback.lift
    (pullback.fst
        ((affineComponentToCoordinateLine K C d z a).left ≫
          (coordinateLine K).hom)
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) ≫
      (affineComponentToCoordinateLine K C d z a).left)
    (supportAmbientToBase K C d z hVs q a)
    (by
      rw [Category.assoc]
      exact pullback.condition)

@[reassoc]
theorem supportAmbientToRefinementAffineLine_comp_fst
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportAmbientToRefinementAffineLine K C d z hVs q a ≫
        pullback.fst (coordinateLine K).hom
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      pullback.fst
          ((affineComponentToCoordinateLine K C d z a).left ≫
            (coordinateLine K).hom)
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) ≫
        (affineComponentToCoordinateLine K C d z a).left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem supportAmbientToRefinementAffineLine_comp_base
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportAmbientToRefinementAffineLine K C d z hVs q a ≫
        (refinementAffineLineFamily K C d z hVs q).hom =
      supportAmbientToBase K C d z hVs q a :=
  pullback.lift_snd _ _ _

/-- Transporting an occurrence ambient to its support owner commutes with
the corresponding relative affine-line coordinate. -/
theorem occurrenceAmbientIso_comp_supportAmbientToRefinementAffineLine
    (i : Fin d) :
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
        supportAmbientToRefinementAffineLine K C d z hVs q
          (geometricPointSupportIndex K C d z i) =
      ambientToRelativeTarget
          (coordinateLine K).hom
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) ≫
        (occurrenceRelativeTargetIsoRefinementAffineLine
          K C d z hVs q i).hom := by
  apply pullback.hom_ext
  · calc
      ((occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
            supportAmbientToRefinementAffineLine K C d z hVs q
              (geometricPointSupportIndex K C d z i)) ≫
          pullback.fst (coordinateLine K).hom
            (refinementToBase K C d z hVs q ≫
              (commonAffineBase K C d z).hom) =
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
          (supportAmbientToRefinementAffineLine K C d z hVs q
              (geometricPointSupportIndex K C d z i) ≫
            pullback.fst (coordinateLine K).hom
              (refinementToBase K C d z hVs q ≫
                (commonAffineBase K C d z).hom)) :=
        Category.assoc _ _ _
      _ = (occurrenceAmbientIsoSupportAmbient
              K C d z hVs q i).hom ≫
          (pullback.fst
              ((affineComponentToCoordinateLine K C d z
                  (geometricPointSupportIndex K C d z i)).left ≫
                (coordinateLine K).hom)
              (refinementToBase K C d z hVs q ≫
                (commonAffineBase K C d z).hom) ≫
            (affineComponentToCoordinateLine K C d z
              (geometricPointSupportIndex K C d z i)).left) := by
        rw [supportAmbientToRefinementAffineLine_comp_fst]
      _ = ((occurrenceAmbientIsoSupportAmbient
                K C d z hVs q i).hom ≫
            pullback.fst
              ((affineComponentToCoordinateLine K C d z
                  (geometricPointSupportIndex K C d z i)).left ≫
                (coordinateLine K).hom)
              (refinementToBase K C d z hVs q ≫
                (commonAffineBase K C d z).hom)) ≫
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left :=
        (Category.assoc _ _ _).symm
      _ = pullback.fst
            ((affineComponentToCoordinateLine K C d z
                (geometricPointSupportIndex K C d z i)).left ≫
              (coordinateLine K).hom)
            (occurrenceCoordinate K C d z hVs q i ≫
              (coordinateLine K).hom) ≫
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left := by
        rw [occurrenceAmbientIsoSupportAmbient_hom_fst]
      _ = ambientToRelativeTarget
            (coordinateLine K).hom
            (affineComponentToCoordinateLine K C d z
              (geometricPointSupportIndex K C d z i)).left
            (occurrenceCoordinate K C d z hVs q i) ≫
          pullback.fst (coordinateLine K).hom
            (occurrenceCoordinate K C d z hVs q i ≫
              (coordinateLine K).hom) :=
        (ambientToRelativeTarget_fst _ _ _).symm
      _ = ambientToRelativeTarget
            (coordinateLine K).hom
            (affineComponentToCoordinateLine K C d z
              (geometricPointSupportIndex K C d z i)).left
            (occurrenceCoordinate K C d z hVs q i) ≫
          ((occurrenceRelativeTargetIsoRefinementAffineLine
                K C d z hVs q i).hom ≫
            pullback.fst (coordinateLine K).hom
              (refinementToBase K C d z hVs q ≫
                (commonAffineBase K C d z).hom)) := by
        rw [occurrenceRelativeTargetIsoRefinementAffineLine_hom_fst]
      _ = (ambientToRelativeTarget
              (coordinateLine K).hom
              (affineComponentToCoordinateLine K C d z
                (geometricPointSupportIndex K C d z i)).left
              (occurrenceCoordinate K C d z hVs q i) ≫
            (occurrenceRelativeTargetIsoRefinementAffineLine
              K C d z hVs q i).hom) ≫
          pullback.fst (coordinateLine K).hom
            (refinementToBase K C d z hVs q ≫
              (commonAffineBase K C d z).hom) :=
        (Category.assoc _ _ _).symm
  · calc
      ((occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
            supportAmbientToRefinementAffineLine K C d z hVs q
              (geometricPointSupportIndex K C d z i)) ≫
          (refinementAffineLineFamily K C d z hVs q).hom =
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
          (supportAmbientToRefinementAffineLine K C d z hVs q
              (geometricPointSupportIndex K C d z i) ≫
            (refinementAffineLineFamily K C d z hVs q).hom) :=
        Category.assoc _ _ _
      _ = (occurrenceAmbientIsoSupportAmbient
              K C d z hVs q i).hom ≫
          supportAmbientToBase K C d z hVs q
            (geometricPointSupportIndex K C d z i) := by
        rw [supportAmbientToRefinementAffineLine_comp_base]
      _ = pullback.snd
          ((affineComponentToCoordinateLine K C d z
              (geometricPointSupportIndex K C d z i)).left ≫
            (coordinateLine K).hom)
          (occurrenceCoordinate K C d z hVs q i ≫
            (coordinateLine K).hom) := by
        rw [occurrenceAmbientIsoSupportAmbient_hom_snd]
      _ = ambientToRelativeTarget
            (coordinateLine K).hom
            (affineComponentToCoordinateLine K C d z
              (geometricPointSupportIndex K C d z i)).left
            (occurrenceCoordinate K C d z hVs q i) ≫
          pullback.snd (coordinateLine K).hom
            (occurrenceCoordinate K C d z hVs q i ≫
              (coordinateLine K).hom) :=
        (ambientToRelativeTarget_snd _ _ _).symm
      _ = ambientToRelativeTarget
            (coordinateLine K).hom
            (affineComponentToCoordinateLine K C d z
              (geometricPointSupportIndex K C d z i)).left
            (occurrenceCoordinate K C d z hVs q i) ≫
          ((occurrenceRelativeTargetIsoRefinementAffineLine
                K C d z hVs q i).hom ≫
            (refinementAffineLineFamily K C d z hVs q).hom) := by
        rw [occurrenceRelativeTargetIsoRefinementAffineLine_hom_base]
      _ = (ambientToRelativeTarget
              (coordinateLine K).hom
              (affineComponentToCoordinateLine K C d z
                (geometricPointSupportIndex K C d z i)).left
              (occurrenceCoordinate K C d z hVs q i) ≫
            (occurrenceRelativeTargetIsoRefinementAffineLine
              K C d z hVs q i).hom) ≫
          (refinementAffineLineFamily K C d z hVs q).hom :=
        (Category.assoc _ _ _).symm

/-- For one occurrence, the transported equal-coordinate locus is the
inverse image of its independent section of the refinement affine line. -/
theorem supportEqualCoordinate_relativeSection_square (i : Fin d) :
    IsPullback
      (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom)
      (pullback.snd
        (affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left
        (occurrenceCoordinate K C d z hVs q i))
      (supportAmbientToRefinementAffineLine K C d z hVs q
        (geometricPointSupportIndex K C d z i))
      (refinementAffineLineGraph K C d z hVs q i) := by
  let h := equalCoordinate_relativeSection_square
    (coordinateLine K).hom
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCoordinate K C d z hVs q i)
  exact h.of_iso
    (Iso.refl _)
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i)
    (Iso.refl _)
    (occurrenceRelativeTargetIsoRefinementAffineLine
      K C d z hVs q i)
    (by simp)
    (by simp)
    (occurrenceAmbientIso_comp_supportAmbientToRefinementAffineLine
      K C d z hVs q i).symm
    (by simp [refinementAffineLineGraph])

/-- The equal-coordinate ideal on a support ambient is the inverse image of
the ideal of its independent affine-line section. -/
theorem refinementAffineLineGraph_ker_comap_supportAmbient
    (i : Fin d) :
    (refinementAffineLineGraph K C d z hVs q i).ker.comap
        (supportAmbientToRefinementAffineLine K C d z hVs q
          (geometricPointSupportIndex K C d z i)) =
      (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom).ker := by
  let graphHom := refinementAffineLineGraph K C d z hVs q i
  let familyHom := (refinementAffineLineFamily K C d z hVs q).hom
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  letI : IsSeparated familyHom := by
    change IsSeparated (pullback.snd (coordinateLine K).hom
      (refinementToBase K C d z hVs q ≫
        (commonAffineBase K C d z).hom))
    infer_instance
  letI : IsClosedImmersion graphHom := by
    haveI : IsClosedImmersion (graphHom ≫ familyHom) := by
      rw [show graphHom ≫ familyHom =
          𝟙 (componentFpqcBlockRefinement K C d z hVs q).left from
        refinementAffineLineGraph_comp_base K C d z hVs q i]
      infer_instance
    exact IsClosedImmersion.of_comp graphHom familyHom
  let h := supportEqualCoordinate_relativeSection_square
    K C d z hVs q i
  calc
    graphHom.ker.comap
        (supportAmbientToRefinementAffineLine K C d z hVs q
          (geometricPointSupportIndex K C d z i)) =
      (pullback.fst
        (supportAmbientToRefinementAffineLine K C d z hVs q
          (geometricPointSupportIndex K C d z i)) graphHom).ker :=
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
          graphHom
          (supportAmbientToRefinementAffineLine K C d z hVs q
            (geometricPointSupportIndex K C d z i))).symm
    _ = (h.isoPullback.hom ≫
        pullback.fst
          (supportAmbientToRefinementAffineLine K C d z hVs q
            (geometricPointSupportIndex K C d z i)) graphHom).ker :=
      (Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom
        (pullback.fst
          (supportAmbientToRefinementAffineLine K C d z hVs q
            (geometricPointSupportIndex K C d z i)) graphHom)).symm
    _ = (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom).ker := by
      rw [h.isoPullback_hom_fst]

/-- The coordinate map on the full support ambient is the base change of
the selected affine-component coordinate. -/
theorem supportAmbientToRefinementAffineLine_isPullback
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    IsPullback
      (supportAmbientToRefinementAffineLine K C d z hVs q a)
      (pullback.fst
        ((affineComponentToCoordinateLine K C d z a).left ≫
          (coordinateLine K).hom)
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom))
      (pullback.fst (coordinateLine K).hom
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom))
      (affineComponentToCoordinateLine K C d z a).left := by
  let hRight := (IsPullback.of_hasPullback
    (coordinateLine K).hom
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom)).flip
  apply (IsPullback.paste_horiz_iff hRight
    (supportAmbientToRefinementAffineLine_comp_fst
      K C d z hVs q a)).mp
  have hbase :
      supportAmbientToRefinementAffineLine K C d z hVs q a ≫
          pullback.snd (coordinateLine K).hom
            (refinementToBase K C d z hVs q ≫
              (commonAffineBase K C d z).hom) =
        supportAmbientToBase K C d z hVs q a :=
    pullback.lift_snd _ _ _
  rw [hbase]
  exact (IsPullback.of_hasPullback
    ((affineComponentToCoordinateLine K C d z a).left ≫
      (coordinateLine K).hom)
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom)).flip

instance supportAmbientToRefinementAffineLine_etale
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (supportAmbientToRefinementAffineLine
      K C d z hVs q a) := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale)
    (supportAmbientToRefinementAffineLine_isPullback
      K C d z hVs q a).flip
    (affineComponentToCoordinateLine_etale K C d z a)

/-- Restrict the refinement-base coordinate map to the selected affine
support open. -/
noncomputable def supportOpenToRefinementAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (N.supportOpen a).toScheme ⟶
      refinementAffineLine K C d z hVs q :=
  (N.supportOpen a).ι ≫
    supportAmbientToRefinementAffineLine K C d z hVs q a

@[reassoc]
theorem supportOpenToRefinementAffineLine_comp_fst
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportOpenToRefinementAffineLine K C d z hVs q m E hE N a ≫
        pullback.fst (coordinateLine K).hom
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) =
      (N.supportOpen a).ι ≫
        pullback.fst
          ((affineComponentToCoordinateLine K C d z a).left ≫
            (coordinateLine K).hom)
          (refinementToBase K C d z hVs q ≫
            (commonAffineBase K C d z).hom) ≫
        (affineComponentToCoordinateLine K C d z a).left := by
  rw [supportOpenToRefinementAffineLine, Category.assoc,
    supportAmbientToRefinementAffineLine_comp_fst]

@[reassoc]
theorem supportOpenToRefinementAffineLine_comp_base
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportOpenToRefinementAffineLine K C d z hVs q m E hE N a ≫
        (refinementAffineLineFamily K C d z hVs q).hom =
      (N.supportOpen a).ι ≫
        supportAmbientToBase K C d z hVs q a := by
  rw [supportOpenToRefinementAffineLine, Category.assoc,
    supportAmbientToRefinementAffineLine_comp_base]

instance supportOpenToRefinementAffineLine_etale
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (supportOpenToRefinementAffineLine
      K C d z hVs q m E hE N a) := by
  dsimp only [supportOpenToRefinementAffineLine]
  infer_instance

/-- The common affine line after base change from the coordinate ground
scheme to the final simultaneous affine base. -/
noncomputable abbrev supportAffineLine : Scheme.{u} :=
  pullback (coordinateLine K).hom
    (baseToCoordinateBase K C d z hVs q m E hE N)

/-- The common base-changed affine line, regarded over the simultaneous
affine base. -/
noncomputable abbrev supportAffineLineFamily : Over N.baseOpen.toScheme :=
  Over.mk (pullback.snd (coordinateLine K).hom
    (baseToCoordinateBase K C d z hVs q m E hE N))

/-- The same final affine line presented as an iterated base change through
the block-refinement affine line. -/
noncomputable abbrev nestedSupportAffineLine : Scheme.{u} :=
  pullback (refinementAffineLineFamily K C d z hVs q).hom
    N.baseOpen.ι

/-- Flattening the iterated affine-line base change gives the direct final
base change used by `supportAffineLine`. -/
noncomputable def nestedSupportAffineLineIso :
    nestedSupportAffineLine K C d z hVs q m E hE N ≅
      supportAffineLine K C d z hVs q m E hE N :=
  pullbackLeftPullbackSndIso
    (coordinateLine K).hom
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom)
    N.baseOpen.ι

@[reassoc]
theorem nestedSupportAffineLineIso_hom_comp_fst :
    (nestedSupportAffineLineIso
        K C d z hVs q m E hE N).hom ≫
      pullback.fst (coordinateLine K).hom
        (baseToCoordinateBase K C d z hVs q m E hE N) =
    pullback.fst
        (refinementAffineLineFamily K C d z hVs q).hom
        N.baseOpen.ι ≫
      pullback.fst (coordinateLine K).hom
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

@[reassoc]
theorem nestedSupportAffineLineIso_hom_comp_snd :
    (nestedSupportAffineLineIso
        K C d z hVs q m E hE N).hom ≫
      pullback.snd (coordinateLine K).hom
        (baseToCoordinateBase K C d z hVs q m E hE N) =
    pullback.snd
      (refinementAffineLineFamily K C d z hVs q).hom
      N.baseOpen.ι :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- Forget the final simultaneous base point while retaining the affine-line
coordinate, thereby mapping the final affine line to the refinement-base
affine line. -/
noncomputable def supportAffineLineToRefinementAffineLine :
    supportAffineLine K C d z hVs q m E hE N ⟶
      refinementAffineLine K C d z hVs q :=
  (nestedSupportAffineLineIso K C d z hVs q m E hE N).inv ≫
    pullback.fst
      (refinementAffineLineFamily K C d z hVs q).hom
      N.baseOpen.ι

@[reassoc]
theorem supportAffineLineToRefinementAffineLine_comp_fst :
    supportAffineLineToRefinementAffineLine
        K C d z hVs q m E hE N ≫
      pullback.fst (coordinateLine K).hom
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) =
    pullback.fst (coordinateLine K).hom
      (baseToCoordinateBase K C d z hVs q m E hE N) := by
  simp only [supportAffineLineToRefinementAffineLine, Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_fst _ _ _

@[reassoc]
theorem supportAffineLineToRefinementAffineLine_comp_base :
    supportAffineLineToRefinementAffineLine
        K C d z hVs q m E hE N ≫
      (refinementAffineLineFamily K C d z hVs q).hom =
    (supportAffineLineFamily K C d z hVs q m E hE N).hom ≫
      N.baseOpen.ι := by
  simp only [supportAffineLineToRefinementAffineLine, Category.assoc]
  exact pullbackLeftPullbackSndIso_inv_fst_snd _ _ _

@[reassoc]
theorem supportAffineLineToRefinementAffineLine_comp_snd :
    supportAffineLineToRefinementAffineLine
        K C d z hVs q m E hE N ≫
      pullback.snd (coordinateLine K).hom
        (refinementToBase K C d z hVs q ≫
          (commonAffineBase K C d z).hom) =
    (supportAffineLineFamily K C d z hVs q m E hE N).hom ≫
      N.baseOpen.ι :=
  supportAffineLineToRefinementAffineLine_comp_base
    K C d z hVs q m E hE N

/-- The final affine line is the base change of the refinement affine line
along the inclusion of the simultaneous affine base. -/
theorem supportAffineLineToRefinementAffineLine_isPullback :
    IsPullback
      (supportAffineLineToRefinementAffineLine
        K C d z hVs q m E hE N)
      (supportAffineLineFamily K C d z hVs q m E hE N).hom
      (refinementAffineLineFamily K C d z hVs q).hom
      N.baseOpen.ι := by
  let h := IsPullback.of_hasPullback
    (refinementAffineLineFamily K C d z hVs q).hom N.baseOpen.ι
  exact h.of_iso
    (nestedSupportAffineLineIso K C d z hVs q m E hE N)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [supportAffineLineToRefinementAffineLine])
    (by
      simpa using (nestedSupportAffineLineIso_hom_comp_snd
        K C d z hVs q m E hE N).symm)
    (by simp) (by simp)

/-- The étale coordinate of one affine support piece, now expressed over
the final common base. -/
noncomputable def supportPieceToSupportAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPiece K C d z hVs q m E hE N a ⟶
      supportAffineLine K C d z hVs q m E hE N :=
  pullback.lift
    (supportPieceToAffineComponent K C d z hVs q m E hE N a ≫
      (affineComponentToCoordinateLine K C d z a).left)
    (supportPieceFamily K C d z hVs q m E hE N a).hom
    (by
      rw [Category.assoc,
        (affineComponentToCoordinateLine K C d z a).w]
      exact supportPieceToAffineComponent_comp_structure
        K C d z hVs q m E hE N a)

@[reassoc]
theorem supportPieceToSupportAffineLine_comp_fst
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceToSupportAffineLine K C d z hVs q m E hE N a ≫
        pullback.fst (coordinateLine K).hom
          (baseToCoordinateBase K C d z hVs q m E hE N) =
      supportPieceToAffineComponent K C d z hVs q m E hE N a ≫
        (affineComponentToCoordinateLine K C d z a).left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem supportPieceToSupportAffineLine_comp_base
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceToSupportAffineLine K C d z hVs q m E hE N a ≫
        (supportAffineLineFamily K C d z hVs q m E hE N).hom =
      (supportPieceFamily K C d z hVs q m E hE N a).hom :=
  pullback.lift_snd _ _ _

/-- The support-piece coordinate map before flattening its iterated base
change presentation. -/
noncomputable def supportPieceToNestedSupportAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPiece K C d z hVs q m E hE N a ⟶
      nestedSupportAffineLine K C d z hVs q m E hE N :=
  pullback.lift
    (pullback.fst
        ((N.supportOpen a).ι ≫
          supportAmbientToBase K C d z hVs q a)
        N.baseOpen.ι ≫
      supportOpenToRefinementAffineLine
        K C d z hVs q m E hE N a)
    (supportPieceFamily K C d z hVs q m E hE N a).hom
    (by
      rw [Category.assoc,
        supportOpenToRefinementAffineLine_comp_base]
      exact pullback.condition)

@[reassoc]
theorem supportPieceToNestedSupportAffineLine_comp_fst
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceToNestedSupportAffineLine
        K C d z hVs q m E hE N a ≫
      pullback.fst
        (refinementAffineLineFamily K C d z hVs q).hom
        N.baseOpen.ι =
      pullback.fst
          ((N.supportOpen a).ι ≫
            supportAmbientToBase K C d z hVs q a)
          N.baseOpen.ι ≫
        supportOpenToRefinementAffineLine
          K C d z hVs q m E hE N a :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem supportPieceToNestedSupportAffineLine_comp_snd
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceToNestedSupportAffineLine
        K C d z hVs q m E hE N a ≫
      pullback.snd
        (refinementAffineLineFamily K C d z hVs q).hom
        N.baseOpen.ι =
      (supportPieceFamily K C d z hVs q m E hE N a).hom :=
  pullback.lift_snd _ _ _

/-- The iterated support-piece coordinate is the base change of the
refinement-base coordinate on the chosen support open. -/
theorem supportPieceToNestedSupportAffineLine_isPullback
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    IsPullback
      (supportPieceToNestedSupportAffineLine
        K C d z hVs q m E hE N a)
      (pullback.fst
        ((N.supportOpen a).ι ≫
          supportAmbientToBase K C d z hVs q a)
        N.baseOpen.ι)
      (pullback.fst
        (refinementAffineLineFamily K C d z hVs q).hom
        N.baseOpen.ι)
      (supportOpenToRefinementAffineLine
        K C d z hVs q m E hE N a) := by
  let hRight := (IsPullback.of_hasPullback
    (refinementAffineLineFamily K C d z hVs q).hom
    N.baseOpen.ι).flip
  apply (IsPullback.paste_horiz_iff hRight
    (supportPieceToNestedSupportAffineLine_comp_fst
      K C d z hVs q m E hE N a)).mp
  have htop :
      supportPieceToNestedSupportAffineLine
          K C d z hVs q m E hE N a ≫
        pullback.snd
          (refinementAffineLineFamily K C d z hVs q).hom
          N.baseOpen.ι =
      (supportPieceFamily K C d z hVs q m E hE N a).hom :=
    pullback.lift_snd _ _ _
  rw [htop, supportOpenToRefinementAffineLine_comp_base]
  exact (IsPullback.of_hasPullback
    ((N.supportOpen a).ι ≫
      supportAmbientToBase K C d z hVs q a)
    N.baseOpen.ι).flip

instance supportPieceToNestedSupportAffineLine_etale
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (supportPieceToNestedSupportAffineLine
      K C d z hVs q m E hE N a) := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale)
    (supportPieceToNestedSupportAffineLine_isPullback
      K C d z hVs q m E hE N a).flip
    (inferInstance : Etale (supportOpenToRefinementAffineLine
      K C d z hVs q m E hE N a))

/-- Flattening the iterated base change recovers the direct support-piece
coordinate map. -/
theorem supportPieceToNestedSupportAffineLine_comp_iso
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceToNestedSupportAffineLine
        K C d z hVs q m E hE N a ≫
      (nestedSupportAffineLineIso
        K C d z hVs q m E hE N).hom =
    supportPieceToSupportAffineLine
      K C d z hVs q m E hE N a := by
  apply pullback.hom_ext
  · rw [Category.assoc, nestedSupportAffineLineIso_hom_comp_fst,
      ← Category.assoc,
      supportPieceToNestedSupportAffineLine_comp_fst,
      Category.assoc,
      supportOpenToRefinementAffineLine_comp_fst,
      supportPieceToSupportAffineLine_comp_fst]
    simp only [supportPieceToAffineComponent, Category.assoc]
  · rw [Category.assoc, nestedSupportAffineLineIso_hom_comp_snd,
      supportPieceToNestedSupportAffineLine_comp_snd]
    exact (supportPieceToSupportAffineLine_comp_base
      K C d z hVs q m E hE N a).symm

/-- Forgetting the final affine-line base after applying the support-piece
coordinate recovers the coordinate map on the selected support open. -/
theorem supportPieceToSupportAffineLine_comp_refinement
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceToSupportAffineLine
        K C d z hVs q m E hE N a ≫
      supportAffineLineToRefinementAffineLine
        K C d z hVs q m E hE N =
    pullback.fst
        ((N.supportOpen a).ι ≫
          supportAmbientToBase K C d z hVs q a)
        N.baseOpen.ι ≫
      supportOpenToRefinementAffineLine
        K C d z hVs q m E hE N a := by
  rw [← supportPieceToNestedSupportAffineLine_comp_iso]
  simp only [supportAffineLineToRefinementAffineLine,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact supportPieceToNestedSupportAffineLine_comp_fst
    K C d z hVs q m E hE N a

instance supportPieceToSupportAffineLine_etale
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (supportPieceToSupportAffineLine
      K C d z hVs q m E hE N a) := by
  rw [← supportPieceToNestedSupportAffineLine_comp_iso]
  infer_instance

/-- After transporting an occurrence to its support owner, its selected
curve coordinate is still the independently varying coordinate indexed by
that occurrence. -/
@[reassoc]
theorem tupleSheetToOccurrenceComponentAtSupport_comp_coordinate
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    tupleSheetToOccurrenceComponentAtSupport
        K C d z hVs q m E hE j a i ≫
      (affineComponentToCoordinateLine K C d z a).left =
    occurrenceCoordinate K C d z hVs q i.1 := by
  rcases i with ⟨i, rfl⟩
  simpa only [tupleSheetToOccurrenceComponentAtSupport, eqToHom_refl,
    Over.id_left, Category.comp_id] using
    tupleSheetToOccurrenceComponent_comp_coordinate
      K C d z hVs q m E hE j i

/-- The section of the common affine line determined by one independently
varying occurrence coordinate on the final simultaneous base. -/
noncomputable def supportAffineLineGraph
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    N.baseOpen.toScheme ⟶
      supportAffineLine K C d z hVs q m E hE N :=
  pullback.lift
    (N.baseOpen.ι ≫ occurrenceCoordinate K C d z hVs q i.1)
    (𝟙 _)
    (by
      rw [Category.assoc,
        occurrenceCoordinate_comp_coordinateLine K C d z hVs q i.1]
      simp only [Category.id_comp]
      rfl)

@[reassoc]
theorem supportAffineLineGraph_comp_fst
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    supportAffineLineGraph K C d z hVs q m E hE N a i ≫
        pullback.fst (coordinateLine K).hom
          (baseToCoordinateBase K C d z hVs q m E hE N) =
      N.baseOpen.ι ≫ occurrenceCoordinate K C d z hVs q i.1 :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem supportAffineLineGraph_comp_base
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    supportAffineLineGraph K C d z hVs q m E hE N a i ≫
        (supportAffineLineFamily K C d z hVs q m E hE N).hom =
      𝟙 N.baseOpen.toScheme :=
  pullback.lift_snd _ _ _

/-- The final occurrence section is the pullback of the corresponding
section over the block-refinement base. -/
theorem supportAffineLineGraph_comp_refinement
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    supportAffineLineGraph K C d z hVs q m E hE N a i ≫
        supportAffineLineToRefinementAffineLine
          K C d z hVs q m E hE N =
      N.baseOpen.ι ≫
        refinementAffineLineGraph K C d z hVs q i.1 := by
  apply pullback.hom_ext
  · rw [Category.assoc,
      supportAffineLineToRefinementAffineLine_comp_fst,
      supportAffineLineGraph_comp_fst,
      Category.assoc, refinementAffineLineGraph_comp_fst]
  · rw [Category.assoc,
      supportAffineLineToRefinementAffineLine_comp_snd,
      ← Category.assoc, supportAffineLineGraph_comp_base,
      Category.id_comp, Category.assoc,
      refinementAffineLineGraph_comp_snd, Category.comp_id]

/-- The final occurrence section is the cartesian base change of its
refinement-base section. -/
theorem supportAffineLineGraph_isPullback
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    IsPullback
      (supportAffineLineGraph K C d z hVs q m E hE N a i)
      N.baseOpen.ι
      (supportAffineLineToRefinementAffineLine
        K C d z hVs q m E hE N)
      (refinementAffineLineGraph K C d z hVs q i.1) := by
  let hRight :=
    (supportAffineLineToRefinementAffineLine_isPullback
      K C d z hVs q m E hE N).flip
  apply (IsPullback.paste_horiz_iff hRight
    (supportAffineLineGraph_comp_refinement
      K C d z hVs q m E hE N a i)).mp
  rw [supportAffineLineGraph_comp_base,
    refinementAffineLineGraph_comp_base]
  exact IsPullback.id_horiz N.baseOpen.ι

/-- Pulling an occurrence section ideal from the refinement affine line to
the final affine line gives exactly the final occurrence-section ideal. -/
theorem refinementAffineLineGraph_ker_comap_supportAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (refinementAffineLineGraph K C d z hVs q i.1).ker.comap
        (supportAffineLineToRefinementAffineLine
          K C d z hVs q m E hE N) =
      (supportAffineLineGraph
        K C d z hVs q m E hE N a i).ker := by
  let graphHom := refinementAffineLineGraph K C d z hVs q i.1
  let familyHom := (refinementAffineLineFamily K C d z hVs q).hom
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  letI : IsSeparated familyHom := by
    change IsSeparated (pullback.snd (coordinateLine K).hom
      (refinementToBase K C d z hVs q ≫
        (commonAffineBase K C d z).hom))
    infer_instance
  letI : IsClosedImmersion graphHom := by
    haveI : IsClosedImmersion (graphHom ≫ familyHom) := by
      rw [show graphHom ≫ familyHom =
          𝟙 (componentFpqcBlockRefinement K C d z hVs q).left from
        refinementAffineLineGraph_comp_base
          K C d z hVs q i.1]
      infer_instance
    exact IsClosedImmersion.of_comp graphHom familyHom
  let h := supportAffineLineGraph_isPullback
    K C d z hVs q m E hE N a i
  calc
    graphHom.ker.comap
        (supportAffineLineToRefinementAffineLine
          K C d z hVs q m E hE N) =
      (pullback.fst
        (supportAffineLineToRefinementAffineLine
          K C d z hVs q m E hE N) graphHom).ker :=
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
          graphHom
          (supportAffineLineToRefinementAffineLine
            K C d z hVs q m E hE N)).symm
    _ = (h.isoPullback.hom ≫
        pullback.fst
          (supportAffineLineToRefinementAffineLine
            K C d z hVs q m E hE N) graphHom).ker :=
      (Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom
        (pullback.fst
          (supportAffineLineToRefinementAffineLine
            K C d z hVs q m E hE N) graphHom)).symm
    _ = (supportAffineLineGraph
        K C d z hVs q m E hE N a i).ker := by
      rw [h.isoPullback_hom_fst]

/-- The occurrence graph ideal on a final affine support piece is exactly
the extension of its independently varying affine-line section ideal. -/
theorem supportAffineLineGraph_ker_comap_supportPiece
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (supportAffineLineGraph K C d z hVs q m E hE N a i).ker.comap
        (supportPieceToSupportAffineLine
          K C d z hVs q m E hE N a) =
      supportPieceGraphIdealAt K C d z hVs q m E hE N a i := by
  rcases i with ⟨i, rfl⟩
  rw [← refinementAffineLineGraph_ker_comap_supportAffineLine,
    ← Scheme.IdealSheafData.comap_comp,
    supportPieceToSupportAffineLine_comp_refinement,
    supportOpenToRefinementAffineLine,
    Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp,
    refinementAffineLineGraph_ker_comap_supportAmbient,
    ← Scheme.IdealSheafData.comap_comp]
  exact supportPiece_equalCoordinateIdeal
    K C d z hVs q m E hE N i

/-- On affine global sections, one occurrence graph ideal is the extension
of its affine-line section ideal along the étale support coordinate. -/
theorem supportPieceGraphIdealAt_top_eq_map_coordinateSection
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (supportPieceGraphIdealAt K C d z hVs q m E hE N a i).ideal
        ⟨⊤, @isAffineOpen_top _
          (supportPiece_isAffine K C d z hVs q m E hE N a)⟩ =
      Ideal.map
        (supportPieceToSupportAffineLine
          K C d z hVs q m E hE N a).appTop.hom
        ((supportAffineLineGraph
          K C d z hVs q m E hE N a i).ker.ideal
          ⟨⊤, @isAffineOpen_top _ (by
            letI : IsAffine N.baseOpen.toScheme := N.base_isAffine
            letI : IsAffine (coordinateBase K) := by
              dsimp only [coordinateBase]
              infer_instance
            letI : IsAffine (coordinateLine K).left := by
              change IsAffine (Spec (.of (coordinateRing K)))
              infer_instance
            exact (inferInstance : IsAffine
              (supportAffineLine K C d z hVs q m E hE N)))⟩) := by
  letI : IsAffine N.baseOpen.toScheme := N.base_isAffine
  letI : IsAffine (coordinateBase K) := by
    dsimp only [coordinateBase]
    infer_instance
  letI : IsAffine (coordinateLine K).left := by
    change IsAffine (Spec (.of (coordinateRing K)))
    infer_instance
  letI : IsAffine
      (supportAffineLine K C d z hVs q m E hE N) := by
    infer_instance
  letI : IsAffine
      (supportPiece K C d z hVs q m E hE N a) :=
    supportPiece_isAffine K C d z hVs q m E hE N a
  rw [← supportAffineLineGraph_ker_comap_supportPiece]
  exact ideal_comap_top_eq_map_of_isAffine
    (supportAffineLineGraph K C d z hVs q m E hE N a i).ker
    (supportPieceToSupportAffineLine K C d z hVs q m E hE N a)

/-- The multiplicity-sensitive product of all independent occurrence-section
ideals owned by one support member, formed on the common affine line. -/
noncomputable def supportAffineLineGraphProductIdeal
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Scheme.IdealSheafData
      (supportAffineLine K C d z hVs q m E hE N) :=
  ∏ i : OccurrencesAtSupport K C d z a,
    (supportAffineLineGraph K C d z hVs q m E hE N a i).ker

/-- Pulling the complete affine-line section product to a support piece gives
the complete occurrence graph product, including repeated factors. -/
theorem supportPieceGraphProductIdeal_eq_coordinateSection_comap
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportPieceGraphProductIdeal K C d z hVs q m E hE N a =
      (supportAffineLineGraphProductIdeal
        K C d z hVs q m E hE N a).comap
        (supportPieceToSupportAffineLine
          K C d z hVs q m E hE N a) := by
  letI : IsAffine N.baseOpen.toScheme := N.base_isAffine
  letI : IsAffine (coordinateBase K) := by
    dsimp only [coordinateBase]
    infer_instance
  letI : IsAffine (coordinateLine K).left := by
    change IsAffine (Spec (.of (coordinateRing K)))
    infer_instance
  letI : IsAffine
      (supportAffineLine K C d z hVs q m E hE N) := by
    infer_instance
  letI : IsAffine
      (supportPiece K C d z hVs q m E hE N a) :=
    supportPiece_isAffine K C d z hVs q m E hE N a
  rw [supportPieceGraphProductIdeal,
    supportAffineLineGraphProductIdeal,
    idealSheaf_comap_finsetProd_of_isAffine]
  apply Finset.prod_congr rfl
  intro i _
  exact (supportAffineLineGraph_ker_comap_supportPiece
    K C d z hVs q m E hE N a i).symm

/-- On affine global sections, the full occurrence graph product is the
extension of the full independent affine-line section product. -/
theorem supportPieceGraphProductIdeal_top_eq_map_coordinateSections
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (supportPieceGraphProductIdeal K C d z hVs q m E hE N a).ideal
        ⟨⊤, @isAffineOpen_top _
          (supportPiece_isAffine K C d z hVs q m E hE N a)⟩ =
      Ideal.map
        (supportPieceToSupportAffineLine
          K C d z hVs q m E hE N a).appTop.hom
        ((supportAffineLineGraphProductIdeal
          K C d z hVs q m E hE N a).ideal
          ⟨⊤, @isAffineOpen_top _ (by
            letI : IsAffine N.baseOpen.toScheme := N.base_isAffine
            letI : IsAffine (coordinateBase K) := by
              dsimp only [coordinateBase]
              infer_instance
            letI : IsAffine (coordinateLine K).left := by
              change IsAffine (Spec (.of (coordinateRing K)))
              infer_instance
            exact (inferInstance : IsAffine
              (supportAffineLine K C d z hVs q m E hE N)))⟩) := by
  letI : IsAffine N.baseOpen.toScheme := N.base_isAffine
  letI : IsAffine (coordinateBase K) := by
    dsimp only [coordinateBase]
    infer_instance
  letI : IsAffine (coordinateLine K).left := by
    change IsAffine (Spec (.of (coordinateRing K)))
    infer_instance
  letI : IsAffine
      (supportAffineLine K C d z hVs q m E hE N) := by
    infer_instance
  letI : IsAffine
      (supportPiece K C d z hVs q m E hE N a) :=
    supportPiece_isAffine K C d z hVs q m E hE N a
  rw [supportPieceGraphProductIdeal_eq_coordinateSection_comap]
  exact ideal_comap_top_eq_map_of_isAffine
    (supportAffineLineGraphProductIdeal
      K C d z hVs q m E hE N a)
    (supportPieceToSupportAffineLine K C d z hVs q m E hE N a)

/-- Forgetting an occurrence graph to its selected affine component recovers
the corresponding tuple-sheet component over the restricted base. -/
@[reassoc]
theorem graphToSupportPiece_comp_affineComponent
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportPiece K C d z hVs q m E hE N a i ≫
        supportPieceToAffineComponent K C d z hVs q m E hE N a =
      N.baseOpen.ι ≫
        tupleSheetToOccurrenceComponentAtSupport
          K C d z hVs q m E hE j a i := by
  simp only [supportPieceToAffineComponent,
    graphToSupportPiece_comp_fst_assoc,
    SimultaneousAffineGraphNeighborhood.graph_comp_ι_assoc,
    graphToSupportAmbientAtSupport_comp_fst]

/-- Every occurrence graph in a support piece is exactly the section of the
common affine line defined by its independent occurrence coordinate. -/
theorem graphToSupportPiece_comp_supportAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportPiece K C d z hVs q m E hE N a i ≫
        supportPieceToSupportAffineLine K C d z hVs q m E hE N a =
      supportAffineLineGraph K C d z hVs q m E hE N a i := by
  apply pullback.hom_ext
  · rw [Category.assoc, supportPieceToSupportAffineLine_comp_fst,
      ← Category.assoc, graphToSupportPiece_comp_affineComponent,
      Category.assoc,
      tupleSheetToOccurrenceComponentAtSupport_comp_coordinate,
      supportAffineLineGraph_comp_fst]
  · calc
      (graphToSupportPiece K C d z hVs q m E hE N a i ≫
          supportPieceToSupportAffineLine K C d z hVs q m E hE N a) ≫
          pullback.snd (coordinateLine K).hom
            (baseToCoordinateBase K C d z hVs q m E hE N) =
        graphToSupportPiece K C d z hVs q m E hE N a i ≫
          (supportPieceToSupportAffineLine
              K C d z hVs q m E hE N a ≫
            (supportAffineLineFamily
              K C d z hVs q m E hE N).hom) :=
        Category.assoc _ _ _
      _ = graphToSupportPiece K C d z hVs q m E hE N a i ≫
          (supportPieceFamily K C d z hVs q m E hE N a).hom := by
        rw [supportPieceToSupportAffineLine_comp_base]
      _ = 𝟙 N.baseOpen.toScheme :=
        graphToSupportPiece_comp_snd K C d z hVs q m E hE N a i
      _ = supportAffineLineGraph K C d z hVs q m E hE N a i ≫
          pullback.snd (coordinateLine K).hom
            (baseToCoordinateBase K C d z hVs q m E hE N) :=
        (supportAffineLineGraph_comp_base
          K C d z hVs q m E hE N a i).symm

/-- On an affine support piece, the étale coordinate map lifts an
intersection-quotient isomorphism to the product quotient.  This is the
collision-sensitive algebra step for two occurrence sections: it preserves
the square-zero structure retained when the sections coincide. -/
theorem supportPiece_extendedQuotientMap_bijective_mul_of_inf
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    (a : Fin (geometricDistinctSupportCard K C d z))
    (I J : Ideal Γ(supportAffineLine K C d z hVs q m E hE N, ⊤)) :
    letI : Algebra
        Γ(supportAffineLine K C d z hVs q m E hE N, ⊤)
        Γ(supportPiece K C d z hVs q m E hE N a, ⊤) :=
      (supportPieceToSupportAffineLine
        K C d z hVs q m E hE N a).appTop.hom.toAlgebra
    Function.Bijective
        (extendedQuotientMap
          Γ(supportAffineLine K C d z hVs q m E hE N, ⊤)
          Γ(supportPiece K C d z hVs q m E hE N a, ⊤) (I ⊓ J)) →
      Function.Bijective
        (extendedQuotientMap
          Γ(supportAffineLine K C d z hVs q m E hE N, ⊤)
          Γ(supportPiece K C d z hVs q m E hE N a, ⊤) (I * J)) := by
  letI : IsAffine N.baseOpen.toScheme := N.base_isAffine
  letI : IsAffine (coordinateBase K) := by
    dsimp only [coordinateBase]
    infer_instance
  letI : IsAffine (coordinateLine K).left := by
    change IsAffine (Spec (.of (coordinateRing K)))
    infer_instance
  letI : IsAffine
      (supportAffineLine K C d z hVs q m E hE N) := by
    infer_instance
  letI : IsAffine
      (supportPiece K C d z hVs q m E hE N a) :=
    supportPiece_isAffine K C d z hVs q m E hE N a
  let f := supportPieceToSupportAffineLine
    K C d z hVs q m E hE N a
  letI : Algebra
      Γ(supportAffineLine K C d z hVs q m E hE N, ⊤)
      Γ(supportPiece K C d z hVs q m E hE N a, ⊤) :=
    f.appTop.hom.toAlgebra
  have hfEtale : f.appTop.hom.Etale :=
    HasRingHomProperty.appTop (P := @Etale) (Q := RingHom.Etale)
      f (inferInstance : Etale f)
  letI : Algebra.Etale
      Γ(supportAffineLine K C d z hVs q m E hE N, ⊤)
      Γ(supportPiece K C d z hVs q m E hE N a, ⊤) :=
    hfEtale.toAlgebra
  exact extendedQuotientMap_bijective_mul_of_inf
    Γ(supportAffineLine K C d z hVs q m E hE N, ⊤)
    Γ(supportPiece K C d z hVs q m E hE N a, ⊤) I J

/-- The finite family of pulled-back support pieces over the common affine
base. -/
noncomputable abbrev supportFamily :
    Fin (geometricDistinctSupportCard K C d z) → Over N.baseOpen.toScheme :=
  supportPieceFamily K C d z hVs q m E hE N

/-- The disjoint union of all affine support pieces over the common affine
base. -/
noncomputable abbrev supportCoproduct : Over N.baseOpen.toScheme :=
  familyCoproduct N.baseOpen.toScheme
    (geometricDistinctSupportCard K C d z)
    (supportFamily K C d z hVs q m E hE N)

/-- The assembled finite support coproduct is affine on an affine
block-refinement chart. -/
theorem supportCoproduct_isAffine
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left] :
    IsAffine (supportCoproduct K C d z hVs q m E hE N).left := by
  letI : ∀ a, IsAffine
      (supportPiece K C d z hVs q m E hE N a) := fun a ↦
    supportPiece_isAffine K C d z hVs q m E hE N a
  change IsAffine (∐ fun a : Fin (geometricDistinctSupportCard K C d z) ↦
    supportPiece K C d z hVs q m E hE N a)
  infer_instance

/-- Insert an occurrence graph into the coproduct summand belonging to its
geometric support owner. -/
noncomputable def graphToSupportCoproduct
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    N.baseOpen.toScheme ⟶
      (supportCoproduct K C d z hVs q m E hE N).left :=
  graphToSupportPiece K C d z hVs q m E hE N a i ≫
    (inclusion N.baseOpen.toScheme
      (geometricDistinctSupportCard K C d z)
      (supportFamily K C d z hVs q m E hE N) a).left

@[reassoc]
theorem graphToSupportCoproduct_comp_structure
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportCoproduct K C d z hVs q m E hE N a i ≫
        (supportCoproduct K C d z hVs q m E hE N).hom =
      𝟙 N.baseOpen.toScheme := by
  rw [graphToSupportCoproduct, Category.assoc]
  have hι := (inclusion N.baseOpen.toScheme
    (geometricDistinctSupportCard K C d z)
    (supportFamily K C d z hVs q m E hE N) a).w
  rw [hι, graphToSupportPiece_comp_snd]

/-- The support coproduct, regarded over the coordinate ground scheme. -/
noncomputable abbrev supportCoproductOverCoordinateBase :
    Over (coordinateBase K) :=
  Over.mk ((supportCoproduct K C d z hVs q m E hE N).hom ≫
    baseToCoordinateBase K C d z hVs q m E hE N)

/-- The pulled-back affine support coproduct maps to the original common
curve-family coproduct, summand by summand. -/
noncomputable def supportCoproductToAffineComponentCoproduct :
    supportCoproductOverCoordinateBase K C d z hVs q m E hE N ⟶
      familyCoproduct (coordinateBase K)
        (geometricDistinctSupportCard K C d z)
        (affineComponentFamily K C d z) :=
  coproductToTarget N.baseOpen.toScheme (coordinateBase K)
    (baseToCoordinateBase K C d z hVs q m E hE N)
    (geometricDistinctSupportCard K C d z)
    (supportFamily K C d z hVs q m E hE N)
    (familyCoproduct (coordinateBase K)
      (geometricDistinctSupportCard K C d z)
      (affineComponentFamily K C d z))
    (fun a ↦ supportPieceToAffineComponent
      K C d z hVs q m E hE N a ≫
        (inclusion (coordinateBase K)
          (geometricDistinctSupportCard K C d z)
          (affineComponentFamily K C d z) a).left)
    (by
      intro a
      rw [Category.assoc,
        (inclusion (coordinateBase K)
          (geometricDistinctSupportCard K C d z)
          (affineComponentFamily K C d z) a).w]
      exact supportPieceToAffineComponent_comp_structure
        K C d z hVs q m E hE N a)

/-- On each support summand, the coproduct comparison is the expected map to
the selected affine curve component followed by its family inclusion. -/
@[reassoc]
theorem inclusion_comp_supportCoproductToAffineComponentCoproduct
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (inclusion N.baseOpen.toScheme
        (geometricDistinctSupportCard K C d z)
        (supportFamily K C d z hVs q m E hE N) a).left ≫
      (supportCoproductToAffineComponentCoproduct
        K C d z hVs q m E hE N).left =
    supportPieceToAffineComponent K C d z hVs q m E hE N a ≫
      (inclusion (coordinateBase K)
        (geometricDistinctSupportCard K C d z)
        (affineComponentFamily K C d z) a).left :=
  inclusion_comp_coproductToTarget
    N.baseOpen.toScheme (coordinateBase K)
    (baseToCoordinateBase K C d z hVs q m E hE N)
    (geometricDistinctSupportCard K C d z)
    (supportFamily K C d z hVs q m E hE N)
    (familyCoproduct (coordinateBase K)
      (geometricDistinctSupportCard K C d z)
      (affineComponentFamily K C d z))
    (fun a ↦ supportPieceToAffineComponent
      K C d z hVs q m E hE N a ≫
        (inclusion (coordinateBase K)
          (geometricDistinctSupportCard K C d z)
          (affineComponentFamily K C d z) a).left)
    _ a

/-- In the assembled common family, each occurrence graph lands in precisely
its owner support summand. -/
@[reassoc]
theorem graphToSupportCoproduct_comp_comparison
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportCoproduct K C d z hVs q m E hE N a i ≫
        (supportCoproductToAffineComponentCoproduct
          K C d z hVs q m E hE N).left =
      graphToSupportPiece K C d z hVs q m E hE N a i ≫
        supportPieceToAffineComponent K C d z hVs q m E hE N a ≫
          (inclusion (coordinateBase K)
            (geometricDistinctSupportCard K C d z)
            (affineComponentFamily K C d z) a).left := by
  rw [graphToSupportCoproduct, Category.assoc,
    inclusion_comp_supportCoproductToAffineComponentCoproduct]

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSupportCoproduct
