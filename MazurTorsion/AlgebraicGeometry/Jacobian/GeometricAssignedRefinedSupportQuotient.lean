/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSupportCoproduct

/-!
# The graph-product quotient after cross-support refinement

The final cross-support refinement changes the affine base as well as the
support opens.  This file therefore rebases the common affine line to that
final base before comparing graph-product quotients.  Every refined owner
graph is the exact pullback of its corresponding section of the rebased
line.  The resulting quotient calculation is the local finite-flat input
used by `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSupportCoproduct

open AffineIdealSheafPullback
open AffineLineSectionProduct
open EtaleQuotientProduct
open FiniteSupportEtaleCoordinates
open GeometricAssignedAffineChart
open GeometricAssignedAffineRootCoordinates
open GeometricAssignedSimultaneousGraphNeighborhood
open GeometricAssignedAffineSimultaneousNeighborhood
open RelativeAffineLinePower
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
variable [IsSeparated C.hom]
variable (R : CrossSupportAffineGraphRefinement
  K C d z hVs q m E hE N)

/-- The common support affine line after rebasing from the simultaneous
affine base to the final cross-support affine base. -/
noncomputable abbrev CrossSupportAffineGraphRefinement.refinedSupportAffineLine :
    Scheme.{u} :=
  pullback
    (supportAffineLineFamily K C d z hVs q m E hE N).hom
    R.baseOpen.ι

/-- The rebased support affine line, regarded over the final base. -/
noncomputable abbrev
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineFamily :
    Over R.baseOpen.toScheme :=
  Over.mk (pullback.snd
    (supportAffineLineFamily K C d z hVs q m E hE N).hom
    R.baseOpen.ι)

instance CrossSupportAffineGraphRefinement.refinedSupportAffineLineFamily_separated :
    IsSeparated (R.refinedSupportAffineLineFamily
      K C d z hVs q m E hE N).hom := by
  letI : IsSeparated (coordinateLine K).hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  letI : IsSeparated
      (supportAffineLineFamily K C d z hVs q m E hE N).hom := by
    change IsSeparated (pullback.snd (coordinateLine K).hom
      (baseToCoordinateBase K C d z hVs q m E hE N))
    infer_instance
  change IsSeparated (pullback.snd
    (supportAffineLineFamily K C d z hVs q m E hE N).hom
    R.baseOpen.ι)
  infer_instance

/-- Forget the final base change on the common support affine line. -/
noncomputable abbrev
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineToSupportAffineLine :
    R.refinedSupportAffineLine K C d z hVs q m E hE N ⟶
      supportAffineLine K C d z hVs q m E hE N :=
  pullback.fst
    (supportAffineLineFamily K C d z hVs q m E hE N).hom
    R.baseOpen.ι

/-- The defining pullback of the rebased support line remains cartesian
after identifying the old support line with standard relative affine
space. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLine_standard_isPullback :
    IsPullback
      (R.refinedSupportAffineLineToSupportAffineLine
          K C d z hVs q m E hE N ≫
        (supportAffineLineIsoAffineSpace
          K C d z hVs q m E hE N).hom)
      (R.refinedSupportAffineLineFamily
        K C d z hVs q m E hE N).hom
      (𝔸(ULift.{u} (Fin 1); N.baseOpen.toScheme) ↘
        N.baseOpen.toScheme)
      R.baseOpen.ι := by
  let h := IsPullback.of_hasPullback
    (supportAffineLineFamily K C d z hVs q m E hE N).hom
    R.baseOpen.ι
  exact h.of_iso
    (Iso.refl _)
    (supportAffineLineIsoAffineSpace K C d z hVs q m E hE N)
    (Iso.refl _)
    (Iso.refl _)
    (by rfl)
    (by simp)
    (supportAffineLineIsoAffineSpace_hom_comp_projection
      K C d z hVs q m E hE N).symm
    (by simp)

/-- The final common support line is standard relative affine one-space
over the cross-support base. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineIsoAffineSpace :
    R.refinedSupportAffineLine K C d z hVs q m E hE N ≅
      𝔸(ULift.{u} (Fin 1); R.baseOpen.toScheme) :=
  (R.refinedSupportAffineLine_standard_isPullback
      K C d z hVs q m E hE N).isoIsPullback
    𝔸(ULift.{u} (Fin 1); N.baseOpen.toScheme)
    R.baseOpen.toScheme
    (AffineSpace.isPullback_map
      (n := ULift.{u} (Fin 1)) R.baseOpen.ι)

/-- The rebased common support line is affine. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLine_isAffine :
    IsAffine (R.refinedSupportAffineLine K C d z hVs q m E hE N) := by
  letI : IsAffine R.baseOpen.toScheme := R.base_isAffine
  exact IsAffine.of_isIso
    (R.refinedSupportAffineLineIsoAffineSpace
      K C d z hVs q m E hE N).hom

@[reassoc]
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineIso_hom_projection :
    (R.refinedSupportAffineLineIsoAffineSpace
        K C d z hVs q m E hE N).hom ≫
      (𝔸(ULift.{u} (Fin 1); R.baseOpen.toScheme) ↘
        R.baseOpen.toScheme) =
    (R.refinedSupportAffineLineFamily
      K C d z hVs q m E hE N).hom :=
  IsPullback.isoIsPullback_hom_snd
    𝔸(ULift.{u} (Fin 1); N.baseOpen.toScheme)
    R.baseOpen.toScheme
    (R.refinedSupportAffineLine_standard_isPullback
      K C d z hVs q m E hE N)
    (AffineSpace.isPullback_map
      (n := ULift.{u} (Fin 1)) R.baseOpen.ι)

/-- Restrict the old support-piece coordinate to a retained support open. -/
noncomputable def
    CrossSupportAffineGraphRefinement.supportOpenToSupportAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (R.supportOpen a).toScheme ⟶
      supportAffineLine K C d z hVs q m E hE N :=
  (R.supportOpen a).ι ≫
    supportPieceToSupportAffineLine K C d z hVs q m E hE N a

@[reassoc]
theorem CrossSupportAffineGraphRefinement.supportOpenToSupportAffineLine_comp_base
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.supportOpenToSupportAffineLine K C d z hVs q m E hE N a ≫
        (supportAffineLineFamily K C d z hVs q m E hE N).hom =
      (R.supportOpen a).ι ≫
        (supportPieceFamily K C d z hVs q m E hE N a).hom := by
  rw [CrossSupportAffineGraphRefinement.supportOpenToSupportAffineLine,
    Category.assoc, supportPieceToSupportAffineLine_comp_base]

instance CrossSupportAffineGraphRefinement.supportOpenToSupportAffineLine_etale
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (R.supportOpenToSupportAffineLine
      K C d z hVs q m E hE N a) := by
  unfold CrossSupportAffineGraphRefinement.supportOpenToSupportAffineLine
  infer_instance

/-- The étale coordinate of a refined support piece, with both source and
affine line rebased to the final cross-support base. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportPieceToSupportAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportPiece K C d z hVs q m E hE N a ⟶
      R.refinedSupportAffineLine K C d z hVs q m E hE N :=
  pullback.map
    ((R.supportOpen a).ι ≫
      (supportPieceFamily K C d z hVs q m E hE N a).hom)
    R.baseOpen.ι
    (supportAffineLineFamily K C d z hVs q m E hE N).hom
    R.baseOpen.ι
    (R.supportOpenToSupportAffineLine K C d z hVs q m E hE N a)
    (𝟙 _)
    (𝟙 _)
    (by
      simpa only [Category.comp_id] using
        (R.supportOpenToSupportAffineLine_comp_base
          K C d z hVs q m E hE N a).symm)
    (by simp)

@[reassoc]
theorem CrossSupportAffineGraphRefinement.refinedSupportPieceToSupportAffineLine_comp_oldLine
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportPieceToSupportAffineLine
        K C d z hVs q m E hE N a ≫
      R.refinedSupportAffineLineToSupportAffineLine
        K C d z hVs q m E hE N =
    R.refinedSupportPieceToSupportPiece K C d z hVs q m E hE N a ≫
      supportPieceToSupportAffineLine K C d z hVs q m E hE N a := by
  simp only [CrossSupportAffineGraphRefinement.refinedSupportPieceToSupportAffineLine,
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineToSupportAffineLine,
    CrossSupportAffineGraphRefinement.refinedSupportPieceToSupportPiece,
    CrossSupportAffineGraphRefinement.supportOpenToSupportAffineLine,
    pullback.map, pullback.lift_fst, Category.assoc]

@[reassoc]
theorem CrossSupportAffineGraphRefinement.refinedSupportPieceToSupportAffineLine_comp_base
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportPieceToSupportAffineLine
        K C d z hVs q m E hE N a ≫
      (R.refinedSupportAffineLineFamily
        K C d z hVs q m E hE N).hom =
    (R.refinedSupportPieceFamily K C d z hVs q m E hE N a).hom := by
  change pullback.lift _ _ _ ≫
      pullback.snd
        (supportAffineLineFamily K C d z hVs q m E hE N).hom
        R.baseOpen.ι =
    pullback.snd
      ((R.supportOpen a).ι ≫
        (supportPieceFamily K C d z hVs q m E hE N a).hom)
      R.baseOpen.ι
  rw [pullback.lift_snd, Category.comp_id]

instance CrossSupportAffineGraphRefinement.refinedSupportPieceToSupportAffineLine_etale
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (R.refinedSupportPieceToSupportAffineLine
      K C d z hVs q m E hE N a) := by
  let coordinate := R.refinedSupportPieceToSupportAffineLine
    K C d z hVs q m E hE N a
  let forgetLine := R.refinedSupportAffineLineToSupportAffineLine
    K C d z hVs q m E hE N
  haveI : Etale
      (R.refinedSupportPieceToSupportPiece
        K C d z hVs q m E hE N a ≫
      supportPieceToSupportAffineLine K C d z hVs q m E hE N a) := by
    unfold CrossSupportAffineGraphRefinement.refinedSupportPieceToSupportPiece
    infer_instance
  haveI : Etale (coordinate ≫ forgetLine) := by
    rw [show coordinate ≫ forgetLine =
      R.refinedSupportPieceToSupportPiece K C d z hVs q m E hE N a ≫
        supportPieceToSupportAffineLine K C d z hVs q m E hE N a from
      R.refinedSupportPieceToSupportAffineLine_comp_oldLine
        K C d z hVs q m E hE N a]
    infer_instance
  haveI : Etale forgetLine := by
    dsimp only [forgetLine,
      CrossSupportAffineGraphRefinement.refinedSupportAffineLineToSupportAffineLine]
    infer_instance
  exact Etale.of_comp coordinate forgetLine

/-- The occurrence section of the rebased support affine line. -/
noncomputable def CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraph
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    R.baseOpen.toScheme ⟶
      R.refinedSupportAffineLine K C d z hVs q m E hE N :=
  pullback.lift
    (R.baseOpen.ι ≫
      supportAffineLineGraph K C d z hVs q m E hE N a i)
    (𝟙 _)
    (by
      rw [Category.assoc, supportAffineLineGraph_comp_base,
        Category.comp_id, Category.id_comp])

@[reassoc]
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraph_comp_oldLine
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    R.refinedSupportAffineLineGraph K C d z hVs q m E hE N a i ≫
      R.refinedSupportAffineLineToSupportAffineLine
        K C d z hVs q m E hE N =
    R.baseOpen.ι ≫
      supportAffineLineGraph K C d z hVs q m E hE N a i :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraph_comp_base
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    R.refinedSupportAffineLineGraph K C d z hVs q m E hE N a i ≫
      (R.refinedSupportAffineLineFamily
        K C d z hVs q m E hE N).hom =
    𝟙 R.baseOpen.toScheme :=
  pullback.lift_snd _ _ _

/-- A rebased affine-line occurrence section is the exact base change of
its section over the simultaneous affine base. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraph_isPullback
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    IsPullback
      (R.refinedSupportAffineLineGraph K C d z hVs q m E hE N a i)
      R.baseOpen.ι
      (R.refinedSupportAffineLineToSupportAffineLine
        K C d z hVs q m E hE N)
      (supportAffineLineGraph K C d z hVs q m E hE N a i) := by
  apply IsPullback.mk'
  · exact R.refinedSupportAffineLineGraph_comp_oldLine
      K C d z hVs q m E hE N a i
  · intro X φ φ' _ hφ
    exact (cancel_mono R.baseOpen.ι).mp hφ
  · intro X p b hpb
    let lift : X ⟶ R.baseOpen.toScheme :=
      p ≫ (R.refinedSupportAffineLineFamily
        K C d z hVs q m E hE N).hom
    have hliftBase : lift ≫ R.baseOpen.ι = b := by
      calc
        lift ≫ R.baseOpen.ι =
            p ≫ pullback.snd
              (supportAffineLineFamily K C d z hVs q m E hE N).hom
              R.baseOpen.ι ≫ R.baseOpen.ι := by rfl
        _ = p ≫ pullback.fst
              (supportAffineLineFamily K C d z hVs q m E hE N).hom
              R.baseOpen.ι ≫
            (supportAffineLineFamily K C d z hVs q m E hE N).hom := by
          rw [pullback.condition]
        _ = (p ≫ pullback.fst
              (supportAffineLineFamily K C d z hVs q m E hE N).hom
              R.baseOpen.ι) ≫
            (supportAffineLineFamily K C d z hVs q m E hE N).hom :=
          (Category.assoc _ _ _).symm
        _ = (b ≫ supportAffineLineGraph
              K C d z hVs q m E hE N a i) ≫
            (supportAffineLineFamily K C d z hVs q m E hE N).hom := by
          rw [hpb]
        _ = b ≫ (supportAffineLineGraph
              K C d z hVs q m E hE N a i ≫
            (supportAffineLineFamily K C d z hVs q m E hE N).hom) :=
          Category.assoc _ _ _
        _ = b := by
          rw [supportAffineLineGraph_comp_base, Category.comp_id]
    refine ⟨lift, ?_, hliftBase⟩
    apply pullback.hom_ext
    · change
        (lift ≫ R.refinedSupportAffineLineGraph
          K C d z hVs q m E hE N a i) ≫
            R.refinedSupportAffineLineToSupportAffineLine
              K C d z hVs q m E hE N =
          p ≫ R.refinedSupportAffineLineToSupportAffineLine
            K C d z hVs q m E hE N
      rw [Category.assoc,
        R.refinedSupportAffineLineGraph_comp_oldLine,
        ← Category.assoc, hliftBase, hpb]
    · change
        (lift ≫ R.refinedSupportAffineLineGraph
          K C d z hVs q m E hE N a i) ≫
            (R.refinedSupportAffineLineFamily
              K C d z hVs q m E hE N).hom =
          p ≫ (R.refinedSupportAffineLineFamily
            K C d z hVs q m E hE N).hom
      rw [Category.assoc,
        R.refinedSupportAffineLineGraph_comp_base,
        Category.comp_id]

/-- A refined owner graph maps to its matching section of the rebased
support affine line. -/
@[reassoc]
theorem CrossSupportAffineGraphRefinement.refinedGraph_comp_supportAffineLine
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    R.refinedGraph K C d z hVs q m E hE N a i ≫
      R.refinedSupportPieceToSupportAffineLine
        K C d z hVs q m E hE N a =
    R.refinedSupportAffineLineGraph K C d z hVs q m E hE N a i := by
  apply pullback.hom_ext
  · rw [Category.assoc,
      R.refinedSupportPieceToSupportAffineLine_comp_oldLine,
      ← Category.assoc, R.refinedGraph_comp_comparison,
      Category.assoc, graphToSupportPiece_comp_supportAffineLine,
      R.refinedSupportAffineLineGraph_comp_oldLine]
  · calc
      (R.refinedGraph K C d z hVs q m E hE N a i ≫
          R.refinedSupportPieceToSupportAffineLine
            K C d z hVs q m E hE N a) ≫
          (R.refinedSupportAffineLineFamily
            K C d z hVs q m E hE N).hom =
        R.refinedGraph K C d z hVs q m E hE N a i ≫
          (R.refinedSupportPieceToSupportAffineLine
              K C d z hVs q m E hE N a ≫
            (R.refinedSupportAffineLineFamily
              K C d z hVs q m E hE N).hom) :=
        Category.assoc _ _ _
      _ = R.refinedGraph K C d z hVs q m E hE N a i ≫
          (R.refinedSupportPieceFamily
            K C d z hVs q m E hE N a).hom := by
        rw [R.refinedSupportPieceToSupportAffineLine_comp_base]
      _ = 𝟙 R.baseOpen.toScheme :=
        R.refinedGraph_comp_structure K C d z hVs q m E hE N a i
      _ = R.refinedSupportAffineLineGraph
          K C d z hVs q m E hE N a i ≫
          (R.refinedSupportAffineLineFamily
            K C d z hVs q m E hE N).hom :=
        (R.refinedSupportAffineLineGraph_comp_base
          K C d z hVs q m E hE N a i).symm

/-- Each refined owner graph is the exact inverse image of its matching
section under the rebased étale coordinate. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraph_isPullback_from_piece
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    IsPullback
      (R.refinedGraph K C d z hVs q m E hE N a i)
      (𝟙 R.baseOpen.toScheme)
      (R.refinedSupportPieceToSupportAffineLine
        K C d z hVs q m E hE N a)
      (R.refinedSupportAffineLineGraph
        K C d z hVs q m E hE N a i) := by
  let hPiece := R.refinedGraph_isPullback
    K C d z hVs q m E hE N a i
  let hCoordinate := supportPiece_coordinateGraph_isPullback
    K C d z hVs q m E hE N a i
  have hBig₀ := hPiece.paste_vert hCoordinate
  have hBig : IsPullback
      (R.refinedGraph K C d z hVs q m E hE N a i)
      R.baseOpen.ι
      (R.refinedSupportPieceToSupportAffineLine
          K C d z hVs q m E hE N a ≫
        R.refinedSupportAffineLineToSupportAffineLine
          K C d z hVs q m E hE N)
      (supportAffineLineGraph K C d z hVs q m E hE N a i) := by
    simpa only [Category.comp_id,
      R.refinedSupportPieceToSupportAffineLine_comp_oldLine] using hBig₀
  exact hBig.of_bot
    (R.refinedGraph_comp_supportAffineLine
      K C d z hVs q m E hE N a i)
    (R.refinedSupportAffineLineGraph_isPullback
      K C d z hVs q m E hE N a i)

/-- The standard affine-line value of a refined occurrence section. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineStandardValue
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    Γ(R.baseOpen.toScheme, ⊤) :=
  (R.refinedSupportAffineLineGraph K C d z hVs q m E hE N a i ≫
      (R.refinedSupportAffineLineIsoAffineSpace
        K C d z hVs q m E hE N).hom).appTop
    (AffineSpace.coord R.baseOpen.toScheme default)

/-- Every refined occurrence section becomes the standard affine-line
section with its transported value. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraph_comp_standardIso
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    R.refinedSupportAffineLineGraph K C d z hVs q m E hE N a i ≫
        (R.refinedSupportAffineLineIsoAffineSpace
          K C d z hVs q m E hE N).hom =
      lineSection (ULift.{u} (Fin 1)) R.baseOpen.toScheme
        (R.refinedSupportAffineLineStandardValue
          K C d z hVs q m E hE N a i) := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc,
      R.refinedSupportAffineLineIso_hom_projection,
      R.refinedSupportAffineLineGraph_comp_base,
      section_comp_projection]
  · intro k
    rw [Unique.eq_default k]
    rw [section_appTop_coordinate]
    rfl

/-- Sections of the rebased support affine line form an algebra over the
cross-support base. -/
noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineSectionsAlgebra :
    Algebra Γ(R.baseOpen.toScheme, ⊤)
      Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤) :=
  (R.refinedSupportAffineLineFamily
    K C d z hVs q m E hE N).hom.appTop.hom.toAlgebra

/-- Sections of a refined support piece form an algebra over the final
cross-support base. -/
noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportPieceSectionsAlgebra
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Algebra Γ(R.baseOpen.toScheme, ⊤)
      Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
  (R.refinedSupportPieceFamily
    K C d z hVs q m E hE N a).hom.appTop.hom.toAlgebra

/-- Transport global sections of the rebased line to standard affine-line
coordinates. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineToStandardSectionsAlgHom :
    Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤) →ₐ[
        Γ(R.baseOpen.toScheme, ⊤)]
      Γ(𝔸(ULift.{u} (Fin 1); R.baseOpen.toScheme), ⊤) where
  toRingHom := (R.refinedSupportAffineLineIsoAffineSpace
    K C d z hVs q m E hE N).inv.appTop.hom
  commutes' b := by
    let e := R.refinedSupportAffineLineIsoAffineSpace
      K C d z hVs q m E hE N
    have hinv : e.inv ≫
        (R.refinedSupportAffineLineFamily
          K C d z hVs q m E hE N).hom =
      (𝔸(ULift.{u} (Fin 1); R.baseOpen.toScheme) ↘
        R.baseOpen.toScheme) := by
      rw [← R.refinedSupportAffineLineIso_hom_projection]
      simp
    change e.inv.appTop
      ((R.refinedSupportAffineLineFamily
        K C d z hVs q m E hE N).hom.appTop b) =
      (𝔸(ULift.{u} (Fin 1); R.baseOpen.toScheme) ↘
        R.baseOpen.toScheme).appTop b
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hinv]

/-- Standard affine-line coordinates give an algebra equivalence on global
sections of the rebased line. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineToStandardSectionsAlgEquiv :
    Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤) ≃ₐ[
        Γ(R.baseOpen.toScheme, ⊤)]
      Γ(𝔸(ULift.{u} (Fin 1); R.baseOpen.toScheme), ⊤) := by
  let f := R.refinedSupportAffineLineToStandardSectionsAlgHom
    K C d z hVs q m E hE N
  apply AlgEquiv.ofBijective f
  exact ConcreteCategory.bijective_of_isIso
    ((R.refinedSupportAffineLineIsoAffineSpace
      K C d z hVs q m E hE N).inv.app
        (⊤ : (R.refinedSupportAffineLine
          K C d z hVs q m E hE N).Opens))

/-- Standard coordinates carry one refined section kernel to the kernel of
the corresponding standard section. -/
theorem CrossSupportAffineGraphRefinement.refinedStandardSectionsEquiv_map_graph_ker
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    Ideal.map
        (R.refinedSupportAffineLineToStandardSectionsAlgEquiv
          K C d z hVs q m E hE N).toRingEquiv.toRingHom
        (RingHom.ker
          (R.refinedSupportAffineLineGraph
            K C d z hVs q m E hE N a i).appTop.hom) =
      RingHom.ker
        (lineSection (ULift.{u} (Fin 1)) R.baseOpen.toScheme
          (R.refinedSupportAffineLineStandardValue
            K C d z hVs q m E hE N a i)).appTop.hom := by
  let e := R.refinedSupportAffineLineIsoAffineSpace
    K C d z hVs q m E hE N
  let graph := R.refinedSupportAffineLineGraph
    K C d z hVs q m E hE N a i
  let standard := lineSection (ULift.{u} (Fin 1)) R.baseOpen.toScheme
    (R.refinedSupportAffineLineStandardValue
      K C d z hVs q m E hE N a i)
  let A := R.refinedSupportAffineLineToStandardSectionsAlgEquiv
    K C d z hVs q m E hE N
  have hscheme : graph = standard ≫ e.inv := by
    have h := R.refinedSupportAffineLineGraph_comp_standardIso
      K C d z hVs q m E hE N a i
    change graph ≫ e.hom = standard at h
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact h
  have hring : graph.appTop.hom =
      standard.appTop.hom.comp e.inv.appTop.hom := by
    rw [hscheme, Scheme.Hom.comp_appTop]
    rfl
  have hA : A.toRingEquiv.toRingHom = e.inv.appTop.hom := by
    apply RingHom.ext
    intro x
    rfl
  rw [hA, hring]
  change Ideal.map e.inv.appTop.hom
      (Ideal.comap e.inv.appTop.hom
        (RingHom.ker standard.appTop.hom)) = _
  exact Ideal.map_comap_of_surjective e.inv.appTop.hom
    (ConcreteCategory.bijective_of_isIso
      (e.inv.app
        (⊤ : (R.refinedSupportAffineLine
          K C d z hVs q m E hE N).Opens))).2
    (RingHom.ker standard.appTop.hom)

/-- The multiplicity-sensitive product of the refined occurrence-section
ideals on the rebased affine line. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdeal
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Scheme.IdealSheafData
      (R.refinedSupportAffineLine K C d z hVs q m E hE N) :=
  ∏ i : OccurrencesAtSupport K C d z a,
    (R.refinedSupportAffineLineGraph
      K C d z hVs q m E hE N a i).ker

/-- The top-open ideal of the complete refined section product. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdealTop
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Ideal Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤) :=
  (R.refinedSupportAffineLineGraphProductIdeal
    K C d z hVs q m E hE N a).ideal
      ⟨⊤, @isAffineOpen_top _
        (R.refinedSupportAffineLine_isAffine
          K C d z hVs q m E hE N)⟩

/-- Standard coordinates identify the complete refined section product
with the standard product of section kernels. -/
theorem CrossSupportAffineGraphRefinement.refinedStandardSectionsEquiv_map_graphProductIdeal_top
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Ideal.map
        (R.refinedSupportAffineLineToStandardSectionsAlgEquiv
          K C d z hVs q m E hE N).toRingEquiv.toRingHom
        (R.refinedSupportAffineLineGraphProductIdealTop
          K C d z hVs q m E hE N a) =
      sectionGraphProductIdeal (ULift.{u} (Fin 1))
        R.baseOpen.toScheme (OccurrencesAtSupport K C d z a)
        (R.refinedSupportAffineLineStandardValue
          K C d z hVs q m E hE N a) := by
  classical
  letI : IsAffine
      (R.refinedSupportAffineLine K C d z hVs q m E hE N) :=
    R.refinedSupportAffineLine_isAffine K C d z hVs q m E hE N
  rw [CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdealTop,
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdeal,
    show
      ((∏ i : OccurrencesAtSupport K C d z a,
          (R.refinedSupportAffineLineGraph
            K C d z hVs q m E hE N a i).ker).ideal
            ⟨⊤, isAffineOpen_top _⟩) =
        ∏ i : OccurrencesAtSupport K C d z a,
          (R.refinedSupportAffineLineGraph
            K C d z hVs q m E hE N a i).ker.ideal
              ⟨⊤, isAffineOpen_top _⟩ by
      let J := fun i : OccurrencesAtSupport K C d z a ↦
        (R.refinedSupportAffineLineGraph
          K C d z hVs q m E hE N a i).ker
      have hprod (t : Finset (OccurrencesAtSupport K C d z a)) :
          (∏ i ∈ t, J i).ideal ⟨⊤, isAffineOpen_top _⟩ =
            ∏ i ∈ t, (J i).ideal ⟨⊤, isAffineOpen_top _⟩ := by
        induction t using Finset.induction_on with
        | empty => simp
        | @insert i t hi ih => simp [hi, ih]
      exact hprod Finset.univ,
    SectionProductRootAlgebra.ideal_map_fintype_prod,
    sectionGraphProductIdeal]
  apply Fintype.prod_congr
  intro i
  rw [Scheme.ker_of_isAffine]
  simp only [RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom,
    Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  exact R.refinedStandardSectionsEquiv_map_graph_ker
    K C d z hVs q m E hE N a i

/-- The graph-product quotient on the rebased common support line. -/
noncomputable abbrev
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductQuotient
    (a : Fin (geometricDistinctSupportCard K C d z)) :=
  Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤) ⧸
    R.refinedSupportAffineLineGraphProductIdealTop
      K C d z hVs q m E hE N a

/-- The refined support-line quotient is the monic root algebra of the
transported occurrence values over the cross-support base. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductQuotientEquivRoot
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportAffineLineGraphProductQuotient
        K C d z hVs q m E hE N a ≃ₐ[Γ(R.baseOpen.toScheme, ⊤)]
      AdjoinRoot
        (SectionProductRootAlgebra.sectionPolynomial
          Γ(R.baseOpen.toScheme, ⊤)
          (OccurrencesAtSupport K C d z a)
          (R.refinedSupportAffineLineStandardValue
            K C d z hVs q m E hE N a)) := by
  letI : IsAffine R.baseOpen.toScheme := R.base_isAffine
  letI : IsAffine
      (R.refinedSupportAffineLine K C d z hVs q m E hE N) :=
    R.refinedSupportAffineLine_isAffine K C d z hVs q m E hE N
  letI : Nonempty (⊤ : R.baseOpen.toScheme.Opens) :=
    ⟨⟨⟨exactBasePoint K C d z hVs q m E hE N,
      R.exact_mem_base⟩, trivial⟩⟩
  exact (Ideal.quotientEquivAlg
      (R.refinedSupportAffineLineGraphProductIdealTop
        K C d z hVs q m E hE N a)
      (sectionGraphProductIdeal (ULift.{u} (Fin 1))
        R.baseOpen.toScheme (OccurrencesAtSupport K C d z a)
        (R.refinedSupportAffineLineStandardValue
          K C d z hVs q m E hE N a))
      (R.refinedSupportAffineLineToStandardSectionsAlgEquiv
        K C d z hVs q m E hE N)
      (R.refinedStandardSectionsEquiv_map_graphProductIdeal_top
        K C d z hVs q m E hE N a).symm).trans
    (sectionGraphProductQuotientEquivRoot
      (ULift.{u} (Fin 1)) R.baseOpen.toScheme
      (OccurrencesAtSupport K C d z a)
      (R.refinedSupportAffineLineStandardValue
        K C d z hVs q m E hE N a))

/-- The quotient on one refined support line has rank equal to the number
of occurrences owned by that support member. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductQuotient_finrank
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.finrank Γ(R.baseOpen.toScheme, ⊤)
        (R.refinedSupportAffineLineGraphProductQuotient
          K C d z hVs q m E hE N a) =
      Fintype.card (OccurrencesAtSupport K C d z a) := by
  letI : IsAffine R.baseOpen.toScheme := R.base_isAffine
  letI : Nonempty (⊤ : R.baseOpen.toScheme.Opens) :=
    ⟨⟨⟨exactBasePoint K C d z hVs q m E hE N,
      R.exact_mem_base⟩, trivial⟩⟩
  rw [(R.refinedSupportAffineLineGraphProductQuotientEquivRoot
    K C d z hVs q m E hE N a).toLinearEquiv.finrank_eq]
  letI : Fact
      (SectionProductRootAlgebra.sectionPolynomial
        Γ(R.baseOpen.toScheme, ⊤)
        (OccurrencesAtSupport K C d z a)
        (R.refinedSupportAffineLineStandardValue
          K C d z hVs q m E hE N a)).Monic :=
    ⟨SectionProductRootAlgebra.sectionPolynomial_monic
      Γ(R.baseOpen.toScheme, ⊤)
      (OccurrencesAtSupport K C d z a)
      (R.refinedSupportAffineLineStandardValue
        K C d z hVs q m E hE N a)⟩
  rw [MonicRootFamily.rootAlgebra_finrank]
  exact SectionProductRootAlgebra.sectionPolynomial_natDegree
    Γ(R.baseOpen.toScheme, ⊤)
    (OccurrencesAtSupport K C d z a)
    (R.refinedSupportAffineLineStandardValue
      K C d z hVs q m E hE N a)

/-- Pulling one rebased affine-line section to a refined support piece gives
the kernel sheaf of the corresponding refined graph. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraph_ker_comap_piece
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (R.refinedSupportAffineLineGraph
        K C d z hVs q m E hE N a i).ker.comap
        (R.refinedSupportPieceToSupportAffineLine
          K C d z hVs q m E hE N a) =
      (R.refinedGraph K C d z hVs q m E hE N a i).ker := by
  let sectionGraph := R.refinedSupportAffineLineGraph
    K C d z hVs q m E hE N a i
  let familyHom := (R.refinedSupportAffineLineFamily
    K C d z hVs q m E hE N).hom
  let coordinateHom := R.refinedSupportPieceToSupportAffineLine
    K C d z hVs q m E hE N a
  let pieceGraph := R.refinedGraph K C d z hVs q m E hE N a i
  letI : IsSeparated familyHom := by
    dsimp only [familyHom,
      CrossSupportAffineGraphRefinement.refinedSupportAffineLineFamily]
    infer_instance
  letI : IsClosedImmersion sectionGraph := by
    haveI : IsClosedImmersion (sectionGraph ≫ familyHom) := by
      rw [show sectionGraph ≫ familyHom = 𝟙 R.baseOpen.toScheme from
        R.refinedSupportAffineLineGraph_comp_base
          K C d z hVs q m E hE N a i]
      infer_instance
    exact IsClosedImmersion.of_comp sectionGraph familyHom
  let h := R.refinedSupportAffineLineGraph_isPullback_from_piece
    K C d z hVs q m E hE N a i
  change sectionGraph.ker.comap coordinateHom = pieceGraph.ker
  calc
    sectionGraph.ker.comap coordinateHom =
        (pullback.fst coordinateHom sectionGraph).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
        sectionGraph coordinateHom).symm
    _ = (h.isoPullback.hom ≫
        pullback.fst coordinateHom sectionGraph).ker :=
      (Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom
        (pullback.fst coordinateHom sectionGraph)).symm
    _ = pieceGraph.ker := by
      rw [h.isoPullback_hom_fst]

/-- The intrinsic product of all owner graph kernels on one refined support
piece. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductIdeal
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Scheme.IdealSheafData
      (R.refinedSupportPiece K C d z hVs q m E hE N a) :=
  ∏ i : OccurrencesAtSupport K C d z a,
    (R.refinedGraph K C d z hVs q m E hE N a i).ker

/-- The refined owner-graph product is the pullback of the corresponding
product of occurrence sections on the rebased affine line. -/
theorem CrossSupportAffineGraphRefinement.refinedPieceGraphProduct_eq_coordinate_comap
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportPieceGraphProductIdeal
        K C d z hVs q m E hE N a =
      (R.refinedSupportAffineLineGraphProductIdeal
        K C d z hVs q m E hE N a).comap
        (R.refinedSupportPieceToSupportAffineLine
          K C d z hVs q m E hE N a) := by
  classical
  letI : IsAffine
      (R.refinedSupportPiece K C d z hVs q m E hE N a) :=
    R.refinedSupportPiece_isAffine K C d z hVs q m E hE N a
  letI : IsAffine
      (R.refinedSupportAffineLine K C d z hVs q m E hE N) :=
    R.refinedSupportAffineLine_isAffine K C d z hVs q m E hE N
  rw [CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductIdeal,
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdeal,
    idealSheaf_comap_finsetProd_of_isAffine]
  apply Finset.prod_congr rfl
  intro i _
  exact (R.refinedSupportAffineLineGraph_ker_comap_piece
    K C d z hVs q m E hE N a i).symm

/-- The top-open ideal of the refined owner-graph product. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductIdealTop
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Ideal Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
  (R.refinedSupportPieceGraphProductIdeal
    K C d z hVs q m E hE N a).ideal
      ⟨⊤, @isAffineOpen_top _
        (R.refinedSupportPiece_isAffine
          K C d z hVs q m E hE N a)⟩

/-- On global sections, the refined owner product is extension of the
rebased affine-line section product. -/
theorem CrossSupportAffineGraphRefinement.refinedPieceGraphProductIdealTop_eq_coordinate_map
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportPieceGraphProductIdealTop
        K C d z hVs q m E hE N a =
      Ideal.map
        (R.refinedSupportPieceToSupportAffineLine
          K C d z hVs q m E hE N a).appTop.hom
        (R.refinedSupportAffineLineGraphProductIdealTop
          K C d z hVs q m E hE N a) := by
  letI : IsAffine
      (R.refinedSupportPiece K C d z hVs q m E hE N a) :=
    R.refinedSupportPiece_isAffine K C d z hVs q m E hE N a
  letI : IsAffine
      (R.refinedSupportAffineLine K C d z hVs q m E hE N) :=
    R.refinedSupportAffineLine_isAffine K C d z hVs q m E hE N
  rw [CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductIdealTop,
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdealTop,
    R.refinedPieceGraphProduct_eq_coordinate_comap]
  exact ideal_comap_top_eq_map_of_isAffine
    (R.refinedSupportAffineLineGraphProductIdeal
      K C d z hVs q m E hE N a)
    (R.refinedSupportPieceToSupportAffineLine
      K C d z hVs q m E hE N a)

/-- For one refined occurrence section, extension along the étale support
coordinate induces an isomorphism on the corresponding quotient. -/
theorem CrossSupportAffineGraphRefinement.refinedPiece_quotientMap_bijective_section
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    letI : Algebra
        Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
        Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
      (R.refinedSupportPieceToSupportAffineLine
        K C d z hVs q m E hE N a).appTop.hom.toAlgebra
    Function.Bijective
      (extendedQuotientMap
        Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
        Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤)
        ((R.refinedSupportAffineLineGraph
          K C d z hVs q m E hE N a i).ker.ideal
            ⟨⊤, @isAffineOpen_top _
              (R.refinedSupportAffineLine_isAffine
                K C d z hVs q m E hE N)⟩)) := by
  letI : IsAffine
      (R.refinedSupportAffineLine K C d z hVs q m E hE N) :=
    R.refinedSupportAffineLine_isAffine K C d z hVs q m E hE N
  letI : IsAffine
      (R.refinedSupportPiece K C d z hVs q m E hE N a) :=
    R.refinedSupportPiece_isAffine K C d z hVs q m E hE N a
  let coordinateHom := R.refinedSupportPieceToSupportAffineLine
    K C d z hVs q m E hE N a
  let pieceGraph := R.refinedGraph K C d z hVs q m E hE N a i
  let sectionGraph := R.refinedSupportAffineLineGraph
    K C d z hVs q m E hE N a i
  let familyHom := (R.refinedSupportAffineLineFamily
    K C d z hVs q m E hE N).hom
  letI : Algebra
      Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
      Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
    coordinateHom.appTop.hom.toAlgebra
  letI : IsSeparated familyHom := by
    dsimp only [familyHom,
      CrossSupportAffineGraphRefinement.refinedSupportAffineLineFamily]
    infer_instance
  letI : IsClosedImmersion sectionGraph := by
    haveI : IsClosedImmersion (sectionGraph ≫ familyHom) := by
      rw [show sectionGraph ≫ familyHom = 𝟙 R.baseOpen.toScheme from
        R.refinedSupportAffineLineGraph_comp_base
          K C d z hVs q m E hE N a i]
      infer_instance
    exact IsClosedImmersion.of_comp sectionGraph familyHom
  let hcart := R.refinedSupportAffineLineGraph_isPullback_from_piece
    K C d z hVs q m E hE N a i
  letI : IsClosedImmersion pieceGraph :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsClosedImmersion) hcart.flip inferInstance
  have hcomp : pieceGraph.appTop.hom.comp coordinateHom.appTop.hom =
      sectionGraph.appTop.hom := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    exact congrArg (fun f : R.baseOpen.toScheme ⟶
        R.refinedSupportAffineLine K C d z hVs q m E hE N ↦
      f.appTop.hom)
      (R.refinedGraph_comp_supportAffineLine
        K C d z hVs q m E hE N a i)
  have hkerR :
      sectionGraph.ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
        RingHom.ker
          (pieceGraph.appTop.hom.comp coordinateHom.appTop.hom) := by
    rw [hcomp, Scheme.ker_of_isAffine]
    simp
  have hkerS :
      Ideal.map coordinateHom.appTop.hom
          (sectionGraph.ker.ideal ⟨⊤, isAffineOpen_top _⟩) =
        RingHom.ker pieceGraph.appTop.hom := by
    rw [← ideal_comap_top_eq_map_of_isAffine]
    rw [show sectionGraph.ker.comap coordinateHom = pieceGraph.ker from
      R.refinedSupportAffineLineGraph_ker_comap_piece
        K C d z hVs q m E hE N a i]
    rw [Scheme.ker_of_isAffine]
    simp
  apply extendedQuotientMap_bijective_of_kernel_square
    _ _ (sectionGraph.ker.ideal ⟨⊤, isAffineOpen_top _⟩)
      pieceGraph.appTop.hom
  · exact pieceGraph.app_surjective ⊤ (isAffineOpen_top _)
  · change Function.Surjective
      (pieceGraph.appTop.hom.comp coordinateHom.appTop.hom)
    rw [hcomp]
    exact sectionGraph.app_surjective ⊤ (isAffineOpen_top _)
  · exact hkerR
  · exact hkerS

/-- Extension along the refined étale coordinate preserves the full
multiplicity-sensitive product quotient. -/
theorem CrossSupportAffineGraphRefinement.refinedPiece_quotientMap_bijective_sections
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    letI : Algebra
        Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
        Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
      (R.refinedSupportPieceToSupportAffineLine
        K C d z hVs q m E hE N a).appTop.hom.toAlgebra
    Function.Bijective
      (extendedQuotientMap
        Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
        Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤)
        (R.refinedSupportAffineLineGraphProductIdealTop
          K C d z hVs q m E hE N a)) := by
  letI : IsAffine
      (R.refinedSupportAffineLine K C d z hVs q m E hE N) :=
    R.refinedSupportAffineLine_isAffine K C d z hVs q m E hE N
  letI : IsAffine
      (R.refinedSupportPiece K C d z hVs q m E hE N a) :=
    R.refinedSupportPiece_isAffine K C d z hVs q m E hE N a
  let coordinateHom := R.refinedSupportPieceToSupportAffineLine
    K C d z hVs q m E hE N a
  letI : Algebra
      Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
      Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
    coordinateHom.appTop.hom.toAlgebra
  have hEtale : coordinateHom.appTop.hom.Etale :=
    HasRingHomProperty.appTop (P := @Etale) (Q := RingHom.Etale)
      coordinateHom (inferInstance : Etale coordinateHom)
  letI : Algebra.Etale
      Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
      Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
    hEtale.toAlgebra
  rw [CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdealTop,
    CrossSupportAffineGraphRefinement.refinedSupportAffineLineGraphProductIdeal]
  rw [show
      ((∏ i : OccurrencesAtSupport K C d z a,
          (R.refinedSupportAffineLineGraph
            K C d z hVs q m E hE N a i).ker).ideal
            ⟨⊤, isAffineOpen_top _⟩) =
        ∏ i : OccurrencesAtSupport K C d z a,
          (R.refinedSupportAffineLineGraph
            K C d z hVs q m E hE N a i).ker.ideal
              ⟨⊤, isAffineOpen_top _⟩ by
    classical
    let J := fun i : OccurrencesAtSupport K C d z a ↦
      (R.refinedSupportAffineLineGraph
        K C d z hVs q m E hE N a i).ker
    have hprod (t : Finset (OccurrencesAtSupport K C d z a)) :
        (∏ i ∈ t, J i).ideal ⟨⊤, isAffineOpen_top _⟩ =
          ∏ i ∈ t, (J i).ideal ⟨⊤, isAffineOpen_top _⟩ := by
      induction t using Finset.induction_on with
      | empty => simp
      | @insert i t hi ih => simp [hi, ih]
    exact hprod Finset.univ]
  exact extendedQuotientMap_bijective_fintypeProd
    Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
    Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤)
    (fun i ↦
      (R.refinedSupportAffineLineGraph
        K C d z hVs q m E hE N a i).ker.ideal
          ⟨⊤, isAffineOpen_top _⟩)
    (R.refinedPiece_quotientMap_bijective_section
      K C d z hVs q m E hE N a)

/-- The refined graph-product quotient on one support piece. -/
noncomputable abbrev
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductQuotient
    (a : Fin (geometricDistinctSupportCard K C d z)) :=
  Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) ⧸
    R.refinedSupportPieceGraphProductIdealTop
      K C d z hVs q m E hE N a

/-- The extension map from the rebased affine-line quotient to the quotient
by the extended ideal on a refined support piece. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportPieceExtendedQuotientAlgHom
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportAffineLineGraphProductQuotient
        K C d z hVs q m E hE N a →ₐ[Γ(R.baseOpen.toScheme, ⊤)]
      (Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) ⧸
        Ideal.map
          (R.refinedSupportPieceToSupportAffineLine
            K C d z hVs q m E hE N a).appTop.hom
          (R.refinedSupportAffineLineGraphProductIdealTop
            K C d z hVs q m E hE N a)) := by
  let coordinateHom := R.refinedSupportPieceToSupportAffineLine
    K C d z hVs q m E hE N a
  letI : Algebra
      Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
      Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
    coordinateHom.appTop.hom.toAlgebra
  refine
    { toRingHom := extendedQuotientMap
        Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
        Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤)
        (R.refinedSupportAffineLineGraphProductIdealTop
          K C d z hVs q m E hE N a)
      commutes' := ?_ }
  intro b
  change Ideal.Quotient.mk _
      (coordinateHom.appTop.hom
        ((R.refinedSupportAffineLineFamily
          K C d z hVs q m E hE N).hom.appTop.hom b)) =
    Ideal.Quotient.mk _
      ((R.refinedSupportPieceFamily
        K C d z hVs q m E hE N a).hom.appTop.hom b)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    R.refinedSupportPieceToSupportAffineLine_comp_base]

/-- Extension along the refined étale coordinate is an equivalence on the
full graph-product quotients. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportPieceExtendedQuotientAlgEquiv
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportAffineLineGraphProductQuotient
        K C d z hVs q m E hE N a ≃ₐ[Γ(R.baseOpen.toScheme, ⊤)]
      (Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) ⧸
        Ideal.map
          (R.refinedSupportPieceToSupportAffineLine
            K C d z hVs q m E hE N a).appTop.hom
          (R.refinedSupportAffineLineGraphProductIdealTop
            K C d z hVs q m E hE N a)) := by
  let coordinateHom := R.refinedSupportPieceToSupportAffineLine
    K C d z hVs q m E hE N a
  letI : Algebra
      Γ(R.refinedSupportAffineLine K C d z hVs q m E hE N, ⊤)
      Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
    coordinateHom.appTop.hom.toAlgebra
  apply AlgEquiv.ofBijective
    (R.refinedSupportPieceExtendedQuotientAlgHom
      K C d z hVs q m E hE N a)
  exact R.refinedPiece_quotientMap_bijective_sections
    K C d z hVs q m E hE N a

/-- A refined support-piece quotient is the monic root algebra determined
by its occurrence coordinates over the cross-support base. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductQuotientEquivRoot
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedSupportPieceGraphProductQuotient
        K C d z hVs q m E hE N a ≃ₐ[Γ(R.baseOpen.toScheme, ⊤)]
      AdjoinRoot
        (SectionProductRootAlgebra.sectionPolynomial
          Γ(R.baseOpen.toScheme, ⊤)
          (OccurrencesAtSupport K C d z a)
          (R.refinedSupportAffineLineStandardValue
            K C d z hVs q m E hE N a)) := by
  let mapIdeal := Ideal.map
    (R.refinedSupportPieceToSupportAffineLine
      K C d z hVs q m E hE N a).appTop.hom
    (R.refinedSupportAffineLineGraphProductIdealTop
      K C d z hVs q m E hE N a)
  let eIdeal :
      (Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) ⧸
        mapIdeal) ≃ₐ[Γ(R.baseOpen.toScheme, ⊤)]
      R.refinedSupportPieceGraphProductQuotient
        K C d z hVs q m E hE N a :=
    Ideal.quotientEquivAlgOfEq Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedPieceGraphProductIdealTop_eq_coordinate_map
        K C d z hVs q m E hE N a).symm
  exact ((R.refinedSupportPieceExtendedQuotientAlgEquiv
      K C d z hVs q m E hE N a).trans eIdeal).symm.trans
    (R.refinedSupportAffineLineGraphProductQuotientEquivRoot
      K C d z hVs q m E hE N a)

/-- One refined support-piece quotient has rank equal to the number of
occurrences owned by its support member. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductQuotient_finrank
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.finrank Γ(R.baseOpen.toScheme, ⊤)
        (R.refinedSupportPieceGraphProductQuotient
          K C d z hVs q m E hE N a) =
      Fintype.card (OccurrencesAtSupport K C d z a) := by
  letI : IsAffine R.baseOpen.toScheme := R.base_isAffine
  letI : Nonempty (⊤ : R.baseOpen.toScheme.Opens) :=
    ⟨⟨⟨exactBasePoint K C d z hVs q m E hE N,
      R.exact_mem_base⟩, trivial⟩⟩
  rw [(R.refinedSupportPieceGraphProductQuotientEquivRoot
    K C d z hVs q m E hE N a).toLinearEquiv.finrank_eq]
  letI : Fact
      (SectionProductRootAlgebra.sectionPolynomial
        Γ(R.baseOpen.toScheme, ⊤)
        (OccurrencesAtSupport K C d z a)
        (R.refinedSupportAffineLineStandardValue
          K C d z hVs q m E hE N a)).Monic :=
    ⟨SectionProductRootAlgebra.sectionPolynomial_monic
      Γ(R.baseOpen.toScheme, ⊤)
      (OccurrencesAtSupport K C d z a)
      (R.refinedSupportAffineLineStandardValue
        K C d z hVs q m E hE N a)⟩
  rw [MonicRootFamily.rootAlgebra_finrank]
  exact SectionProductRootAlgebra.sectionPolynomial_natDegree
    Γ(R.baseOpen.toScheme, ⊤)
    (OccurrencesAtSupport K C d z a)
    (R.refinedSupportAffineLineStandardValue
      K C d z hVs q m E hE N a)

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductQuotient_free
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.Free Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedSupportPieceGraphProductQuotient
        K C d z hVs q m E hE N a) := by
  letI : Fact
      (SectionProductRootAlgebra.sectionPolynomial
        Γ(R.baseOpen.toScheme, ⊤)
        (OccurrencesAtSupport K C d z a)
        (R.refinedSupportAffineLineStandardValue
          K C d z hVs q m E hE N a)).Monic :=
    ⟨SectionProductRootAlgebra.sectionPolynomial_monic
      Γ(R.baseOpen.toScheme, ⊤)
      (OccurrencesAtSupport K C d z a)
      (R.refinedSupportAffineLineStandardValue
        K C d z hVs q m E hE N a)⟩
  exact Module.Free.of_equiv
    (R.refinedSupportPieceGraphProductQuotientEquivRoot
      K C d z hVs q m E hE N a).symm.toLinearEquiv

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductQuotient_finite
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.Finite Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedSupportPieceGraphProductQuotient
        K C d z hVs q m E hE N a) := by
  letI : Fact
      (SectionProductRootAlgebra.sectionPolynomial
        Γ(R.baseOpen.toScheme, ⊤)
        (OccurrencesAtSupport K C d z a)
        (R.refinedSupportAffineLineStandardValue
          K C d z hVs q m E hE N a)).Monic :=
    ⟨SectionProductRootAlgebra.sectionPolynomial_monic
      Γ(R.baseOpen.toScheme, ⊤)
      (OccurrencesAtSupport K C d z a)
      (R.refinedSupportAffineLineStandardValue
        K C d z hVs q m E hE N a)⟩
  exact Module.Finite.equiv
    (R.refinedSupportPieceGraphProductQuotientEquivRoot
      K C d z hVs q m E hE N a).symm.toLinearEquiv

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductQuotient_flat
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.Flat Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedSupportPieceGraphProductQuotient
        K C d z hVs q m E hE N a) := by
  infer_instance

/-- The product of all refined support-piece graph quotients. -/
noncomputable abbrev
    CrossSupportAffineGraphRefinement.refinedSupportGraphProductQuotientAlgebra :=
  ∀ a : Fin (geometricDistinctSupportCard K C d z),
    R.refinedSupportPieceGraphProductQuotient
      K C d z hVs q m E hE N a

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportGraphProductQuotientAlgebra_free :
    Module.Free Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedSupportGraphProductQuotientAlgebra
        K C d z hVs q m E hE N) := by
  infer_instance

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportGraphProductQuotientAlgebra_finite :
    Module.Finite Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedSupportGraphProductQuotientAlgebra
        K C d z hVs q m E hE N) := by
  infer_instance

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedSupportGraphProductQuotientAlgebra_flat :
    Module.Flat Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedSupportGraphProductQuotientAlgebra
        K C d z hVs q m E hE N) := by
  infer_instance

/-- The ranks of the refined support-piece quotients sum to the original
ordered degree. -/
theorem CrossSupportAffineGraphRefinement.sum_refinedSupportPieceGraphProductQuotient_finrank :
    ∑ a : Fin (geometricDistinctSupportCard K C d z),
        Module.finrank Γ(R.baseOpen.toScheme, ⊤)
          (R.refinedSupportPieceGraphProductQuotient
            K C d z hVs q m E hE N a) = d := by
  rw [Finset.sum_congr rfl (fun a _ ↦
    R.refinedSupportPieceGraphProductQuotient_finrank
      K C d z hVs q m E hE N a)]
  exact FiniteSupportIndex.sum_supportMultiplicity
    (Spec (.of K)) d C z

/-- The assembled refined graph-product algebra is finite free of rank the
original ordered degree, including on collision strata. -/
theorem CrossSupportAffineGraphRefinement.refinedSupportGraphProductQuotientAlgebra_finrank :
    Module.finrank Γ(R.baseOpen.toScheme, ⊤)
        (R.refinedSupportGraphProductQuotientAlgebra
          K C d z hVs q m E hE N) = d := by
  letI : IsAffine R.baseOpen.toScheme := R.base_isAffine
  letI : Nonempty (⊤ : R.baseOpen.toScheme.Opens) :=
    ⟨⟨⟨exactBasePoint K C d z hVs q m E hE N,
      R.exact_mem_base⟩, trivial⟩⟩
  rw [Module.finrank_pi_fintype]
  exact R.sum_refinedSupportPieceGraphProductQuotient_finrank
    K C d z hVs q m E hE N

/-- The pulled-back universal coordinate-graph product on a refined support
piece is its intrinsic owner-graph product. -/
theorem CrossSupportAffineGraphRefinement.refinedCoordinateGraphProduct_eq_pieceGraphProduct
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (∏ i : Fin d,
      R.refinedCoordinateGraphIdealAt
        K C d z hVs q m E hE N a i) =
      R.refinedSupportPieceGraphProductIdeal
        K C d z hVs q m E hE N a := by
  rw [R.refinedCoordinateGraphProduct_eq_ownerGraphs]
  rfl

/-- The top-open ideal of the pulled-back universal coordinate-graph
product on one refined support summand. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductIdealTop
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Ideal Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) :=
  (∏ i : Fin d,
    R.refinedCoordinateGraphIdealAt
      K C d z hVs q m E hE N a i).ideal
      ⟨⊤, @isAffineOpen_top _
        (R.refinedSupportPiece_isAffine
          K C d z hVs q m E hE N a)⟩

/-- On affine global sections, the pulled-back universal coordinate ideal
is the intrinsic owner-graph product ideal. -/
theorem CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductIdealTop_eq_ownerGraphProduct
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedCoordinateGraphProductIdealTop
        K C d z hVs q m E hE N a =
      R.refinedSupportPieceGraphProductIdealTop
        K C d z hVs q m E hE N a := by
  rw [CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductIdealTop,
    CrossSupportAffineGraphRefinement.refinedSupportPieceGraphProductIdealTop,
    R.refinedCoordinateGraphProduct_eq_pieceGraphProduct]

/-- The quotient by the pulled-back universal coordinate-graph product on
one refined support summand. -/
noncomputable abbrev
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductQuotient
    (a : Fin (geometricDistinctSupportCard K C d z)) :=
  Γ(R.refinedSupportPiece K C d z hVs q m E hE N a, ⊤) ⧸
    R.refinedCoordinateGraphProductIdealTop
      K C d z hVs q m E hE N a

/-- The universal-coordinate quotient on a refined summand is the checked
intrinsic owner-graph quotient. -/
noncomputable def
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductQuotientEquivOwnerGraphs
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    R.refinedCoordinateGraphProductQuotient
        K C d z hVs q m E hE N a ≃ₐ[Γ(R.baseOpen.toScheme, ⊤)]
      R.refinedSupportPieceGraphProductQuotient
        K C d z hVs q m E hE N a :=
  Ideal.quotientEquivAlgOfEq Γ(R.baseOpen.toScheme, ⊤)
    (R.refinedCoordinateGraphProductIdealTop_eq_ownerGraphProduct
      K C d z hVs q m E hE N a)

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductQuotient_free
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.Free Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedCoordinateGraphProductQuotient
        K C d z hVs q m E hE N a) := by
  exact Module.Free.of_equiv
    (R.refinedCoordinateGraphProductQuotientEquivOwnerGraphs
      K C d z hVs q m E hE N a).symm.toLinearEquiv

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductQuotient_finite
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.Finite Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedCoordinateGraphProductQuotient
        K C d z hVs q m E hE N a) := by
  exact Module.Finite.equiv
    (R.refinedCoordinateGraphProductQuotientEquivOwnerGraphs
      K C d z hVs q m E hE N a).symm.toLinearEquiv

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductQuotient_flat
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.Flat Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedCoordinateGraphProductQuotient
        K C d z hVs q m E hE N a) := by
  infer_instance

/-- The universal-coordinate quotient on one refined summand has rank its
owner multiplicity. -/
theorem CrossSupportAffineGraphRefinement.refinedCoordinateGraphProductQuotient_finrank
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    Module.finrank Γ(R.baseOpen.toScheme, ⊤)
        (R.refinedCoordinateGraphProductQuotient
          K C d z hVs q m E hE N a) =
      Fintype.card (OccurrencesAtSupport K C d z a) := by
  rw [(R.refinedCoordinateGraphProductQuotientEquivOwnerGraphs
    K C d z hVs q m E hE N a).toLinearEquiv.finrank_eq]
  exact R.refinedSupportPieceGraphProductQuotient_finrank
    K C d z hVs q m E hE N a

/-- The product algebra of the universal-coordinate quotients on all
refined support summands. -/
noncomputable abbrev
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphQuotientAlgebra :=
  ∀ a : Fin (geometricDistinctSupportCard K C d z),
    R.refinedCoordinateGraphProductQuotient
      K C d z hVs q m E hE N a

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphQuotientAlgebra_free :
    Module.Free Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedCoordinateGraphQuotientAlgebra
        K C d z hVs q m E hE N) := by
  infer_instance

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphQuotientAlgebra_finite :
    Module.Finite Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedCoordinateGraphQuotientAlgebra
        K C d z hVs q m E hE N) := by
  infer_instance

noncomputable instance
    CrossSupportAffineGraphRefinement.refinedCoordinateGraphQuotientAlgebra_flat :
    Module.Flat Γ(R.baseOpen.toScheme, ⊤)
      (R.refinedCoordinateGraphQuotientAlgebra
        K C d z hVs q m E hE N) := by
  infer_instance

/-- Across the complete refined support family, the pulled-back universal
incidence quotient is finite free of rank the original ordered degree. -/
theorem CrossSupportAffineGraphRefinement.refinedCoordinateGraphQuotientAlgebra_finrank :
    Module.finrank Γ(R.baseOpen.toScheme, ⊤)
        (R.refinedCoordinateGraphQuotientAlgebra
          K C d z hVs q m E hE N) = d := by
  letI : IsAffine R.baseOpen.toScheme := R.base_isAffine
  letI : Nonempty (⊤ : R.baseOpen.toScheme.Opens) :=
    ⟨⟨⟨exactBasePoint K C d z hVs q m E hE N,
      R.exact_mem_base⟩, trivial⟩⟩
  rw [Module.finrank_pi_fintype]
  rw [Finset.sum_congr rfl (fun a _ ↦
    R.refinedCoordinateGraphProductQuotient_finrank
      K C d z hVs q m E hE N a)]
  exact FiniteSupportIndex.sum_supportMultiplicity
    (Spec (.of K)) d C z

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineSupportCoproduct
