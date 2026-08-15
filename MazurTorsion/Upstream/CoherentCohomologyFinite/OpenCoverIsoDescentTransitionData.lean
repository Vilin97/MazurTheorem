/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentObject
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentBaseChange

/-!
# Pair-overlap transition data for an isomorphism of open covers

The component maps of an open-cover isomorphism and its induced maps on
pair overlaps form commutative squares for both legs of every descent
transition.  This file packages the resulting pullback transition and a
common normal form used to compare it with canonical global restriction.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Restriction to a glued-cover chart, with the chart scheme exposed in
the result type. -/
abbrev openCoverRestriction
    (𝒰 : X.OpenCover) (W : 𝒰.gluedCover.glued.Modules)
    (i : 𝒰.I₀) : (𝒰.X i).Modules :=
  (pullback (gluedCoverChartMap 𝒰 i)).obj W

/-- The two publicly typed routes from an open-cover overlap to its glued
scheme agree. -/
theorem openCoverRestrictionComposite_eq
    (𝒰 : X.OpenCover) (i j : 𝒰.I₀) :
    overlapFst 𝒰 i j ≫ gluedCoverChartMap 𝒰 i =
      overlapTarget 𝒰 i j ≫ gluedCoverChartMap 𝒰 j :=
  coverRestrictionComposite_eq 𝒰.gluedCover i j

/-- The canonical transition for an open cover, with both chart schemes
and overlap legs exposed in its public type. -/
noncomputable def openCoverRestrictionTransition
    (𝒰 : X.OpenCover) (W : 𝒰.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    (pullback (overlapFst 𝒰 i j)).obj
        (openCoverRestriction 𝒰 W i) ≅
      (pullback (overlapTarget 𝒰 i j)).obj
        (openCoverRestriction 𝒰 W j) :=
  (pullbackComp
      (overlapFst 𝒰 i j)
      (gluedCoverChartMap 𝒰 i)).app W ≪≫
    (pullbackCongr
      (openCoverRestrictionComposite_eq 𝒰 i j)).app W ≪≫
    (pullbackComp
      (overlapTarget 𝒰 i j)
      (gluedCoverChartMap 𝒰 j)).symm.app W

@[simp]
theorem restrictionFunctor_gluedCover_obj_chart
    (𝒰 : X.OpenCover) (W : 𝒰.gluedCover.glued.Modules)
    (i : 𝒰.I₀) :
    ((restrictionFunctor (D := 𝒰.gluedCover)).obj W).chart i =
      openCoverRestriction 𝒰 W i :=
  rfl

@[simp]
theorem restrictionFunctor_gluedCover_obj_transition
    (𝒰 : X.OpenCover) (W : 𝒰.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    ((restrictionFunctor (D := 𝒰.gluedCover)).obj W).transition i j =
      openCoverRestrictionTransition 𝒰 W i j :=
  rfl

private theorem three_square_composite
    {C : Type*} [Category C]
    {A₀ B₀ C₀ D₀ E₀ F₀ G₀ H₀ : C}
    {f : A₀ ⟶ B₀} {sB : B₀ ⟶ C₀}
    {sA : A₀ ⟶ D₀} {mi : D₀ ⟶ C₀}
    {tB : C₀ ⟶ E₀} {tA : D₀ ⟶ F₀}
    {mj : F₀ ⟶ E₀} {uB : E₀ ⟶ H₀}
    {uA : F₀ ⟶ G₀} {fj : G₀ ⟶ H₀}
    (hs : f ≫ sB = sA ≫ mi)
    (hc : mi ≫ tB = tA ≫ mj)
    (hi : mj ≫ uB = uA ≫ fj) :
    f ≫ ((sB ≫ tB) ≫ uB) =
      ((sA ≫ tA) ≫ uA) ≫ fj := by
  calc
    f ≫ ((sB ≫ tB) ≫ uB) =
        ((f ≫ sB) ≫ tB) ≫ uB := by
      simp only [Category.assoc]
    _ = ((sA ≫ mi) ≫ tB) ≫ uB :=
      congrArg (fun z => (z ≫ tB) ≫ uB) hs
    _ = (sA ≫ (mi ≫ tB)) ≫ uB :=
      congrArg (fun z => z ≫ uB) (Category.assoc sA mi tB)
    _ = (sA ≫ (tA ≫ mj)) ≫ uB :=
      congrArg (fun z => (sA ≫ z) ≫ uB) hc
    _ = ((sA ≫ tA) ≫ mj) ≫ uB :=
      congrArg (fun z => z ≫ uB) (Category.assoc sA tA mj).symm
    _ = (sA ≫ tA) ≫ (mj ≫ uB) :=
      Category.assoc (sA ≫ tA) mj uB
    _ = (sA ≫ tA) ≫ (uA ≫ fj) :=
      congrArg (fun z => (sA ≫ tA) ≫ z) hi
    _ = ((sA ≫ tA) ≫ uA) ≫ fj :=
      (Category.assoc (sA ≫ tA) uA fj).symm

/-- The overlap comparison commutes with the target-chart leg. -/
@[reassoc]
theorem coverIsoOverlapMap_gluedCover_target
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    coverIsoOverlapMap e i j ≫
        overlapTarget 𝒱 (e.hom.s₀ i) (e.hom.s₀ j) =
      overlapTarget 𝒰 i j ≫
        e.hom.h₀ j := by
  simpa [overlapTarget, Scheme.Cover.gluedCover,
    Category.assoc] using coverIsoOverlapMap_overlapSnd e i j

/-- Reassociate the source chart pullback over a pair overlap. -/
noncomputable def coverIsoSourceOverlapIso
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover)
    (i j : 𝒰.I₀) :
    (pullback (overlapFst 𝒰 i j)).obj
        ((pullback (e.hom.h₀ i)).obj
          (A.chart (e.hom.s₀ i))) ≅
      (pullback (coverIsoOverlapMap e i j)).obj
        ((pullback
          (overlapFst 𝒱
            (e.hom.s₀ i) (e.hom.s₀ j))).obj
          (A.chart (e.hom.s₀ i))) :=
  pullbackSquareIso
    (overlapFst 𝒰 i j)
    (e.hom.h₀ i)
    (coverIsoOverlapMap e i j)
    (overlapFst 𝒱
      (e.hom.s₀ i) (e.hom.s₀ j))
    (coverIsoOverlapMap_overlapFst e i j).symm
    (A.chart (e.hom.s₀ i))

/-- Reassociate the target chart pullback over a pair overlap. -/
noncomputable def coverIsoTargetOverlapIso
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover)
    (i j : 𝒰.I₀) :
    (pullback (overlapTarget 𝒰 i j)).obj
        ((pullback (e.hom.h₀ j)).obj
          (A.chart (e.hom.s₀ j))) ≅
      (pullback (coverIsoOverlapMap e i j)).obj
        ((pullback
          (overlapTarget 𝒱
            (e.hom.s₀ i) (e.hom.s₀ j))).obj
          (A.chart (e.hom.s₀ j))) :=
  pullbackSquareIso
    (overlapTarget 𝒰 i j)
    (e.hom.h₀ j)
    (coverIsoOverlapMap e i j)
    (overlapTarget 𝒱
      (e.hom.s₀ i) (e.hom.s₀ j))
    (coverIsoOverlapMap_gluedCover_target e i j).symm
    (A.chart (e.hom.s₀ j))

/-- Pull a target-cover transition back to the corresponding source
overlap. -/
noncomputable def coverIsoPullbackTransition
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover) :
    CoverTransition 𝒰.gluedCover
      (fun i =>
        (pullback (e.hom.h₀ i)).obj
          (A.chart (e.hom.s₀ i))) :=
  fun i j =>
    coverIsoSourceOverlapIso e A i j ≪≫
      (pullback (coverIsoOverlapMap e i j)).mapIso
        (A.transition
          (e.hom.s₀ i) (e.hom.s₀ j)) ≪≫
      (coverIsoTargetOverlapIso e A i j).symm

/-- The pullback of the canonical target-cover transition, with all
open-cover chart types exposed. -/
noncomputable def coverIsoCanonicalPullbackIso
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    (pullback (overlapFst 𝒰 i j)).obj
        ((pullback (e.hom.h₀ i)).obj
          (openCoverRestriction 𝒱 W (e.hom.s₀ i))) ≅
      (pullback (overlapTarget 𝒰 i j)).obj
        ((pullback (e.hom.h₀ j)).obj
          (openCoverRestriction 𝒱 W (e.hom.s₀ j))) :=
  pullbackSquareIso
      (overlapFst 𝒰 i j)
      (e.hom.h₀ i)
      (coverIsoOverlapMap e i j)
      (overlapFst 𝒱 (e.hom.s₀ i) (e.hom.s₀ j))
      (coverIsoOverlapMap_overlapFst e i j).symm
      (openCoverRestriction 𝒱 W (e.hom.s₀ i)) ≪≫
    (pullback (coverIsoOverlapMap e i j)).mapIso
      (openCoverRestrictionTransition
        𝒱 W (e.hom.s₀ i) (e.hom.s₀ j)) ≪≫
    (pullbackSquareIso
      (overlapTarget 𝒰 i j)
      (e.hom.h₀ j)
      (coverIsoOverlapMap e i j)
      (overlapTarget 𝒱 (e.hom.s₀ i) (e.hom.s₀ j))
      (coverIsoOverlapMap_gluedCover_target e i j).symm
      (openCoverRestriction 𝒱 W (e.hom.s₀ j))).symm

/-- The general pullback-transition construction agrees definitionally
with its publicly typed open-cover form on canonical restrictions. -/
theorem coverIsoPullbackTransition_restriction_eq_typed
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    coverIsoPullbackTransition e
        ((restrictionFunctor (D := 𝒱.gluedCover)).obj W) i j =
      coverIsoCanonicalPullbackIso e W i j :=
  rfl

/-- The canonical chart comparison along a cover isomorphism, with the
open-cover chart schemes exposed. -/
noncomputable def coverIsoCanonicalChartIsoTyped
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i : 𝒰.I₀) :
    (pullback (gluedCoverChartMap 𝒰 i)).obj
        ((pullback (coverIsoGluedIso e).hom).obj W) ≅
      (pullback (e.hom.h₀ i)).obj
        (openCoverRestriction 𝒱 W (e.hom.s₀ i)) :=
  pullbackSquareIso
    (gluedCoverChartMap 𝒰 i)
    (coverIsoGluedIso e).hom
    (e.hom.h₀ i)
    (gluedCoverChartMap 𝒱 (e.hom.s₀ i))
    (gluedCover_ι_coverIsoGluedIso_hom e i)
    W

/-- The glue-data chart comparison and its publicly typed form agree. -/
theorem coverIsoCanonicalChartIso_eq_typed
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i : 𝒰.I₀) :
    coverIsoCanonicalChartIso e W i =
      coverIsoCanonicalChartIsoTyped e W i :=
  rfl

/-- The transported canonical transition, with open-cover chart types
exposed. -/
noncomputable def coverIsoCanonicalTransportIso
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    (pullback (overlapFst 𝒰 i j)).obj
        ((pullback (e.hom.h₀ i)).obj
          (openCoverRestriction 𝒱 W (e.hom.s₀ i))) ≅
      (pullback (overlapTarget 𝒰 i j)).obj
        ((pullback (e.hom.h₀ j)).obj
          (openCoverRestriction 𝒱 W (e.hom.s₀ j))) :=
  (pullback (overlapFst 𝒰 i j)).mapIso
      (coverIsoCanonicalChartIsoTyped e W i).symm ≪≫
    openCoverRestrictionTransition 𝒰
      ((pullback (coverIsoGluedIso e).hom).obj W) i j ≪≫
    (pullback (overlapTarget 𝒰 i j)).mapIso
      (coverIsoCanonicalChartIsoTyped e W j)

/-- The general chart-transport construction agrees with its publicly
typed form for the canonical cover-isomorphism comparison. -/
theorem coverIsoCanonicalTransport_eq_typed
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    transportTransition
        ((restrictionFunctor (D := 𝒰.gluedCover)).obj
          ((pullback (coverIsoGluedIso e).hom).obj W))
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (((restrictionFunctor
              (D := 𝒱.gluedCover)).obj W).chart
                (e.hom.s₀ i)))
        (coverIsoCanonicalChartIso e W) i j =
      coverIsoCanonicalTransportIso e W i j :=
  rfl

/-- Pulling chart morphisms along a cover isomorphism preserves
compatibility with the pulled transitions. -/
theorem coverIsoPullbackTransition_naturality
    (e : 𝒰 ≅ 𝒱)
    {A B : CoverDescentData 𝒱.gluedCover}
    (φ : A ⟶ B) (i j : 𝒰.I₀) :
    (pullback (overlapFst 𝒰 i j)).map
          ((pullback (e.hom.h₀ i)).map
            (φ.app (e.hom.s₀ i))) ≫
        (coverIsoPullbackTransition e B i j).hom =
      (coverIsoPullbackTransition e A i j).hom ≫
        (pullback (overlapTarget 𝒰 i j)).map
          ((pullback (e.hom.h₀ j)).map
            (φ.app (e.hom.s₀ j))) := by
    have hs :
        (pullback (overlapFst 𝒰 i j)).map
              ((pullback (e.hom.h₀ i)).map
                (φ.app (e.hom.s₀ i))) ≫
            (coverIsoSourceOverlapIso e B i j).hom =
          (coverIsoSourceOverlapIso e A i j).hom ≫
            (pullback (coverIsoOverlapMap e i j)).map
              ((pullback
                (overlapFst 𝒱
                  (e.hom.s₀ i) (e.hom.s₀ j))).map
                (φ.app (e.hom.s₀ i))) :=
      pullbackSquareIso_naturality
        (overlapFst 𝒰 i j)
        (e.hom.h₀ i)
        (coverIsoOverlapMap e i j)
        (overlapFst 𝒱 (e.hom.s₀ i) (e.hom.s₀ j))
        (coverIsoOverlapMap_overlapFst e i j).symm
        (φ.app (e.hom.s₀ i))
    have hc :
        (pullback (coverIsoOverlapMap e i j)).map
              ((pullback
                (overlapFst 𝒱
                  (e.hom.s₀ i) (e.hom.s₀ j))).map
                (φ.app (e.hom.s₀ i))) ≫
            (pullback (coverIsoOverlapMap e i j)).map
              (B.transition
                (e.hom.s₀ i) (e.hom.s₀ j)).hom =
          (pullback (coverIsoOverlapMap e i j)).map
                (A.transition
                  (e.hom.s₀ i) (e.hom.s₀ j)).hom ≫
            (pullback (coverIsoOverlapMap e i j)).map
              ((pullback
                (overlapTarget 𝒱
                  (e.hom.s₀ i) (e.hom.s₀ j))).map
                (φ.app (e.hom.s₀ j))) := by
      have hcompatible :
          ((pullback
              (overlapFst 𝒱
                (e.hom.s₀ i) (e.hom.s₀ j))).map
              (φ.app (e.hom.s₀ i))) ≫
              (B.transition
                (e.hom.s₀ i) (e.hom.s₀ j)).hom =
            (A.transition
                (e.hom.s₀ i) (e.hom.s₀ j)).hom ≫
              (pullback
                (overlapTarget 𝒱
                  (e.hom.s₀ i) (e.hom.s₀ j))).map
                (φ.app (e.hom.s₀ j)) :=
        φ.compatible (e.hom.s₀ i) (e.hom.s₀ j)
      let F := pullback (coverIsoOverlapMap e i j)
      have hmap :
          F.map (((pullback
              (overlapFst 𝒱
                (e.hom.s₀ i) (e.hom.s₀ j))).map
              (φ.app (e.hom.s₀ i))) ≫
            (B.transition
              (e.hom.s₀ i) (e.hom.s₀ j)).hom) =
            F.map ((A.transition
              (e.hom.s₀ i) (e.hom.s₀ j)).hom ≫
            (pullback
              (overlapTarget 𝒱
                (e.hom.s₀ i) (e.hom.s₀ j))).map
              (φ.app (e.hom.s₀ j))) := by
        exact congrArg (fun z => F.map z) hcompatible
      exact
        (F.map_comp
          ((pullback
            (overlapFst 𝒱
              (e.hom.s₀ i) (e.hom.s₀ j))).map
            (φ.app (e.hom.s₀ i)))
          (B.transition
            (e.hom.s₀ i) (e.hom.s₀ j)).hom).symm |>.trans <|
          hmap.trans <|
            F.map_comp
              (A.transition
                (e.hom.s₀ i) (e.hom.s₀ j)).hom
              ((pullback
                (overlapTarget 𝒱
                  (e.hom.s₀ i) (e.hom.s₀ j))).map
                (φ.app (e.hom.s₀ j)))
    have hi :
        (pullback (coverIsoOverlapMap e i j)).map
              ((pullback
                (overlapTarget 𝒱
                  (e.hom.s₀ i) (e.hom.s₀ j))).map
                (φ.app (e.hom.s₀ j))) ≫
            (coverIsoTargetOverlapIso e B i j).inv =
          (coverIsoTargetOverlapIso e A i j).inv ≫
            (pullback (overlapTarget 𝒰 i j)).map
              ((pullback (e.hom.h₀ j)).map
                (φ.app (e.hom.s₀ j))) :=
      pullbackSquareIso_inv_naturality
        (overlapTarget 𝒰 i j)
        (e.hom.h₀ j)
        (coverIsoOverlapMap e i j)
        (overlapTarget 𝒱
          (e.hom.s₀ i) (e.hom.s₀ j))
        (coverIsoOverlapMap_gluedCover_target
          e i j).symm
        (φ.app (e.hom.s₀ j))
    exact three_square_composite
      (f := (pullback (overlapFst 𝒰 i j)).map
        ((pullback (e.hom.h₀ i)).map (φ.app (e.hom.s₀ i))))
      (sB := (coverIsoSourceOverlapIso e B i j).hom)
      (sA := (coverIsoSourceOverlapIso e A i j).hom)
      (mi := (pullback (coverIsoOverlapMap e i j)).map
        ((pullback (overlapFst 𝒱
          (e.hom.s₀ i) (e.hom.s₀ j))).map
          (φ.app (e.hom.s₀ i))))
      (tB := (pullback (coverIsoOverlapMap e i j)).map
        (B.transition (e.hom.s₀ i) (e.hom.s₀ j)).hom)
      (tA := (pullback (coverIsoOverlapMap e i j)).map
        (A.transition (e.hom.s₀ i) (e.hom.s₀ j)).hom)
      (mj := (pullback (coverIsoOverlapMap e i j)).map
        ((pullback (overlapTarget 𝒱
          (e.hom.s₀ i) (e.hom.s₀ j))).map
          (φ.app (e.hom.s₀ j))))
      (uB := (coverIsoTargetOverlapIso e B i j).inv)
      (uA := (coverIsoTargetOverlapIso e A i j).inv)
      (fj := (pullback (overlapTarget 𝒰 i j)).map
        ((pullback (e.hom.h₀ j)).map (φ.app (e.hom.s₀ j))))
      hs hc hi

/-- The two threefold pullback routes across a source overlap agree. -/
theorem coverIsoCanonicalComposite_eq
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    ((overlapFst 𝒰 i j ≫
        e.hom.h₀ i) ≫
      gluedCoverChartMap 𝒱 (e.hom.s₀ i)) =
    ((overlapTarget 𝒰 i j ≫
        e.hom.h₀ j) ≫
      gluedCoverChartMap 𝒱 (e.hom.s₀ j)) := by
  let p := coverIsoOverlapMap e i j
  have hsource :
      𝒰.gluedCover.f i j ≫ e.hom.h₀ i =
        p ≫ 𝒱.gluedCover.f
          (e.hom.s₀ i) (e.hom.s₀ j) :=
    (coverIsoOverlapMap_fst e i j).symm
  have htarget :
      p ≫
          (𝒱.gluedCover.t
              (e.hom.s₀ i) (e.hom.s₀ j) ≫
            𝒱.gluedCover.f
              (e.hom.s₀ j) (e.hom.s₀ i)) =
        (𝒰.gluedCover.t i j ≫
            𝒰.gluedCover.f j i) ≫
          e.hom.h₀ j :=
    coverIsoOverlapMap_gluedCover_target e i j
  have hglue :
      𝒱.gluedCover.f
            (e.hom.s₀ i) (e.hom.s₀ j) ≫
          𝒱.gluedCover.ι (e.hom.s₀ i) =
        (𝒱.gluedCover.t
              (e.hom.s₀ i) (e.hom.s₀ j) ≫
            𝒱.gluedCover.f
              (e.hom.s₀ j) (e.hom.s₀ i)) ≫
          𝒱.gluedCover.ι (e.hom.s₀ j) := by
    rw [Category.assoc]
    exact
      (𝒱.gluedCover.glue_condition
        (e.hom.s₀ i) (e.hom.s₀ j)).symm
  calc
    ((𝒰.gluedCover.f i j ≫
          e.hom.h₀ i) ≫
        𝒱.gluedCover.ι (e.hom.s₀ i)) =
      (p ≫ 𝒱.gluedCover.f
          (e.hom.s₀ i) (e.hom.s₀ j)) ≫
        𝒱.gluedCover.ι (e.hom.s₀ i) :=
      congrArg
        (fun q =>
          q ≫ 𝒱.gluedCover.ι (e.hom.s₀ i))
        hsource
    _ = p ≫
        (𝒱.gluedCover.f
            (e.hom.s₀ i) (e.hom.s₀ j) ≫
          𝒱.gluedCover.ι (e.hom.s₀ i)) :=
      Category.assoc _ _ _
    _ = p ≫
        ((𝒱.gluedCover.t
              (e.hom.s₀ i) (e.hom.s₀ j) ≫
            𝒱.gluedCover.f
              (e.hom.s₀ j) (e.hom.s₀ i)) ≫
          𝒱.gluedCover.ι (e.hom.s₀ j)) :=
      congrArg (fun q => p ≫ q) hglue
    _ = (p ≫
          (𝒱.gluedCover.t
              (e.hom.s₀ i) (e.hom.s₀ j) ≫
            𝒱.gluedCover.f
              (e.hom.s₀ j) (e.hom.s₀ i))) ≫
        𝒱.gluedCover.ι (e.hom.s₀ j) :=
      (Category.assoc _ _ _).symm
    _ = (((𝒰.gluedCover.t i j ≫
            𝒰.gluedCover.f j i) ≫
          e.hom.h₀ j) ≫
        𝒱.gluedCover.ι (e.hom.s₀ j)) :=
      congrArg
        (fun q =>
          q ≫ 𝒱.gluedCover.ι (e.hom.s₀ j))
        htarget

/-- Common normal form for the canonical and explicit pulled
transitions. -/
noncomputable def coverIsoCanonicalNormalIso
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    (pullback (overlapFst 𝒰 i j)).obj
        ((pullback (e.hom.h₀ i)).obj
          ((pullback
            (gluedCoverChartMap 𝒱 (e.hom.s₀ i))).obj W)) ≅
      (pullback
        (overlapTarget 𝒰 i j)).obj
        ((pullback (e.hom.h₀ j)).obj
          ((pullback
            (gluedCoverChartMap 𝒱 (e.hom.s₀ j))).obj W)) :=
  (pullbackComp
      (overlapFst 𝒰 i j)
      (e.hom.h₀ i)).app
        ((pullback
          (gluedCoverChartMap 𝒱 (e.hom.s₀ i))).obj W) ≪≫
    (pullbackComp
      (overlapFst 𝒰 i j ≫ e.hom.h₀ i)
      (gluedCoverChartMap 𝒱 (e.hom.s₀ i))).app W ≪≫
    (pullbackCongr
      (coverIsoCanonicalComposite_eq e i j)).app W ≪≫
    (pullbackComp
      (overlapTarget 𝒰 i j ≫ e.hom.h₀ j)
      (gluedCoverChartMap 𝒱 (e.hom.s₀ j))).symm.app W ≪≫
    (pullbackComp
      (overlapTarget 𝒰 i j)
      (e.hom.h₀ j)).symm.app
        ((pullback
          (gluedCoverChartMap 𝒱 (e.hom.s₀ j))).obj W)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
