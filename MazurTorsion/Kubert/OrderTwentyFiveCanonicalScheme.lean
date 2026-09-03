/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalAffineOverlap
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The represented order-25 canonical curve

This file glues the two explicit affine complete-intersection charts along
the verified localization isomorphism. The result is an actual scheme with
a two-member open cover and a structural morphism to the coefficient ring.
Both chart maps are open immersions, their restrictions agree on the
transition, and the glued scheme is locally Noetherian whenever the base is.

Smoothness, integrality, and properness are deliberately separate geometric
obligations; no such property is built into the gluing definition.
-/

noncomputable section

open _root_.AlgebraicGeometry
open CategoryTheory

namespace MazurTorsion.Kubert.OrderTwentyFiveCanonicalScheme

universe u

open OrderTwentyFiveCanonicalAffineCharts

variable (K : Type u) [CommRing K]

inductive Chart : Type u
  | left
  | right
  deriving DecidableEq

noncomputable abbrev chartScheme : Chart → Scheme
  | .left => leftScheme K
  | .right => rightScheme K

noncomputable abbrev overlapScheme :
    ∀ i j : Chart, i ≠ j → Scheme
  | .left, .right, _ => Spec (.of (LeftOverlapRing K))
  | .right, .left, _ => Spec (.of (RightOverlapRing K))
  | .left, .left, h => (h rfl).elim
  | .right, .right, h => (h rfl).elim

noncomputable def overlapInclusion :
    ∀ i j : Chart, (h : i ≠ j) →
      overlapScheme K i j h ⟶ chartScheme K i
  | .left, .right, _ =>
      Spec.map (CommRingCat.ofHom
        (algebraMap (LeftRing K) (LeftOverlapRing K)))
  | .right, .left, _ =>
      Spec.map (CommRingCat.ofHom
        (algebraMap (RightRing K) (RightOverlapRing K)))
  | .left, .left, h => (h rfl).elim
  | .right, .right, h => (h rfl).elim

noncomputable def overlapTransition :
    ∀ i j : Chart, (h : i ≠ j) →
      overlapScheme K i j h ⟶ overlapScheme K j i h.symm
  | .left, .right, _ => (overlapSchemeIso K).hom
  | .right, .left, _ => (overlapSchemeIso K).inv
  | .left, .left, h => (h rfl).elim
  | .right, .right, h => (h rfl).elim

private theorem overlapInclusion_open (i j : Chart) (h : i ≠ j) :
    IsOpenImmersion (overlapInclusion K i j h) := by
  rcases i with (_ | _) <;> rcases j with (_ | _)
  · exact (h rfl).elim
  · exact IsOpenImmersion.of_isLocalization (leftOverlapElement K)
  · exact IsOpenImmersion.of_isLocalization (rightOverlapElement K)
  · exact (h rfl).elim

private theorem overlapInclusion_mono (i j : Chart) (h : i ≠ j) :
    CategoryTheory.Mono (overlapInclusion K i j h) := by
  haveI : IsOpenImmersion (overlapInclusion K i j h) :=
    overlapInclusion_open K i j h
  infer_instance

noncomputable abbrev categoricalGlueData :
    CategoryTheory.GlueData' Scheme.{u} where
  J := Chart
  U := chartScheme K
  V := overlapScheme K
  f := overlapInclusion K
  f_mono := overlapInclusion_mono K
  f_hasPullback := by
    intro i j k hij hik
    infer_instance
  t := overlapTransition K
  t' := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction
  t_fac := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction
  t_inv := by
    intro i j hij
    rcases i with (_ | _) <;> rcases j with (_ | _)
    · exact (hij rfl).elim
    · exact (overlapSchemeIso K).hom_inv_id
    · exact (overlapSchemeIso K).inv_hom_id
    · exact (hij rfl).elim
  cocycle := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction

private theorem categoricalGlueData_f'_open (i j : Chart) :
    IsOpenImmersion ((categoricalGlueData K).f' i j) := by
  classical
  delta CategoryTheory.GlueData'.f'
  by_cases h : i = j
  · simp only [dif_pos h]
    exact IsOpenImmersion.of_isIso _
  · simp only [dif_neg h]
    haveI : IsOpenImmersion (overlapInclusion K i j h) :=
      overlapInclusion_open K i j h
    exact IsOpenImmersion.comp _ _

noncomputable abbrev glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (categoricalGlueData K)
  f_open := categoricalGlueData_f'_open K

noncomputable def curve : Scheme := (glueData K).glued

noncomputable def leftChartMap : leftScheme K ⟶ curve K :=
  (glueData K).ι Chart.left

noncomputable def rightChartMap : rightScheme K ⟶ curve K :=
  (glueData K).ι Chart.right

instance leftChartMap_isOpenImmersion : IsOpenImmersion (leftChartMap K) := by
  dsimp [leftChartMap]
  exact Scheme.GlueData.ι_isOpenImmersion (glueData K) Chart.left

instance rightChartMap_isOpenImmersion : IsOpenImmersion (rightChartMap K) := by
  dsimp [rightChartMap]
  exact Scheme.GlueData.ι_isOpenImmersion (glueData K) Chart.right

noncomputable def openCover : (curve K).OpenCover := (glueData K).openCover

noncomputable def leftChartToBase :
    leftScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (LeftRing K)))

noncomputable def rightChartToBase :
    rightScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (RightRing K)))

noncomputable def chartToBase :
    ∀ i : Chart, chartScheme K i ⟶ Spec (.of K)
  | .left => leftChartToBase K
  | .right => rightChartToBase K

private theorem left_ne_right : (Chart.left : Chart.{u}) ≠ Chart.right := by
  intro h
  cases h

private theorem right_ne_left : (Chart.right : Chart.{u}) ≠ Chart.left := by
  intro h
  cases h

private theorem left_right_base_compatible :
    Spec.map (CommRingCat.ofHom
        (algebraMap (LeftRing K) (LeftOverlapRing K))) ≫
        leftChartToBase K =
      Spec.map (CommRingCat.ofHom (rightToLeft K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (RightRing K) (RightOverlapRing K))) ≫
        rightChartToBase K := by
  simp only [leftChartToBase, rightChartToBase]
  rw [← Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply K (LeftRing K) (LeftOverlapRing K)]
  simp

private theorem right_left_base_compatible :
    Spec.map (CommRingCat.ofHom
        (algebraMap (RightRing K) (RightOverlapRing K))) ≫
        rightChartToBase K =
      Spec.map (CommRingCat.ofHom (leftToRight K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (LeftRing K) (LeftOverlapRing K))) ≫
        leftChartToBase K := by
  simp only [leftChartToBase, rightChartToBase]
  rw [← Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply K (RightRing K) (RightOverlapRing K)]
  simp

private theorem chartToBase_transition_compatible
    (i j : Chart) (h : i ≠ j) :
    overlapInclusion K i j h ≫ chartToBase K i =
      overlapTransition K i j h ≫
        overlapInclusion K j i h.symm ≫ chartToBase K j := by
  rcases i with (_ | _) <;> rcases j with (_ | _)
  · exact (h rfl).elim
  · exact left_right_base_compatible K
  · exact right_left_base_compatible K
  · exact (h rfl).elim

noncomputable def curveToBase : curve K ⟶ Spec (.of K) := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  exact Limits.Multicoequalizer.desc (glueData K).toGlueData.diagram
    (Spec (.of K)) (chartToBase K) (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          Limits.MultispanShape.prod]
        simp
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          left_ne_right, right_ne_left,
          Limits.MultispanShape.prod]
        simp only [dif_neg left_ne_right,
          dif_neg right_ne_left, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact chartToBase_transition_compatible K _ _ left_ne_right
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          left_ne_right, right_ne_left,
          Limits.MultispanShape.prod]
        simp only [dif_neg left_ne_right,
          dif_neg right_ne_left, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact chartToBase_transition_compatible K _ _ right_ne_left
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          Limits.MultispanShape.prod]
        simp)

@[simp, reassoc]
theorem leftChartMap_curveToBase :
    leftChartMap K ≫ curveToBase K = leftChartToBase K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  unfold leftChartMap curveToBase
  apply Limits.Multicoequalizer.π_desc

@[simp, reassoc]
theorem rightChartMap_curveToBase :
    rightChartMap K ≫ curveToBase K = rightChartToBase K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  unfold rightChartMap curveToBase
  apply Limits.Multicoequalizer.π_desc

instance curve_isLocallyNoetherian [IsNoetherianRing K] :
    IsLocallyNoetherian (curve K) := by
  rw [isLocallyNoetherian_iff_openCover (openCover K)]
  intro i
  rcases i with (_ | _)
  · change IsLocallyNoetherian (leftScheme K)
    infer_instance
  · change IsLocallyNoetherian (rightScheme K)
    infer_instance

end MazurTorsion.Kubert.OrderTwentyFiveCanonicalScheme

