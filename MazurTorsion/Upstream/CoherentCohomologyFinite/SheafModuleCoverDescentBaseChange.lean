/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeOverlap
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCategory

/-!
# Module descent data under base change of an open cover

This file gives the pair-overlap part of pullback for module descent
data.  The comparison is written only in terms of the canonical maps on
charts and overlaps, so it can later be used independently of the
effective gluing construction.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback around a commutative square, with the two iterated
pullbacks reassociated on both sides. -/
noncomputable def pullbackSquareIso
    {X' X Y' Y : Scheme.{0}}
    (q : X' ⟶ X) (a : X ⟶ Y)
    (p : X' ⟶ Y') (r : Y' ⟶ Y)
    (h : q ≫ a = p ≫ r) (M : Y.Modules) :
    (pullback q).obj ((pullback a).obj M) ≅
      (pullback p).obj ((pullback r).obj M) :=
  (pullbackComp q a).app M ≪≫
    (pullbackCongr h).app M ≪≫
    (pullbackComp p r).symm.app M

/-- The square comparison is natural in the pulled-back module. -/
@[reassoc]
theorem pullbackSquareIso_naturality
    {X' X Y' Y : Scheme.{0}}
    (q : X' ⟶ X) (a : X ⟶ Y)
    (p : X' ⟶ Y') (r : Y' ⟶ Y)
    (h : q ≫ a = p ≫ r)
    {M N : Y.Modules} (φ : M ⟶ N) :
    (pullback q).map ((pullback a).map φ) ≫
        (pullbackSquareIso q a p r h N).hom =
      (pullbackSquareIso q a p r h M).hom ≫
        (pullback p).map ((pullback r).map φ) := by
    simp only [pullbackSquareIso, Iso.trans_hom]
    change
      (pullback q).map ((pullback a).map φ) ≫
            (pullbackComp q a).hom.app N ≫
              (pullbackCongr h).hom.app N ≫
                (pullbackComp p r).inv.app N =
        (pullbackComp q a).hom.app M ≫
            (pullbackCongr h).hom.app M ≫
              (pullbackComp p r).inv.app M ≫
                (pullback p).map ((pullback r).map φ)
    have h₁ :
        (pullback q).map ((pullback a).map φ) ≫
            (pullbackComp q a).hom.app N =
          (pullbackComp q a).hom.app M ≫
            (pullback (q ≫ a)).map φ := by
      simpa only [Functor.comp_map] using
        (pullbackComp q a).hom.naturality φ
    have h₂ :
        (pullback (q ≫ a)).map φ ≫
            (pullbackCongr h).hom.app N =
          (pullbackCongr h).hom.app M ≫
            (pullback (p ≫ r)).map φ :=
      (pullbackCongr h).hom.naturality φ
    have h₃ :
        (pullback (p ≫ r)).map φ ≫
            (pullbackComp p r).inv.app N =
          (pullbackComp p r).inv.app M ≫
            (pullback p).map ((pullback r).map φ) := by
      simpa only [Functor.comp_map] using
        (pullbackComp p r).inv.naturality φ
    rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- Naturality of the inverse square comparison. -/
@[reassoc]
theorem pullbackSquareIso_inv_naturality
    {X' X Y' Y : Scheme.{0}}
    (q : X' ⟶ X) (a : X ⟶ Y)
    (p : X' ⟶ Y') (r : Y' ⟶ Y)
    (h : q ≫ a = p ≫ r)
    {M N : Y.Modules} (φ : M ⟶ N) :
    (pullback p).map ((pullback r).map φ) ≫
        (pullbackSquareIso q a p r h N).inv =
      (pullbackSquareIso q a p r h M).inv ≫
        (pullback q).map ((pullback a).map φ) := by
  apply (cancel_mono
    (pullbackSquareIso q a p r h N).hom).1
  simp only [Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  have hn :=
    pullbackSquareIso_naturality q a p r h φ
  symm
  calc
    (pullbackSquareIso q a p r h M).inv ≫
          (pullback q).map ((pullback a).map φ) ≫
            (pullbackSquareIso q a p r h N).hom =
        (pullbackSquareIso q a p r h M).inv ≫
          ((pullback q).map ((pullback a).map φ) ≫
            (pullbackSquareIso q a p r h N).hom) :=
      Category.assoc _ _ _
    _ =
        (pullbackSquareIso q a p r h M).inv ≫
          ((pullbackSquareIso q a p r h M).hom ≫
            (pullback p).map ((pullback r).map φ)) :=
      congrArg
        (fun z =>
          (pullbackSquareIso q a p r h M).inv ≫ z) hn
    _ = (pullback p).map ((pullback r).map φ) := by
      simp

/-- A square comparison conjugates an equality transition to the
corresponding equality transition on its source. -/
theorem pullbackSquareIso_eqToIso
    {X' X Y' Y : Scheme.{0}}
    {q q' : X' ⟶ X} (c : X ⟶ Y)
    (p : X' ⟶ Y') {a a' : Y' ⟶ Y}
    (hq : q = q') (ha : a = a')
    (h : q ≫ c = p ≫ a)
    (h' : q' ≫ c = p ≫ a')
    (M : Y.Modules) :
    pullbackSquareIso q c p a h M ≪≫
        (pullback p).mapIso
          (eqToIso (congrArg
            (fun z => (pullback z).obj M) ha)) ≪≫
        (pullbackSquareIso q' c p a' h' M).symm =
      eqToIso (congrArg
        (fun z =>
          (pullback z).obj ((pullback c).obj M)) hq) := by
  subst q'
  subst a'
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  simp [pullbackSquareIso, pullbackCongr]

namespace CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- The overlap map of a pulled-back cover also commutes with the
second (target-chart) leg. -/
@[reassoc]
theorem baseChangeOverlapMap_gluedCover_target (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫
        (𝒰.gluedCover.t i j ≫ 𝒰.gluedCover.f j i) =
      ((gluedCover (𝒰.pullback₁ f)).t i j ≫
          (gluedCover (𝒰.pullback₁ f)).f j i) ≫
        𝒰.pullbackHom f j := by
  simpa [Scheme.Cover.gluedCover, Category.assoc] using
    (baseChangeOverlapMap_snd 𝒰 f i j)

/-- Reassociate the first chart restriction over an overlap of the
pulled-back cover. -/
noncomputable def baseChangeSourceOverlapIso
    (A : CoverDescentData 𝒰.gluedCover) (i j : 𝒰.I₀) :
    (pullback ((gluedCover (𝒰.pullback₁ f)).f i j)).obj
        ((pullback (𝒰.pullbackHom f i)).obj (A.chart i)) ≅
      (pullback (baseChangeOverlapMap 𝒰 f i j)).obj
        ((pullback (𝒰.gluedCover.f i j)).obj (A.chart i)) :=
  pullbackSquareIso
    ((gluedCover (𝒰.pullback₁ f)).f i j)
    (𝒰.pullbackHom f i)
    (baseChangeOverlapMap 𝒰 f i j) (𝒰.gluedCover.f i j)
    (baseChangeOverlapMap_gluedCover_f 𝒰 f i j).symm
    (A.chart i)

/-- Naturality of the source-side overlap reassociation. -/
@[reassoc]
theorem baseChangeSourceOverlapIso_naturality
    {A B : CoverDescentData 𝒰.gluedCover}
    (φ : A ⟶ B) (i j : 𝒰.I₀) :
    (pullback ((gluedCover (𝒰.pullback₁ f)).f i j)).map
          ((pullback (𝒰.pullbackHom f i)).map (φ.app i)) ≫
        (baseChangeSourceOverlapIso 𝒰 f B i j).hom =
      (baseChangeSourceOverlapIso 𝒰 f A i j).hom ≫
        (pullback (baseChangeOverlapMap 𝒰 f i j)).map
          ((pullback (𝒰.gluedCover.f i j)).map (φ.app i)) := by
  exact pullbackSquareIso_naturality
    ((gluedCover (𝒰.pullback₁ f)).f i j)
    (𝒰.pullbackHom f i)
    (baseChangeOverlapMap 𝒰 f i j)
    (𝒰.gluedCover.f i j)
    (baseChangeOverlapMap_gluedCover_f 𝒰 f i j).symm
    (φ.app i)

/-- Reassociate the second chart restriction over an overlap of the
pulled-back cover. -/
noncomputable def baseChangeTargetOverlapIso
    (A : CoverDescentData 𝒰.gluedCover) (i j : 𝒰.I₀) :
    (pullback ((gluedCover (𝒰.pullback₁ f)).t i j ≫
        (gluedCover (𝒰.pullback₁ f)).f j i)).obj
        ((pullback (𝒰.pullbackHom f j)).obj (A.chart j)) ≅
      (pullback (baseChangeOverlapMap 𝒰 f i j)).obj
        ((pullback (𝒰.gluedCover.t i j ≫
            𝒰.gluedCover.f j i)).obj
          (A.chart j)) :=
  pullbackSquareIso
    ((gluedCover (𝒰.pullback₁ f)).t i j ≫
      (gluedCover (𝒰.pullback₁ f)).f j i)
    (𝒰.pullbackHom f j)
    (baseChangeOverlapMap 𝒰 f i j)
    (𝒰.gluedCover.t i j ≫ 𝒰.gluedCover.f j i)
    (baseChangeOverlapMap_gluedCover_target 𝒰 f i j).symm
    (A.chart j)

/-- Naturality of the inverse target-side overlap reassociation. -/
@[reassoc]
theorem baseChangeTargetOverlapIso_inv_naturality
    {A B : CoverDescentData 𝒰.gluedCover}
    (φ : A ⟶ B) (i j : 𝒰.I₀) :
    (pullback (baseChangeOverlapMap 𝒰 f i j)).map
          ((pullback (𝒰.gluedCover.t i j ≫
            𝒰.gluedCover.f j i)).map (φ.app j)) ≫
        (baseChangeTargetOverlapIso 𝒰 f B i j).inv =
      (baseChangeTargetOverlapIso 𝒰 f A i j).inv ≫
        (pullback
          ((gluedCover (𝒰.pullback₁ f)).t i j ≫
            (gluedCover (𝒰.pullback₁ f)).f j i)).map
          ((pullback (𝒰.pullbackHom f j)).map (φ.app j)) := by
  exact pullbackSquareIso_inv_naturality
    ((gluedCover (𝒰.pullback₁ f)).t i j ≫
      (gluedCover (𝒰.pullback₁ f)).f j i)
    (𝒰.pullbackHom f j)
    (baseChangeOverlapMap 𝒰 f i j)
    (𝒰.gluedCover.t i j ≫ 𝒰.gluedCover.f j i)
    (baseChangeOverlapMap_gluedCover_target 𝒰 f i j).symm
    (φ.app j)

/-- Pull an overlap transition to the corresponding overlap of a
base-changed cover. -/
noncomputable def baseChangeTransition
    (A : CoverDescentData 𝒰.gluedCover) :
    CoverTransition (gluedCover (𝒰.pullback₁ f))
      (fun i =>
        (pullback (𝒰.pullbackHom f i)).obj (A.chart i)) :=
  fun (i j : 𝒰.I₀) =>
    baseChangeSourceOverlapIso 𝒰 f A i j ≪≫
      (pullback (baseChangeOverlapMap 𝒰 f i j)).mapIso
        (A.transition i j) ≪≫
      (baseChangeTargetOverlapIso 𝒰 f A i j).symm

/-- A morphism of descent data remains compatible after pulling all
chart objects and transitions to a base-changed cover. -/
theorem baseChangeTransition_naturality
    {A B : CoverDescentData 𝒰.gluedCover}
    (φ : A ⟶ B) (i j : 𝒰.I₀) :
    (pullback ((gluedCover (𝒰.pullback₁ f)).f i j)).map
          ((pullback (𝒰.pullbackHom f i)).map (φ.app i)) ≫
        (baseChangeTransition 𝒰 f B i j).hom =
      (baseChangeTransition 𝒰 f A i j).hom ≫
        (pullback
          ((gluedCover (𝒰.pullback₁ f)).t i j ≫
            (gluedCover (𝒰.pullback₁ f)).f j i)).map
          ((pullback (𝒰.pullbackHom f j)).map (φ.app j)) := by
    simp only [baseChangeTransition, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom]
    rw [baseChangeSourceOverlapIso_naturality_assoc]
    simp only [Category.assoc]
    have hc :
        (pullback (baseChangeOverlapMap 𝒰 f i j)).map
              ((pullback (𝒰.gluedCover.f i j)).map
                (φ.app i)) ≫
            (pullback (baseChangeOverlapMap 𝒰 f i j)).map
              (B.transition i j).hom =
          (pullback (baseChangeOverlapMap 𝒰 f i j)).map
              (A.transition i j).hom ≫
            (pullback (baseChangeOverlapMap 𝒰 f i j)).map
              ((pullback
                (𝒰.gluedCover.t i j ≫
                  𝒰.gluedCover.f j i)).map (φ.app j)) := by
      rw [← (pullback
          (baseChangeOverlapMap 𝒰 f i j)).map_comp,
        φ.compatible i j,
        (pullback
          (baseChangeOverlapMap 𝒰 f i j)).map_comp]
    have hi :=
      baseChangeTargetOverlapIso_inv_naturality
        𝒰 f φ i j
    have htail :
        (pullback (baseChangeOverlapMap 𝒰 f i j)).map
              ((pullback (𝒰.gluedCover.f i j)).map
                (φ.app i)) ≫
            (pullback (baseChangeOverlapMap 𝒰 f i j)).map
                (B.transition i j).hom ≫
              (baseChangeTargetOverlapIso
                𝒰 f B i j).inv =
          (pullback (baseChangeOverlapMap 𝒰 f i j)).map
                (A.transition i j).hom ≫
              (baseChangeTargetOverlapIso
                  𝒰 f A i j).inv ≫
                (pullback
                  ((gluedCover (𝒰.pullback₁ f)).t i j ≫
                    (gluedCover (𝒰.pullback₁ f)).f j i)).map
                  ((pullback (𝒰.pullbackHom f j)).map
                    (φ.app j)) := by
      rw [reassoc_of% hc]
      exact congrArg
        (fun z =>
          (pullback (baseChangeOverlapMap 𝒰 f i j)).map
              (A.transition i j).hom ≫ z) hi
    simpa only [Category.assoc] using
      congrArg
        (fun z =>
          (baseChangeSourceOverlapIso 𝒰 f A i j).hom ≫ z)
        htail

/-- Base change preserves the diagonal identity law for descent
transitions. -/
theorem baseChangeTransition_self
    (A : CoverDescentData 𝒰.gluedCover) (i : 𝒰.I₀) :
    baseChangeTransition 𝒰 f A i i =
      eqToIso (congrArg
        (fun φ =>
          (pullback φ).obj
            ((pullback (𝒰.pullbackHom f i)).obj
              (A.chart i)))
        (show
          (gluedCover (𝒰.pullback₁ f)).f i i =
            (gluedCover (𝒰.pullback₁ f)).t i i ≫
              (gluedCover (𝒰.pullback₁ f)).f i i by
          rw [(gluedCover (𝒰.pullback₁ f)).t_id i,
            Category.id_comp])) := by
  rw [baseChangeTransition, A.identity i]
  exact pullbackSquareIso_eqToIso
    (𝒰.pullbackHom f i)
    (baseChangeOverlapMap 𝒰 f i i)
    (show
      (gluedCover (𝒰.pullback₁ f)).f i i =
        (gluedCover (𝒰.pullback₁ f)).t i i ≫
          (gluedCover (𝒰.pullback₁ f)).f i i by
      rw [(gluedCover (𝒰.pullback₁ f)).t_id i,
        Category.id_comp])
    (show
      𝒰.gluedCover.f i i =
        𝒰.gluedCover.t i i ≫ 𝒰.gluedCover.f i i by
      rw [𝒰.gluedCover.t_id i, Category.id_comp])
    (baseChangeOverlapMap_gluedCover_f 𝒰 f i i).symm
    (baseChangeOverlapMap_gluedCover_target 𝒰 f i i).symm
    (A.chart i)

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
