/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescent

/-!
# Coherence of the canonical cover descent datum

The canonical transition maps obtained by restricting one module sheaf to the
charts of a scheme glue datum satisfy the identity and cocycle axioms.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{u})

private lemma cancel_factored_isos {C : Type*} [Category C]
    {x₀ x₁ x₂ x₃ : C} {a : x₀ ⟶ x₁} {b : x₀ ⟶ x₂}
    (c : x₂ ≅ x₃) (d : x₃ ≅ x₁) (ha : a = b ≫ c.hom ≫ d.hom) :
    a ≫ d.inv ≫ c.inv = b := by
  rw [ha]
  simp

private lemma pullbackCongr_inv_app_eq_hom_symm {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (W : Y.Modules) :
    (pullbackCongr h).inv.app W = (pullbackCongr h.symm).hom.app W := by
  rw [pullbackCongr_inv_app_eqToHom, pullbackCongr_hom_app_eqToHom]

private def pullbackComparison {P A B X : Scheme.{u}}
    (a : P ⟶ A) (ι : A ⟶ X) (b : P ⟶ B) (κ : B ⟶ X)
    (h : a ≫ ι = b ≫ κ) (W : X.Modules) :
    (pullback a).obj ((pullback ι).obj W) ≅
      (pullback b).obj ((pullback κ).obj W) :=
  (pullbackComp a ι).app W ≪≫
    (pullbackCongr h).app W ≪≫
    (pullbackComp b κ).symm.app W

private theorem pullbackComparison_transport_bridge
    {Q P A B C X : Scheme.{u}}
    (u : Q ⟶ P) (a : P ⟶ A) (ι : A ⟶ X)
    (t : P ⟶ B) (κ : B ⟶ X) (τ : Q ⟶ C) (b : C ⟶ B)
    (hpair : t ≫ κ = a ≫ ι) (hmid : u ≫ t = τ ≫ b)
    (htriple : τ ≫ (b ≫ κ) = (u ≫ a) ≫ ι) (W : X.Modules) :
    pullbackBaseChangeTransport u a t
        (pullbackComparison a ι t κ hpair.symm W) ≪≫
      (pullbackCongr hmid).app ((pullback κ).obj W) ≪≫
      (pullbackComp τ b).symm.app ((pullback κ).obj W)
    =
      (pullbackComp (u ≫ a) ι).app W ≪≫
        (pullbackCongr htriple.symm).app W ≪≫
        (pullbackComp τ (b ≫ κ)).symm.app W ≪≫
        (pullback τ).mapIso ((pullbackComp b κ).symm.app W) := by
  apply Iso.ext
  have hcast :=
    pullback_cast_compat u a ι t κ τ b hpair hmid htriple W
  rw [pullbackCongr_inv_app_eq_hom_symm] at hcast
  simp only [pullbackBaseChangeTransport, pullbackComparison,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  erw [← hcast]
  rfl

private theorem coverRestrictionTransition_eq_pullbackComparison
    (W : D.glued.Modules) (i j : D.J)
    (hpair : (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i) :
    coverRestrictionTransition D W i j =
      pullbackComparison (D.f i j) (D.ι i)
        (D.t i j ≫ D.f j i) (D.ι j) hpair.symm W := by
  rfl

private theorem pullbackComparison_transport
    {Q P A B C X : Scheme.{u}}
    (u : Q ⟶ P) (a : P ⟶ A) (ι : A ⟶ X)
    (t : P ⟶ B) (κ : B ⟶ X) (τ : Q ⟶ C) (b : C ⟶ B)
    (hpair : t ≫ κ = a ≫ ι) (hmid : u ≫ t = τ ≫ b)
    (htriple : τ ≫ (b ≫ κ) = (u ≫ a) ≫ ι) (W : X.Modules) :
    pullbackBaseChangeTransport u a t
        (pullbackComparison a ι t κ hpair.symm W) ≪≫
      (pullbackCongr hmid).app ((pullback κ).obj W)
    =
      ((pullbackComp (u ≫ a) ι).app W ≪≫
          (pullbackCongr htriple.symm).app W ≪≫
          (pullbackComp τ (b ≫ κ)).symm.app W ≪≫
          (pullback τ).mapIso ((pullbackComp b κ).symm.app W)) ≪≫
        (pullbackComp τ b).app ((pullback κ).obj W) := by
  let e := (pullbackComp τ b).symm.app ((pullback κ).obj W)
  have h := pullbackComparison_transport_bridge u a ι t κ τ b
    hpair hmid htriple W
  calc
    pullbackBaseChangeTransport u a t
          (pullbackComparison a ι t κ hpair.symm W) ≪≫
        (pullbackCongr hmid).app ((pullback κ).obj W)
      = (pullbackBaseChangeTransport u a t
            (pullbackComparison a ι t κ hpair.symm W) ≪≫
          (pullbackCongr hmid).app ((pullback κ).obj W) ≪≫ e) ≪≫ e.symm := by
            simp
    _ = ((pullbackComp (u ≫ a) ι).app W ≪≫
          (pullbackCongr htriple.symm).app W ≪≫
          (pullbackComp τ (b ≫ κ)).symm.app W ≪≫
          (pullback τ).mapIso ((pullbackComp b κ).symm.app W)) ≪≫ e.symm :=
      congrArg (fun z => z ≪≫ e.symm) h
    _ = ((pullbackComp (u ≫ a) ι).app W ≪≫
          (pullbackCongr htriple.symm).app W ≪≫
          (pullbackComp τ (b ≫ κ)).symm.app W ≪≫
          (pullback τ).mapIso ((pullbackComp b κ).symm.app W)) ≪≫
        (pullbackComp τ b).app ((pullback κ).obj W) := by rfl

private theorem pullbackBaseChangeTransport_pullbackComparison
    {Q P A B X : Scheme.{u}}
    (u : Q ⟶ P) (a : P ⟶ A) (ι : A ⟶ X)
    (b : P ⟶ B) (κ : B ⟶ X)
    (h : a ≫ ι = b ≫ κ) (W : X.Modules) :
    pullbackBaseChangeTransport u a b
      (pullbackComparison a ι b κ h W) =
        (pullbackComp u a).symm.app ((pullback ι).obj W) ≪≫
          (((pullback u).mapIso ((pullbackComp a ι).app W) ≪≫
              (pullback u).mapIso ((pullbackCongr h).app W) ≪≫
              (pullback u).mapIso ((pullbackComp b κ).symm.app W)) ≪≫
            (pullbackComp u b).app ((pullback κ).obj W)) := by
  unfold pullbackBaseChangeTransport pullbackComparison
  rw [Functor.mapIso_trans, Functor.mapIso_trans]

private lemma iso_cancel_two_comparisons_grouped {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    (p : X₀ ≅ X₁) (c : X₂ ≅ X₁) (e : X₂ ≅ X₃)
    (q : X₁ ≅ X₄) (r : X₄ ≅ X₅) (g : X₅ ≅ X₆)
    (s : X₆ ≅ X₇) :
    ((p ≪≫ c.symm) ≪≫ e) ≪≫
        ((e.symm ≪≫ ((c ≪≫ q ≪≫ r) ≪≫ g)) ≪≫ s) =
      (p ≪≫ q ≪≫ r ≪≫ g) ≪≫ s := by
  simp [Iso.trans_assoc]

private theorem pullbackComp_symm_trans_map_pullbackCongr
    {Q P X : Scheme.{u}} (u : Q ⟶ P) {a b : P ⟶ X}
    (h : a = b) (W : X.Modules) :
    (pullbackComp u a).symm.app W ≪≫
        (pullback u).mapIso ((pullbackCongr h).app W)
      =
        (pullbackCongr (show u ≫ a = u ≫ b by rw [h])).app W ≪≫
          (pullbackComp u b).symm.app W := by
  subst b
  apply Iso.ext
  simp [pullbackCongr]

private theorem pullbackCongr_trans_pullbackComp
    {Q P X : Scheme.{u}} {u v : Q ⟶ P} (h : u = v)
    (κ : P ⟶ X) (W : X.Modules) :
    (pullbackCongr h).app ((pullback κ).obj W) ≪≫
        (pullbackComp v κ).app W
      =
        (pullbackComp u κ).app W ≪≫
          (pullbackCongr (show u ≫ κ = v ≫ κ by rw [h])).app W := by
  subst v
  apply Iso.ext
  simp [pullbackCongr]

private theorem pullbackCongr_pair_eq_pair
    {Q X : Scheme.{u}} {a b c b' : Q ⟶ X}
    (h₁ : a = b) (h₂ : b = c) (h₁' : a = b') (h₂' : b' = c)
    (W : X.Modules) :
    (pullbackCongr h₁).app W ≪≫ (pullbackCongr h₂).app W =
      (pullbackCongr h₁').app W ≪≫ (pullbackCongr h₂').app W := by
  subst b
  subst b'
  subst c
  simp [pullbackCongr]

private lemma iso_cancel_tail_grouped {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ : C} (s : X₀ ≅ X₁) (t : X₁ ≅ X₂)
    (e : X₃ ≅ X₂) :
    (s ≪≫ t ≪≫ e.symm) ≪≫ e = s ≪≫ t := by
  simp [Iso.trans_assoc]

private lemma iso_cast_pipeline_grouped {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₃ ≅ X₄) (r : X₄ ≅ X₅) (g : X₅ ≅ X₆)
    (s : X₀ ≅ X₇) (h : X₇ ≅ X₈) (i : X₈ ≅ X₉)
    (e : X₂ ≅ X₉) (f : X₉ ≅ X₄) (j : X₁ ≅ X₈)
    (hcd : c ≪≫ d = e ≪≫ f)
    (hsh : s ≪≫ h = a ≪≫ j)
    (hbe : b ≪≫ e = j ≪≫ i) :
    (a ≪≫ b ≪≫ c) ≪≫ d ≪≫ r ≪≫ g =
      s ≪≫ ((h ≪≫ i ≪≫ f ≪≫ r) ≪≫ g) := by
  have hcdh := congrArg Iso.hom hcd
  have hshh := congrArg Iso.hom hsh
  have hbeh := congrArg Iso.hom hbe
  simp only [Iso.trans_hom] at hcdh hshh hbeh
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% hcdh, reassoc_of% hbeh, ← reassoc_of% hshh]

/-- The canonical cover transition on a diagonal overlap is the identity cast. -/
theorem coverRestrictionTransition_self (W : D.glued.Modules) (i : D.J) :
    coverRestrictionTransition D W i i =
      eqToIso (congrArg
        (fun φ => (pullback φ).obj (coverRestriction D W i))
        (show D.f i i = D.t i i ≫ D.f i i by
          rw [D.t_id i, Category.id_comp])) := by
  apply Iso.ext
  have h : D.f i i = D.t i i ≫ D.f i i := by
    rw [D.t_id i, Category.id_comp]
  have q : D.f i i ≫ D.ι i =
      (D.t i i ≫ D.f i i) ≫ D.ι i := by
    rw [Category.assoc]
    exact (D.glue_condition i i).symm
  have hfactor := pullbackComp_hom_app_congr_fst h (D.ι i) W
  have hcongr :
      (pullbackCongr q.symm).inv.app W =
        (pullbackCongr q).hom.app W := by
    rw [pullbackCongr_inv_app_eqToHom, pullbackCongr_hom_app_eqToHom]
  have hcongrApp :
      ((pullbackCongr q.symm).app W).inv =
        ((pullbackCongr q).app W).hom := hcongr
  have core := cancel_factored_isos
    (C := (D.V (i, i)).Modules)
    (a := (pullbackComp (D.f i i) (D.ι i)).hom.app W)
    (b := (pullbackCongr h).hom.app ((pullback (D.ι i)).obj W))
    ((pullbackComp (D.t i i ≫ D.f i i) (D.ι i)).app W)
    ((pullbackCongr q.symm).app W) hfactor
  rw [hcongrApp] at core
  simp only [coverRestrictionTransition, Iso.trans_hom]
  exact core.trans
    (pullbackCongr_hom_app_eqToHom h ((pullback (D.ι i)).obj W))

private theorem coverPairSquare (D : Scheme.GlueData.{u}) (i j : D.J) :
    (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i := by
  rw [Category.assoc]
  exact D.glue_condition i j

private theorem coverTripleLeftSquare (D : Scheme.GlueData.{u}) (i j k : D.J) :
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫
        (D.f j k ≫ D.ι j) =
      (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j) ≫ D.ι i := by
  rw [← Category.assoc, ← glueData_bridge_mid D i j k]
  simp only [Category.assoc]
  rw [D.glue_condition i j]

private theorem coverTripleRightSquare (D : Scheme.GlueData.{u}) (i j k : D.J) :
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫
        ((D.t j k ≫ D.f k j) ≫ D.ι k) =
      (pullback.snd (D.f i j) (D.f i k) ≫ D.f i k) ≫ D.ι i := by
  rw [← Category.assoc, glueData_bridge_tgt D i j k]
  simp only [Category.assoc]
  rw [← Category.assoc (D.t i k) (D.f k i) (D.ι k),
    coverPairSquare D i k]

private theorem coverTripleMiddleWhisker (D : Scheme.GlueData.{u}) (i j k : D.J) :
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫
        (D.f j k ≫ D.ι j) =
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫
        ((D.t j k ≫ D.f k j) ≫ D.ι k) := by
  rw [(coverPairSquare D j k).symm]

private theorem coverTripleSourceWhisker (D : Scheme.GlueData.{u}) (i j k : D.J) :
    (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j) ≫ D.ι i =
      (pullback.snd (D.f i j) (D.f i k) ≫ D.f i k) ≫ D.ι i := by
  rw [glueData_bridge_src D i j k]

private def coverTripleLeftNormal (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :=
  (pullbackComp
      (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j) (D.ι i)).app W ≪≫
    (pullbackCongr (coverTripleLeftSquare D i j k).symm).app W ≪≫
    (pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.f j k ≫ D.ι j)).symm.app W ≪≫
    (pullback
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
        ((pullbackCongr (coverPairSquare D j k).symm).app W) ≪≫
    (pullback
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
        ((pullbackComp (D.t j k ≫ D.f k j) (D.ι k)).symm.app W) ≪≫
    (pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.t j k ≫ D.f k j)).app ((pullback (D.ι k)).obj W)

private def coverTripleRightNormal (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :=
  ((pullbackComp
        (pullback.snd (D.f i j) (D.f i k) ≫ D.f i k) (D.ι i)).app W ≪≫
      (pullbackCongr (coverTripleRightSquare D i j k).symm).app W ≪≫
      (pullbackComp
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        ((D.t j k ≫ D.f k j) ≫ D.ι k)).symm.app W ≪≫
      (pullback
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
          ((pullbackComp
            (D.t j k ≫ D.f k j) (D.ι k)).symm.app W)) ≪≫
    (pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.t j k ≫ D.f k j)).app ((pullback (D.ι k)).obj W)

private def coverTripleFirstNormal (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :=
  ((pullbackComp
        (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j) (D.ι i)).app W ≪≫
      (pullbackCongr (coverTripleLeftSquare D i j k).symm).app W ≪≫
      (pullbackComp
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k ≫ D.ι j)).symm.app W ≪≫
      (pullback
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
          ((pullbackComp (D.f j k) (D.ι j)).symm.app W)) ≪≫
    (pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.f j k)).app ((pullback (D.ι j)).obj W)

private theorem coverTripleFirst_collapse (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i)
        (coverRestrictionTransition D W i j) ≪≫
      (pullbackCongr (glueData_bridge_mid D i j k)).app
        (coverRestriction D W j)
    =
      coverTripleFirstNormal D W i j k := by
  unfold coverTripleFirstNormal
  rw [coverRestrictionTransition_eq_pullbackComparison D W i j
    (coverPairSquare D i j)]
  exact pullbackComparison_transport
    (pullback.fst (D.f i j) (D.f i k)) (D.f i j) (D.ι i)
    (D.t i j ≫ D.f j i) (D.ι j)
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
    (D.f j k) (coverPairSquare D i j)
    (glueData_bridge_mid D i j k) (coverTripleLeftSquare D i j k) W

private theorem coverTripleSecond_collapse (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :
    coverTripleFirstNormal D W i j k ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j)
        (coverRestrictionTransition D W j k) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
        (coverRestriction D W k)
    =
      coverTripleLeftNormal D W i j k ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k)).app
          (coverRestriction D W k) := by
  unfold coverTripleFirstNormal coverTripleLeftNormal
  rw [coverRestrictionTransition_eq_pullbackComparison D W j k
    (coverPairSquare D j k)]
  rw [pullbackBaseChangeTransport_pullbackComparison
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
    (D.f j k) (D.ι j) (D.t j k ≫ D.f k j) (D.ι k)
    (coverPairSquare D j k).symm W]
  exact iso_cancel_two_comparisons_grouped
    ((pullbackComp
        (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j) (D.ι i)).app W ≪≫
      (pullbackCongr (coverTripleLeftSquare D i j k).symm).app W ≪≫
      (pullbackComp
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k ≫ D.ι j)).symm.app W)
    ((pullback
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
        ((pullbackComp (D.f j k) (D.ι j)).app W))
    ((pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.f j k)).app ((pullback (D.ι j)).obj W))
    ((pullback
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
        ((pullbackCongr (coverPairSquare D j k).symm).app W))
    ((pullback
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
        ((pullbackComp (D.t j k ≫ D.f k j) (D.ι k)).symm.app W))
    ((pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.t j k ≫ D.f k j)).app ((pullback (D.ι k)).obj W))
    ((pullbackCongr (glueData_bridge_tgt D i j k)).app
      (coverRestriction D W k))

private theorem coverTripleLeft_collapse (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i)
        (coverRestrictionTransition D W i j) ≪≫
      (pullbackCongr (glueData_bridge_mid D i j k)).app
        (coverRestriction D W j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j)
        (coverRestrictionTransition D W j k) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
        (coverRestriction D W k)
    =
      coverTripleLeftNormal D W i j k ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k)).app
          (coverRestriction D W k) := by
  rw [← Iso.trans_assoc]
  rw [coverTripleFirst_collapse D W i j k]
  exact coverTripleSecond_collapse D W i j k

private theorem coverTripleNormal_cast (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :
    coverTripleLeftNormal D W i j k =
      (pullbackCongr (glueData_bridge_src D i j k)).app
          (coverRestriction D W i) ≪≫
        coverTripleRightNormal D W i j k := by
  unfold coverTripleLeftNormal coverTripleRightNormal
  have hcd := pullbackComp_symm_trans_map_pullbackCongr
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
    (coverPairSquare D j k).symm W
  have hsh := pullbackCongr_trans_pullbackComp
    (glueData_bridge_src D i j k) (D.ι i) W
  have hbe := pullbackCongr_pair_eq_pair
    (coverTripleLeftSquare D i j k).symm
    (coverTripleMiddleWhisker D i j k)
    (coverTripleSourceWhisker D i j k)
    (coverTripleRightSquare D i j k).symm W
  exact iso_cast_pipeline_grouped
    ((pullbackComp
      (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j) (D.ι i)).app W)
    ((pullbackCongr (coverTripleLeftSquare D i j k).symm).app W)
    ((pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.f j k ≫ D.ι j)).symm.app W)
    ((pullback
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
        ((pullbackCongr (coverPairSquare D j k).symm).app W))
    ((pullback
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))).mapIso
        ((pullbackComp (D.t j k ≫ D.f k j) (D.ι k)).symm.app W))
    ((pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      (D.t j k ≫ D.f k j)).app ((pullback (D.ι k)).obj W))
    ((pullbackCongr (glueData_bridge_src D i j k)).app
      ((pullback (D.ι i)).obj W))
    ((pullbackComp
      (pullback.snd (D.f i j) (D.f i k) ≫ D.f i k) (D.ι i)).app W)
    ((pullbackCongr (coverTripleRightSquare D i j k).symm).app W)
    ((pullbackCongr (coverTripleMiddleWhisker D i j k)).app W)
    ((pullbackComp
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
      ((D.t j k ≫ D.f k j) ≫ D.ι k)).symm.app W)
    ((pullbackCongr (coverTripleSourceWhisker D i j k)).app W)
    hcd hsh hbe

private theorem coverTripleRight_collapse (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :
    pullbackBaseChangeTransport
        (pullback.snd (D.f i j) (D.f i k))
        (D.f i k) (D.t i k ≫ D.f k i)
        (coverRestrictionTransition D W i k) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k).symm).app
        (coverRestriction D W k)
    =
      coverTripleRightNormal D W i j k := by
  unfold coverTripleRightNormal
  rw [coverRestrictionTransition_eq_pullbackComparison D W i k
    (coverPairSquare D i k)]
  exact pullbackComparison_transport
    (pullback.snd (D.f i j) (D.f i k)) (D.f i k) (D.ι i)
    (D.t i k ≫ D.f k i) (D.ι k)
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
    (D.t j k ≫ D.f k j) (coverPairSquare D i k)
    (glueData_bridge_tgt D i j k).symm
    (coverTripleRightSquare D i j k) W

private theorem coverTriple_cancel (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :
    ((pullbackCongr (glueData_bridge_src D i j k)).app
          (coverRestriction D W i) ≪≫
        pullbackBaseChangeTransport
          (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i)
          (coverRestrictionTransition D W i k) ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k).symm).app
          (coverRestriction D W k)) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
        (coverRestriction D W k)
    =
      (pullbackCongr (glueData_bridge_src D i j k)).app
          (coverRestriction D W i) ≪≫
        pullbackBaseChangeTransport
          (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i)
          (coverRestrictionTransition D W i k) := by
  exact iso_cancel_tail_grouped
    (C := (Limits.pullback (D.f i j) (D.f i k)).Modules)
    ((pullbackCongr (glueData_bridge_src D i j k)).app
      (coverRestriction D W i))
    (pullbackBaseChangeTransport
      (pullback.snd (D.f i j) (D.f i k))
      (D.f i k) (D.t i k ≫ D.f k i)
      (coverRestrictionTransition D W i k))
    ((pullbackCongr (glueData_bridge_tgt D i j k)).app
      (coverRestriction D W k))

private theorem coverTriple_finish (D : Scheme.GlueData.{u})
    (W : D.glued.Modules) (i j k : D.J) :
    coverTripleLeftNormal D W i j k ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k)).app
          (coverRestriction D W k)
      =
        (pullbackCongr (glueData_bridge_src D i j k)).app
            (coverRestriction D W i) ≪≫
          pullbackBaseChangeTransport
            (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i)
            (coverRestrictionTransition D W i k) := by
  rw [coverTripleNormal_cast D W i j k]
  rw [← coverTripleRight_collapse D W i j k]
  exact coverTriple_cancel D W i j k

/-- The canonical cover transitions satisfy the triple-overlap cocycle. -/
theorem coverRestrictionTransition_cocycle (W : D.glued.Modules) (i j k : D.J) :
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i)
        (coverRestrictionTransition D W i j) ≪≫
      (pullbackCongr (glueData_bridge_mid D i j k)).app
        (coverRestriction D W j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j)
        (coverRestrictionTransition D W j k) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
        (coverRestriction D W k)
    =
      (pullbackCongr (glueData_bridge_src D i j k)).app
          (coverRestriction D W i) ≪≫
        pullbackBaseChangeTransport
          (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i)
          (coverRestrictionTransition D W i k) := by
  rw [coverTripleLeft_collapse D W i j k]
  exact coverTriple_finish D W i j k

end AlgebraicGeometry.Scheme.Modules
