/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCategory

/-!
# Transporting module descent data across chartwise isomorphisms

Descent data may be conjugated by an arbitrary family of isomorphisms
on its chart objects.  This elementary operation is useful when a
geometric pullback is first constructed globally and then rewritten in
the expected chartwise form.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable {D : Scheme.GlueData.{0}}

/-- Equality casts for pullback are natural under conjugation by an
isomorphism of coefficients. -/
theorem pullbackCongr_conjugate
    {X Y : Scheme.{0}} {p q : X ⟶ Y}
    (h : p = q) {A B : Y.Modules} (e : A ≅ B) :
    (pullback p).map e.inv ≫
          (pullbackCongr h).hom.app A ≫
        (pullback q).map e.hom =
      (pullbackCongr h).hom.app B := by
  rw [← (pullbackCongr h).hom.naturality e.hom]
  simp

/-- Naturality of a pullback equality cast, packaged as an equality of
isomorphism composites. -/
theorem pullbackMapIso_trans_pullbackCongr
    {X Y : Scheme.{0}} {p q : X ⟶ Y}
    (h : p = q) {A B : Y.Modules} (e : A ≅ B) :
    (pullback p).mapIso e ≪≫
        (pullbackCongr h).app B =
      (pullbackCongr h).app A ≪≫
        (pullback q).mapIso e := by
  apply Iso.ext
  exact (pullbackCongr h).hom.naturality e.hom

/-- Pullback transport of a transition commutes with conjugating its
two coefficient objects. -/
theorem pullbackBaseChangeTransport_conjugate
    {W V Yi Yj : Scheme.{0}} (p : W ⟶ V)
    (a : V ⟶ Yi) (b : V ⟶ Yj)
    {Mi Ni : Yi.Modules} {Mj Nj : Yj.Modules}
    (ei : Mi ≅ Ni) (ej : Mj ≅ Nj)
    (g : (pullback a).obj Mi ≅ (pullback b).obj Mj) :
    pullbackBaseChangeTransport p a b
        ((pullback a).mapIso ei.symm ≪≫ g ≪≫
          (pullback b).mapIso ej) =
      (pullback (p ≫ a)).mapIso ei.symm ≪≫
        pullbackBaseChangeTransport p a b g ≪≫
        (pullback (p ≫ b)).mapIso ej := by
    apply Iso.ext
    simp only [pullbackBaseChangeTransport, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp]
    change
      (pullbackComp p a).inv.app Ni ≫
            (pullback p).map ((pullback a).map ei.inv) ≫
              (pullback p).map g.hom ≫
                (pullback p).map ((pullback b).map ej.hom) ≫
                  (pullbackComp p b).hom.app Nj =
        (pullback (p ≫ a)).map ei.inv ≫
            (pullbackComp p a).inv.app Mi ≫
              (pullback p).map g.hom ≫
                (pullbackComp p b).hom.app Mj ≫
                  (pullback (p ≫ b)).map ej.hom
    have ha :
        (pullbackComp p a).inv.app Ni ≫
            (pullback p).map ((pullback a).map ei.inv) =
          (pullback (p ≫ a)).map ei.inv ≫
            (pullbackComp p a).inv.app Mi :=
      by
        simpa only [Functor.comp_map] using
          ((pullbackComp p a).inv.naturality ei.inv).symm
    have hb :
        (pullback p).map ((pullback b).map ej.hom) ≫
            (pullbackComp p b).hom.app Nj =
          (pullbackComp p b).hom.app Mj ≫
            (pullback (p ≫ b)).map ej.hom :=
      (pullbackComp p b).hom.naturality ej.hom
    rw [reassoc_of% ha]
    rw [hb]

/-- Abstract cancellation pattern for two conjugated transition maps
separated by equality-cast bridges. -/
theorem conjugatedTwoStepIsoChain
    {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : C}
    (p : X₀ ≅ X₁) (g : X₁ ≅ X₂)
    (e : X₂ ≅ X₃) (c : X₃ ≅ X₄)
    (e' : X₅ ≅ X₄) (h : X₅ ≅ X₆)
    (k : X₆ ≅ X₇) (t : X₇ ≅ X₈)
    (r : X₉ ≅ X₈) (c' : X₂ ≅ X₅)
    (t' : X₆ ≅ X₉)
    (he : e ≪≫ c = c' ≪≫ e')
    (hk : k ≪≫ t = t' ≪≫ r) :
    (p ≪≫ g ≪≫ e) ≪≫ c ≪≫
        (e'.symm ≪≫ h ≪≫ k) ≪≫ t =
      p ≪≫ (g ≪≫ c' ≪≫ h ≪≫ t') ≪≫ r := by
  apply Iso.ext
  have heh := congrArg Iso.hom he
  have hkh := congrArg Iso.hom hk
  simp only [Iso.trans_hom, Iso.symm_hom] at heh hkh ⊢
  simp only [Category.assoc]
  rw [reassoc_of% heh]
  simp only [Iso.hom_inv_id_assoc]
  rw [hkh]

/-- Abstract cancellation pattern for the source bridge on the
one-transition side of a cocycle. -/
theorem conjugatedOneStepIsoChain
    {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (c : X₀ ≅ X₁) (p' : X₁ ≅ X₂)
    (h : X₂ ≅ X₃) (r : X₃ ≅ X₄)
    (p : X₀ ≅ X₅) (c' : X₅ ≅ X₂)
    (hp : p ≪≫ c' = c ≪≫ p') :
    c ≪≫ p' ≪≫ h ≪≫ r =
      p ≪≫ c' ≪≫ h ≪≫ r := by
  apply Iso.ext
  have hph := congrArg Iso.hom hp
  simp only [Iso.trans_hom] at hph ⊢
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ h.hom ≫ r.hom) hph.symm

/-- Conjugate a descent transition by chartwise isomorphisms. -/
noncomputable def transportTransition
    (A : CoverDescentData D)
    (M : ∀ i, (D.U i).Modules)
    (e : ∀ i, A.chart i ≅ M i) :
    CoverTransition D M :=
  fun i j =>
    (pullback (D.f i j)).mapIso (e i).symm ≪≫
      A.transition i j ≪≫
      (pullback (D.t i j ≫ D.f j i)).mapIso (e j)

/-- Conjugating transitions preserves the diagonal identity law. -/
theorem transportTransition_self
    (A : CoverDescentData D)
    (M : ∀ i, (D.U i).Modules)
    (e : ∀ i, A.chart i ≅ M i)
    (i : D.J) :
    transportTransition A M e i i =
      eqToIso (congrArg
        (fun φ => (pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by
          rw [D.t_id i, Category.id_comp])) := by
  rw [transportTransition, A.identity i]
  apply Iso.ext
  let h : D.f i i = D.t i i ≫ D.f i i := by
    rw [D.t_id i, Category.id_comp]
  simpa only [Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, eqToIso.hom,
    pullbackCongr_hom_app_eqToHom] using
    (pullbackCongr_conjugate h (e i))

/-- Conjugating transitions preserves the triple-overlap cocycle. -/
theorem transportTransition_cocycle
    (A : CoverDescentData D)
    (M : ∀ i, (D.U i).Modules)
    (e : ∀ i, A.chart i ≅ M i) :
    (transportTransition A M e).IsCocycle D := by
  intro i j k
  unfold transportTransition
  rw [pullbackBaseChangeTransport_conjugate,
    pullbackBaseChangeTransport_conjugate,
    pullbackBaseChangeTransport_conjugate]
  let p₁₂ := pullback.fst (D.f i j) (D.f i k)
  let p₁₃ := pullback.snd (D.f i j) (D.f i k)
  let p₂₃ :=
    D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)
  let s :=
    (pullback (p₁₂ ≫ D.f i j)).mapIso (e i).symm
  let gij :=
    pullbackBaseChangeTransport p₁₂
      (D.f i j) (D.t i j ≫ D.f j i)
      (A.transition i j)
  let mij :=
    (pullback (p₁₂ ≫ (D.t i j ≫ D.f j i))).mapIso
      (e j)
  let cm :=
    (pullbackCongr
      (glueData_bridge_mid D i j k)).app (M j)
  let cA :=
    (pullbackCongr
      (glueData_bridge_mid D i j k)).app (A.chart j)
  let mjk :=
    (pullback (p₂₃ ≫ D.f j k)).mapIso (e j)
  let gjk :=
    pullbackBaseChangeTransport p₂₃
      (D.f j k) (D.t j k ≫ D.f k j)
      (A.transition j k)
  let tk :=
    (pullback (p₂₃ ≫ (D.t j k ≫ D.f k j))).mapIso
      (e k)
  let tm :=
    (pullbackCongr
      (glueData_bridge_tgt D i j k)).app (M k)
  let tA :=
    (pullbackCongr
      (glueData_bridge_tgt D i j k)).app (A.chart k)
  let r :=
    (pullback (p₁₃ ≫ (D.t i k ≫ D.f k i))).mapIso
      (e k)
  let csM :=
    (pullbackCongr
      (glueData_bridge_src D i j k)).app (M i)
  let csA :=
    (pullbackCongr
      (glueData_bridge_src D i j k)).app (A.chart i)
  let s' :=
    (pullback (p₁₃ ≫ D.f i k)).mapIso (e i).symm
  let gik :=
    pullbackBaseChangeTransport p₁₃
      (D.f i k) (D.t i k ≫ D.f k i)
      (A.transition i k)
  calc
    _ = s ≪≫ (gij ≪≫ cA ≪≫ gjk ≪≫ tA) ≪≫ r := by
      exact conjugatedTwoStepIsoChain
        s gij mij cm mjk gjk tk tm r cA tA
        (pullbackMapIso_trans_pullbackCongr
          (glueData_bridge_mid D i j k) (e j))
        (pullbackMapIso_trans_pullbackCongr
          (glueData_bridge_tgt D i j k) (e k))
    _ = s ≪≫ (csA ≪≫ gik) ≪≫ r := by
      exact congrArg (fun z => s ≪≫ z ≪≫ r)
        (A.cocycle i j k)
    _ = _ := by
      exact (conjugatedOneStepIsoChain
        csM s' gik r s csA
        (pullbackMapIso_trans_pullbackCongr
          (glueData_bridge_src D i j k) (e i).symm)).symm

/-- Transport a cover descent datum across chartwise
isomorphisms. -/
noncomputable def transport
    (A : CoverDescentData D)
    (M : ∀ i, (D.U i).Modules)
    (e : ∀ i, A.chart i ≅ M i) :
    CoverDescentData D where
  chart := M
  transition := transportTransition A M e
  identity := transportTransition_self A M e
  cocycle := transportTransition_cocycle A M e

/-- Transporting successively through two chart isomorphisms is the
same as transporting through their composite. -/
theorem transportTransition_comp
    (A : CoverDescentData D)
    (M N : ∀ i, (D.U i).Modules)
    (e : ∀ i, A.chart i ≅ M i)
    (d : ∀ i, M i ≅ N i) (i j : D.J) :
    transportTransition A N (fun i => e i ≪≫ d i) i j =
      transportTransition (transport A M e) N d i j := by
  apply Iso.ext
  simp [transportTransition, transport]

/-- A compatible family of chart isomorphisms conjugates one raw
transition family to the other. -/
theorem conjugatedTransition_eq_of_compatible
    (M N : ∀ i, (D.U i).Modules)
    (g : CoverTransition D M)
    (h : CoverTransition D N)
    (e : ∀ i, M i ≅ N i)
    (hcompat : DescentMorphismCompatible
      D M N g h (fun i => (e i).hom))
    (i j : D.J) :
    (pullback (D.f i j)).mapIso (e i).symm ≪≫
        g i j ≪≫
        (pullback (D.t i j ≫ D.f j i)).mapIso (e j) =
      h i j := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  rw [← hcompat i j]
  simp

/-- The original datum is canonically isomorphic to its chartwise
transport. -/
noncomputable def transportIso
    (A : CoverDescentData D)
    (M : ∀ i, (D.U i).Modules)
    (e : ∀ i, A.chart i ≅ M i) :
    A ≅ transport A M e where
  hom :=
    { app := fun i => (e i).hom
      compatible := by
        intro i j
        simp [transport, transportTransition] }
  inv :=
    { app := fun i => (e i).inv
      compatible := by
        intro i j
        simp [transport, transportTransition] }
  hom_inv_id := by
    apply Hom.ext
    intro i
    change (e i).hom ≫ (e i).inv = 𝟙 (A.chart i)
    exact (e i).hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    intro i
    change (e i).inv ≫ (e i).hom = 𝟙 (M i)
    exact (e i).inv_hom_id

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
