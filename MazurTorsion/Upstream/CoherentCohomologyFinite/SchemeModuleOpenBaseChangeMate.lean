/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenBaseChange

/-!
# The canonical mate for open base change

For a scheme morphism restricted over an open of its target, the
explicit pullback base-change isomorphism is the mate of the concrete
pushforward/restriction isomorphism.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Conjugating pullback along an equality of scheme morphisms gives
pushforward along the reversed equality. -/
lemma pullbackCongr_conjugate
    {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) :
    conjugateEquiv
        (pullbackPushforwardAdjunction g)
        (pullbackPushforwardAdjunction f)
        (pullbackCongr h).hom =
      (pushforwardCongr h.symm).hom := by
  subst g
  have hp :
      (pullbackCongr (rfl : f = f)).hom =
        𝟙 (pullback f) := by
    rfl
  rw [hp, conjugateEquiv_id]
  have hq :
      (pushforwardCongr (rfl : f = f)).hom =
        𝟙 (pushforward f) := by
    ext M U x
    rw [pushforwardCongr_hom_app_app]
    exact congr($(M.presheaf.map_id _) x)
  exact hq.symm

/-- The inverse comparison from open restriction to pullback has
identity conjugate. -/
lemma restrictFunctorIsoPullback_inv_conjugate
    {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] :
    conjugateEquiv
        (restrictAdjunction j)
        (pullbackPushforwardAdjunction j)
        (restrictFunctorIsoPullback j).inv =
      𝟙 (pushforward j) := by
  have h :=
    conjugateEquiv_comm
      (pullbackPushforwardAdjunction j)
      (restrictAdjunction j)
      ((restrictFunctorIsoPullback j).inv_hom_id)
  rw [restrictFunctorIsoPullback_conjugate] at h
  simpa using h

/-- Whiskering the restriction-to-pullback comparison on the right
still has identity conjugate. -/
lemma restrictFunctorIsoPullback_hom_whiskerRight_conjugate
    {A B C : Scheme.{u}}
    (j : A ⟶ B) [IsOpenImmersion j] (g : C ⟶ A) :
    conjugateEquiv
        ((pullbackPushforwardAdjunction j).comp
          (pullbackPushforwardAdjunction g))
        ((restrictAdjunction j).comp
          (pullbackPushforwardAdjunction g))
        (Functor.whiskerRight
          (restrictFunctorIsoPullback j).hom
          (pullback g)) =
      𝟙 (pushforward g ⋙ pushforward j) := by
  rw [conjugateEquiv_whiskerRight,
    restrictFunctorIsoPullback_conjugate]
  ext
  simp

/-- Whiskering the inverse restriction-to-pullback comparison on the
left still has identity conjugate. -/
lemma restrictFunctorIsoPullback_inv_whiskerLeft_conjugate
    {A B C : Scheme.{u}}
    (f : B ⟶ C) (j : A ⟶ B) [IsOpenImmersion j] :
    conjugateEquiv
        ((pullbackPushforwardAdjunction f).comp
          (restrictAdjunction j))
        ((pullbackPushforwardAdjunction f).comp
          (pullbackPushforwardAdjunction j))
        (Functor.whiskerLeft
          (pullback f)
          (restrictFunctorIsoPullback j).inv) =
      𝟙 (pushforward j ⋙ pushforward f) := by
  rw [conjugateEquiv_whiskerLeft,
    restrictFunctorIsoPullback_inv_conjugate]
  ext
  simp

/-- The conjugate of the explicit open pullback comparison is the
canonical comparison between the corresponding composite
pushforwards. -/
lemma pullbackRestrictBaseChangeIso_conjugate
    (f : X ⟶ Y) (U : Y.Opens) :
    conjugateEquiv
        ((pullbackPushforwardAdjunction f).comp
          (restrictAdjunction (f ⁻¹ᵁ U).ι))
        ((restrictAdjunction U.ι).comp
          (pullbackPushforwardAdjunction (f ∣_ U)))
        (pullbackRestrictBaseChangeIso f U).hom =
      (pushforwardComp (f ⁻¹ᵁ U).ι f).hom ≫
        (pushforwardCongr
          (morphismRestrict_ι f U).symm).hom ≫
        (pushforwardComp (f ∣_ U) U.ι).inv := by
  let A₀ :=
    (restrictAdjunction U.ι).comp
      (pullbackPushforwardAdjunction (f ∣_ U))
  let A₁ :=
    (pullbackPushforwardAdjunction U.ι).comp
      (pullbackPushforwardAdjunction (f ∣_ U))
  let A₂ :=
    pullbackPushforwardAdjunction ((f ∣_ U) ≫ U.ι)
  let A₃ :=
    pullbackPushforwardAdjunction ((f ⁻¹ᵁ U).ι ≫ f)
  let A₄ :=
    (pullbackPushforwardAdjunction f).comp
      (pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι)
  let A₅ :=
    (pullbackPushforwardAdjunction f).comp
      (restrictAdjunction (f ⁻¹ᵁ U).ι)
  change
    conjugateEquiv A₅ A₀
      (Functor.whiskerRight
            (restrictFunctorIsoPullback U.ι).hom
            (pullback (f ∣_ U)) ≫
        (pullbackComp (f ∣_ U) U.ι).hom ≫
        (pullbackCongr (morphismRestrict_ι f U)).hom ≫
        (pullbackComp (f ⁻¹ᵁ U).ι f).inv ≫
        Functor.whiskerLeft
          (pullback f)
          (restrictFunctorIsoPullback
            (f ⁻¹ᵁ U).ι).inv) =
      _
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp A₅ A₄ A₀]
  rw [← conjugateEquiv_comp A₄ A₃ A₀]
  rw [← conjugateEquiv_comp A₃ A₂ A₀]
  rw [← conjugateEquiv_comp A₂ A₁ A₀]
  rw [
    restrictFunctorIsoPullback_inv_whiskerLeft_conjugate,
    conjugateEquiv_pullbackComp_inv,
    pullbackCongr_conjugate,
    pullbackComp_hom_conjugate,
    restrictFunctorIsoPullback_hom_whiskerRight_conjugate]
  simp

private lemma restrictMate_app_app_apply
    (f : X ⟶ Y) (U : Y.Opens)
    (β : TwoSquare
      (pushforward f)
      (restrictFunctor (f ⁻¹ᵁ U).ι)
      (restrictFunctor U.ι)
      (pushforward (f ∣_ U)))
    (M : (↑(f ⁻¹ᵁ U) : Scheme.{u}).Modules)
    (V : Y.Opens)
    (x : Γ(
      (pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj M,
      V)) :
    (((mateEquiv
        (restrictAdjunction (f ⁻¹ᵁ U).ι)
        (restrictAdjunction U.ι) β).natTrans).app M).app V x =
      (((restrictAdjunction U.ι).unit.app
            ((pushforward f).obj
              ((pushforward (f ⁻¹ᵁ U).ι).obj M)) ≫
          (pushforward U.ι).map
            (β.natTrans.app
              ((pushforward (f ⁻¹ᵁ U).ι).obj M)) ≫
          (pushforward U.ι).map
            ((pushforward (f ∣_ U)).map
              ((restrictAdjunction
                (f ⁻¹ᵁ U).ι).counit.app M))).app V x) := by
  simp only [mateEquiv_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map,
    Hom.comp_app, ConcreteCategory.comp_apply]
  change
    ConcreteCategory.hom
      (((restrictAdjunction U.ι).unit.app
            ((pushforward f).obj
              ((pushforward (f ⁻¹ᵁ U).ι).obj M)) ≫
          (pushforward U.ι).map
            (β.natTrans.app
              ((pushforward (f ⁻¹ᵁ U).ι).obj M)) ≫
          (pushforward U.ι).map
            ((pushforward (f ∣_ U)).map
              ((restrictAdjunction
                (f ⁻¹ᵁ U).ι).counit.app M))).app V) x =
      _
  rfl

/-- The mate of pushforward/restriction base change is the canonical
pullback/restriction base-change isomorphism. -/
theorem pullbackRestrictMate_eq_baseChange
    (f : X ⟶ Y) (U : Y.Opens) :
    pullbackRestrictMate f U =
      (pullbackRestrictBaseChangeIso f U).hom := by
  let e :=
    mateEquiv
      (G := restrictFunctor U.ι)
      (H := restrictFunctor (f ⁻¹ᵁ U).ι)
      (pullbackPushforwardAdjunction f)
      (pullbackPushforwardAdjunction (f ∣_ U))
  let α : TwoSquare
      (restrictFunctor U.ι)
      (pullback f)
      (pullback (f ∣_ U))
      (restrictFunctor (f ⁻¹ᵁ U).ι) :=
    TwoSquare.mk _ _ _ _
      (pullbackRestrictBaseChangeIso f U).hom
  let β : TwoSquare
      (pushforward f)
      (restrictFunctor (f ⁻¹ᵁ U).ι)
      (restrictFunctor U.ι)
      (pushforward (f ∣_ U)) :=
    TwoSquare.mk _ _ _ _
      (pushforwardRestrictIso f U).hom
  have h : e.symm β = α := by
    apply e.injective
    rw [e.apply_symm_apply]
    let e' :=
      mateEquiv
        (G := pushforward f)
        (H := pushforward (f ∣_ U))
        (restrictAdjunction (f ⁻¹ᵁ U).ι)
        (restrictAdjunction U.ι)
    apply e'.injective
    change (e' β).natTrans = (e' (e α)).natTrans
    rw [show
      (e' (e α)).natTrans =
        conjugateEquiv
          ((pullbackPushforwardAdjunction f).comp
            (restrictAdjunction (f ⁻¹ᵁ U).ι))
          ((restrictAdjunction U.ι).comp
            (pullbackPushforwardAdjunction (f ∣_ U)))
          α
      from iterated_mateEquiv_conjugateEquiv
        (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ∣_ U))
        (restrictAdjunction U.ι)
        (restrictAdjunction (f ⁻¹ᵁ U).ι)
        α]
    change
      (e' β).natTrans =
        conjugateEquiv
          ((pullbackPushforwardAdjunction f).comp
            (restrictAdjunction (f ⁻¹ᵁ U).ι))
          ((restrictAdjunction U.ι).comp
            (pullbackPushforwardAdjunction (f ∣_ U)))
          (pullbackRestrictBaseChangeIso f U).hom
    rw [pullbackRestrictBaseChangeIso_conjugate]
    ext M V x
    dsimp only [e']
    rw [restrictMate_app_app_apply]
    have hβ :
        β.natTrans =
          (pushforwardRestrictIso f U).hom := by
      rfl
    rw [hβ]
    simp only [Functor.comp_obj, pushforward_obj_obj, Functor.id_obj,
      Hom.comp_app, restrictAdjunction_unit_app_app, homOfLE_leOfHom,
      pushforward_obj_presheaf_map_op, Functor.op_obj, Functor.op_map,
      Quiver.Hom.unop_op, TopologicalSpace.Opens.map_homOfLE,
      pushforward_map_app, pushforwardRestrictIso_hom_app_app,
      eqToHom_op, eqToHom_unop, restrictAdjunction_counit_app_app,
      NatTrans.comp_app, Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
      pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
      pushforwardComp_inv_app_app, Category.comp_id, Category.id_comp]
    apply ConcreteCategory.congr_hom
    exact (congrArg (· ≫ _) (M.presheaf.map_comp _ _).symm).trans
      (M.presheaf.map_comp _ _).symm
  exact congrArg TwoSquare.natTrans h

end AlgebraicGeometry.Scheme.Modules
