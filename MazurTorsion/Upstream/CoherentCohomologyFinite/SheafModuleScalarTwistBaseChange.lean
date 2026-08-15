/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentBaseChangeTransition

/-!
# Scalar twisting commutes with base change on cover descent data

The base-change functor has literal pullback chart objects and its
transition is the explicit pulled-back transition.  Consequently the
identity maps on those chart objects identify base change after scalar
twisting with scalar twisting by the pulled-back cocycle after base
change.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

private abbrev D' := gluedCover (𝒰.pullback₁ f)

/-- The chartwise identity comparison between the two orders of
scalar twisting and base change. -/
noncomputable def scalarTwistBaseChangeHom
    (a : ∀ i j, Γ((D 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition (D 𝒰) a)
    (A : CoverDescentData (D 𝒰)) :
    ((scalarTwistFunctor a hself hcocycle ⋙
        baseChangeFunctor 𝒰 f).obj A) ⟶
      ((baseChangeFunctor 𝒰 f ⋙
        scalarTwistFunctor
          (baseChangeCoverUnit 𝒰 f a)
          (baseChangeCoverUnit_self 𝒰 f a hself)
          (baseChangeCoverUnit_cocycle 𝒰 f a hcocycle)).obj A) where
  app i := 𝟙 _
  compatible := by
      let M : ∀ i : 𝒰.I₀,
          ((D' 𝒰 f).U i).Modules :=
        fun i =>
          (pullback (𝒰.pullbackHom f i)).obj
            (A.chart i)
      let g : CoverTransition (D' 𝒰 f) M :=
        fun i j =>
          (baseChangeObject 𝒰 f
            (scalarTwistObject
              a hself hcocycle A)).transition i j
      let h : CoverTransition (D' 𝒰 f) M :=
        fun i j =>
          scalarTwistedTransition
            (baseChangeObject 𝒰 f A)
            (baseChangeCoverUnit 𝒰 f a) i j
      change DescentMorphismCompatible
        (D' 𝒰 f) M M g h (fun i => 𝟙 (M i))
      have htransition : h = g := by
        funext i j
        dsimp only [h, g]
        unfold scalarTwistedTransition
        rw [baseChangeObject_transition 𝒰 f A i j,
          baseChangeObject_transition 𝒰 f
            (scalarTwistObject
              a hself hcocycle A) i j]
        exact
          (baseChangeTransition_scalarTwist
            𝒰 f A a hself hcocycle i j).symm
      rw [htransition]
      exact descentMorphismCompatible_id
        (D' 𝒰 f) M g

@[simp]
theorem scalarTwistBaseChangeHom_app
    (a : ∀ i j, Γ((D 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition (D 𝒰) a)
    (A : CoverDescentData (D 𝒰)) (i : 𝒰.I₀) :
    (scalarTwistBaseChangeHom
      𝒰 f a hself hcocycle A).app i = 𝟙 _ :=
  rfl

/-- Objectwise isomorphism between scalar twisting before and after
base change. -/
noncomputable def scalarTwistBaseChangeIso
    (a : ∀ i j, Γ((D 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition (D 𝒰) a)
    (A : CoverDescentData (D 𝒰)) :
    ((scalarTwistFunctor a hself hcocycle ⋙
        baseChangeFunctor 𝒰 f).obj A) ≅
      ((baseChangeFunctor 𝒰 f ⋙
        scalarTwistFunctor
          (baseChangeCoverUnit 𝒰 f a)
          (baseChangeCoverUnit_self 𝒰 f a hself)
          (baseChangeCoverUnit_cocycle 𝒰 f a hcocycle)).obj A) := by
  let h := scalarTwistBaseChangeHom
    𝒰 f a hself hcocycle A
  letI : ∀ i, IsIso (h.app i) := fun i => by
    change IsIso (𝟙 _)
    infer_instance
  exact h.isoOfComponents

@[simp]
theorem scalarTwistBaseChangeIso_hom_app
    (a : ∀ i j, Γ((D 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition (D 𝒰) a)
    (A : CoverDescentData (D 𝒰)) (i : 𝒰.I₀) :
    (scalarTwistBaseChangeIso
      𝒰 f a hself hcocycle A).hom.app i = 𝟙 _ :=
  rfl

/-- Scalar twisting of cover descent data commutes naturally with
base change, with the cocycle pulled back to the base-changed cover. -/
noncomputable def scalarTwistBaseChangeNatIso
    (a : ∀ i j, Γ((D 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition (D 𝒰) a) :
    scalarTwistFunctor a hself hcocycle ⋙
        baseChangeFunctor 𝒰 f ≅
      baseChangeFunctor 𝒰 f ⋙
        scalarTwistFunctor
          (baseChangeCoverUnit 𝒰 f a)
          (baseChangeCoverUnit_self 𝒰 f a hself)
          (baseChangeCoverUnit_cocycle 𝒰 f a hcocycle) :=
  NatIso.ofComponents
    (scalarTwistBaseChangeIso 𝒰 f a hself hcocycle)
    (fun {A B} φ => by
      apply Hom.ext
      intro i
      simp only [comp_app, Functor.comp_map]
      rw [scalarTwistBaseChangeIso_hom_app
          𝒰 f a hself hcocycle B i,
        scalarTwistBaseChangeIso_hom_app
          𝒰 f a hself hcocycle A i]
      rw [baseChangeFunctor_map_app 𝒰 f
          ((scalarTwistFunctor a hself hcocycle).map φ) i,
        scalarTwistFunctor_map_app a hself hcocycle φ i]
      rw [scalarTwistFunctor_map_app
          (baseChangeCoverUnit 𝒰 f a)
          (baseChangeCoverUnit_self 𝒰 f a hself)
          (baseChangeCoverUnit_cocycle 𝒰 f a hcocycle)
          ((baseChangeFunctor 𝒰 f).map φ) i,
        baseChangeFunctor_map_app 𝒰 f φ i]
      exact
        (Category.comp_id
          ((pullback (𝒰.pullbackHom f i)).map
            (φ.app i))).trans
          (Category.id_comp
            ((pullback (𝒰.pullbackHom f i)).map
              (φ.app i))).symm)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
