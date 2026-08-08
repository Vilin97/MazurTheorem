/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Topology.Sheaves.Flasque

/-!
# Restriction of sheaves to an open subspace

This file supplies the restriction functor along an open embedding, its adjunction with
pushforward, and the exactness properties needed to restrict short exact sequences of sheaves of
abelian groups.
-/

open CategoryTheory Limits Opposite TopologicalSpace Topology

universe u v w

variable (C : Type v) [Category.{w} C] {X Y : TopCat.{u}} {f : Y ⟶ X}
  (hf : IsOpenEmbedding f)

namespace TopCat.Sheaf

/-- Restriction of sheaves along an open embedding. -/
abbrev restrict : Sheaf C X ⥤ Sheaf C Y :=
  haveI := hf.functor_isContinuous
  hf.functor.sheafPushforwardContinuous C ..

/-- Restriction along an open embedding is left adjoint to pushforward. -/
abbrev restrictPushforwardAdjunction : restrict C hf ⊣ pushforward C f :=
  haveI := hf.functor_isContinuous
  Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction ..

instance restrict_isLeftAdjoint : (restrict C hf).IsLeftAdjoint :=
  (restrictPushforwardAdjunction C hf).isLeftAdjoint

variable (F : Sheaf C X) (U V : Opens X)

/-- The adjunction unit from a sheaf to the pushforward of its restriction to an open. -/
abbrev toRestrict := (restrictPushforwardAdjunction C U.isOpenEmbedding).unit

lemma toRestrict_obj_obj_obj :
    ((restrict C U.isOpenEmbedding ⋙ pushforward C U.inclusion').obj F).obj.obj (op V) =
      F.obj.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V))) := rfl

lemma toRestrict_app_hom_app :
    ((toRestrict C U).app F).hom.app (op V) =
      F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op := by
  letI := U.isOpenEmbedding.functor_isContinuous
  exact Adjunction.sheafPushforwardContinuous_unit_app_hom_app
    U.isOpenEmbedding.isOpenMap.adjunction _ _ F (op V)

private lemma restrict_comp_sheafToPresheaf_preservesFiniteLimits
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    PreservesFiniteLimits
      (restrict AddCommGrpCat.{u} hf ⋙
        sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) := by
  letI := hf.functor_isContinuous
  letI : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  letI : PreservesFiniteLimits
      ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
        hf.functor.op) := inferInstance
  change PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringLeft _ _ _).obj hf.functor.op)
  exact comp_preservesFiniteLimits _ _

private lemma sheafToPresheaf_reflectsFiniteShape
    {Y : TopCat.{u}} (J : Type) [SmallCategory J] [FinCategory J] :
    ReflectsLimitsOfShape J
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) := by
  infer_instance

/-- Restriction of sheaves of abelian groups along an open embedding preserves finite limits. -/
instance restrict_preservesFiniteLimits
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    PreservesFiniteLimits (restrict AddCommGrpCat.{u} hf) := by
  letI := restrict_comp_sheafToPresheaf_preservesFiniteLimits hf
  constructor
  intro J _ _
  have hPreserve : PreservesLimitsOfShape J
      (restrict AddCommGrpCat.{u} hf ⋙
        sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) := inferInstance
  have hReflect := sheafToPresheaf_reflectsFiniteShape (Y := Y) J
  exact @preservesLimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _
    (restrict AddCommGrpCat.{u} hf)
    (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    hPreserve hReflect

/-- Restriction of sheaves of abelian groups is additive. -/
instance restrict_additive {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    (restrict AddCommGrpCat.{u} hf).Additive where
  map_add := by
    intros
    apply CategoryTheory.Sheaf.hom_ext
    rfl

/-- Pushforward of sheaves of abelian groups is additive. -/
instance pushforward_additive {X Y : TopCat.{u}} (f : Y ⟶ X) :
    (pushforward AddCommGrpCat.{u} f).Additive where
  map_add := by
    intros
    apply CategoryTheory.Sheaf.hom_ext
    rfl

/-- Restriction of a flasque sheaf to an open subspace is flasque. -/
theorem IsFlasque.of_restrict {X Y : TopCat.{u}} {f : Y ⟶ X}
    (F : Sheaf C X) [F.IsFlasque] (hf : IsOpenEmbedding f) :
    ((restrict C hf).obj F).IsFlasque where
  epi i := by
    change Epi (F.obj.map (hf.functor.op.map i))
    infer_instance

end TopCat.Sheaf
