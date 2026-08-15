/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Restriction of sheaves to open subspaces

This file records the restriction functor associated to an open embedding,
its adjunction with pushforward, and the two adjointness instances needed by
the local-vanishing argument.
-/

open CategoryTheory Opposite TopologicalSpace Topology

universe u

variable (C : Type*) [Category* C]
variable {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)

namespace TopCat.Sheaf

/-- Restriction of sheaves along an open embedding. -/
abbrev restrict : Sheaf C X ⥤ Sheaf C Y :=
  haveI := hf.functor_isContinuous
  hf.functor.sheafPushforwardContinuous C ..

/-- Restriction to an open subspace is left adjoint to pushforward. -/
abbrev restrictPushforwardAdjunction :
    restrict C hf ⊣ pushforward C f :=
  haveI := hf.functor_isContinuous
  Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction ..

instance restrict_isLeftAdjoint : (restrict C hf).IsLeftAdjoint :=
  (restrictPushforwardAdjunction C hf).isLeftAdjoint

/--
For sheaves of abelian groups, restriction along an open embedding is also
a right adjoint.  The explicit sheaf-pullback adjunction keeps this proof
independent of any inferred continuity instance.
-/
instance restrict_isRightAdjoint_addCommGrpCat :
    (restrict AddCommGrpCat.{u} hf).IsRightAdjoint := by
  letI := hf.functor_isContinuous
  exact
    (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      hf.functor AddCommGrpCat
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).isRightAdjoint

variable (F : Sheaf C X) (U V : Opens X)

/-- The unit map from a sheaf to extension by zero after restriction. -/
abbrev toRestrict :=
  (restrictPushforwardAdjunction C U.isOpenEmbedding).unit

lemma toRestrict_obj_obj_obj :
    ((restrict C U.isOpenEmbedding ⋙
      pushforward C U.inclusion').obj F).obj.obj (op V) =
      F.obj.obj
        (op (U.isOpenEmbedding.functor.obj
          ((Opens.map U.inclusion').obj V))) :=
  rfl

lemma toRestrict_app_hom_app :
    ((toRestrict C U).app F).hom.app (op V) =
      F.obj.map
        (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op := by
  dsimp only [toRestrict, restrictPushforwardAdjunction, restrict,
    Adjunction.sheafPushforwardContinuous]
  rw [Adjunction.whiskerLeft_unit_app_app, Adjunction.op_unit]
  congr 1

end TopCat.Sheaf
