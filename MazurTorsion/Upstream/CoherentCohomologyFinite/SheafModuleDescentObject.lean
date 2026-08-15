/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib

/-!
# The equalizer object attached to module descent data

Mathlib has scheme gluing and pullback/pushforward functors for sheaves of
modules, but no packaged effective-descent construction for module sheaves.
This file contains only the small, construction-level part needed below:
the pullback transport used to state a cocycle and the equalizer of the two
overlap restriction maps.

The much stronger assertion that this equalizer restricts to the prescribed
module on every chart is deliberately kept separate from the construction.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

open _root_.AlgebraicGeometry

/-- Pull a transition isomorphism back to a further base and reassociate the
two iterated pullbacks. -/
noncomputable def pullbackTransport {W V : Scheme.{u}} (p : W ⟶ V)
    {Y₁ Y₂ : Scheme.{u}} (a : V ⟶ Y₁) (b : V ⟶ Y₂)
    {M₁ : Y₁.Modules} {M₂ : Y₂.Modules}
    (e : (Scheme.Modules.pullback a).obj M₁ ≅
      (Scheme.Modules.pullback b).obj M₂) :
    (Scheme.Modules.pullback (p ≫ a)).obj M₁ ≅
      (Scheme.Modules.pullback (p ≫ b)).obj M₂ :=
  (Scheme.Modules.pullbackComp p a).symm.app M₁ ≪≫
    (Scheme.Modules.pullback p).mapIso e ≪≫
    (Scheme.Modules.pullbackComp p b).app M₂

/-- On a triple overlap, the two maps to the source chart agree. -/
lemma bridgeSource (D : Scheme.GlueData.{u}) (i j k : D.J) :
    pullback.fst (D.f i j) (D.f i k) ≫ D.f i j =
      pullback.snd (D.f i j) (D.f i k) ≫ D.f i k :=
  pullback.condition

/-- On a triple overlap, the target of the first transition is the source of
the second transition. -/
lemma bridgeMiddle (D : Scheme.GlueData.{u}) (i j k : D.J) :
    pullback.fst (D.f i j) (D.f i k) ≫ (D.t i j ≫ D.f j i) =
      (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫ D.f j k := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc,
    D.t_fac i j k, Category.assoc]

/-- On a triple overlap, the target of the composite transition is the target
of the direct transition. -/
lemma bridgeTarget (D : Scheme.GlueData.{u}) (i j k : D.J) :
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫
        (D.t j k ≫ D.f k j) =
      pullback.snd (D.f i j) (D.f i k) ≫ (D.t i k ≫ D.f k i) := by
  have h :
      pullback.fst (D.f k i) (D.f k j) ≫ D.f k i =
        D.t' k i j ≫ pullback.snd (D.f i j) (D.f i k) ≫
          D.t i k ≫ D.f k i := by
    rw [D.t_fac_assoc k i j, ← Category.assoc (D.t k i) (D.t i k),
      D.t_inv, Category.id_comp]
  rw [Category.assoc, ← D.t_fac_assoc j k i,
    ← @pullback.condition _ _ _ _ _ (D.f k i) (D.f k j) _, h,
    D.cocycle_assoc i j k]

/-- The equalizer-of-pushforwards object associated to module descent data.

The identity and cocycle fields are part of the interface because they are
needed to prove effective descent, although construction of the equalizer
itself only uses the transition maps. -/
noncomputable def glueObject (D : Scheme.GlueData)
    (M : ∀ i, (D.U i).Modules)
    (e : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
      (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    (_identity : ∀ i, e i i =
      eqToIso (congrArg
        (fun φ => (Scheme.Modules.pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by
          rw [D.t_id i, Category.id_comp])))
    (_cocycle : ∀ i j k,
      pullbackTransport (pullback.fst (D.f i j) (D.f i k))
          (D.f i j) (D.t i j ≫ D.f j i) (e i j) ≪≫
        (Scheme.Modules.pullbackCongr
          (bridgeMiddle D i j k)).app (M j) ≪≫
        pullbackTransport
          (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
          (D.f j k) (D.t j k ≫ D.f k j) (e j k) ≪≫
        (Scheme.Modules.pullbackCongr
          (bridgeTarget D i j k)).app (M k) =
      (Scheme.Modules.pullbackCongr
        (bridgeSource D i j k)).app (M i) ≪≫
        pullbackTransport (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i) (e i k)) :
    D.glued.Modules :=
  let overlap : D.J × D.J → D.glued.Modules := fun p =>
    (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
      ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))
  let charts : D.glued.Modules :=
    ∏ᶜ fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)
  let firstComponent : ∀ p : D.J × D.J,
      (Scheme.Modules.pushforward (D.ι p.1)).obj (M p.1) ⟶
        overlap p := fun p =>
    (Scheme.Modules.pushforward (D.ι p.1)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (D.f p.1 p.2)).unit.app (M p.1)) ≫
      (Scheme.Modules.pushforwardComp
        (D.f p.1 p.2) (D.ι p.1)).hom.app
          ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))
  let secondComponent : ∀ p : D.J × D.J,
      (Scheme.Modules.pushforward (D.ι p.2)).obj (M p.2) ⟶
        overlap p := fun p =>
    (Scheme.Modules.pushforward (D.ι p.2)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
      (Scheme.Modules.pushforwardComp
        (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
          ((Scheme.Modules.pullback
            (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
      (Scheme.Modules.pushforward
        ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map
          (e p.1 p.2).inv ≫
      (Scheme.Modules.pushforwardCongr
        (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 =
            D.f p.1 p.2 ≫ D.ι p.1 by
          rw [Category.assoc]
          exact D.glue_condition p.1 p.2)).hom.app
            ((Scheme.Modules.pullback
              (D.f p.1 p.2)).obj (M p.1))
  let first : charts ⟶ ∏ᶜ overlap :=
    Pi.lift fun p => Pi.π _ p.1 ≫ firstComponent p
  let second : charts ⟶ ∏ᶜ overlap :=
    Pi.lift fun p => Pi.π _ p.2 ≫ secondComponent p
  equalizer first second

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
