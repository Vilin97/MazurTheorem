/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Limits of pushforwards of presheaves of modules

Pushforward of presheaves of modules is sectionwise precomposition
followed by restriction of scalars.  Both operations preserve limits.
This file packages the finite-limit consequence that is not exposed as
an instance at the pinned Mathlib revision.
-/


universe u

open CategoryTheory Limits

namespace PresheafOfModules

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R)

private abbrev ringMap :
    S ⋙ forget₂ CommRingCat RingCat ⟶
      F.op ⋙ R ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

/-- Pushforward of presheaves of modules preserves finite limits. -/
noncomputable instance pushforward_preservesFiniteLimits :
    PreservesFiniteLimits (pushforward (ringMap φ)) where
  preservesFiniteLimits J _ _ :=
    { preservesLimit := fun {K} =>
        { preserves := fun {c} hc =>
            ⟨by
              apply evaluationJointlyReflectsLimits
                (K ⋙ pushforward (ringMap φ))
                ((pushforward (ringMap φ)).mapCone c)
              intro X
              apply isLimitOfReflects
                (forget₂
                  (ModuleCat
                    ((S ⋙ forget₂ CommRingCat RingCat).obj X))
                  AddCommGrpCat)
              exact
                isLimitOfPreserves
                  (evaluation
                      (R ⋙ forget₂ CommRingCat RingCat)
                      (F.op.obj X) ⋙
                    forget₂ _ AddCommGrpCat)
                  hc⟩ } }

end PresheafOfModules
