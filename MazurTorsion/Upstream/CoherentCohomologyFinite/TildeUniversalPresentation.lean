/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# A universal presentation of an affine tilde module

Taking all elements as generators and all elements of the relation
module as relations gives a canonical, possibly infinite presentation
of every associated module sheaf.
-/


universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The universal free presentation of `M̃`. -/
noncomputable def universalTildePresentation
    (M : ModuleCat R) : (tilde M).Presentation :=
  presentationTilde.{u} M .univ (by simp)
    _ (Submodule.span_eq _)

end AlgebraicGeometry
