/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineAwaySections
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction

/-!
# Quasicoherence after an affine away restriction

These specialized instances expose the general open-restriction theorem at
the concrete morphism `Spec R_g ⟶ Spec R`.  Keeping that specialization in
its own declaration avoids repeatedly unfolding the full site-theoretic
construction in later affine finiteness arguments.
-/

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- Restriction of a quasicoherent module sheaf from `Spec R` to
`Spec R_g` remains quasicoherent. -/
instance restrictAway_isQuasicoherent
    (F : (Spec R).Modules) [F.IsQuasicoherent] (g : R) :
    (F.restrict
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (Localization.Away g))))).IsQuasicoherent :=
  isQuasicoherent_restrictFunctor _ F

/-- The affine tilde counit is an isomorphism after restricting a
quasicoherent module sheaf to `Spec R_g`. -/
instance restrictAway_fromTildeΓ_isIso
    (F : (Spec R).Modules) [F.IsQuasicoherent] (g : R) :
    IsIso
      (Scheme.Modules.fromTildeΓ
        (R := CommRingCat.of (Localization.Away g))
        (F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away g)))))) :=
  isIso_fromTildeΓ_of_isQuasicoherent _

end AlgebraicGeometry.Scheme.Modules
