/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineBasicOpenDirectRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineExtensionRestriction

/-!
# Extension data from a presentation near a basic open

This file packages the categorical presentation transport and the
elementwise away-localization transport into one local lemma.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.QuasicoherentTilde

variable {R : CommRingCat.{u}}

/-- A presentation on a neighborhood of `D(g)` supplies extension data on
`D(g)`. -/
theorem basicOpenExtensionData_of_overPresentation
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (M.over U).Presentation) (g : R)
    (hg : PrimeSpectrum.basicOpen g ≤ U) :
    BasicOpenExtensionData M
      (PrimeSpectrum.basicOpen g) := by
  let Maway :=
    M.restrict
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (Localization.Away g))))
  let Paway : Maway.Presentation :=
    presentationDirectAwayOfOver M U P g hg
  have hiso :=
    AlgebraicGeometry.isIso_fromTildeΓ_of_presentation
      (R := CommRingCat.of (Localization.Away g))
      Maway Paway
  have hlocal :
      IsLocalizing (modulesSpecToSheaf.obj Maway) :=
    (isIso_fromTildeΓ_iff_isLocalizing
      (R := CommRingCat.of (Localization.Away g))
      Maway).mp hiso
  have hext : BasicOpenExtensionData Maway ⊤ :=
    (isLocalizing_iff_extensionData Maway).mp hlocal
  exact basicOpenExtensionData_of_restrictAway M g hext

end AlgebraicGeometry.QuasicoherentTilde
