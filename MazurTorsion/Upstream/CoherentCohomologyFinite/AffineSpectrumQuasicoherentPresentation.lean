/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentTilde
import MazurTorsion.Upstream.CoherentCohomologyFinite.TildeUniversalPresentation

/-!
# Presentations of quasicoherent modules on a spectrum

The affine tilde-counit transports the universal presentation of the
module of global sections to the original quasicoherent module sheaf.
-/


universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- A global presentation of a quasicoherent module on a spectrum. -/
noncomputable def quasicoherentPresentationSpec
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    M.Presentation := by
  letI : IsIso M.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent M
  let P :
      (tilde (moduleSpecΓFunctor.obj M)).Presentation :=
    universalTildePresentation
      (moduleSpecΓFunctor.obj M)
  exact
    @SheafOfModules.Presentation.ofIsIso.{u}
      _ _ _ _ _ _ _ _ M.fromTildeΓ
      (isIso_fromTildeΓ_of_isQuasicoherent M) P

end AlgebraicGeometry.Scheme.Modules
