/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentTilde
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent

/-!
# The affine tilde-counit input

This file connects the elementwise affine-patching theorem to the
categorical quasicoherence API used by affine vanishing.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Affine patching supplies an invertible tilde counit for every
quasicoherent module sheaf on a spectrum. -/
instance hasQuasicoherentTildeCounit (R : CommRingCat.{u}) :
    HasQuasicoherentTildeCounit R where
  isIso M :=
    isIso_fromTildeΓ_of_isQuasicoherent M

end AlgebraicGeometry.Scheme.Modules
