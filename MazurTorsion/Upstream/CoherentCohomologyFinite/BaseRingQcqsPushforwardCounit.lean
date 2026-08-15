/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingQcqsPushforwardModulesSpec

/-!
# The affine tilde counit of a qcqs direct image
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The tilde counit of a qcqs pushforward to the affine base is an
isomorphism. -/
theorem isIso_fromTildeΓ_pushforward_structural
    (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsIso
      (Scheme.Modules.fromTildeΓ (R := CommRingCat.of k)
        ((Scheme.Modules.pushforward
          (X ↘ Spec (CommRingCat.of k))).obj M)) :=
  (isIso_fromTildeΓ_iff_isLocalizing (R := CommRingCat.of k)
    ((Scheme.Modules.pushforward
      (X ↘ Spec (CommRingCat.of k))).obj M)).mpr
    (isLocalizing_modulesSpec_pushforward_structural
      (k := k) M)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
