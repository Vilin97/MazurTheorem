/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.QcqsPushforwardAffineTarget
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffinePresentationData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardRestriction

/-!
# Quasicoherent pushforward along a qcqs morphism

Restriction of a direct image to an affine open is the direct image
along the restricted morphism.  The affine-target theorem supplies a
quasicoherent presentation on each such restriction, and the standard
affine cover glues these presentations.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Pushforward along a quasi-compact, quasi-separated morphism
preserves quasicoherent modules. -/
theorem isQuasicoherent_pushforward_qcqs
    (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (M : X.Modules)
    [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let P :
      ∀ U : Y.affineOpens,
        (((pushforward f).obj M).restrict
          (U : Y.Opens).ι).Presentation :=
    fun U => by
      letI :
          IsAffine
            (↑(U : Y.Opens) : Scheme.{u}) :=
        U.2
      let N :
          (↑(U : Y.Opens) : Scheme.{u}).Modules :=
        (pushforward
          (f ∣_ (U : Y.Opens))).obj
          (M.restrict
            (f ⁻¹ᵁ (U : Y.Opens)).ι)
      haveI : N.IsQuasicoherent :=
        isQuasicoherent_pushforward_affineTarget
          (f ∣_ (U : Y.Opens))
          (M.restrict
            (f ⁻¹ᵁ (U : Y.Opens)).ι)
      let e :
          ((pushforward f).obj M).restrict
              (U : Y.Opens).ι ≅ N :=
        (pushforwardRestrictIso
          f (U : Y.Opens)).app M
      haveI :
          (((pushforward f).obj M).restrict
            (U : Y.Opens).ι).IsQuasicoherent :=
        isQuasicoherent_of_iso e.symm
      exact
        quasicoherentPresentation
          (((pushforward f).obj M).restrict
            (U : Y.Opens).ι)
  exact
    (quasicoherentDataOfAffineOpenPresentations
      ((pushforward f).obj M) P).isQuasicoherent

end AlgebraicGeometry.Scheme.Modules
