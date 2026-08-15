/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffinePresentationData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit

/-!
# Quasicoherent pushforward along an affine morphism

For an affine morphism, restricting a pushforward to an affine open is
pushforward between two affine schemes.  Affine pushforward preserves
quasicoherence, so affine-local presentations assemble to a global
quasicoherent structure.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/--
Pushforward along an affine morphism preserves quasicoherent modules.

This is the affine-morphism case of Stacks Project, Tag 01XJ.  It is
proved using only affine reconstruction and the restriction/pushforward
comparison, rather than the heavier general qcqs pushforward theorem.
-/
theorem isQuasicoherent_pushforward_affineHom
    (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let P :
      ∀ U : Y.affineOpens,
        (((pushforward f).obj M).restrict
          (U : Y.Opens).ι).Presentation :=
    fun U => by
      letI : IsAffine (↑(U : Y.Opens) : Scheme.{u}) := U.2
      letI : IsAffine
          (↑(f ⁻¹ᵁ (U : Y.Opens)) : Scheme.{u}) :=
        U.2.preimage f
      let N :
          (↑(U : Y.Opens) : Scheme.{u}).Modules :=
        (pushforward (f ∣_ (U : Y.Opens))).obj
          (M.restrict
            (f ⁻¹ᵁ (U : Y.Opens)).ι)
      haveI : N.IsQuasicoherent :=
        isQuasicoherent_pushforward_affine
          (f ∣_ (U : Y.Opens))
          (M.restrict
            (f ⁻¹ᵁ (U : Y.Opens)).ι)
      let e :
          ((pushforward f).obj M).restrict
              (U : Y.Opens).ι ≅ N :=
        (pushforwardRestrictIso f (U : Y.Opens)).app M
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
