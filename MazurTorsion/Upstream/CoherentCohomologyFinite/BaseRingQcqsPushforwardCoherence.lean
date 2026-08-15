/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingQcqsPushforwardCounit

/-!
# Quasicoherence of a qcqs direct image over an affine base
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- Pushforward to an affine base preserves quasicoherence when the source is
quasi-compact and quasi-separated. -/
theorem isQuasicoherent_pushforward_structural
    (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ((Scheme.Modules.pushforward
      (X ↘ Spec (CommRingCat.of k))).obj M).IsQuasicoherent :=
  by
    let N :=
      (Scheme.Modules.pushforward
        (X ↘ Spec (CommRingCat.of k))).obj M
    let counit :=
      Scheme.Modules.fromTildeΓ (R := CommRingCat.of k) N
    have hCounit : IsIso counit :=
      isIso_fromTildeΓ_pushforward_structural (k := k) M
    exact @ObjectProperty.prop_of_isIso _ _
      (SheafOfModules.isQuasicoherent
        (Spec (CommRingCat.of k)).ringCatSheaf)
      inferInstance _ _ counit hCounit
      (inferInstance :
        (tilde ((modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤))).IsQuasicoherent)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
