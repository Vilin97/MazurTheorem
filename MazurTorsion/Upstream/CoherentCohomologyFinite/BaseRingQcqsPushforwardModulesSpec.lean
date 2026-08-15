/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingQcqsPushforward

/-!
# Localizing scheme-module direct images over an affine base

This file transports the fixed-base localizing theorem from the topological
direct image to Mathlib's `modulesSpecToSheaf` wrapper.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The scheme-module direct image along the structural morphism has a
localizing underlying fixed-base sheaf. -/
theorem isLocalizing_modulesSpec_pushforward_structural
    (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsLocalizing
      (modulesSpecToSheaf.obj
        ((Scheme.Modules.pushforward
          (X ↘ Spec (CommRingCat.of k))).obj M)) := by
  let p := X ↘ Spec (CommRingCat.of k)
  let N :=
    (Scheme.Modules.pushforward p).obj M
  have hp :
      p ≫
          (Spec (CommRingCat.of k) ↘
            Spec (CommRingCat.of k)) =
        X ↘ Spec (CommRingCat.of k) := by
    simp [p]
  let e :
      modulesSpecToSheaf.obj N ≅
        (TopCat.Sheaf.pushforward
          (ModuleCat.{u} k) p.base).obj
          (moduleSheaf (k := k) M :
            (X.toPresheafedSpace : TopCat).Sheaf
              (ModuleCat.{u} k)) :=
    (moduleSheafSpecIso (k := k) N).symm ≪≫
      moduleSheafPushforwardIso
        (k := k) p hp M
  exact
    (isLocalizing_iff_of_iso e).mpr
      (isLocalizing_pushforward_structural
        (k := k) M)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
