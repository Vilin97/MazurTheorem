/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffinePresentationData

/-!
# Building finite-presentation data from affine opens

Mathlib defines a finitely presented module sheaf by presentations on a
site-theoretic cover.  This file packages the standard affine-open cover:
if every geometric restriction to an affine open has a finite global
presentation, then the original module sheaf is finitely presented.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- Pointwise finite affine presentations give finite quasicoherent data. -/
instance quasicoherentDataOfAffineOpenPresentations_isFinitePresentation
    (P : ∀ U : X.affineOpens,
      (M.restrict (U : X.Opens).ι).Presentation)
    [hP : ∀ U, (P U).IsFinite] :
    (quasicoherentDataOfAffineOpenPresentations M P).IsFinitePresentation where
  isFinite_presentation U := by
    change X.affineOpens at U
    dsimp [quasicoherentDataOfAffineOpenPresentations]
    exact Presentation.overOfRestrict_isFinite
      (U := (U : X.Opens)) M (P U)

/--
If every affine-open restriction has a finite global presentation, then
the module sheaf is finitely presented.
-/
theorem isFinitePresentation_of_affineOpenPresentations
    (P : ∀ U : X.affineOpens,
      (M.restrict (U : X.Opens).ι).Presentation)
    [∀ U, (P U).IsFinite] :
    M.IsFinitePresentation where
  exists_quasicoherentData :=
    ⟨quasicoherentDataOfAffineOpenPresentations M P,
      inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
