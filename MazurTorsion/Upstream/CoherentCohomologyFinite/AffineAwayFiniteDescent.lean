/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineAwaySections
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite generation from a distinguished-open cover

This file packages the final commutative-algebra descent step: if the
restrictions of a module sheaf to finitely many affine away localizations
have finite global sections and the corresponding elements generate the
unit ideal, then the original global sections are finite.
-/

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- Finiteness of top sections descends from finitely many away
localizations whose defining elements generate the unit ideal. -/
theorem finite_top_sections_of_finite_away_restrictions
    (F : (Spec R).Modules) [IsIso F.fromTildeΓ]
    (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    (hfinite : ∀ r : t,
      Module.Finite
        (CommRingCat.of (Localization.Away r.1))
        Γ(F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away r.1)))),
          ⊤)) :
    Module.Finite R Γ(F, ⊤) := by
  letI (r : t) :
      Module R
        Γ(F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away r.1)))),
          ⊤) :=
    restrictAwaySectionsModule F r.1
  letI (r : t) :
      IsScalarTower R
        (CommRingCat.of (Localization.Away r.1))
        Γ(F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away r.1)))),
          ⊤) :=
    IsScalarTower.of_compHom R
      (CommRingCat.of (Localization.Away r.1))
      Γ(F.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away r.1)))),
        ⊤)
  let f (r : t) :
      Γ(F, ⊤) →ₗ[R]
        Γ(F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away r.1)))),
          ⊤) :=
    restrictAwaySectionsLinearMap F r.1
  haveI (r : t) :
      IsLocalizedModule (Submonoid.powers r.1) (f r) := by
    dsimp only [f]
    exact restrictAwaySections_isLocalizedModule F r.1
  exact Module.Finite.of_localizationSpan_finite'
    t ht f hfinite

end AlgebraicGeometry.Scheme.Modules
