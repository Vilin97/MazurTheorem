/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineAwayQuasicoherent

/-!
# Finite sections on affine away restrictions

Finite generating sections on a neighbourhood of `D(g)` transport to
`Spec R_g`.  Quasicoherent affine reconstruction then shows that the top
sections of the restricted sheaf form a finite `R_g`-module.
-/

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- A finite generating family near `D(g)` makes the top sections after
restriction to `Spec R_g` finite over `R_g`. -/
theorem finite_away_sections_of_generators_on_neighborhood
    (F : (Spec R).Modules) [F.IsQuasicoherent]
    (U : (Spec R).Opens) (G : (F.over U).GeneratingSections)
    (g : R) (hg : PrimeSpectrum.basicOpen g ≤ U)
    (hG : Finite G.I) :
    Module.Finite
      (CommRingCat.of (Localization.Away g))
      Γ(F.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away g)))),
        ⊤) := by
  letI :
      SheafOfModules.GeneratingSections.IsFiniteType.{u, u, u} G :=
    SheafOfModules.GeneratingSections.IsFiniteType.mk
      (σ := G) hG
  let Faway :
      (Spec (CommRingCat.of (Localization.Away g))).Modules :=
    F.restrict
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (Localization.Away g))))
  let Gaway : Faway.GeneratingSections :=
    generatingSectionsDirectAwayOfOver F U G g hg
  letI : Gaway.IsFiniteType := {
    finite := by
      dsimp only [Gaway]
      exact hG }
  exact finite_top_sections_of_finite_generatingSections Faway Gaway

end AlgebraicGeometry.Scheme.Modules
