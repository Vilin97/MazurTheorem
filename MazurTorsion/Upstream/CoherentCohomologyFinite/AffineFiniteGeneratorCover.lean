/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteGenerators
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentCover

/-!
# Finite distinguished-open generator covers

This packages the quasi-compactness reduction for a finite-type module sheaf
so downstream affine arguments do not need to unfold local-generator data.
-/

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- A finite-type module sheaf on `Spec R` has a finite distinguished-open
generator cover. -/
theorem exists_finiteBasicOpen_generatorCover
    (F : (Spec R).Modules) [hF : F.IsFiniteType] :
    ∃ (n : ℕ) (g : Fin n → R)
      (U : Fin n → (Spec R).Opens)
      (G : ∀ j, (F.over (U j)).GeneratingSections),
      (∀ j, Finite (G j).I) ∧
        (∀ j, PrimeSpectrum.basicOpen (g j) ≤ U j) ∧
          Ideal.span (Set.range g) = ⊤ := by
  obtain ⟨P, hP⟩ :=
    SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have htop : ⨆ i, P.X i = ⊤ :=
    iSup_eq_top_of_coversTop P.X P.coversTop
  obtain ⟨n, g, φ, hg, hspan⟩ :=
    exists_finite_basicOpen_refinement P.X htop
  exact ⟨n, g, fun j => P.X (φ j),
    fun j => P.generators (φ j),
    fun j =>
      (SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType
        (p := P) (φ j)).finite,
    hg, hspan⟩

end AlgebraicGeometry.Scheme.Modules
