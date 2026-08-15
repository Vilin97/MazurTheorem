/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineAwayFiniteDescent
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineAwayFiniteGenerators
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteGeneratorCover

/-!
# Finite sections of finite-type quasicoherent affine modules

A finite-type module sheaf supplies finitely many generators locally.  On an
affine spectrum, quasi-compactness refines this to a finite distinguished-open
cover.  Affine quasicoherent reconstruction turns the restricted generators
into finite localized modules, and finite generation descends across the
distinguished cover.
-/

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- A finite-type quasicoherent module sheaf on an affine spectrum has a
finite module of global sections. -/
theorem finite_top_sections_of_isFiniteType_isQuasicoherent
    (F : (Spec R).Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    Module.Finite R Γ(F, ⊤) := by
  classical
  obtain ⟨n, g, U, G, hGfinite, hg, hspan⟩ :=
    exists_finiteBasicOpen_generatorCover F
  let t : Finset R := Finset.univ.image g
  have htSet : (t : Set R) = Set.range g := by
    ext r
    simp [t]
  have ht : Ideal.span (t : Set R) = ⊤ := by
    rw [htSet]
    exact hspan
  have htMem (r : t) : ∃ j : Fin n, g j = r.1 := by
    have hr : r.1 ∈ Finset.univ.image g := r.2
    rw [Finset.mem_image] at hr
    obtain ⟨j, -, hj⟩ := hr
    exact ⟨j, hj⟩
  let jOf (r : t) : Fin n := (htMem r).choose
  have hjOf (r : t) : g (jOf r) = r.1 :=
    (htMem r).choose_spec
  have hrle (r : t) :
      PrimeSpectrum.basicOpen r.1 ≤ U (jOf r) := by
    rw [← hjOf r]
    exact hg (jOf r)
  have hfinite (r : t) :
      Module.Finite
        (CommRingCat.of (Localization.Away r.1))
        Γ(F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away r.1)))),
          ⊤) :=
    finite_away_sections_of_generators_on_neighborhood
      F (U (jOf r)) (G (jOf r)) r.1
      (hrle r) (hGfinite (jOf r))
  exact finite_top_sections_of_finite_away_restrictions
    F t ht hfinite

end AlgebraicGeometry.Scheme.Modules
