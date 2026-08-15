/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType

/-!
# Closed embeddings of finite-type affine schemes

A finite-type affine algebra is a quotient of a polynomial ring in
finitely many variables.  Contravariance of `Spec` turns such a
presentation into a closed immersion into finite-dimensional affine
space.  This is the first relative geometric ingredient in a genuine
Chow compactification.
-/

open AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

/-- A finite-type algebra admits a finite polynomial presentation whose
map on spectra is a closed immersion. -/
theorem exists_closedImmersion_spec_mvPolynomial
    (k A : Type u) [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) k →ₐ[k] A),
      Function.Surjective φ ∧
        IsClosedImmersion
          (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  obtain ⟨n, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType k A)
  exact
    ⟨n, φ, hφ,
      IsClosedImmersion.spec_of_surjective
        (CommRingCat.ofHom φ.toRingHom) hφ⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
