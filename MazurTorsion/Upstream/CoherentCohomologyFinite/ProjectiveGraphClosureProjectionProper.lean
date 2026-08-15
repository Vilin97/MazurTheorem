/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveGraphClosure
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Properness of the absolute graph-closure projection

Let `S` be proper over `Spec k`.  The projection from a closed subscheme
of `S ×_{Spec k} ℙ^d_k` to `ℙ^d_k` is proper: the product projection is a
base change of `S ⟶ Spec k`, and the inclusion of the closed subscheme is
proper.

Applied to a projective graph closure, this shows that its second
projection is a closed immersion exactly when it is a monomorphism.
Thus the remaining graph-assembly obligation in Chow's lemma is purely
the separation-of-points condition expressed by `Mono`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- If the base scheme is proper over `Spec k`, then the projection from
relative projective space to absolute projective space is proper. -/
theorem isProper_relativeToProjective
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (d : ℕ) :
    IsProper (relativeToProjective s d) :=
  inferInstance

/-- If `S` is proper over `Spec k`, the second projection of every
projective graph closure over `S` is proper. -/
instance isProper_projectiveGraphClosureToProjective
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (d : ℕ) (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsProper (projectiveGraphClosureToProjective s d u p h) := by
  rw [projectiveGraphClosureToProjective]
  infer_instance

/-- For a proper base scheme, the graph-closure projection to absolute
projective space is a closed immersion iff it is a monomorphism. -/
theorem isClosedImmersion_projectiveGraphClosureToProjective_iff_mono
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (d : ℕ) (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsClosedImmersion
        (projectiveGraphClosureToProjective s d u p h) ↔
      Mono (projectiveGraphClosureToProjective s d u p h) := by
  rw [IsClosedImmersion.iff_isProper_and_mono]
  simp only [isProper_projectiveGraphClosureToProjective, true_and]

/-- A monomorphic second projection of a projective graph closure over a
proper base is automatically a closed immersion. -/
theorem isClosedImmersion_projectiveGraphClosureToProjective_of_mono
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (d : ℕ) (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d)
    [Mono (projectiveGraphClosureToProjective s d u p h)] :
    IsClosedImmersion
      (projectiveGraphClosureToProjective s d u p h) :=
  (isClosedImmersion_projectiveGraphClosureToProjective_iff_mono
    s d u p h).2 inferInstance

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
