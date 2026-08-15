/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib

/-!
# The slice site of an open subspace

For an open `U` of a topological space `X`, the inverse of the standard
equivalence `Over U ≌ Opens U` is a dense subsite functor.  This is the
site-theoretic input for transporting sheaves of modules between geometric
restriction to `U` and restriction to the slice site over `U`.
-/

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Type u} [TopologicalSpace X]
  (U : TopologicalSpace.Opens X)

/-- Covering sieves correspond under the open-subspace equivalence. -/
private lemma overEquiv_image_cover_iff
    (W : TopologicalSpace.Opens ↥U) (S : Sieve W) :
    (S.functorPushforward
      ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙
        Over.forget U))
        ∈ (Opens.grothendieckTopology X)
          (((TopologicalSpace.Opens.overEquivalence U).inverse ⋙
            Over.forget U).obj W) ↔
      S ∈ (Opens.grothendieckTopology ↥U) W := by
  constructor
  · intro h y hy
    have hx : (y : X) ∈
        (((TopologicalSpace.Opens.overEquivalence U).inverse ⋙
          Over.forget U).obj W) :=
      ⟨y, hy, rfl⟩
    obtain ⟨V, f, hf, hxV⟩ := h y hx
    obtain ⟨W', a, b, hSa, _⟩ := hf
    refine ⟨W', a, hSa, ?_⟩
    have hyim : (y : X) ∈
        ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙
          Over.forget U).obj W' :=
      b.le hxV
    obtain ⟨z, hz, hzeq⟩ := hyim
    rw [← (Subtype.ext hzeq : z = y)]
    exact hz
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨W', a, hSa, hyW'⟩ := h y hy
    refine
      ⟨((TopologicalSpace.Opens.overEquivalence U).inverse ⋙
          Over.forget U).obj W',
        ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙
          Over.forget U).map a, ?_, ⟨y, hyW', rfl⟩⟩
    exact ⟨W', a, 𝟙 _, hSa, by simp⟩

/--
The inverse of `Opens.overEquivalence U` identifies the open-subspace site
with a dense subsite of the slice of the ambient opens site.
-/
instance overEquivInverseIsDenseSubsite :
      (TopologicalSpace.Opens.overEquivalence U).inverse.IsDenseSubsite
      (Opens.grothendieckTopology ↥U)
      ((Opens.grothendieckTopology X).over U) where
  functorPushforward_mem_iff {W S} := by
    rw [GrothendieckTopology.mem_over_iff]
    rw [show
      Sieve.overEquiv
          ((TopologicalSpace.Opens.overEquivalence U).inverse.obj W)
          (S.functorPushforward
            (TopologicalSpace.Opens.overEquivalence U).inverse) =
        S.functorPushforward
          ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙
            Over.forget U) by
      rw [Sieve.functorPushforward_comp]
      rfl]
    exact overEquiv_image_cover_iff U W S

end AlgebraicGeometry.Scheme.Modules
