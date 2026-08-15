/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Transporting finite generation through semilinear equivalences

Finite generation descends along an additive equivalence whose scalar
map is surjective.  This elementary lemma is useful when comparing
section modules on canonically isomorphic affine schemes, where the
coefficient rings are naturally isomorphic but not definitionally equal.
-/


universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/--
An additive equivalence which is semilinear for a surjective scalar map
transports finite generation from its codomain to its domain.
-/
theorem Module.Finite.of_surjectiveSemilinearAddEquiv
    {R S M N : Type u}
    [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module S N]
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (e : M ≃+ N)
    (he : ∀ (r : R) (x : M),
      e (r • x) = σ r • e x)
    (hN : Module.Finite S N) :
    Module.Finite R M := by
  obtain ⟨n, w, hw⟩ :=
    hN.exists_fin (R := S) (M := N)
  refine
    Module.finite_def.mpr
      (Submodule.fg_def.mpr
        ⟨⇑e.symm '' Set.range w,
          (Set.finite_range w).image _, ?_⟩)
  rw [eq_top_iff]
  intro x _
  have hx :
      e x ∈ Submodule.span S (Set.range w) := by
    rw [hw]
    exact Submodule.mem_top
  have key :
      ∀ y : N,
        y ∈ Submodule.span S (Set.range w) →
          e.symm y ∈
            Submodule.span R
              (⇑e.symm '' Set.range w) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        exact
          Submodule.subset_span
            ⟨z, hz, rfl⟩
    | zero =>
        rw [map_zero]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    | smul s y _ ih =>
        obtain ⟨r, rfl⟩ := hσ s
        have hsmul :
            e.symm (σ r • y) =
              r • e.symm y := by
          apply e.injective
          rw [he, e.apply_symm_apply,
            e.apply_symm_apply]
        rw [hsmul]
        exact Submodule.smul_mem _ _ ih
  simpa using key (e x) hx

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
