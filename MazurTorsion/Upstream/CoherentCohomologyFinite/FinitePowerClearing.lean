/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib

/-!
# Clearing powers over a finite family

The local-to-global arguments for Serre twists repeatedly produce one
denominator exponent for each member of a finite affine cover.  This file
packages the elementary uniformisation step.  It is deliberately stated for
linear maps, independently of schemes.
-/

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

variable {R : Type*} [CommSemiring R]
  {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- If every member of a finite family enters the image of a linear map
after multiplication by some power of `f`, then one common power works for
the entire family. -/
theorem exists_uniform_pow_smul_mem_range
    {ι : Type*} [Finite ι] (φ : M →ₗ[R] N) (f : R) (x : ι → N)
    (h : ∀ i, ∃ n : ℕ, f ^ n • x i ∈ LinearMap.range φ) :
    ∃ N : ℕ, ∀ i, f ^ N • x i ∈ LinearMap.range φ := by
  choose n hn using h
  let N : ℕ := ⨆ i, n i
  refine ⟨N, fun i => ?_⟩
  obtain ⟨y, hy⟩ := hn i
  refine ⟨f ^ (N - n i) • y, ?_⟩
  rw [map_smul, hy, smul_smul, ← pow_add]
  congr 2
  exact Nat.sub_add_cancel
    (le_ciSup (Finite.bddAbove_range n) i)

/-- Elementwise form of `exists_uniform_pow_smul_mem_range`, retaining a
simultaneous family of chosen preimages. -/
theorem exists_uniform_pow_smul_preimage
    {ι : Type*} [Finite ι] (φ : M →ₗ[R] N) (f : R) (x : ι → N)
    (h : ∀ i, ∃ (n : ℕ) (y : M), φ y = f ^ n • x i) :
    ∃ (N : ℕ) (y : ι → M), ∀ i, φ (y i) = f ^ N • x i := by
  have hRange : ∀ i, ∃ n : ℕ,
      f ^ n • x i ∈ LinearMap.range φ := by
    intro i
    obtain ⟨n, y, hy⟩ := h i
    exact ⟨n, y, hy⟩
  obtain ⟨N, hN⟩ :=
    exists_uniform_pow_smul_mem_range φ f x hRange
  choose y hy using hN
  exact ⟨N, y, hy⟩

/-- If every member of a finite family is killed by some power of `f`, then
one common power kills the whole family. -/
theorem exists_uniform_pow_smul_eq_zero
    {ι : Type*} [Finite ι] (f : R) (x : ι → M)
    (h : ∀ i, ∃ n : ℕ, f ^ n • x i = 0) :
    ∃ N : ℕ, ∀ i, f ^ N • x i = 0 := by
  choose n hn using h
  let N : ℕ := ⨆ i, n i
  refine ⟨N, fun i => ?_⟩
  rw [show N = (N - n i) + n i by
    exact (Nat.sub_add_cancel
      (le_ciSup (Finite.bddAbove_range n) i)).symm,
    pow_add, mul_smul, hn, smul_zero]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
