/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteModuleSupportAnnihilation

/-!
# Uniform support annihilation over a finite family

Local support arguments produce one annihilating ideal power for each
member of a finite affine family.  Taking the maximum exponent gives one
power that works simultaneously, even when the rings, modules, and ideals
vary with the index.
-/

noncomputable section

namespace Module

variable {ι : Type*} [Finite ι]
variable (R : ι → Type*) [∀ i, CommRing (R i)]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)]
variable [∀ i, Module (R i) (M i)]
variable (I : ∀ i, Ideal (R i))

/--
A finite family of independently annihilating ideal powers admits one
common exponent.
-/
theorem exists_uniform_pow_le_annihilator
    (h : ∀ i, ∃ n : ℕ,
      I i ^ n ≤ Module.annihilator (R i) (M i)) :
    ∃ N : ℕ, ∀ i,
      I i ^ N ≤ Module.annihilator (R i) (M i) := by
  choose n hn using h
  let N : ℕ := ⨆ i, n i
  refine ⟨N, fun i => ?_⟩
  exact
    (Ideal.pow_le_pow_right
      (le_ciSup (Finite.bddAbove_range n) i)).trans (hn i)

/--
For finite modules over Noetherian rings, support containment on a finite
family admits one common annihilating exponent.
-/
theorem exists_uniform_pow_le_annihilator_of_support_subset_zeroLocus
    [∀ i, Module.Finite (R i) (M i)]
    [∀ i, IsNoetherianRing (R i)]
    (hsupport : ∀ i,
      Module.support (R i) (M i) ⊆
        PrimeSpectrum.zeroLocus (I i)) :
    ∃ N : ℕ, ∀ i,
      I i ^ N ≤ Module.annihilator (R i) (M i) := by
  apply exists_uniform_pow_le_annihilator R M I
  intro i
  exact
    Module.exists_pow_le_annihilator_of_support_subset_zeroLocus
      (I i) (hsupport i)

/--
The common exponent can equivalently be returned as quotient-module
annihilation witnesses on every member of the family.
-/
theorem exists_uniform_pow_isTorsionBySet_of_support_subset_zeroLocus
    [∀ i, Module.Finite (R i) (M i)]
    [∀ i, IsNoetherianRing (R i)]
    (hsupport : ∀ i,
      Module.support (R i) (M i) ⊆
        PrimeSpectrum.zeroLocus (I i)) :
    ∃ N : ℕ, ∀ i,
      Module.IsTorsionBySet (R i) (M i)
        ((I i ^ N : Ideal (R i)) : Set (R i)) := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_pow_le_annihilator_of_support_subset_zeroLocus
      R M I hsupport
  exact
    ⟨N, fun i =>
      (Module.isTorsionBySet_iff_subset_annihilator
        (R := R i) (M := M i)).mpr (hN i)⟩

/--
Positive-exponent form, convenient when the support of the ideal power
must agree with the support of the original ideal.
-/
theorem exists_uniform_succ_pow_isTorsionBySet_of_support_subset_zeroLocus
    [∀ i, Module.Finite (R i) (M i)]
    [∀ i, IsNoetherianRing (R i)]
    (hsupport : ∀ i,
      Module.support (R i) (M i) ⊆
        PrimeSpectrum.zeroLocus (I i)) :
    ∃ N : ℕ, ∀ i,
      Module.IsTorsionBySet (R i) (M i)
        ((I i ^ (N + 1) : Ideal (R i)) : Set (R i)) := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_pow_isTorsionBySet_of_support_subset_zeroLocus
      R M I hsupport
  refine ⟨N, fun i => ?_⟩
  apply
    (Module.isTorsionBySet_iff_subset_annihilator
      (R := R i) (M := M i)).mpr
  exact
    (Ideal.pow_le_pow_right (Nat.le_add_right N 1)).trans
      ((Module.isTorsionBySet_iff_subset_annihilator
        (R := R i) (M := M i)).mp (hN i))

end Module
