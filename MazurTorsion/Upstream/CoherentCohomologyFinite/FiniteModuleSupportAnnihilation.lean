/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Support

/-!
# Annihilating a finite module by a power of a support ideal

If the support of a finite module is contained in the zero locus of a
finitely generated ideal `I`, then a power of `I` annihilates the module.
Over a Noetherian ring the finite-generation hypothesis on `I` is automatic.

This is the affine algebra input for realizing a coherent module supported
on a closed subset as a module on a finite infinitesimal thickening of that
subset.
-/

open PrimeSpectrum

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

/--
If the support of a finite module is contained in `V(I)` and `I` is finitely
generated, then some power of `I` is contained in the module annihilator.
-/
theorem exists_pow_le_annihilator_of_fg_of_support_subset_zeroLocus
    [Module.Finite R M] (I : Ideal R) (hI : I.FG)
    (hsupport : Module.support R M ⊆ zeroLocus I) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R M := by
  rw [Module.support_eq_zeroLocus] at hsupport
  have hradical : I ≤ (Module.annihilator R M).radical := by
    exact
      (zeroLocus_subset_zeroLocus_iff
        (Module.annihilator R M) I).mp hsupport
  exact Ideal.exists_pow_le_of_le_radical_of_fg hradical hI

/--
Noetherian form of
`Module.exists_pow_le_annihilator_of_fg_of_support_subset_zeroLocus`.
-/
theorem exists_pow_le_annihilator_of_support_subset_zeroLocus
    [Module.Finite R M] [IsNoetherianRing R] (I : Ideal R)
    (hsupport : Module.support R M ⊆ zeroLocus I) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R M :=
  exists_pow_le_annihilator_of_fg_of_support_subset_zeroLocus
    I (IsNoetherian.noetherian I) hsupport

/--
Under the same hypotheses, `M` is a module killed by every element of a
power of `I`. The resulting witness can be passed directly to
`Module.IsTorsionBySet.module` to equip `M` with an `R ⧸ I ^ n`-module
structure.
-/
theorem exists_pow_isTorsionBySet_of_support_subset_zeroLocus
    [Module.Finite R M] [IsNoetherianRing R] (I : Ideal R)
    (hsupport : Module.support R M ⊆ zeroLocus I) :
    ∃ n : ℕ, Module.IsTorsionBySet R M ((I ^ n : Ideal R) : Set R) := by
  obtain ⟨n, hn⟩ :=
    exists_pow_le_annihilator_of_support_subset_zeroLocus I hsupport
  exact
    ⟨n, (isTorsionBySet_iff_subset_annihilator (R := R) (M := M)).mpr hn⟩

end Module
