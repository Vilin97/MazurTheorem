/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `FiniteModuleSupportAnnihilation.lean`
in Vilin97/Clawristotle.
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Support

/-!
# Annihilating a finite module by a power of a support ideal

If the support of a finite module is contained in the zero locus of a
finitely generated ideal, then one power of that ideal annihilates the
module.
-/

open PrimeSpectrum

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

/-- A finitely generated ideal cutting out the support has a power in the annihilator. -/
theorem exists_pow_le_annihilator_of_fg_of_support_subset_zeroLocus
    [Module.Finite R M] (I : Ideal R) (hI : I.FG)
    (hsupport : Module.support R M ⊆ zeroLocus I) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R M := by
  rw [Module.support_eq_zeroLocus] at hsupport
  have hradical : I ≤ (Module.annihilator R M).radical :=
    (zeroLocus_subset_zeroLocus_iff (Module.annihilator R M) I).mp hsupport
  exact Ideal.exists_pow_le_of_le_radical_of_fg hradical hI

/-- Noetherian form of support-ideal annihilation. -/
theorem exists_pow_le_annihilator_of_support_subset_zeroLocus
    [Module.Finite R M] [IsNoetherianRing R] (I : Ideal R)
    (hsupport : Module.support R M ⊆ zeroLocus I) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R M :=
  exists_pow_le_annihilator_of_fg_of_support_subset_zeroLocus
    I (IsNoetherian.noetherian I) hsupport

/-- Return support-ideal annihilation in the quotient-module interface. -/
theorem exists_pow_isTorsionBySet_of_support_subset_zeroLocus
    [Module.Finite R M] [IsNoetherianRing R] (I : Ideal R)
    (hsupport : Module.support R M ⊆ zeroLocus I) :
    ∃ n : ℕ, Module.IsTorsionBySet R M ((I ^ n : Ideal R) : Set R) := by
  obtain ⟨n, hn⟩ :=
    exists_pow_le_annihilator_of_support_subset_zeroLocus I hsupport
  exact
    ⟨n, (isTorsionBySet_iff_subset_annihilator (R := R) (M := M)).mpr hn⟩

end Module
