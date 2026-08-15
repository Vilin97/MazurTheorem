/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rationalization and finite generation

Generic lemmas for transporting finite-dimensionality through exact
sequences after tensoring abelian groups with `ℚ`.
-/

open TensorProduct

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u

local instance : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

section ExactSequences

variable {A B C : Type u}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module ℤ A] [Module ℤ B] [Module ℤ C]

/--
Finite-dimensionality after rationalization passes across an exact pair.

This is the algebraic dévissage lemma needed when a long exact sequence is
initially obtained in abelian groups rather than in rational vector spaces.
-/
theorem rationalization_finite_middle
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) (hfg : Function.Exact f g)
    [Module.Finite ℚ (ℚ ⊗[ℤ] A)] [Module.Finite ℚ (ℚ ⊗[ℤ] C)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] B) := by
  let fQ : ℚ ⊗[ℤ] A →ₗ[ℚ] ℚ ⊗[ℤ] B :=
    TensorProduct.AlgebraTensorModule.lTensor ℚ ℚ f
  let gQ : ℚ ⊗[ℤ] B →ₗ[ℚ] ℚ ⊗[ℤ] C :=
    TensorProduct.AlgebraTensorModule.lTensor ℚ ℚ g
  have hQ : Function.Exact fQ gQ := by
    simpa [fQ, gQ] using Module.Flat.lTensor_exact ℚ hfg
  have hQ' : Function.Exact fQ gQ.rangeRestrict := by
    intro y
    rw [← hQ y]
    exact ⟨fun hy ↦ congrArg Subtype.val hy, fun hy ↦ Subtype.ext hy⟩
  exact Module.Finite.of_exact hQ' gQ.surjective_rangeRestrict

/--
Finite-dimensionality after rationalization descends along an injective map.

This is the degree-zero endpoint needed when a long exact sequence starts with
an injection rather than a preceding `Ext` group.
-/
theorem rationalization_finite_of_injective
    (f : A →ₗ[ℤ] B) (hf : Function.Injective f)
    [Module.Finite ℚ (ℚ ⊗[ℤ] B)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] A) := by
  apply Module.Finite.of_injective
    (TensorProduct.AlgebraTensorModule.lTensor ℚ ℚ f)
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

end ExactSequences

section AdditiveEquivalences

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B]

/-- Rationalization transports additive equivalences to `ℚ`-linear equivalences. -/
noncomputable def rationalizationMapAddEquiv (e : A ≃+ B) :
    ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] B :=
  LinearEquiv.baseChange ℤ ℚ A B e.toIntLinearEquiv

/-- Finite-dimensionality after rationalization is invariant under additive equivalence. -/
theorem rationalization_finite_congr (e : A ≃+ B) :
    Module.Finite ℚ (ℚ ⊗[ℤ] A) ↔ Module.Finite ℚ (ℚ ⊗[ℤ] B) := by
  constructor
  · intro h
    letI := h
    exact Module.Finite.equiv (rationalizationMapAddEquiv e)
  · intro h
    letI := h
    exact Module.Finite.equiv (rationalizationMapAddEquiv e).symm

end AdditiveEquivalences

section RationalModules

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

/--
For a rational vector space, extension of scalars from `ℤ` back to `ℚ` is
canonically equivalent to the original vector space.
-/
noncomputable def rationalizationLinearEquiv :
    ℚ ⊗[ℤ] V ≃ₗ[ℚ] V :=
  TensorProduct.lidOfCompatibleSMul ℤ ℚ V

/--
A rational vector space is finite-dimensional exactly when its underlying
abelian group becomes finite-dimensional after rationalization.
-/
theorem rationalization_finite_iff :
    Module.Finite ℚ (ℚ ⊗[ℤ] V) ↔ Module.Finite ℚ V := by
  constructor
  · intro h
    letI := h
    exact Module.Finite.equiv (rationalizationLinearEquiv V)
  · intro h
    letI := h
    exact Module.Finite.equiv (rationalizationLinearEquiv V).symm

end RationalModules

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
