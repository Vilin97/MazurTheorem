/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.Rationalization
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import MazurTorsion.Upstream.LeanPool.GrothendieckVanishing.CohomologyAPI

/-!
# Cohomological dévissage

This file combines the long exact sequence of `Ext` with exactness of
rationalization.  It is independent of algebraic geometry and therefore
applies to every short exact sequence of abelian sheaves.
-/

open CategoryTheory TensorProduct

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u v w

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/--
All `Ext` groups from `X` to `Y` are finite-dimensional after
rationalization.
-/
def RationalExtFinite (X Y : C) : Prop :=
  ∀ n : ℕ, Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X Y n))

/-- Postcomposition on `Ext` regarded as a `ℤ`-linear map. -/
noncomputable def extPostcompLinearMap {X Y Z : C} (f : Y ⟶ Z) (n : ℕ) :
    Abelian.Ext X Y n →ₗ[ℤ] Abelian.Ext X Z n :=
  ((Abelian.Ext.mk₀ f).postcomp X (add_zero n)).toIntLinearMap

/-- The connecting morphism in the covariant `Ext` sequence as a `ℤ`-linear map. -/
noncomputable def extConnectingLinearMap {X : C} {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) :
    Abelian.Ext X S.X₃ n →ₗ[ℤ] Abelian.Ext X S.X₁ (n + 1) :=
  (hS.extClass.postcomp X rfl).toIntLinearMap

/--
For a short exact sequence in an abelian category, rationalized
finite-dimensionality of the outer `Ext` groups implies that of the middle
group in the same degree.
-/
theorem rationalized_ext_finite_middle {X : C} {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ)
    [Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₁ n))]
    [Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₃ n))] :
    Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₂ n)) := by
  apply rationalization_finite_middle
    (extPostcompLinearMap S.f n) (extPostcompLinearMap S.g n)
  have h := Abelian.Ext.covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/--
Rational `Ext`-finiteness is closed under extensions in the covariant
variable.
-/
theorem RationalExtFinite.middle {X : C} {S : ShortComplex C}
    (hS : S.ShortExact)
    (h₁ : RationalExtFinite X S.X₁)
    (h₃ : RationalExtFinite X S.X₃) :
    RationalExtFinite X S.X₂ := by
  intro n
  letI := h₁ n
  letI := h₃ n
  exact rationalized_ext_finite_middle hS n

/--
In a short exact sequence, rationalized finite-dimensionality of the first
two terms implies that of the quotient.
-/
theorem rationalized_ext_finite_right {X : C} {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ)
    [Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₂ n))]
    [Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₁ (n + 1)))] :
    Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₃ n)) := by
  apply rationalization_finite_middle
    (extPostcompLinearMap S.g n) (extConnectingLinearMap hS n)
  have h := Abelian.Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Rational `Ext`-finiteness is closed under taking quotients. -/
theorem RationalExtFinite.right {X : C} {S : ShortComplex C}
    (hS : S.ShortExact)
    (h₁ : RationalExtFinite X S.X₁)
    (h₂ : RationalExtFinite X S.X₂) :
    RationalExtFinite X S.X₃ := by
  intro n
  letI := h₂ n
  letI := h₁ (n + 1)
  exact rationalized_ext_finite_right hS n

/--
In positive degree, rationalized finite-dimensionality of the quotient and
middle term implies that of the subobject.
-/
theorem rationalized_ext_finite_left_succ {X : C} {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ)
    [Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₃ n))]
    [Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₂ (n + 1)))] :
    Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₁ (n + 1))) := by
  apply rationalization_finite_middle
    (extConnectingLinearMap hS n) (extPostcompLinearMap S.f (n + 1))
  have h := Abelian.Ext.covariant_sequence_exact₁' X hS n (n + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/--
In degree zero, rationalized finite-dimensionality descends from the middle
term to a subobject.
-/
theorem rationalized_ext_finite_left_zero {X : C} {S : ShortComplex C}
    (hS : S.ShortExact)
    [Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₂ 0))] :
    Module.Finite ℚ (ℚ ⊗[ℤ] (Abelian.Ext X S.X₁ 0)) := by
  letI : Mono S.f := hS.mono_f
  apply rationalization_finite_of_injective (extPostcompLinearMap S.f 0)
  exact Abelian.Ext.postcomp_mk₀_injective_of_mono X S.f

/-- Rational `Ext`-finiteness is closed under taking subobjects. -/
theorem RationalExtFinite.left {X : C} {S : ShortComplex C}
    (hS : S.ShortExact)
    (h₂ : RationalExtFinite X S.X₂)
    (h₃ : RationalExtFinite X S.X₃) :
    RationalExtFinite X S.X₁ := by
  intro n
  cases n with
  | zero =>
      letI := h₂ 0
      exact rationalized_ext_finite_left_zero hS
  | succ n =>
      letI := h₃ n
      letI := h₂ (n + 1)
      exact rationalized_ext_finite_left_succ hS n

end Ext

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
