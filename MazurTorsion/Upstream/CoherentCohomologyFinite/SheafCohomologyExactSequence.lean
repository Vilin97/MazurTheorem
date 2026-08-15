/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCohomologyExact

/-!
# Compatibility names for long exact sheaf cohomology sequences

MazurTheorem already contains the option-free AINTLIB long exact sequence
API.  The coherent-cohomology development used two additional names and one
degree-zero consequence.  This file supplies only those additions, so the two
independently developed copies of the core exact-sequence API do not collide.
-/

open CategoryTheory

universe w' w v u

namespace CategoryTheory.Sheaf.H

open Abelian AddCommGrpCat Opposite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
variable (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- Compatibility name for the connecting homomorphism. -/
noncomputable abbrev connectingHom : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  δ hS n₀ n₁ h

variable {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
variable (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

/-- Naturality of the connecting homomorphism under the compatibility name. -/
theorem connectingHom_naturality (x : H S₁.X₃ n₀) :
    connectingHom h₂ n₀ n₁ h (map f.τ₃ n₀ x) =
      map f.τ₁ n₁ (connectingHom h₁ n₀ n₁ h x) :=
  δ_naturality n₀ n₁ h h₁ h₂ f x

variable {T : C} (hT : Limits.IsTerminal T)

/-- Exactness after the connecting homomorphism, with degree-zero
cohomology expressed as sections over a terminal object. -/
lemma longSequence_equiv₀_exact₁ (x₁ : S.X₁.H 1)
    (hx₁ : map S.f 1 x₁ = 0) :
    ∃ x₃ : S.X₃.obj.obj (op T),
      connectingHom hS 0 1 rfl
        ((equiv₀ S.X₃ hT).symm x₃) = x₁ := by
  obtain ⟨x₃, hx₃⟩ :=
    longSequence_exact₁ hS 0 1 rfl x₁ hx₁
  exact ⟨equiv₀ S.X₃ hT x₃, by simpa using hx₃⟩

end CategoryTheory.Sheaf.H
