/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Exact sequences in sheaf cohomology

This file contains the option-free core of Mathlib PR #36218. For a short
exact sequence of additive sheaves, it constructs the connecting morphism and
the associated six-term window of the long exact sequence, together with
elementwise exactness lemmas.

This is a source-preserving Apache-2.0 port of AINTLIB's
`ForMathlib/SheafCohomologyExact.lean` at commit
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.
-/

open CategoryTheory Abelian AddCommGrpCat

universe w' w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

namespace H

/-- The connecting homomorphism in the long exact sequence of sheaf
cohomology. -/
noncomputable def δ : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

variable {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
  (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

/-- Naturality of the connecting homomorphism. -/
theorem δ_naturality (x : H S₁.X₃ n₀) :
    δ h₂ n₀ n₁ h (map f.τ₃ n₀ x) = map f.τ₁ n₁ (δ h₁ n₀ n₁ h x) := by
  delta δ H map
  simp [ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]

/-- A six-term window of the long exact sequence of sheaf cohomology. -/
noncomputable abbrev longSequence (h : n₀ + 1 = n₁ := by omega) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  ComposableArrows.mk₅
    (ofHom (map S.f n₀))
    (ofHom (map S.g n₀))
    (ofHom (δ hS n₀ n₁ h))
    (ofHom (map S.f n₁))
    (ofHom (map S.g n₁))

/-- Exactness of the six-term window in sheaf cohomology. -/
theorem longSequence_exact : (longSequence hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact _ hS n₀ n₁ h

/-- The connecting map followed by the next cohomology map is zero. -/
lemma longSequence_comp_zero₁ (x : H S.X₃ n₀) :
    map S.f n₁ (δ hS n₀ n₁ h x) = 0 := by
  change (x.comp hS.extClass h).comp (Ext.mk₀ S.f) (add_zero n₁) = 0
  simp only [Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_comp, Ext.comp_zero]

/-- The previous cohomology map followed by the connecting map is zero. -/
lemma longSequence_comp_zero₃ (x : H S.X₂ n₀) :
    δ hS n₀ n₁ h (map S.g n₀ x) = 0 := by
  change (x.comp (Ext.mk₀ S.g) (add_zero n₀)).comp hS.extClass h = 0
  simp only [Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- Consecutive cohomology maps induced by a short complex compose to zero. -/
lemma longSequence_comp_zero₂ (n : ℕ) (x : H S.X₁ n) :
    map S.g n (map S.f n x) = 0 := by
  simp only [map_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    ShortComplex.zero, Ext.mk₀_zero, Ext.comp_zero]

include hS in
/-- Elementwise exactness at the middle sheaf in a fixed degree. -/
lemma longSequence_exact₂ (n : ℕ) (x₂ : H S.X₂ n) (hx₂ : map S.g n x₂ = 0) :
    ∃ x₁ : H S.X₁ n, map S.f n x₁ = x₂ :=
  Ext.covariant_sequence_exact₂ _ hS _ hx₂

include hS in
/-- In a short exact sequence, vanishing of the same cohomology degree at the
two ends implies vanishing at the middle. -/
lemma subsingleton_H_X₂_of_shortExact (n : ℕ)
    (hleft : Subsingleton (H S.X₁ n))
    (hright : Subsingleton (H S.X₃ n)) :
    Subsingleton (H S.X₂ n) := by
  letI : Subsingleton (H S.X₁ n) := hleft
  letI : Subsingleton (H S.X₃ n) := hright
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x₁, hx₁⟩ := longSequence_exact₂ hS n x (Subsingleton.elim _ _)
  rw [Subsingleton.elim x₁ 0, map_zero] at hx₁
  exact hx₁.symm

/-- Elementwise exactness before the connecting homomorphism. -/
lemma longSequence_exact₃ (x₃ : H S.X₃ n₀) (hx₃ : δ hS n₀ n₁ h x₃ = 0) :
    ∃ x₂ : H S.X₂ n₀, map S.g n₀ x₂ = x₃ :=
  Ext.covariant_sequence_exact₃ _ _ _ h hx₃

/-- Elementwise exactness after the connecting homomorphism. -/
lemma longSequence_exact₁ (x₁ : H S.X₁ n₁) (hx₁ : map S.f n₁ x₁ = 0) :
    ∃ x₃ : H S.X₃ n₀, δ hS n₀ n₁ h x₃ = x₁ :=
  Ext.covariant_sequence_exact₁ _ _ _ hx₁ h

include hS in
/-- In a short exact sequence, vanishing of `H^q` of the right term and
`H^(q+1)` of the middle term implies vanishing of `H^(q+1)` of the left
term. -/
lemma subsingleton_H_X₁_succ_of_shortExact (q : ℕ)
    (hright : Subsingleton (H S.X₃ q))
    (hmiddle : Subsingleton (H S.X₂ (q + 1))) :
    Subsingleton (H S.X₁ (q + 1)) := by
  letI : Subsingleton (H S.X₃ q) := hright
  letI : Subsingleton (H S.X₂ (q + 1)) := hmiddle
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x₃, hx₃⟩ := longSequence_exact₁
    hS q (q + 1) rfl x (Subsingleton.elim _ _)
  rw [Subsingleton.elim x₃ 0, map_zero] at hx₃
  exact hx₃.symm

include hS in
/-- In a short exact sequence, surjectivity on `H^q` from the middle to the
right and vanishing of `H^(q+1)` of the middle imply vanishing of
`H^(q+1)` of the left term. -/
lemma subsingleton_H_X₁_succ_of_shortExact_of_surjective (q : ℕ)
    (hsurj : Function.Surjective (map S.g q))
    (hmiddle : Subsingleton (H S.X₂ (q + 1))) :
    Subsingleton (H S.X₁ (q + 1)) := by
  letI : Subsingleton (H S.X₂ (q + 1)) := hmiddle
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x₃, hx₃⟩ := longSequence_exact₁
    hS q (q + 1) rfl x (Subsingleton.elim _ _)
  obtain ⟨x₂, hx₂⟩ := hsurj x₃
  rw [← hx₃, ← hx₂, longSequence_comp_zero₃]

variable {T : C} (hT : Limits.IsTerminal T)

open Opposite

include hS hT in
/-- Degree-zero exactness at the middle sheaf, expressed using sections over
a terminal object. -/
lemma longSequence_equiv₀_exact₂ (x₂ : S.X₂.obj.obj (op T))
    (hx₂ : S.g.hom.app (op T) x₂ = 0) :
    ∃ x₁ : S.X₁.obj.obj (op T), S.f.hom.app (op T) x₁ = x₂ := by
  let y₂ := (equiv₀ S.X₂ hT).symm x₂
  have hy₂ : map S.g 0 y₂ = 0 := by
    rw [equiv₀_symm_naturality, hx₂]
    exact map_zero _
  obtain ⟨y₁, hy₁⟩ := longSequence_exact₂ hS 0 y₂ hy₂
  refine ⟨equiv₀ S.X₁ hT y₁, ?_⟩
  rw [equiv₀_naturality, hy₁]
  simp [y₂]

/-- Degree-zero exactness expressed using sections over a terminal object. -/
lemma longSequence_equiv₀_exact₃ (x₃ : S.X₃.obj.obj (op T))
    (hx₃ : δ hS 0 1 rfl ((equiv₀ S.X₃ hT).symm x₃) = 0) :
    ∃ x₂ : S.X₂.obj.obj (op T), S.g.hom.app (op T) x₂ = x₃ := by
  obtain ⟨x₂, hx₂⟩ := longSequence_exact₃ hS 0 1 rfl
    ((equiv₀ S.X₃ hT).symm x₃) hx₃
  exact ⟨equiv₀ S.X₂ hT x₂, by simp [equiv₀_naturality, hx₂]⟩

include hS hT in
/-- If `H¹` of the first sheaf vanishes, the map on terminal-object
sections is surjective. -/
lemma longSequence_surjective_of_subsingleton_H
    [Subsingleton (S.X₁.H 1)] :
    Function.Surjective (S.g.hom.app (op T)) :=
  fun x₃ ↦ longSequence_equiv₀_exact₃ hS hT x₃
    (Subsingleton.elim _ _)

end H

end CategoryTheory.Sheaf
