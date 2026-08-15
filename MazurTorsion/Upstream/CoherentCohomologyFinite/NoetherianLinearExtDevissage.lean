/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Linear Ext dévissage over a Noetherian ring

The usual descending Serre dévissage only uses that submodules of finite
modules remain finite.  Thus the coefficient ring need not be a field:
a commutative Noetherian ring suffices.  This file records the exact
two-out-of-three lemma and the resulting bounded quotient-presentation
argument in that generality.
-/


open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u v w t

variable {R : Type t} [CommRing R] [IsNoetherianRing R]

/-- In an exact pair over a Noetherian ring, finiteness of the outer
modules implies finiteness of the middle module. -/
theorem moduleFinite_middle_of_exact_noetherian
    {A : Type*} {B : Type*} {C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hfg : Function.Exact f g)
    [Module.Finite R A] [Module.Finite R C] :
    Module.Finite R B := by
  have hfg' : Function.Exact f g.rangeRestrict := by
    intro y
    rw [← hfg y]
    exact
      ⟨fun hy => congrArg Subtype.val hy,
        fun hy => Subtype.ext hy⟩
  letI : Module.Finite R g.range := by
    infer_instance
  exact
    Module.Finite.of_exact hfg'
      g.surjective_rangeRestrict

variable {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasExt.{w} C]

/-- Postcomposition by a degree-zero morphism, as an `R`-linear map on
Ext. -/
noncomputable abbrev noetherianExtPostcompLinearMap
    {X Y Z : C} (f : Y ⟶ Z) (n : ℕ) :
    Abelian.Ext X Y n →ₗ[R] Abelian.Ext X Z n :=
  (Abelian.Ext.mk₀ f).postcompOfLinear R X (add_zero n)

/-- The connecting morphism in a covariant Ext sequence, as an
`R`-linear map. -/
noncomputable abbrev noetherianExtConnectingLinearMap
    {X : C} {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) :
    Abelian.Ext X S.X₃ n →ₗ[R]
      Abelian.Ext X S.X₁ (n + 1) :=
  hS.extClass.postcompOfLinear R X rfl

/-- Ext-finiteness over a Noetherian ring is closed under quotients in
the covariant variable. -/
theorem noetherianLinearExtFinite_right
    {X : C} {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ)
    [Module.Finite R (Abelian.Ext X S.X₂ n)]
    [Module.Finite R (Abelian.Ext X S.X₁ (n + 1))] :
    Module.Finite R (Abelian.Ext X S.X₃ n) := by
  apply
    moduleFinite_middle_of_exact_noetherian
      (noetherianExtPostcompLinearMap S.g n)
      (noetherianExtConnectingLinearMap hS n)
  have h :=
    Abelian.Ext.covariant_sequence_exact₃'
      X hS n (n + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Bounded cohomology and quotient presentations by objects with finite
Ext imply finite Ext for the whole class over a Noetherian coefficient
ring. -/
theorem noetherianLinearExtFinite_of_bounded_quotient_presentations
    (X : C) (P Good : C → Prop) (bound : ℕ)
    (hvanish :
      ∀ (Y : C), P Y → ∀ n : ℕ, bound < n →
        Subsingleton (Abelian.Ext X Y n))
    (hpresentation :
      ∀ (Y : C), P Y →
        ∃ (E : C) (f : E ⟶ Y),
          Epi f ∧ Good E ∧ P (kernel f))
    (hgood :
      ∀ (E : C), Good E → ∀ n : ℕ,
        Module.Finite R (Abelian.Ext X E n))
    (Y : C) (hY : P Y) (n : ℕ) :
    Module.Finite R (Abelian.Ext X Y n) := by
  by_cases hn : bound < n
  · letI : Subsingleton (Abelian.Ext X Y n) :=
      hvanish Y hY n hn
    infer_instance
  · have hnle : n ≤ bound := Nat.le_of_not_gt hn
    let distance := bound - n
    induction hdistance : distance using Nat.strong_induction_on
      generalizing n Y with
    | h k ih =>
        obtain ⟨E, f, hf, hE, hker⟩ :=
          hpresentation Y hY
        letI : Epi f := hf
        let S := ShortComplex.kernelSequence f
        haveI : Epi S.g := by
          dsimp [S, ShortComplex.kernelSequence]
          infer_instance
        have hS : S.ShortExact :=
          { exact := ShortComplex.kernelSequence_exact f }
        have hkernel :
            Module.Finite R
              (Abelian.Ext X (kernel f) (n + 1)) := by
          by_cases htop : bound < n + 1
          · letI :
                Subsingleton
                  (Abelian.Ext X (kernel f) (n + 1)) :=
              hvanish (kernel f) hker (n + 1) htop
            infer_instance
          · have hnextle : n + 1 ≤ bound :=
              Nat.le_of_not_gt htop
            have hlt :
                bound - (n + 1) < k := by
              dsimp [distance] at hdistance
              omega
            exact
              ih (bound - (n + 1)) hlt
                (kernel f) hker (n + 1)
                htop hnextle rfl
        letI :
            Module.Finite R
              (Abelian.Ext X S.X₁ (n + 1)) :=
          hkernel
        letI :
            Module.Finite R
              (Abelian.Ext X S.X₂ n) :=
          hgood E hE n
        exact noetherianLinearExtFinite_right hS n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
