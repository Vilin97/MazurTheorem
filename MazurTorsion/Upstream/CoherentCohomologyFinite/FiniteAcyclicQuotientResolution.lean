/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SubsingletonExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Finite acyclic quotient resolutions

A finite sequence of epimorphisms

`E₀ ↠ Y`, `E₁ ↠ ker(E₀ ↠ Y)`, ...

dimension-shifts positive Ext from `Y` into Ext of the terminal kernel.
This is the finite-resolution form of the standard Serre-vanishing
argument: after one sufficiently large common twist, the finitely many
middle objects are acyclic.
-/


open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/--
A quotient resolution of `Y` of length `r`, with every middle object
satisfying `Good`, and with terminal kernel `Z`.
-/
inductive FiniteQuotientResolution (Good : C → Prop) :
    (r : ℕ) → C → C → Prop
  | nil (Y : C) : FiniteQuotientResolution Good 0 Y Y
  | cons {r : ℕ} {Y Z : C}
      (E : C) (f : E ⟶ Y)
      (epi : Epi f) (good : Good E)
      (tail : FiniteQuotientResolution Good r (kernel f) Z) :
      FiniteQuotientResolution Good (r + 1) Y Z

/--
Rebasing the source of a quotient resolution along an isomorphism
changes its terminal kernel only up to isomorphism.
-/
theorem FiniteQuotientResolution.rebaseSource
    (Good : C → Prop)
    {r : ℕ} {Y Z Y' : C}
    (T : FiniteQuotientResolution Good r Y Z)
    (e : Y' ≅ Y) :
    ∃ Z' : C,
      Nonempty (Z' ≅ Z) ∧
        FiniteQuotientResolution Good r Y' Z' := by
  induction T generalizing Y' with
  | nil Y =>
      exact
        ⟨Y', ⟨e⟩,
          FiniteQuotientResolution.nil Y'⟩
  | @cons r Y Z E f hf hE tail ih =>
      letI : Epi f := hf
      let f' : E ⟶ Y' := f ≫ e.inv
      have hf' : Epi f' := by
        dsimp only [f']
        infer_instance
      let eKernel : kernel f' ≅ kernel f :=
        kernel.mapIso (f := f') f
          (Iso.refl E) e
          (by simp [f'])
      obtain ⟨Z', eZ, T'⟩ :=
        ih eKernel
      exact
        ⟨Z', eZ,
          FiniteQuotientResolution.cons
            E f' hf' hE T'⟩

universe u' v'

/--
A finite quotient resolution can be transported through a
finite-limit-preserving functor which preserves epimorphisms.  The
terminal object is preserved up to isomorphism because the chosen
kernels in the two categories need not be definitionally equal.
-/
theorem FiniteQuotientResolution.map
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (Good : C → Prop) (Good' : D → Prop)
    {r : ℕ} {Y Z : C}
    (T : FiniteQuotientResolution Good r Y Z)
    (F : C ⥤ D)
    [PreservesFiniteLimits F]
    [F.PreservesEpimorphisms]
    (hgood :
      ∀ E : C, Good E → Good' (F.obj E)) :
    ∃ Z' : D,
      Nonempty (Z' ≅ F.obj Z) ∧
        FiniteQuotientResolution
          Good' r (F.obj Y) Z' := by
  induction T with
  | nil Y =>
      exact
        ⟨F.obj Y, ⟨Iso.refl _⟩,
          FiniteQuotientResolution.nil (F.obj Y)⟩
  | @cons r Y Z E f hf hE tail ih =>
      letI : Epi f := hf
      have hfmap : Epi (F.map f) :=
        inferInstance
      obtain ⟨Z₀, ⟨eZ₀⟩, T₀⟩ := ih
      obtain ⟨Z', ⟨eZ'⟩, T'⟩ :=
        T₀.rebaseSource Good'
          (PreservesKernel.iso F f).symm
      exact
        ⟨Z', ⟨eZ' ≪≫ eZ₀⟩,
          FiniteQuotientResolution.cons
            (F.obj E) (F.map f) hfmap
              (hgood E hE) T'⟩

/--
For a natural-number-indexed family of exact functors, finitely many
middle objects share one common parameter after which their images all
satisfy the target good-object predicate.
-/
theorem FiniteQuotientResolution.map_eventually
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (Good : C → Prop) (Good' : D → Prop)
    {r : ℕ} {Y Z : C}
    (T : FiniteQuotientResolution Good r Y Z)
    (F : ℕ → C ⥤ D)
    [∀ n, PreservesFiniteLimits (F n)]
    [∀ n, (F n).PreservesEpimorphisms]
    (hgood :
      ∀ (E : C), Good E →
        ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
          Good' ((F n).obj E)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ Z' : D,
        Nonempty (Z' ≅ (F n).obj Z) ∧
          FiniteQuotientResolution
            Good' r ((F n).obj Y) Z' := by
  induction T with
  | nil Y =>
      exact
        ⟨0, fun n _ =>
          ⟨(F n).obj Y, ⟨Iso.refl _⟩,
            FiniteQuotientResolution.nil ((F n).obj Y)⟩⟩
  | @cons r Y Z E f hf hE tail ih =>
      obtain ⟨bE, hbE⟩ := hgood E hE
      obtain ⟨bT, hbT⟩ := ih
      refine ⟨max bE bT, fun n hn => ?_⟩
      letI : Epi f := hf
      have hfmap : Epi ((F n).map f) :=
        inferInstance
      have hEn : Good' ((F n).obj E) :=
        hbE n (le_trans (le_max_left _ _) hn)
      obtain ⟨Z₀, ⟨eZ₀⟩, T₀⟩ :=
        hbT n (le_trans (le_max_right _ _) hn)
      obtain ⟨Z', ⟨eZ'⟩, T'⟩ :=
        T₀.rebaseSource Good'
          (PreservesKernel.iso (F n) f).symm
      exact
        ⟨Z', ⟨eZ' ≪≫ eZ₀⟩,
          FiniteQuotientResolution.cons
            ((F n).obj E) ((F n).map f)
              hfmap hEn T'⟩

/--
If every middle object of a finite quotient resolution is Ext-acyclic
in positive degree, then positive Ext of its source vanishes whenever
the appropriately shifted Ext of the terminal kernel vanishes.
-/
theorem FiniteQuotientResolution.ext_subsingleton
    [HasExt.{w} C]
    (X : C) (Good : C → Prop)
    {r : ℕ} {Y Z : C}
    (T : FiniteQuotientResolution Good r Y Z)
    (hgood :
      ∀ (E : C), Good E → ∀ q : ℕ, 0 < q →
        Subsingleton (Abelian.Ext X E q))
    (q : ℕ) (hq : 0 < q)
    (hterminal :
      Subsingleton (Abelian.Ext X Z (q + r))) :
    Subsingleton (Abelian.Ext X Y q) := by
  induction T generalizing q with
  | nil Y =>
      simpa using hterminal
  | @cons r Y Z E f hf hE tail ih =>
      letI : Epi f := hf
      let S := ShortComplex.kernelSequence f
      haveI : Epi S.g := by
        dsimp [S, ShortComplex.kernelSequence]
        infer_instance
      have hS : S.ShortExact :=
        { exact := ShortComplex.kernelSequence_exact f }
      letI :
          Subsingleton (Abelian.Ext X E q) :=
        hgood E hE q hq
      letI :
          Subsingleton
            (Abelian.Ext X (kernel f) (q + 1)) := by
        apply ih (q + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hterminal
      letI :
          Subsingleton (Abelian.Ext X S.X₂ q) :=
        inferInstanceAs
          (Subsingleton (Abelian.Ext X E q))
      letI :
          Subsingleton (Abelian.Ext X S.X₁ (q + 1)) :=
        inferInstanceAs
          (Subsingleton
            (Abelian.Ext X (kernel f) (q + 1)))
      apply
        subsingleton_middle_of_exact
          ((Abelian.Ext.mk₀ S.g).postcomp X (add_zero q))
          (hS.extClass.postcomp X rfl)
      have hex :=
        Abelian.Ext.covariant_sequence_exact₃'
          X hS q (q + 1) rfl
      rw [ShortComplex.ab_exact_iff_function_exact] at hex
      exact hex

/--
A quotient resolution whose length is a cohomological-dimension bound
is acyclic in every positive degree, provided the terminal kernel
vanishes above that bound.
-/
theorem FiniteQuotientResolution.ext_subsingleton_of_bound
    [HasExt.{w} C]
    (X : C) (Good : C → Prop) (bound : ℕ)
    {Y Z : C}
    (T : FiniteQuotientResolution Good bound Y Z)
    (hgood :
      ∀ (E : C), Good E → ∀ q : ℕ, 0 < q →
        Subsingleton (Abelian.Ext X E q))
    (hterminal :
      ∀ q : ℕ, bound < q →
        Subsingleton (Abelian.Ext X Z q))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Abelian.Ext X Y q) :=
  T.ext_subsingleton X Good hgood q hq
    (hterminal (q + bound) (by omega))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
