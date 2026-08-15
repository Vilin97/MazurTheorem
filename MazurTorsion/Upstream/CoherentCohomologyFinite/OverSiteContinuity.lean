/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.Over
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# The open-over-site equivalence is continuous

This supplies the site-theoretic compatibility missing from the pinned
Mathlib version.  It is the bridge between presentations on an over site
and restrictions to the corresponding open subscheme.
-/

open CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace.Opens

/-- The forward functor of `overEquivalence U` preserves covering sieves. -/
theorem overEquivalenceFunctorCoverPreserving
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    CoverPreserving ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology U) U.overEquivalence.functor where
  cover_preserve {Y S} hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS
    intro y hy
    obtain ⟨V, f, hVf, hyV⟩ := hS y.1 hy
    obtain ⟨W, h, h', hSh, hfeq⟩ := hVf
    refine ⟨U.overEquivalence.functor.obj W,
      U.overEquivalence.functor.map h, ⟨W, h, 𝟙 _, hSh, by simp⟩, ?_⟩
    exact leOfHom h' hyV

/-- The inverse functor of `overEquivalence U` preserves covering sieves. -/
theorem overEquivalenceInverseCoverPreserving
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    CoverPreserving (Opens.grothendieckTopology U)
      ((Opens.grothendieckTopology X).over U) U.overEquivalence.inverse where
  cover_preserve {Y S} hS := by
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    obtain ⟨⟨x', hx'U⟩, hx'Y, rfl⟩ := hx
    obtain ⟨P, f, hSf, hxP⟩ := hS ⟨x', hx'U⟩ hx'Y
    exact ⟨(U.overEquivalence.inverse.obj P).left,
      (U.overEquivalence.inverse.map f).left,
      ⟨U.overEquivalence.inverse.obj P, U.overEquivalence.inverse.map f, 𝟙 _,
        ⟨P, f, 𝟙 _, hSf, by simp⟩, by simp⟩,
      ⟨⟨x', hx'U⟩, hxP, rfl⟩⟩

/-- The forward functor of `overEquivalence U` is continuous. -/
instance overEquivalenceFunctorIsContinuous
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U) :=
  Functor.IsCoverDense.isContinuous _ _ _
    (overEquivalenceFunctorCoverPreserving U)

/-- The inverse functor of `overEquivalence U` is continuous. -/
instance overEquivalenceInverseIsContinuous
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    U.overEquivalence.inverse.IsContinuous
      (Opens.grothendieckTopology U) ((Opens.grothendieckTopology X).over U) :=
  Functor.IsCoverDense.isContinuous _ _ _
    (overEquivalenceInverseCoverPreserving U)

end TopologicalSpace.Opens
