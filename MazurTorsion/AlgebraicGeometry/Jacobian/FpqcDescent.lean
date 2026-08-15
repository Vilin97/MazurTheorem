/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Fpqc descent for finite-flat families

This file packages the two descent steps used after an explicit affine
calculation on an fpqc chart: flatness descends, and a constant value of the
finite-flat rank descends along a surjective base change.

The named downstream consumer is the local monic-root calculation for the
pointed universal effective divisor in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits MorphismProperty
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FpqcDescent

/-- Flat ring maps codescend along faithfully flat ring maps. -/
lemma flatRingHom_codescendsAlong_faithfullyFlat :
    _root_.RingHom.CodescendsAlong _root_.RingHom.Flat
      _root_.RingHom.FaithfullyFlat := by
  apply _root_.RingHom.CodescendsAlong.mk _root_.RingHom.FaithfullyFlat
    _root_.RingHom.Flat.respectsIso
  intro R S T _ _ _ _ _ hq hf
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hq
  rw [RingHom.flat_algebraMap_iff] at hf ⊢
  exact Module.Flat.of_flat_tensorProduct R T S

/-- Flatness of scheme morphisms descends along fpqc morphisms. -/
instance : MorphismProperty.DescendsAlong
    (@Flat : MorphismProperty Scheme.{u})
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat
    flatRingHom_codescendsAlong_faithfullyFlat

/-- A morphism is flat when its pullback along an fpqc cover is flat. -/
lemma flat_of_fpqc_pullback {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (q : T ⟶ Y)
    [Surjective q] [Flat q] [QuasiCompact q]
    [Flat (pullback.fst q f)] : Flat f := by
  exact MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := @Flat) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := q) (g := f) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- A constant rank for a finite flat morphism descends along any
surjective base change. -/
lemma finrank_eq_of_surjective_baseChange {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (q : T ⟶ Y) [Flat f] [IsFinite f]
    [Surjective q] (n : ℕ)
    (h : (pullback.fst q f).finrank = fun _ ↦ n) :
    f.finrank = fun _ ↦ n := by
  funext y
  obtain ⟨t, rfl⟩ := q.surjective y
  rw [← Scheme.Hom.finrank_pullback_fst f q]
  exact congrFun h t

end MazurTorsion.AlgebraicGeometry.Jacobian.FpqcDescent
