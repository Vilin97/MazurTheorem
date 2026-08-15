/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Exact.Basic

/-!
# Subsingleton middle terms of exact triples

An exact pair whose source and target are subsingletons has a
subsingleton middle term.  This elementary form is convenient for
vanishing arguments in long exact cohomology sequences.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/--
If `A → B → C` is exact and both outer additive groups are
subsingletons, then `B` is a subsingleton.
-/
theorem subsingleton_middle_of_exact
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C)
    (h : Function.Exact f g)
    [Subsingleton A] [Subsingleton C] :
    Subsingleton B := by
  refine ⟨fun x y => ?_⟩
  suffices ∀ z : B, z = 0 by
    rw [this x, this y]
  intro z
  have hz : g z = 0 :=
    Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := (h z).mp hz
  calc
    z = f a := ha.symm
    _ = f 0 := congrArg f (Subsingleton.elim a 0)
    _ = 0 := map_zero f

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
