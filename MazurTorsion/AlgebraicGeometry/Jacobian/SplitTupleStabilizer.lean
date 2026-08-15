/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteSymmetricQuotient
import Mathlib.GroupTheory.Perm.Subgroup

/-!
# Stabilizers of split-sheet tuples

The stabilizer of a tuple of sheet labels is the product of the permutation
groups of its fibers.  This identifies the residual symmetry on one
component of a split ordered power with independent symmetric groups on the
coordinates belonging to each sheet.

The named downstream consumer is the blockwise fundamental theorem of
symmetric polynomials used to identify the actual split symmetric quotient
with the joint coefficient chart in `SplitComponentUniversalRoot`.
-/

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitTupleStabilizer

open SplitFiniteSymmetricQuotient

variable (d m : ℕ) (a : Fin d → Fin m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

private lemma stabilizer_preserves
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) (i : Fin d) :
    a (g.1 i) = a i := by
  have h := congrFun g.2 (g.1 i)
  change a (g.1⁻¹ (g.1 i)) = a (g.1 i) at h
  simpa using h.symm

private lemma stabilizer_inv_preserves
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) (i : Fin d) :
    a (g.1⁻¹ i) = a i :=
  congrFun g.2 i

/-- Restrict a tuple stabilizer to the permutation induced on one fiber. -/
noncomputable def stabilizerToFiberPerm
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a)
    (j : Fin m) : Equiv.Perm { i : Fin d // a i = j } where
  toFun i := ⟨g.1 i, (stabilizer_preserves d m a g i).trans i.2⟩
  invFun i := ⟨g.1⁻¹ i, (stabilizer_inv_preserves d m a g i).trans i.2⟩
  left_inv i := Subtype.ext (g.1.symm_apply_apply i)
  right_inv i := Subtype.ext (g.1.apply_symm_apply i)

@[simp]
theorem coe_stabilizerToFiberPerm
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a)
    (j : Fin m) (i : { i : Fin d // a i = j }) :
    (stabilizerToFiberPerm d m a g j i : Fin d) = g.1 i := rfl

/-- Restriction to all fibers as a group homomorphism. -/
noncomputable def stabilizerToFiberPermHom :
    MulAction.stabilizer (Equiv.Perm (Fin d)) a →*
      (∀ j : Fin m, Equiv.Perm { i : Fin d // a i = j }) where
  toFun g := stabilizerToFiberPerm d m a g
  map_one' := by
    funext j
    ext i
    rfl
  map_mul' g h := by
    funext j
    ext i
    rfl

/-- Combine independent fiber permutations into a permutation of all tuple
positions. -/
noncomputable def fiberPermToPerm
    (h : ∀ j : Fin m, Equiv.Perm { i : Fin d // a i = j }) :
    Equiv.Perm (Fin d) :=
  (Equiv.sigmaFiberEquiv a).permCongr (Equiv.Perm.sigmaCongrRight h)

private theorem fiberPermToPerm_preserves
    (h : ∀ j : Fin m, Equiv.Perm { i : Fin d // a i = j }) (i : Fin d) :
    a (fiberPermToPerm d m a h i) = a i := by
  obtain ⟨⟨j, x⟩, rfl⟩ := (Equiv.sigmaFiberEquiv a).surjective i
  rw [fiberPermToPerm, Equiv.permCongr_apply,
    Equiv.symm_apply_apply]
  exact (h j x).2.trans x.2.symm

/-- The combined permutation acts on a fiber by its prescribed fiber
permutation. -/
theorem fiberPermToPerm_apply
    (h : ∀ j : Fin m, Equiv.Perm { i : Fin d // a i = j })
    (j : Fin m) (i : { i : Fin d // a i = j }) :
    fiberPermToPerm d m a h i = h j i := by
  have he : (Equiv.sigmaFiberEquiv a).symm (i : Fin d) = ⟨j, i⟩ := by
    simpa using (Equiv.sigmaFiberEquiv a).symm_apply_apply ⟨j, i⟩
  rw [fiberPermToPerm, Equiv.permCongr_apply, he]
  rfl

/-- Combine fiber permutations and package the result in the tuple
stabilizer. -/
noncomputable def fiberPermToStabilizer
    (h : ∀ j : Fin m, Equiv.Perm { i : Fin d // a i = j }) :
    MulAction.stabilizer (Equiv.Perm (Fin d)) a := by
  refine ⟨fiberPermToPerm d m a h, ?_⟩
  funext i
  change a ((fiberPermToPerm d m a h)⁻¹ i) = a i
  exact fiberPermToPerm_preserves d m a (fun j ↦ (h j).symm) i

@[simp]
theorem coe_fiberPermToStabilizer
    (h : ∀ j : Fin m, Equiv.Perm { i : Fin d // a i = j })
    (i : Fin d) :
    (fiberPermToStabilizer d m a h).1 i = fiberPermToPerm d m a h i := rfl

theorem stabilizerToFiberPerm_leftInverse :
    Function.LeftInverse (fiberPermToStabilizer d m a)
      (stabilizerToFiberPerm d m a) := by
  intro g
  apply Subtype.ext
  ext i
  simp [fiberPermToStabilizer, fiberPermToPerm, stabilizerToFiberPerm]

theorem stabilizerToFiberPerm_rightInverse :
    Function.RightInverse (fiberPermToStabilizer d m a)
      (stabilizerToFiberPerm d m a) := by
  intro h
  funext j
  ext i
  rw [coe_stabilizerToFiberPerm, coe_fiberPermToStabilizer]
  exact congrArg Fin.val (fiberPermToPerm_apply d m a h j i)

/-- The tuple stabilizer is the product of the symmetric groups of its
sheet fibers. -/
noncomputable def stabilizerEquivFiberPerm :
    MulAction.stabilizer (Equiv.Perm (Fin d)) a ≃*
      (∀ j : Fin m, Equiv.Perm { i : Fin d // a i = j }) :=
  MulEquiv.ofBijective (stabilizerToFiberPermHom d m a)
    ⟨(stabilizerToFiberPerm_leftInverse d m a).injective,
      (stabilizerToFiberPerm_rightInverse d m a).surjective⟩

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitTupleStabilizer
