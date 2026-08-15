/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSymmetricPower
import MazurTorsion.AlgebraicGeometry.Jacobian.BlockSymmetricPolynomial
import Mathlib.GroupTheory.Perm.Subgroup

/-!
# Invariants of independent coordinate blocks

A product of symmetric groups acts on a polynomial ring whose variables are
partitioned into fibers.  Elementary symmetric polynomials in each fiber are
fixed under this action, so the joint coefficient map canonically factors
through the invariant subring.

The named downstream consumer is `SplitSymmetricQuotientChart`, where the
fibers are the positions carrying each sheet label of a split finite étale
curve chart.
-/

noncomputable section

universe u v w

namespace MazurTorsion.AlgebraicGeometry.Jacobian.BlockPermutationInvariants

open AffineLineSymmetricPower

variable (R : Type u) [CommRing R]
variable (J : Type v) (α : J → Type w)

/-- The group of independent permutations of all variable blocks. -/
abbrev fiberPermutationGroup := ∀ j : J, Equiv.Perm (α j)

/-- The permutation of the total sigma type induced by independent
permutations in its fibers. -/
noncomputable def totalFiberPermutation
    (g : fiberPermutationGroup J α) : Equiv.Perm (Σ j, α j) :=
  Equiv.Perm.sigmaCongrRight g

/-- Independent fiber permutations act on the total polynomial ring by
renaming variables. -/
@[instance_reducible]
noncomputable def fiberPermutationAction :
    MulSemiringAction (fiberPermutationGroup J α)
      (MvPolynomial (Σ j, α j) R) := by
  letI := coordinatePermutationAction R (Σ j, α j)
  exact MulSemiringAction.compHom (MvPolynomial (Σ j, α j) R)
    (Equiv.Perm.sigmaCongrRightHom α)

theorem fiber_smul_eq_rename (g : fiberPermutationGroup J α)
    (p : MvPolynomial (Σ j, α j) R) :
    letI := fiberPermutationAction R J α
    g • p = MvPolynomial.rename (totalFiberPermutation J α g) p := by
  change
    (coordinatePermutationRingAut R (Σ j, α j)
      (Equiv.Perm.sigmaCongrRightHom α g)) p = _
  rfl

/-- The block-permutation action commutes with the coefficient-ring scalar
action. -/
theorem fiberPermutationSMulCommClass :
    letI := fiberPermutationAction R J α
    SMulCommClass (fiberPermutationGroup J α) R
      (MvPolynomial (Σ j, α j) R) := by
  letI := fiberPermutationAction R J α
  constructor
  intro g r p
  change MvPolynomial.rename (totalFiberPermutation J α g) (r • p) =
    r • MvPolynomial.rename (totalFiberPermutation J α g) p
  simp [Algebra.smul_def]

variable [∀ j, Fintype (α j)]

/-- The `q`-th elementary symmetric polynomial in one fiber, embedded in the
total polynomial ring. -/
noncomputable def blockElementarySymmetric (j : J) (q : ℕ) :
    MvPolynomial (Σ j, α j) R :=
  MvPolynomial.rename (Sigma.mk j) (MvPolynomial.esymm (α j) R q)

/-- Every elementary symmetric polynomial in one fiber is fixed by every
independent permutation of all fibers. -/
theorem rename_blockElementarySymmetric
    (g : fiberPermutationGroup J α) (j : J) (q : ℕ) :
    MvPolynomial.rename (totalFiberPermutation J α g)
        (blockElementarySymmetric R J α j q) =
      blockElementarySymmetric R J α j q := by
  simp only [blockElementarySymmetric, MvPolynomial.rename_rename]
  have hcomp :
      totalFiberPermutation J α g ∘ Sigma.mk j = Sigma.mk j ∘ g j := by
    funext i
    rfl
  rw [hcomp, ← MvPolynomial.rename_rename]
  rw [MvPolynomial.esymm_isSymmetric (α j) R q (g j)]

/-- The joint coefficient map sends one coefficient variable for every fiber
to the corresponding elementary symmetric polynomial in that fiber. -/
noncomputable def jointElementarySymmetricAlgHom :
    MvPolynomial (Σ j, Fin (Fintype.card (α j))) R →ₐ[R]
      MvPolynomial (Σ j, α j) R :=
  MvPolynomial.aeval fun x ↦
    blockElementarySymmetric R J α x.1 (x.2 + 1)

@[simp]
theorem jointElementarySymmetricAlgHom_X
    (i : Σ j, Fin (Fintype.card (α j))) :
    jointElementarySymmetricAlgHom R J α (MvPolynomial.X i) =
      blockElementarySymmetric R J α i.1 (i.2 + 1) := by
  exact MvPolynomial.aeval_X _ i

/-- The joint elementary-symmetric coefficient map takes values in the fixed
subring for the product of the fiber permutation groups. -/
noncomputable def jointElementarySymmetricToFixedPoints
    :
    letI := fiberPermutationAction R J α
    letI := fiberPermutationSMulCommClass R J α
    MvPolynomial (Σ j, Fin (Fintype.card (α j))) R →ₐ[R]
      FixedPoints.subalgebra R (MvPolynomial (Σ j, α j) R)
        (fiberPermutationGroup J α) := by
  letI := fiberPermutationAction R J α
  letI := fiberPermutationSMulCommClass R J α
  refine (jointElementarySymmetricAlgHom R J α).codRestrict _ ?_
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
      change ∀ g, g • (jointElementarySymmetricAlgHom R J α)
        (MvPolynomial.C r) = _
      intro g
      rw [fiber_smul_eq_rename]
      simp
  | add p q hp hq =>
      change ∀ g, g • (jointElementarySymmetricAlgHom R J α) (p + q) = _
      intro g
      rw [map_add, smul_add, hp g, hq g]
  | mul_X p i hp =>
      change ∀ g, g • (jointElementarySymmetricAlgHom R J α)
        (p * MvPolynomial.X i) = _
      intro g
      rw [map_mul, jointElementarySymmetricAlgHom_X,
        fiber_smul_eq_rename, map_mul, ← fiber_smul_eq_rename, hp g,
        rename_blockElementarySymmetric]

@[simp]
theorem jointElementarySymmetricToFixedPoints_X
    (i : Σ j, Fin (Fintype.card (α j))) :
    letI := fiberPermutationAction R J α
    letI := fiberPermutationSMulCommClass R J α
    ((jointElementarySymmetricToFixedPoints R J α)
      (MvPolynomial.X i)).1 =
        blockElementarySymmetric R J α i.1 (i.2 + 1) := by
  letI := fiberPermutationAction R J α
  letI := fiberPermutationSMulCommClass R J α
  exact jointElementarySymmetricAlgHom_X R J α i

end MazurTorsion.AlgebraicGeometry.Jacobian.BlockPermutationInvariants
