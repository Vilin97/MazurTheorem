/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteBlockReindexing

/-!
# Invariants of a finite family of coordinate blocks

Transport the recursive blockwise fundamental theorem through the canonical
sigma reindexing.  For block sizes `n : Fin m → ℕ`, the invariant ring of
the joint root-coordinate polynomial ring under independent permutations in
each fiber is a polynomial ring on the same sigma-shaped family of
elementary-symmetric coefficient coordinates.

The named downstream consumer is `SplitSymmetricQuotientChart`, with `n`
specialized to the sheet multiplicities of one split symmetric-power
component.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFiberPermutationInvariants

open IteratedBlockInvariants
open FiniteBlockReindexing
open BlockPermutationInvariants

variable (R : Type u) [CommRing R]
variable (m : ℕ) (n : Fin m → ℕ)

/-- Renaming recursive block variables by the sigma reindexing intertwines
the recursive block action with independent permutations of the sigma
fibers. -/
theorem rename_blockAction_eq_fiberAction
    (g : blockPermutationGroup (finBlockSizes m n))
    (p : MvPolynomial (blockIndex (finBlockSizes m n)) R) :
    letI := jointBlockPermutationAction R (finBlockSizes m n)
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    MvPolynomial.rename (blockIndexOfFnEquivSigma m n) (g • p) =
      blockPermutationGroupOfFnMulEquiv m n g •
        MvPolynomial.rename (blockIndexOfFnEquivSigma m n) p := by
  letI := jointBlockPermutationAction R (finBlockSizes m n)
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  change MvPolynomial.rename (blockIndexOfFnEquivSigma m n)
      (MvPolynomial.rename
        (blockIndexPermutationHom (finBlockSizes m n) g) p) =
    MvPolynomial.rename
      (Equiv.Perm.sigmaCongrRight
        (blockPermutationGroupOfFnMulEquiv m n g))
      (MvPolynomial.rename (blockIndexOfFnEquivSigma m n) p)
  rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
  apply congrArg (fun f ↦ MvPolynomial.rename f p)
  funext i
  exact blockIndexOfFnEquivSigma_equivariant m n g i

/-- The sigma reindexing induces an equivalence between the recursive fixed
ring and the ordinary fixed ring for independent fiber permutations. -/
noncomputable def recursiveFixedAlgEquivFiberFixed :
    letI := jointBlockPermutationAction R (finBlockSizes m n)
    letI := jointBlockPermutationSMulCommClass R (finBlockSizes m n)
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
    FixedPoints.subalgebra R
        (MvPolynomial (blockIndex (finBlockSizes m n)) R)
        (blockPermutationGroup (finBlockSizes m n)) ≃ₐ[R]
      FixedPoints.subalgebra R
        (MvPolynomial (Σ j : Fin m, Fin (n j)) R)
        (∀ j : Fin m, Equiv.Perm (Fin (n j))) := by
  letI := jointBlockPermutationAction R (finBlockSizes m n)
  letI := jointBlockPermutationSMulCommClass R (finBlockSizes m n)
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
  let e := MvPolynomial.renameEquiv R (blockIndexOfFnEquivSigma m n)
  let G := blockPermutationGroup (finBlockSizes m n)
  let H := ∀ j : Fin m, Equiv.Perm (Fin (n j))
  let A := FixedPoints.subalgebra R
    (MvPolynomial (blockIndex (finBlockSizes m n)) R) G
  let B := FixedPoints.subalgebra R
    (MvPolynomial (Σ j : Fin m, Fin (n j)) R) H
  let forward : A →ₐ[R] B :=
    { toFun := fun p ↦ ⟨e p.1, fun h ↦ by
          let g := (blockPermutationGroupOfFnMulEquiv m n).symm h
          calc
            h • e p.1 = e (g • p.1) := by
              simpa [g, e] using
                (rename_blockAction_eq_fiberAction R m n g p.1).symm
            _ = e p.1 := congrArg e (p.2 g)⟩
      map_one' := by apply Subtype.ext; exact e.map_one
      map_mul' := fun p q ↦ by apply Subtype.ext; exact e.map_mul p.1 q.1
      map_zero' := by apply Subtype.ext; exact e.map_zero
      map_add' := fun p q ↦ by apply Subtype.ext; exact e.map_add p.1 q.1
      commutes' := fun r ↦ by apply Subtype.ext; exact e.commutes r }
  let backward : B →ₐ[R] A :=
    { toFun := fun p ↦ ⟨e.symm p.1, fun g ↦ by
          apply e.injective
          change MvPolynomial.rename (blockIndexOfFnEquivSigma m n)
              (g • e.symm p.1) =
            MvPolynomial.rename (blockIndexOfFnEquivSigma m n) (e.symm p.1)
          rw [rename_blockAction_eq_fiberAction]
          change blockPermutationGroupOfFnMulEquiv m n g • e (e.symm p.1) =
            e (e.symm p.1)
          rw [e.apply_symm_apply]
          exact p.2 (blockPermutationGroupOfFnMulEquiv m n g)⟩
      map_one' := by apply Subtype.ext; exact e.symm.map_one
      map_mul' := fun p q ↦ by apply Subtype.ext; exact e.symm.map_mul p.1 q.1
      map_zero' := by apply Subtype.ext; exact e.symm.map_zero
      map_add' := fun p q ↦ by apply Subtype.ext; exact e.symm.map_add p.1 q.1
      commutes' := fun r ↦ by apply Subtype.ext; exact e.symm.commutes r }
  apply AlgEquiv.ofAlgHom forward backward
  · apply DFunLike.ext _ _
    intro p
    apply Subtype.ext
    exact e.apply_symm_apply p.1
  · apply DFunLike.ext _ _
    intro p
    apply Subtype.ext
    exact e.symm_apply_apply p.1

@[simp]
theorem recursiveFixedAlgEquivFiberFixed_apply_val
    :
    letI := jointBlockPermutationAction R (finBlockSizes m n)
    letI := jointBlockPermutationSMulCommClass R (finBlockSizes m n)
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
    ∀ p : FixedPoints.subalgebra R
        (MvPolynomial (blockIndex (finBlockSizes m n)) R)
        (blockPermutationGroup (finBlockSizes m n)),
      ((recursiveFixedAlgEquivFiberFixed R m n) p).1 =
        MvPolynomial.rename (blockIndexOfFnEquivSigma m n) p.1 := by
  letI := jointBlockPermutationAction R (finBlockSizes m n)
  letI := jointBlockPermutationSMulCommClass R (finBlockSizes m n)
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
  intro p
  rfl

/-- Finite-family form of the blockwise fundamental theorem of symmetric
polynomials. -/
noncomputable def finiteFiberInvariantAlgEquiv :
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
    MvPolynomial (Σ j : Fin m, Fin (n j)) R ≃ₐ[R]
      FixedPoints.subalgebra R
        (MvPolynomial (Σ j : Fin m, Fin (n j)) R)
        (∀ j : Fin m, Equiv.Perm (Fin (n j))) := by
  letI := jointBlockPermutationAction R (finBlockSizes m n)
  letI := jointBlockPermutationSMulCommClass R (finBlockSizes m n)
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
  exact (MvPolynomial.renameEquiv R
      (blockIndexOfFnEquivSigma m n).symm).trans
    ((jointBlockInvariantAlgEquiv R (finBlockSizes m n)).trans
      (recursiveFixedAlgEquivFiberFixed R m n))

/-- On generators, the finite-family invariant equivalence is exactly the
joint elementary-symmetric coefficient map. -/
theorem finiteFiberInvariantAlgEquiv_X
    (i : Σ j : Fin m, Fin (n j)) :
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
    ((finiteFiberInvariantAlgEquiv R m n) (MvPolynomial.X i)).1 =
      blockElementarySymmetric R (Fin m) (fun j ↦ Fin (n j))
        i.1 (i.2 + 1) := by
  letI := jointBlockPermutationAction R (finBlockSizes m n)
  letI := jointBlockPermutationSMulCommClass R (finBlockSizes m n)
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
  change MvPolynomial.rename (blockIndexOfFnEquivSigma m n)
      (((jointBlockInvariantAlgEquiv R (finBlockSizes m n))
        (MvPolynomial.rename (blockIndexOfFnEquivSigma m n).symm
          (MvPolynomial.X i))).1) = _
  rw [MvPolynomial.rename_X, jointBlockInvariantAlgEquiv_X,
    rename_recursiveBlockElementarySymmetric, Equiv.apply_symm_apply]

/-- Scheme form: the affine invariant quotient for a finite family of root
blocks is its joint elementary-symmetric coefficient space. -/
noncomputable def finiteFiberInvariantSchemeIso :
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
    _root_.AlgebraicGeometry.Spec (.of
      (FixedPoints.subalgebra R
        (MvPolynomial (Σ j : Fin m, Fin (n j)) R)
        (∀ j : Fin m, Equiv.Perm (Fin (n j))))) ≅
      _root_.AlgebraicGeometry.Spec
        (.of (MvPolynomial (Σ j : Fin m, Fin (n j)) R)) := by
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
  exact _root_.AlgebraicGeometry.Scheme.Spec.mapIso
    (finiteFiberInvariantAlgEquiv R m n).toRingEquiv.toCommRingCatIso.op

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFiberPermutationInvariants
