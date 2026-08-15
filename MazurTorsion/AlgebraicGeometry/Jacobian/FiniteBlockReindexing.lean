/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.IteratedBlockInvariants
import MazurTorsion.AlgebraicGeometry.Jacobian.BlockPermutationInvariants
import Mathlib.Data.List.OfFn

/-!
# Reindexing finite block presentations

The recursive list presentation used for iterated block invariants is
canonically reindexed by a sigma type over `Fin m`.  The same recursion
identifies its product of permutation groups with the dependent product of
the permutation groups of the sigma fibers.

The named downstream consumer is `SplitSymmetricQuotientChart`, which takes
the block sizes to be the sheet multiplicities of a split symmetric-power
component.
-/

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteBlockReindexing

open IteratedBlockInvariants

/-- Split a sigma type over `Fin (m + 1)` into its zeroth fiber and the sigma
type over the successor fibers. -/
def finSuccSigmaEquiv {m : ℕ} (n : Fin (m + 1) → ℕ) :
    Fin (n 0) ⊕ (Σ j : Fin m, Fin (n j.succ)) ≃
      Σ j : Fin (m + 1), Fin (n j) where
  toFun
    | Sum.inl i => ⟨0, i⟩
    | Sum.inr x => ⟨x.1.succ, x.2⟩
  invFun x := Fin.cases (fun i ↦ Sum.inl i)
    (fun j i ↦ Sum.inr ⟨j, i⟩) x.1 x.2
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr x => rfl
  right_inv x := by
    rcases x with ⟨j, i⟩
    induction j using Fin.cases with
    | zero => rfl
    | succ j => rfl

/-- Recursive list of the values of a function on `Fin m`, arranged from the
zeroth fiber through the successor fibers. -/
abbrev finBlockSizes : (m : ℕ) → (Fin m → ℕ) → List ℕ
  | 0, _ => []
  | m + 1, n => n 0 :: finBlockSizes m (fun j ↦ n j.succ)

theorem finBlockSizes_eq_ofFn :
    (m : ℕ) → (n : Fin m → ℕ) → finBlockSizes m n = List.ofFn n
  | 0, n => by simp [finBlockSizes]
  | m + 1, n => by
      rw [finBlockSizes, finBlockSizes_eq_ofFn]
      rw [← List.ofFn_cons]
      apply congrArg List.ofFn
      funext j
      exact Fin.cases rfl (fun _ ↦ rfl) j

/-- The nested sum of the recursively listed block sizes is equivalent
to the sigma type of the same fibers over `Fin m`. -/
def blockIndexOfFnEquivSigma :
    (m : ℕ) → (n : Fin m → ℕ) →
      blockIndex (finBlockSizes m n) ≃ Σ j : Fin m, Fin (n j)
  | 0, n => by
      change PEmpty ≃ Σ j : Fin 0, Fin (n j)
      exact Equiv.equivOfIsEmpty _ _
  | m + 1, n =>
      (Equiv.sumCongr (Equiv.refl (Fin (n 0)))
        (blockIndexOfFnEquivSigma m (fun j ↦ n j.succ))).trans
        (finSuccSigmaEquiv n)

/-- The recursive product of the symmetric groups of `finBlockSizes m n` is the
dependent product of the symmetric groups of the corresponding sigma
fibers. -/
def blockPermutationGroupOfFnMulEquiv :
    (m : ℕ) → (n : Fin m → ℕ) →
      blockPermutationGroup (finBlockSizes m n) ≃*
        (∀ j : Fin m, Equiv.Perm (Fin (n j)))
  | 0, _ =>
      { toFun := fun _ j ↦ Fin.elim0 j
        invFun := fun _ ↦ PUnit.unit
        left_inv := fun g ↦ by cases g; rfl
        right_inv := fun h ↦ by funext j; exact Fin.elim0 j
        map_mul' := fun _ _ ↦ by funext j; exact Fin.elim0 j }
  | m + 1, n =>
      { toFun := fun g ↦ Fin.cases g.1
          (blockPermutationGroupOfFnMulEquiv m (fun j ↦ n j.succ) g.2)
        invFun := fun h ↦
          (h 0, (blockPermutationGroupOfFnMulEquiv m
            (fun j ↦ n j.succ)).symm (fun j ↦ h j.succ))
        left_inv := fun g ↦ by
          apply Prod.ext
          · rfl
          · exact (blockPermutationGroupOfFnMulEquiv m
              (fun j ↦ n j.succ)).symm_apply_apply g.2
        right_inv := fun h ↦ by
          funext j
          induction j using Fin.cases with
          | zero => rfl
          | succ i =>
              exact congrFun ((blockPermutationGroupOfFnMulEquiv m
                (fun j ↦ n j.succ)).apply_symm_apply
                  (fun j ↦ h j.succ)) i
        map_mul' := fun g h ↦ by
          funext j
          induction j using Fin.cases with
          | zero => rfl
          | succ i =>
              exact congrFun ((blockPermutationGroupOfFnMulEquiv m
                (fun j ↦ n j.succ)).map_mul g.2 h.2) i }

@[simp]
theorem blockIndexOfFnEquivSigma_inl {m : ℕ}
    (n : Fin (m + 1) → ℕ) (i : Fin (n 0)) :
    blockIndexOfFnEquivSigma (m + 1) n (Sum.inl i) = ⟨0, i⟩ := rfl

@[simp]
theorem blockIndexOfFnEquivSigma_inr {m : ℕ}
    (n : Fin (m + 1) → ℕ)
    (i : blockIndex (finBlockSizes m (fun j ↦ n j.succ))) :
    blockIndexOfFnEquivSigma (m + 1) n (Sum.inr i) =
      ⟨(blockIndexOfFnEquivSigma m (fun j ↦ n j.succ) i).1.succ,
        (blockIndexOfFnEquivSigma m (fun j ↦ n j.succ) i).2⟩ := rfl

/-- Reindexing the recursively defined block elementary-symmetric polynomial
gives the elementary-symmetric polynomial in the corresponding sigma fiber. -/
theorem rename_recursiveBlockElementarySymmetric
    (R : Type*) [CommRing R] :
    (m : ℕ) → (n : Fin m → ℕ) →
      ∀ i : blockIndex (finBlockSizes m n),
      MvPolynomial.rename (blockIndexOfFnEquivSigma m n)
          (IteratedBlockInvariants.blockElementarySymmetric R
            (finBlockSizes m n) i) =
        BlockPermutationInvariants.blockElementarySymmetric R
          (Fin m) (fun j ↦ Fin (n j))
          (blockIndexOfFnEquivSigma m n i).1
          ((blockIndexOfFnEquivSigma m n i).2 + 1)
  | 0, _, i => PEmpty.elim i
  | m + 1, n, Sum.inl i => by
      rw [IteratedBlockInvariants.blockElementarySymmetric,
        MvPolynomial.rename_rename, blockIndexOfFnEquivSigma_inl,
        BlockPermutationInvariants.blockElementarySymmetric]
      apply congrArg (fun f ↦ MvPolynomial.rename f
        (MvPolynomial.esymm (Fin (n 0)) R (i + 1)))
      funext x
      rfl
  | m + 1, n, Sum.inr i => by
      let lift : (Σ j : Fin m, Fin (n j.succ)) →
          (Σ j : Fin (m + 1), Fin (n j)) :=
        fun x ↦ ⟨x.1.succ, x.2⟩
      have hcomp :
          blockIndexOfFnEquivSigma (m + 1) n ∘ Sum.inr =
            lift ∘ blockIndexOfFnEquivSigma m (fun j ↦ n j.succ) := rfl
      rw [IteratedBlockInvariants.blockElementarySymmetric,
        MvPolynomial.rename_rename, hcomp,
        ← MvPolynomial.rename_rename]
      rw [rename_recursiveBlockElementarySymmetric R m
        (fun j ↦ n j.succ) i]
      rw [blockIndexOfFnEquivSigma_inr,
        BlockPermutationInvariants.blockElementarySymmetric,
        BlockPermutationInvariants.blockElementarySymmetric,
        MvPolynomial.rename_rename]
      apply congrArg (fun f ↦ MvPolynomial.rename f
        (MvPolynomial.esymm
          (Fin (n (blockIndexOfFnEquivSigma m
            (fun j ↦ n j.succ) i).1.succ)) R
          ((blockIndexOfFnEquivSigma m
            (fun j ↦ n j.succ) i).2 + 1)))
      funext x
      rfl

@[simp]
theorem blockPermutationGroupOfFnMulEquiv_zero {m : ℕ}
    (n : Fin (m + 1) → ℕ)
    (g : blockPermutationGroup (finBlockSizes (m + 1) n)) :
    blockPermutationGroupOfFnMulEquiv (m + 1) n g 0 = g.1 := rfl

@[simp]
theorem blockPermutationGroupOfFnMulEquiv_succ {m : ℕ}
    (n : Fin (m + 1) → ℕ)
    (g : blockPermutationGroup (finBlockSizes (m + 1) n)) (j : Fin m) :
    blockPermutationGroupOfFnMulEquiv (m + 1) n g j.succ =
      blockPermutationGroupOfFnMulEquiv m (fun j ↦ n j.succ) g.2 j := rfl

@[simp]
theorem blockIndexPermutationHom_cons_inl (n : ℕ) (ns : List ℕ)
    (g : blockPermutationGroup (n :: ns)) (i : Fin n) :
    blockIndexPermutationHom (n :: ns) g (Sum.inl i) = Sum.inl (g.1 i) := rfl

@[simp]
theorem blockIndexPermutationHom_cons_inr (n : ℕ) (ns : List ℕ)
    (g : blockPermutationGroup (n :: ns)) (i : blockIndex ns) :
    blockIndexPermutationHom (n :: ns) g (Sum.inr i) =
      Sum.inr (blockIndexPermutationHom ns g.2 i) := rfl

/-- Reindexing the recursive block variables conjugates their induced
permutation to the ordinary sigma-fiber permutation. -/
theorem blockIndexOfFnEquivSigma_equivariant :
    (m : ℕ) → (n : Fin m → ℕ) →
      ∀ (g : blockPermutationGroup (finBlockSizes m n))
        (i : blockIndex (finBlockSizes m n)),
        blockIndexOfFnEquivSigma m n
            (blockIndexPermutationHom (finBlockSizes m n) g i) =
          Equiv.Perm.sigmaCongrRight
              (blockPermutationGroupOfFnMulEquiv m n g)
            (blockIndexOfFnEquivSigma m n i)
  | 0, _, _, i => by
      change PEmpty at i
      exact PEmpty.elim i
  | m + 1, n, g, i => by
      change Equiv.Perm (Fin (n 0)) ×
        blockPermutationGroup (finBlockSizes m (fun j ↦ n j.succ)) at g
      change Fin (n 0) ⊕
        blockIndex (finBlockSizes m (fun j ↦ n j.succ)) at i
      cases i with
      | inl i =>
          change blockIndexOfFnEquivSigma (m + 1) n (Sum.inl (g.1 i)) =
            Equiv.Perm.sigmaCongrRight
              (blockPermutationGroupOfFnMulEquiv (m + 1) n g)
              (blockIndexOfFnEquivSigma (m + 1) n (Sum.inl i))
          rw [blockIndexOfFnEquivSigma_inl,
            blockIndexOfFnEquivSigma_inl,
            Equiv.sigmaCongrRight_apply]
          change (⟨0, g.1 i⟩ : Σ j : Fin (m + 1), Fin (n j)) = ⟨0, g.1 i⟩
          rfl
      | inr i =>
          change blockIndexOfFnEquivSigma (m + 1) n
              (Sum.inr (blockIndexPermutationHom
                (finBlockSizes m (fun j ↦ n j.succ)) g.2 i)) =
            Equiv.Perm.sigmaCongrRight
              (blockPermutationGroupOfFnMulEquiv (m + 1) n g)
              (blockIndexOfFnEquivSigma (m + 1) n (Sum.inr i))
          rw [blockIndexOfFnEquivSigma_inr,
            blockIndexOfFnEquivSigma_inr,
            Equiv.sigmaCongrRight_apply]
          change
            (fun x : (Σ j : Fin m, Fin (n j.succ)) ↦
                (⟨x.1.succ, x.2⟩ : Σ j : Fin (m + 1), Fin (n j)))
              (blockIndexOfFnEquivSigma m (fun j ↦ n j.succ)
                (blockIndexPermutationHom
                  (finBlockSizes m (fun j ↦ n j.succ)) g.2 i)) =
            (fun x : (Σ j : Fin m, Fin (n j.succ)) ↦
                (⟨x.1.succ, x.2⟩ : Σ j : Fin (m + 1), Fin (n j)))
              (Equiv.Perm.sigmaCongrRight
                (blockPermutationGroupOfFnMulEquiv m
                  (fun j ↦ n j.succ) g.2)
                (blockIndexOfFnEquivSigma m (fun j ↦ n j.succ) i))
          exact congrArg
            (fun x : (Σ j : Fin m, Fin (n j.succ)) ↦
              (⟨x.1.succ, x.2⟩ : Σ j : Fin (m + 1), Fin (n j)))
            (blockIndexOfFnEquivSigma_equivariant m
              (fun j ↦ n j.succ) g.2 i)

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteBlockReindexing
