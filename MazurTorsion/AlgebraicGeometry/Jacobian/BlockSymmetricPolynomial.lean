/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Symmetric polynomials in one block of variables

After separating a polynomial ring into two blocks of variables, this file
applies the fundamental theorem of symmetric polynomials to the first block
while retaining the second block as coefficients.  The resulting equivalence
is the algebraic induction step needed to compute invariants under products of
symmetric groups.

The named downstream consumer is `SplitSymmetricQuotientChart`: iterating the
equivalence over the fibers of a split-sheet tuple identifies its stabilizer
invariants with the joint elementary-symmetric coefficient chart.
-/

noncomputable section

universe u v w

namespace MazurTorsion.AlgebraicGeometry.Jacobian.BlockSymmetricPolynomial

variable (R : Type u) [CommRing R]
variable (σ : Type v) (τ : Type w)

/-- Extend a permutation of the first block by the identity on the second. -/
def firstBlockPermutation (g : Equiv.Perm σ) : Equiv.Perm (σ ⊕ τ) :=
  Equiv.sumCongr g (Equiv.refl τ)

/-- Separating the two variable blocks intertwines a permutation supported on
the first block with the ordinary coordinate permutation of the outer
polynomial ring. -/
theorem sumAlgEquiv_rename_first (g : Equiv.Perm σ)
    (p : MvPolynomial (σ ⊕ τ) R) :
    MvPolynomial.sumAlgEquiv R σ τ
        (MvPolynomial.rename (firstBlockPermutation σ τ g) p) =
      MvPolynomial.rename g (MvPolynomial.sumAlgEquiv R σ τ p) := by
  apply MvPolynomial.induction_on p
  · intro r
    simp [firstBlockPermutation]
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p i hp
    cases i with
    | inl i =>
        simpa [firstBlockPermutation] using
          congrArg (fun q ↦ q * MvPolynomial.X (g i)) hp
    | inr i =>
        simpa [firstBlockPermutation] using
          congrArg (fun q ↦ q * MvPolynomial.C (MvPolynomial.X i)) hp

/-- Polynomials in two blocks that are symmetric in the first block.  This is
defined by transporting the usual symmetric subalgebra through the standard
equivalence between polynomials in a sum and iterated polynomial rings. -/
noncomputable def leftSymmetricSubalgebra :
    Subalgebra R (MvPolynomial (σ ⊕ τ) R) :=
  ((MvPolynomial.symmetricSubalgebra σ (MvPolynomial τ R)).restrictScalars R).map
    (MvPolynomial.sumAlgEquiv R σ τ).symm.toAlgHom

/-- A polynomial lies in the first-block symmetric subalgebra exactly when it
is fixed by every coordinate permutation supported on that block. -/
theorem mem_leftSymmetricSubalgebra_iff
    (p : MvPolynomial (σ ⊕ τ) R) :
    p ∈ leftSymmetricSubalgebra R σ τ ↔
      ∀ g : Equiv.Perm σ,
        MvPolynomial.rename (firstBlockPermutation σ τ g) p = p := by
  constructor
  · rintro ⟨q, hq, rfl⟩ g
    apply (MvPolynomial.sumAlgEquiv R σ τ).injective
    rw [sumAlgEquiv_rename_first]
    simpa using hq g
  · intro hp
    change p ∈
      ((MvPolynomial.symmetricSubalgebra σ (MvPolynomial τ R)).restrictScalars R).map
        (MvPolynomial.sumAlgEquiv R σ τ).symm.toAlgHom
    rw [Subalgebra.mem_map]
    refine ⟨MvPolynomial.sumAlgEquiv R σ τ p, ?_, ?_⟩
    · intro g
      rw [← sumAlgEquiv_rename_first]
      rw [hp]
    · exact (MvPolynomial.sumAlgEquiv R σ τ).symm_apply_apply p

/-- The fundamental theorem of symmetric polynomials for the first of two
blocks: its elementary-symmetric coefficients, together with the untouched
second-block variables, freely generate all polynomials symmetric in the
first block. -/
noncomputable def leftSymmetricAlgEquiv (n : ℕ) [Fintype σ]
    (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) (MvPolynomial τ R) ≃ₐ[R]
      leftSymmetricSubalgebra R σ τ :=
  ((MvPolynomial.esymmAlgEquiv σ (MvPolynomial τ R) hn).restrictScalars R).trans
    (AlgEquiv.subalgebraMap (MvPolynomial.sumAlgEquiv R σ τ).symm
      ((MvPolynomial.symmetricSubalgebra σ (MvPolynomial τ R)).restrictScalars R))

/-- Under the block equivalence, the `i`-th coefficient variable is the
`(i+1)`-st elementary symmetric polynomial in the first block. -/
theorem leftSymmetricAlgEquiv_X (n : ℕ) [Fintype σ]
    (hn : Fintype.card σ = n) (i : Fin n) :
    ((leftSymmetricAlgEquiv R σ τ n hn)
      (MvPolynomial.X i)).1 =
        (MvPolynomial.sumAlgEquiv R σ τ).symm
          (MvPolynomial.esymm σ (MvPolynomial τ R) (i + 1)) := by
  change
    ((MvPolynomial.sumAlgEquiv R σ τ).symm
      (((MvPolynomial.esymmAlgEquiv σ (MvPolynomial τ R) hn)
        (MvPolynomial.X i)).1)) = _
  simp [MvPolynomial.esymmAlgEquiv, MvPolynomial.esymmAlgHom]

/-- The variables in the untouched block remain coefficient variables under
the block-symmetric equivalence. -/
theorem leftSymmetricAlgEquiv_C_X (n : ℕ) [Fintype σ]
    (hn : Fintype.card σ = n) (j : τ) :
    ((leftSymmetricAlgEquiv R σ τ n hn)
      (MvPolynomial.C (MvPolynomial.X j))).1 =
        MvPolynomial.X (Sum.inr j) := by
  change
    ((MvPolynomial.sumAlgEquiv R σ τ).symm
      (((MvPolynomial.esymmAlgEquiv σ (MvPolynomial τ R) hn)
        (MvPolynomial.C (MvPolynomial.X j))).1)) = _
  rw [← MvPolynomial.algebraMap_eq]
  rw [(MvPolynomial.esymmAlgEquiv σ (MvPolynomial τ R) hn).commutes]
  exact MvPolynomial.sumAlgEquiv_symm_C_X R σ τ j

end MazurTorsion.AlgebraicGeometry.Jacobian.BlockSymmetricPolynomial
