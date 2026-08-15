/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFiberPermutationInvariants
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineMonicCoordinates

/-!
# Monic coordinates for a finite family of root blocks

Apply Vieta's signed coefficient reversal independently in every block of a
finite sigma-shaped polynomial ring.  Composing this automorphism with the
finite-family fundamental theorem identifies monic coefficient variables
with the signed elementary-symmetric functions of the ordered roots in the
same fiber.

The named downstream consumer is `SplitSymmetricQuotientChart`, where the
blocks are the sheet multiplicities of a split symmetric-power component.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFiberMonicCoordinates

open BlockPermutationInvariants
open FiniteFiberPermutationInvariants

variable (R : Type u) [CommRing R]
variable (m : ℕ) (n : Fin m → ℕ)

/-- Reverse the coefficient order and insert Vieta signs independently in
every finite fiber. -/
noncomputable def signedReverseHom :
    MvPolynomial (Σ j : Fin m, Fin (n j)) R →ₐ[R]
      MvPolynomial (Σ j : Fin m, Fin (n j)) R :=
  MvPolynomial.aeval fun x ↦
    MvPolynomial.C ((-1 : R) ^ (n x.1 - (x.2 : ℕ))) *
      MvPolynomial.X ⟨x.1, x.2.rev⟩

/-- The inverse signed reversal on a finite family of coefficient blocks. -/
noncomputable def signedReverseInvHom :
    MvPolynomial (Σ j : Fin m, Fin (n j)) R →ₐ[R]
      MvPolynomial (Σ j : Fin m, Fin (n j)) R :=
  MvPolynomial.aeval fun x ↦
    MvPolynomial.C ((-1 : R) ^ ((x.2 : ℕ) + 1)) *
      MvPolynomial.X ⟨x.1, x.2.rev⟩

/-- Fiberwise signed reversal is an algebra automorphism. -/
noncomputable def signedReverseEquiv :
    MvPolynomial (Σ j : Fin m, Fin (n j)) R ≃ₐ[R]
      MvPolynomial (Σ j : Fin m, Fin (n j)) R := by
  apply AlgEquiv.ofAlgHom (signedReverseHom R m n)
    (signedReverseInvHom R m n)
  · apply MvPolynomial.algHom_ext
    intro x
    rcases x with ⟨j, i⟩
    simp only [AlgHom.comp_apply, signedReverseHom, signedReverseInvHom,
      map_mul, MvPolynomial.aeval_def, MvPolynomial.eval₂_X,
      Fin.rev_rev, Fin.val_rev, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq, map_pow, map_neg, map_one]
    have hi : (i : ℕ) + 1 ≤ n j := i.isLt
    have he : n j - (n j - ((i : ℕ) + 1)) = (i : ℕ) + 1 := by omega
    rw [he, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  · apply MvPolynomial.algHom_ext
    intro x
    rcases x with ⟨j, i⟩
    simp only [AlgHom.comp_apply, signedReverseHom, signedReverseInvHom,
      map_mul, MvPolynomial.aeval_def, MvPolynomial.eval₂_X,
      Fin.rev_rev, Fin.val_rev, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq, map_pow, map_neg, map_one]
    have hi : (i : ℕ) + 1 ≤ n j := i.isLt
    have he : n j - ((i : ℕ) + 1) + 1 = n j - (i : ℕ) := by omega
    rw [he, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

/-- Monic coefficients identify the joint coefficient space with the fixed
ring of independent permutations in every root fiber. -/
noncomputable def monicCoefficientInvariantAlgEquiv :
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
    MvPolynomial (Σ j : Fin m, Fin (n j)) R ≃ₐ[R]
      FixedPoints.subalgebra R
        (MvPolynomial (Σ j : Fin m, Fin (n j)) R)
        (∀ j : Fin m, Equiv.Perm (Fin (n j))) := by
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
  exact (signedReverseEquiv R m n).trans
    (finiteFiberInvariantAlgEquiv R m n)

/-- A monic coefficient variable is the Vieta-signed elementary-symmetric
function of complementary degree in its own root block. -/
theorem monicCoefficientInvariantAlgEquiv_X
    (x : Σ j : Fin m, Fin (n j)) :
    letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
    letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
    ((monicCoefficientInvariantAlgEquiv R m n) (MvPolynomial.X x)).1 =
      MvPolynomial.C ((-1 : R) ^ (n x.1 - (x.2 : ℕ))) *
        blockElementarySymmetric R (Fin m) (fun j ↦ Fin (n j))
          x.1 (n x.1 - (x.2 : ℕ)) := by
  letI := fiberPermutationAction R (Fin m) (fun j ↦ Fin (n j))
  letI := fiberPermutationSMulCommClass R (Fin m) (fun j ↦ Fin (n j))
  change ((finiteFiberInvariantAlgEquiv R m n)
    (signedReverseEquiv R m n (MvPolynomial.X x))).1 = _
  rw [show signedReverseEquiv R m n (MvPolynomial.X x) =
      MvPolynomial.C ((-1 : R) ^ (n x.1 - (x.2 : ℕ))) *
        MvPolynomial.X ⟨x.1, x.2.rev⟩ by
    change signedReverseHom R m n (MvPolynomial.X x) = _
    simp [signedReverseHom]]
  rw [map_mul]
  change (((finiteFiberInvariantAlgEquiv R m n)
      (MvPolynomial.C ((-1 : R) ^ (n x.1 - (x.2 : ℕ))))).1) *
      ((finiteFiberInvariantAlgEquiv R m n)
        (MvPolynomial.X ⟨x.1, x.2.rev⟩)).1 = _
  rw [show ((finiteFiberInvariantAlgEquiv R m n)
      (MvPolynomial.C ((-1 : R) ^ (n x.1 - (x.2 : ℕ))))).1 =
        MvPolynomial.C ((-1 : R) ^ (n x.1 - (x.2 : ℕ))) by
    rw [← MvPolynomial.algebraMap_eq]
    exact congrArg Subtype.val
      ((finiteFiberInvariantAlgEquiv R m n).commutes
        ((-1 : R) ^ (n x.1 - (x.2 : ℕ))))]
  rw [finiteFiberInvariantAlgEquiv_X]
  congr 2
  simp only [Fin.val_rev]
  omega

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFiberMonicCoordinates
