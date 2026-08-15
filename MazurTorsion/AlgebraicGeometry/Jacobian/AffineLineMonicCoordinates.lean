/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Data.Fin.Rev
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSymmetricPower

/-!
# Monic coefficient coordinates on symmetric powers of the affine line

The elementary-symmetric coordinates on `Symⁿ(A¹)` occur in increasing
degree, whereas `Polynomial.freeMonic` stores the coefficient of `X^i` in
variable `i`.  This file supplies the signed reversal between those two
coordinate conventions.  It is characteristic-free: the signs are units
even in characteristic two.

The named downstream consumer is `UniversalEffectiveDivisorDescent`.  It
uses these coordinates to compare the pointed symmetric-power incidence map
with the universal monic-root family.
-/

noncomputable section

open CategoryTheory
open Polynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineMonicCoordinates

variable (R : Type*) [CommRing R] (n : ℕ)

/-- Reindex monic coefficients in reverse order and insert the signs from
Vieta's formula. -/
noncomputable def signedReverseHom :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval fun i ↦
    MvPolynomial.C ((-1 : R) ^ (n - (i : ℕ))) *
      MvPolynomial.X i.rev

/-- The inverse signed reversal. -/
noncomputable def signedReverseInvHom :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval fun i ↦
    MvPolynomial.C ((-1 : R) ^ ((i : ℕ) + 1)) *
      MvPolynomial.X i.rev

private theorem rev_val_add_one (i : Fin n) :
    (i.rev : ℕ) + 1 = n - (i : ℕ) := by
  simp only [Fin.val_rev]
  omega

/-- Signed reversal is an algebra automorphism of the coefficient ring. -/
noncomputable def signedReverseEquiv :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R := by
  apply AlgEquiv.ofAlgHom (signedReverseHom R n) (signedReverseInvHom R n)
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, signedReverseHom, signedReverseInvHom,
      map_mul, MvPolynomial.aeval_def, MvPolynomial.eval₂_X,
      Fin.rev_rev, Fin.val_rev, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq, map_pow, map_neg, map_one]
    have hi : (i : ℕ) + 1 ≤ n := i.isLt
    have he : n - (n - ((i : ℕ) + 1)) = (i : ℕ) + 1 := by omega
    rw [he, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, signedReverseHom, signedReverseInvHom,
      map_mul, MvPolynomial.aeval_def, MvPolynomial.eval₂_X,
      Fin.rev_rev, Fin.val_rev, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq, map_pow, map_neg, map_one]
    have hi : (i : ℕ) + 1 ≤ n := i.isLt
    have he : n - ((i : ℕ) + 1) + 1 = n - (i : ℕ) := by omega
    rw [he, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

/-- Monic polynomial coefficients identify the affine symmetric quotient
with the fixed ring of ordered roots. -/
noncomputable def monicCoefficientEquivFixedPoints :
    letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
    letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
    MvPolynomial (Fin n) R ≃ₐ[R]
      FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
        (Equiv.Perm (Fin n)) := by
  letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
  letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
  exact (signedReverseEquiv R n).trans
    (AffineLineSymmetricPower.coefficientEquivFixedPoints R n)

/-- In monic coordinates, variable `i` is the signed elementary symmetric
function of degree `n - i`, exactly as in Vieta's formula. -/
theorem monicCoefficientEquivFixedPoints_X (i : Fin n) :
    letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
    letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
    ((monicCoefficientEquivFixedPoints R n) (MvPolynomial.X i)).1 =
      MvPolynomial.C ((-1 : R) ^ (n - (i : ℕ))) *
        MvPolynomial.esymm (Fin n) R (n - (i : ℕ)) := by
  letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
  letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
  change
    ((AffineLineSymmetricPower.coefficientEquivFixedPoints R n)
      (signedReverseEquiv R n (MvPolynomial.X i))).1 = _
  rw [show signedReverseEquiv R n (MvPolynomial.X i) =
      MvPolynomial.C ((-1 : R) ^ (n - (i : ℕ))) *
        MvPolynomial.X i.rev by
    change signedReverseHom R n (MvPolynomial.X i) = _
    simp [signedReverseHom]]
  rw [map_mul]
  change
    ((AffineLineSymmetricPower.coefficientEquivFixedPoints R n)
        (MvPolynomial.C ((-1 : R) ^ (n - (i : ℕ))))).1 *
      ((AffineLineSymmetricPower.coefficientEquivFixedPoints R n)
        (MvPolynomial.X i.rev)).1 = _
  rw [AffineLineSymmetricPower.coefficientEquivFixedPoints_C,
    AffineLineSymmetricPower.coefficientEquivFixedPoints_X]
  congr 2
  simp only [Fin.val_rev]
  omega

/-- The inclusion of monic coefficient functions into the full ordered-root
polynomial ring. -/
noncomputable def monicCoefficientToRoots :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R := by
  letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
  letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
  exact (FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))).val.comp
      (monicCoefficientEquivFixedPoints R n).toAlgHom

/-- Formula for each monic coefficient as a symmetric function of the
ordered roots. -/
theorem monicCoefficientToRoots_X (i : Fin n) :
    monicCoefficientToRoots R n (MvPolynomial.X i) =
      MvPolynomial.C ((-1 : R) ^ (n - (i : ℕ))) *
        MvPolynomial.esymm (Fin n) R (n - (i : ℕ)) := by
  letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
  letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
  exact monicCoefficientEquivFixedPoints_X R n i

/-- The multiset of coordinate functions on ordered-root space. -/
noncomputable abbrev orderedRoots :
    Multiset (MvPolynomial (Fin n) R) :=
  Finset.univ.val.map MvPolynomial.X

/-- The monic polynomial whose roots are the ordered coordinates. -/
noncomputable def orderedRootPolynomial :
    Polynomial (MvPolynomial (Fin n) R) :=
  ((orderedRoots R n).map fun r ↦ Polynomial.X - Polynomial.C r).prod

theorem orderedRoots_card : Multiset.card (orderedRoots R n) = n := by
  simp [orderedRoots]

theorem orderedRoots_esymm (j : ℕ) :
    (orderedRoots R n).esymm j =
      MvPolynomial.esymm (Fin n) R j :=
  congrFun (MvPolynomial.esymm_eq_multiset_esymm (Fin n) R).symm j

/-- The ordered-root polynomial is monic. -/
theorem orderedRootPolynomial_monic :
    (orderedRootPolynomial R n).Monic :=
  Polynomial.monic_multisetProd_X_sub_C (orderedRoots R n)

variable [Nontrivial R]

/-- The ordered-root polynomial has degree `n`. -/
theorem orderedRootPolynomial_natDegree :
    (orderedRootPolynomial R n).natDegree = n := by
  have hmonic : ∀ p ∈
      ((orderedRoots R n).map fun r ↦ Polynomial.X - Polynomial.C r),
      p.Monic := by
    intro p hp
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hp
    exact Polynomial.monic_X_sub_C r
  rw [orderedRootPolynomial,
    Polynomial.natDegree_multiset_prod_of_monic _ hmonic]
  have hmap :
      Multiset.map Polynomial.natDegree
          (Multiset.map (fun r ↦ Polynomial.X - Polynomial.C r)
            (orderedRoots R n)) =
        Multiset.map (fun _ ↦ 1) (orderedRoots R n) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r hr
    exact Polynomial.natDegree_X_sub_C r
  rw [hmap]
  calc
    (Multiset.map (fun _ ↦ 1) (orderedRoots R n)).sum =
        Multiset.card (orderedRoots R n) := by
      induction (orderedRoots R n) using Multiset.induction_on with
      | empty => rfl
      | cons a s hs => simp only [Multiset.map_cons, Multiset.sum_cons,
          Multiset.card_cons, hs, Nat.add_comm]
    _ = n := orderedRoots_card R n

/-- Mapping the universal monic polynomial to ordered-root functions gives
the product of its linear root factors. -/
theorem freeMonic_map_monicCoefficientToRoots :
    (Polynomial.freeMonic R n).map
        (monicCoefficientToRoots R n).toRingHom =
      orderedRootPolynomial R n := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic,
      dif_pos hk]
    change monicCoefficientToRoots R n (MvPolynomial.X ⟨k, hk⟩) = _
    rw [monicCoefficientToRoots_X]
    rw [orderedRootPolynomial,
      Multiset.prod_X_sub_C_coeff (orderedRoots R n)]
    · rw [orderedRoots_card, orderedRoots_esymm]
      simp
    · rw [orderedRoots_card]
      exact hk.le
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    by_cases hkn : k = n
    · subst k
      rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic]
      simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, map_one]
      calc
        1 = (orderedRootPolynomial R n).coeff
            (orderedRootPolynomial R n).natDegree :=
          (orderedRootPolynomial_monic R n).coeff_natDegree.symm
        _ = (orderedRootPolynomial R n).coeff n := congrArg
          (orderedRootPolynomial R n).coeff
          (orderedRootPolynomial_natDegree R n)
    · have hgt : n < k := lt_of_le_of_ne hnk (Ne.symm hkn)
      rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic,
        dif_neg hk, if_neg hkn, map_zero]
      have hdeg : (orderedRootPolynomial R n).natDegree < k := by
        rw [orderedRootPolynomial_natDegree]
        exact hgt
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt
        hdeg).symm

/-- The affine symmetric quotient written in monic coefficient coordinates. -/
noncomputable def invariantRootSchemeIsoMonicCoefficientSpace :
    AffineLineSymmetricPower.invariantRootScheme R n ≅
      Spec (CommRingCat.of (MvPolynomial (Fin n) R)) := by
  letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
  letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
  exact Scheme.Spec.mapIso
    (monicCoefficientEquivFixedPoints R n).toRingEquiv.toCommRingCatIso.op

omit [Nontrivial R] in
/-- After the quotient target is put in monic coordinates, the ordered-root
projection is induced by the map sending universal coefficients to their
signed elementary-symmetric functions. -/
theorem coordinateQuotientProjection_comp_monicCoefficientIso :
    AffineLineSymmetricPower.coordinateQuotientProjection R n ≫
        (invariantRootSchemeIsoMonicCoefficientSpace R n).hom =
      Spec.map (CommRingCat.ofHom
        (monicCoefficientToRoots R n).toRingHom) := by
  letI := AffineLineSymmetricPower.coordinatePermutationAction R (Fin n)
  letI := AffineLineSymmetricPower.coordinatePermutationSMulCommClass R (Fin n)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  rfl

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineMonicCoordinates
