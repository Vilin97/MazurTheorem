/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Ideal.Operations
import MazurTorsion.NumberTheory.XOneThirteenMumford

/-!
# The affine coordinate ring of the fixed `X₁(13)` sextic

This file introduces the quadratic `ℚ[X]`-algebra

`A = ℚ[X][Y] / (Y² - f(X))`

for the fixed sextic used by the `X₁(13)` descent.  It supplies the explicit
rank-two basis `{1,Y}`, the hyperelliptic conjugation `Y ↦ -Y`, and the norm
formula

`N(p + qY) = p² - f q²`.

The final section records the two-generator ideal attached to an affine point
and its elementary conjugate-product identity when the ordinate is nonzero.
These are coordinate-ring statements only: no Picard quotient, Jacobian group
law, or divisor-class equivalence is defined here.
-/

namespace MazurTorsion.XOneThirteenPicard

open Ideal Module Polynomial

open XOneThirteenMumford

noncomputable section

/-! ## The quadratic coordinate algebra -/

/-- The monic quadratic relation `Y² - f(X)` over `ℚ[X]`. -/
def relationPolynomial : ℚ[X][X] :=
  X ^ 2 - C sexticPolynomial

/-- The relation is monic in `Y`. -/
theorem relationPolynomial_monic : relationPolynomial.Monic := by
  simpa only [relationPolynomial] using
    (monic_X_pow_sub_C sexticPolynomial (by norm_num : (2 : ℕ) ≠ 0))

/-- The relation has degree two in `Y`. -/
@[simp]
theorem relationPolynomial_natDegree : relationPolynomial.natDegree = 2 := by
  simp only [relationPolynomial, natDegree_X_pow_sub_C]

/-- The affine coordinate ring `ℚ[X,Y]/(Y²-f(X))`. -/
abbrev CoordinateRing : Type :=
  AdjoinRoot relationPolynomial

namespace CoordinateRing

noncomputable instance : Algebra ℚ[X] CoordinateRing := inferInstance

/-- The quotient map from polynomials in `Y` to the coordinate ring. -/
noncomputable abbrev mk : ℚ[X][X] →+* CoordinateRing :=
  AdjoinRoot.mk relationPolynomial

/-- The class of the coordinate `Y`. -/
noncomputable def yCoordinate : CoordinateRing :=
  AdjoinRoot.root relationPolynomial

/-- The defining relation inside the quotient. -/
@[simp]
theorem yCoordinate_sq :
    yCoordinate ^ 2 = algebraMap ℚ[X] CoordinateRing sexticPolynomial := by
  change mk X ^ 2 = mk (C sexticPolynomial)
  rw [← map_pow]
  exact AdjoinRoot.mk_eq_mk.mpr dvd_rfl

/-- The power basis `{1,Y}` of the quadratic coordinate algebra. -/
protected noncomputable def basis : Basis (Fin 2) ℚ[X] CoordinateRing :=
  (AdjoinRoot.powerBasis' relationPolynomial_monic).basis.reindex
    (finCongr relationPolynomial_natDegree)

set_option backward.isDefEq.respectTransparency.types false in
theorem basis_apply (n : Fin 2) :
    CoordinateRing.basis n =
      (AdjoinRoot.powerBasis' relationPolynomial_monic).gen ^ (n : ℕ) := by
  classical
  rw [CoordinateRing.basis, Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]

@[simp]
theorem basis_zero : CoordinateRing.basis 0 = 1 := by
  simpa only [basis_apply] using! pow_zero
    (AdjoinRoot.powerBasis' relationPolynomial_monic).gen

@[simp]
theorem basis_one : CoordinateRing.basis 1 = yCoordinate := by
  simpa only [basis_apply, yCoordinate] using! pow_one
    (AdjoinRoot.powerBasis' relationPolynomial_monic).gen

/-- Uniqueness of the coefficient pair in `p + qY`. -/
theorem smul_basis_eq_zero {p q : ℚ[X]}
    (h : p • (1 : CoordinateRing) + q • yCoordinate = 0) :
    p = 0 ∧ q = 0 := by
  have hlin := Fintype.linearIndependent_iff.mp
    CoordinateRing.basis.linearIndependent ![p, q]
  rw [Fin.sum_univ_succ, basis_zero, Fin.sum_univ_one,
    Fin.succ_zero_eq_one, basis_one] at hlin
  exact ⟨hlin h 0, hlin h 1⟩

/-- Every coordinate-ring element has a unique rank-two presentation. -/
theorem exists_smul_basis_eq (z : CoordinateRing) :
    ∃ p q : ℚ[X], p • (1 : CoordinateRing) + q • yCoordinate = z := by
  have h := CoordinateRing.basis.sum_equivFun z
  rw [Fin.sum_univ_succ, Fin.sum_univ_one, basis_zero,
    Fin.succ_zero_eq_one, basis_one] at h
  exact ⟨_, _, h⟩

/-- Multiplication by `Y` in the rank-two basis. -/
theorem smul_basis_mul_yCoordinate (p q : ℚ[X]) :
    (p • (1 : CoordinateRing) + q • yCoordinate) * yCoordinate =
      (q * sexticPolynomial) • (1 : CoordinateRing) + p • yCoordinate := by
  simp only [Algebra.smul_def, mul_one, add_mul]
  rw [mul_assoc, ← pow_two, yCoordinate_sq, map_mul]
  ring

/-! ## Hyperelliptic conjugation and norm -/

private theorem relationPolynomial_eval_neg_y :
    relationPolynomial.eval₂ (algebraMap ℚ[X] CoordinateRing) (-yCoordinate) = 0 := by
  simp only [relationPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, neg_sq, yCoordinate_sq, sub_self]

/-- Hyperelliptic conjugation, fixing `ℚ[X]` and sending `Y` to `-Y`. -/
noncomputable def conjugation : CoordinateRing →ₐ[ℚ[X]] CoordinateRing :=
  AdjoinRoot.liftAlgHom relationPolynomial (Algebra.ofId ℚ[X] CoordinateRing)
    (-yCoordinate) relationPolynomial_eval_neg_y

@[simp]
theorem conjugation_yCoordinate : conjugation yCoordinate = -yCoordinate := by
  simp only [conjugation, yCoordinate, AdjoinRoot.liftAlgHom_root]

/-- Conjugation in rank-two coordinates. -/
@[simp]
theorem conjugation_smul_basis (p q : ℚ[X]) :
    conjugation (p • (1 : CoordinateRing) + q • yCoordinate) =
      p • (1 : CoordinateRing) - q • yCoordinate := by
  simp only [map_add, map_smul, map_one, conjugation_yCoordinate, smul_neg]
  ring

/-- Hyperelliptic conjugation is involutive. -/
theorem conjugation_involutive (z : CoordinateRing) :
    conjugation (conjugation z) = z := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq z
  rw [conjugation_smul_basis]
  rw [show p • (1 : CoordinateRing) - q • yCoordinate =
    p • (1 : CoordinateRing) + (-q) • yCoordinate by
      rw [sub_eq_add_neg, neg_smul]]
  rw [conjugation_smul_basis]
  simp

/-- Multiplication by the conjugate realizes the quadratic norm in the base
ring. -/
theorem mul_conjugation_smul_basis (p q : ℚ[X]) :
    (p • (1 : CoordinateRing) + q • yCoordinate) *
        conjugation (p • (1 : CoordinateRing) + q • yCoordinate) =
      (p ^ 2 - sexticPolynomial * q ^ 2) • (1 : CoordinateRing) := by
  rw [conjugation_smul_basis]
  simp only [Algebra.smul_def, mul_one]
  calc
    ((algebraMap ℚ[X] CoordinateRing) p +
        (algebraMap ℚ[X] CoordinateRing) q * yCoordinate) *
        ((algebraMap ℚ[X] CoordinateRing) p -
          (algebraMap ℚ[X] CoordinateRing) q * yCoordinate) =
      (algebraMap ℚ[X] CoordinateRing) (p ^ 2) -
        (algebraMap ℚ[X] CoordinateRing) (q ^ 2) * yCoordinate ^ 2 := by
          simp only [map_pow]
          ring
    _ = (algebraMap ℚ[X] CoordinateRing)
        (p ^ 2 - sexticPolynomial * q ^ 2) := by
      rw [yCoordinate_sq]
      simp only [map_sub, map_mul, map_pow]
      ring

/-- The algebra norm in the basis `{1,Y}` is `p²-fq²`. -/
theorem norm_smul_basis (p q : ℚ[X]) :
    Algebra.norm ℚ[X]
        (p • (1 : CoordinateRing) + q • yCoordinate) =
      p ^ 2 - sexticPolynomial * q ^ 2 := by
  simp_rw [Algebra.norm_eq_matrix_det CoordinateRing.basis,
    Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul, basis_zero,
    mul_one, basis_one, smul_basis_mul_yCoordinate, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero,
    ← basis_one, Basis.repr_self_apply, if_pos, one_ne_zero, if_false,
    smul_eq_mul]
  ring

/-- The base-ring norm maps to the product with the hyperelliptic conjugate. -/
theorem algebraMap_norm_eq_mul_conjugation (z : CoordinateRing) :
    algebraMap ℚ[X] CoordinateRing (Algebra.norm ℚ[X] z) =
      z * conjugation z := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq z
  rw [norm_smul_basis, mul_conjugation_smul_basis]
  simp only [Algebra.smul_def, mul_one]

/-! ## Point ideals -/

/-- The class of `X-x` in the coordinate ring. -/
noncomputable def xClass (x : ℚ) : CoordinateRing :=
  algebraMap ℚ[X] CoordinateRing (X - C x)

/-- The class of `Y-y` in the coordinate ring. -/
noncomputable def yClass (y : ℚ) : CoordinateRing :=
  yCoordinate - algebraMap ℚ[X] CoordinateRing (C y)

/-- The principal ideal generated by `X-x`. -/
noncomputable def xIdeal (x : ℚ) : Ideal CoordinateRing :=
  .span {xClass x}

/-- The two-generator ideal `⟨X-x,Y-y⟩`. -/
noncomputable def pointIdeal (x y : ℚ) : Ideal CoordinateRing :=
  .span {xClass x, yClass y}

/-- The elementary affine equation used by the point-ideal certificate. -/
def IsAffinePoint (x y : ℚ) : Prop :=
  y ^ 2 = sexticPolynomial.eval x

/-- Conjugation fixes `X-x`. -/
@[simp]
theorem conjugation_xClass (x : ℚ) :
    conjugation (xClass x) = xClass x := by
  exact conjugation.commutes (X - C x)

/-- Conjugation sends `Y-y` to the negative of `Y+y`. -/
@[simp]
theorem conjugation_yClass (y : ℚ) :
    conjugation (yClass y) = -yClass (-y) := by
  rw [yClass, map_sub, conjugation_yCoordinate,
    conjugation.commutes (C y)]
  simp only [yClass, map_neg]
  ring

/-- The two conjugate `Y`-generators multiply to the base polynomial
`f(X)-y²`. -/
theorem yClass_neg_mul_yClass (y : ℚ) :
    yClass (-y) * yClass y =
      algebraMap ℚ[X] CoordinateRing (sexticPolynomial - C (y ^ 2)) := by
  calc
    yClass (-y) * yClass y =
        yCoordinate ^ 2 -
          (algebraMap ℚ[X] CoordinateRing (C y)) ^ 2 := by
      simp only [yClass, map_neg]
      ring
    _ = algebraMap ℚ[X] CoordinateRing sexticPolynomial -
        algebraMap ℚ[X] CoordinateRing (C (y ^ 2)) := by
      rw [yCoordinate_sq, ← map_pow, C_pow]
    _ = algebraMap ℚ[X] CoordinateRing
        (sexticPolynomial - C (y ^ 2)) := by
      rw [map_sub]

/-- For a point with nonzero ordinate, the conjugate point ideals multiply to
the principal ideal `⟨X-x⟩`.

The `y ≠ 0` hypothesis is the elementary smoothness branch needed to recover
the generator `X-x` from the two mixed products. -/
theorem pointIdeal_neg_mul_pointIdeal
    {x y : ℚ} (hcurve : IsAffinePoint x y) (hy : y ≠ 0) :
    pointIdeal x (-y) * pointIdeal x y = xIdeal x := by
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := sexticPolynomial) (a := x)
  have hlast : yClass (-y) * yClass y =
      xClass x * algebraMap ℚ[X] CoordinateRing g := by
    calc
      yClass (-y) * yClass y =
          algebraMap ℚ[X] CoordinateRing
            (sexticPolynomial - C (y ^ 2)) := yClass_neg_mul_yClass y
      _ = algebraMap ℚ[X] CoordinateRing
          (sexticPolynomial - C (sexticPolynomial.eval x)) := by
            rw [hcurve]
      _ = algebraMap ℚ[X] CoordinateRing ((X - C x) * g) := by
            rw [hg]
      _ = xClass x * algebraMap ℚ[X] CoordinateRing g := by
            rw [map_mul]
            rfl
  rw [pointIdeal, pointIdeal, xIdeal, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change xClass x * xClass x ∈
        (Ideal.span {xClass x} : Ideal CoordinateRing)
      exact (Ideal.span {xClass x}).mul_mem_left (xClass x)
        (Ideal.mem_span_singleton_self (xClass x))
    · change xClass x * yClass y ∈
        (Ideal.span {xClass x} : Ideal CoordinateRing)
      exact (Ideal.span {xClass x}).mul_mem_right (yClass y)
          (Ideal.mem_span_singleton_self (xClass x))
    · change yClass (-y) * xClass x ∈
        (Ideal.span {xClass x} : Ideal CoordinateRing)
      exact (Ideal.span {xClass x}).mul_mem_left (yClass (-y))
        (Ideal.mem_span_singleton_self (xClass x))
    · rw [hlast]
      change xClass x * algebraMap ℚ[X] CoordinateRing g ∈
        (Ideal.span {xClass x} : Ideal CoordinateRing)
      exact (Ideal.span {xClass x}).mul_mem_right
          (algebraMap ℚ[X] CoordinateRing g)
          (Ideal.mem_span_singleton_self (xClass x))
  · rw [Ideal.span_singleton_le_iff_mem]
    let J : Ideal CoordinateRing :=
      .span {xClass x * xClass x, xClass x * yClass y,
        yClass (-y) * xClass x, yClass (-y) * yClass y}
    change xClass x ∈ J
    have hminus : xClass x * yClass y ∈ J := by
      exact Ideal.subset_span (by simp)
    have hplus : yClass (-y) * xClass x ∈ J := by
      exact Ideal.subset_span (by simp)
    have htwo :
        algebraMap ℚ[X] CoordinateRing (C (2 * y)) * xClass x ∈ J := by
      convert J.sub_mem hplus hminus using 1
      simp only [yClass, map_neg]
      rw [show algebraMap ℚ[X] CoordinateRing (C (2 * y)) =
        2 * algebraMap ℚ[X] CoordinateRing (C y) by
          calc
            algebraMap ℚ[X] CoordinateRing (C (2 * y)) =
                algebraMap ℚ[X] CoordinateRing (C 2 * C y) := by
              rw [C_mul]
            _ = algebraMap ℚ[X] CoordinateRing (C 2) *
                algebraMap ℚ[X] CoordinateRing (C y) := by
              rw [map_mul]
            _ = 2 * algebraMap ℚ[X] CoordinateRing (C y) := by
              rw [C_ofNat, map_ofNat]]
      ring
    have hunit :
        algebraMap ℚ[X] CoordinateRing (C ((2 * y)⁻¹)) *
            algebraMap ℚ[X] CoordinateRing (C (2 * y)) = 1 := by
      have h2y : (2 * y : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hy
      rw [← map_mul, ← C_mul, inv_mul_cancel₀ h2y, C_1, map_one]
    have hinv := J.mul_mem_left
      (algebraMap ℚ[X] CoordinateRing (C ((2 * y)⁻¹))) htwo
    simpa only [← mul_assoc, hunit, one_mul] using hinv

/-! ## The affine cusp `(0,1)` -/

private theorem cuspZero_isAffinePoint : IsAffinePoint 0 1 := by
  norm_num [IsAffinePoint, sexticPolynomial]

/-- The coordinate-ring ideal of the affine cusp `(0,1)`. -/
noncomputable def cuspZeroIdeal : Ideal CoordinateRing :=
  pointIdeal 0 1

/-- The concrete cusp ideal satisfies the conjugate-product certificate. -/
theorem cuspZeroIdeal_conjugate_mul :
    pointIdeal 0 (-1) * cuspZeroIdeal = xIdeal 0 := by
  exact pointIdeal_neg_mul_pointIdeal cuspZero_isAffinePoint one_ne_zero

end CoordinateRing

end

end MazurTorsion.XOneThirteenPicard
