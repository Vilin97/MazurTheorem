/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPicardClass
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Evaluation at rational affine points of `X₁(13)`

For every rational affine point `(x,y)` on the fixed sextic, this file
constructs the evaluation homomorphism from the affine coordinate ring to
`ℚ`.  Its kernel is proved to be exactly the two-generator point ideal
`⟨X-x,Y-y⟩`.  Consequently that ideal is maximal and its residue field is
explicitly ring-equivalent to `ℚ`.

The final results recover both rational coordinates from the point ideal and
package injectivity of the map from rational affine points to ideals.  These
are affine coordinate-ring statements; no identification with the
degree-zero Picard group of the projective curve is asserted.
-/

namespace MazurTorsion.XOneThirteenPicard

open Ideal Polynomial

open XOneThirteenMumford

noncomputable section

namespace CoordinateRing

private theorem relationPolynomial_eval_affinePoint
    {x y : ℚ} (hcurve : IsAffinePoint x y) :
    relationPolynomial.eval₂ (Polynomial.evalRingHom x) y = 0 := by
  simp only [relationPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C]
  rw [show Polynomial.evalRingHom x sexticPolynomial =
    sexticPolynomial.eval x by rfl, ← hcurve]
  ring

/-- Evaluation of a coordinate-ring function at a rational affine point. -/
def pointEval (x y : ℚ) (hcurve : IsAffinePoint x y) :
    CoordinateRing →+* ℚ :=
  AdjoinRoot.lift (Polynomial.evalRingHom x) y
    (relationPolynomial_eval_affinePoint hcurve)

@[simp] theorem pointEval_yCoordinate
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    pointEval x y hcurve yCoordinate = y := by
  exact AdjoinRoot.lift_root (relationPolynomial_eval_affinePoint hcurve)

@[simp] theorem pointEval_algebraMap
    (x y : ℚ) (hcurve : IsAffinePoint x y) (p : ℚ[X]) :
    pointEval x y hcurve (algebraMap ℚ[X] CoordinateRing p) = p.eval x := by
  exact AdjoinRoot.lift_of (relationPolynomial_eval_affinePoint hcurve)

@[simp] theorem pointEval_of
    (x y : ℚ) (hcurve : IsAffinePoint x y) (p : ℚ[X]) :
    pointEval x y hcurve (AdjoinRoot.of relationPolynomial p) = p.eval x := by
  exact AdjoinRoot.lift_of (relationPolynomial_eval_affinePoint hcurve)

@[simp] theorem pointEval_xClass
    (x y : ℚ) (hcurve : IsAffinePoint x y) (a : ℚ) :
    pointEval x y hcurve (xClass a) = x - a := by
  rw [xClass, pointEval_algebraMap]
  simp

@[simp] theorem pointEval_yClass
    (x y : ℚ) (hcurve : IsAffinePoint x y) (b : ℚ) :
    pointEval x y hcurve (yClass b) = y - b := by
  rw [yClass, map_sub, pointEval_yCoordinate, pointEval_algebraMap]
  simp

@[simp] theorem pointEval_smul_basis
    (x y : ℚ) (hcurve : IsAffinePoint x y) (p q : ℚ[X]) :
    pointEval x y hcurve
        (p • (1 : CoordinateRing) + q • yCoordinate) =
      p.eval x + q.eval x * y := by
  simp only [Algebra.smul_def, map_add, map_mul,
    pointEval_yCoordinate, mul_one]
  rw [pointEval_algebraMap, pointEval_algebraMap]

/-- Both defining generators of the point ideal vanish under evaluation. -/
theorem pointIdeal_le_pointEval_ker
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    pointIdeal x y ≤ RingHom.ker (pointEval x y hcurve) := by
  rw [pointIdeal, Ideal.span_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact RingHom.mem_ker.mpr (by simp)
  · exact RingHom.mem_ker.mpr (by simp)

private theorem algebraMap_sub_eval_mem_pointIdeal
    (x y : ℚ) (p : ℚ[X]) :
    algebraMap ℚ[X] CoordinateRing p -
        algebraMap ℚ[X] CoordinateRing (C (p.eval x)) ∈
      pointIdeal x y := by
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := p) (a := x)
  rw [← map_sub, hg, map_mul]
  change xClass x * algebraMap ℚ[X] CoordinateRing g ∈ pointIdeal x y
  exact (pointIdeal x y).mul_mem_right _
    (Ideal.subset_span (by simp))

private theorem smul_sub_eval_mem_pointIdeal
    (x y : ℚ) (q : ℚ[X]) :
    (algebraMap ℚ[X] CoordinateRing q -
        algebraMap ℚ[X] CoordinateRing (C (q.eval x))) * yCoordinate ∈
      pointIdeal x y :=
  (pointIdeal x y).mul_mem_right yCoordinate
    (algebraMap_sub_eval_mem_pointIdeal x y q)

private theorem eval_mul_yClass_mem_pointIdeal
    (x y : ℚ) (q : ℚ[X]) :
    algebraMap ℚ[X] CoordinateRing (C (q.eval x)) * yClass y ∈
      pointIdeal x y :=
  (pointIdeal x y).mul_mem_left
    (algebraMap ℚ[X] CoordinateRing (C (q.eval x)))
    (Ideal.subset_span (by simp))

/-- Every function vanishing at the rational point belongs to its point
ideal. -/
theorem pointEval_ker_le_pointIdeal
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    RingHom.ker (pointEval x y hcurve) ≤ pointIdeal x y := by
  intro z hz
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq z
  have heval : p.eval x + q.eval x * y = 0 := by
    simpa only [pointEval_smul_basis] using RingHom.mem_ker.mp hz
  have hmem := (pointIdeal x y).add_mem
    (algebraMap_sub_eval_mem_pointIdeal x y p)
    ((pointIdeal x y).add_mem
      (smul_sub_eval_mem_pointIdeal x y q)
      (eval_mul_yClass_mem_pointIdeal x y q))
  have hconstant :
      algebraMap ℚ[X] CoordinateRing (C (p.eval x)) +
          algebraMap ℚ[X] CoordinateRing (C (q.eval x)) *
            algebraMap ℚ[X] CoordinateRing (C y) = 0 := by
    calc
      algebraMap ℚ[X] CoordinateRing (C (p.eval x)) +
            algebraMap ℚ[X] CoordinateRing (C (q.eval x)) *
              algebraMap ℚ[X] CoordinateRing (C y) =
          algebraMap ℚ[X] CoordinateRing
            (C (p.eval x) + C (q.eval x) * C y) := by
              rw [map_add, map_mul]
      _ = algebraMap ℚ[X] CoordinateRing
          (C (p.eval x + q.eval x * y)) := by rw [C_add, C_mul]
      _ = 0 := by rw [heval, C_0, map_zero]
  have hdecomp :
      (algebraMap ℚ[X] CoordinateRing p -
          algebraMap ℚ[X] CoordinateRing (C (p.eval x))) +
        ((algebraMap ℚ[X] CoordinateRing q -
            algebraMap ℚ[X] CoordinateRing (C (q.eval x))) * yCoordinate +
          algebraMap ℚ[X] CoordinateRing (C (q.eval x)) * yClass y) =
        algebraMap ℚ[X] CoordinateRing p +
          algebraMap ℚ[X] CoordinateRing q * yCoordinate := by
    rw [yClass]
    calc
      _ = algebraMap ℚ[X] CoordinateRing p +
          algebraMap ℚ[X] CoordinateRing q * yCoordinate -
            (algebraMap ℚ[X] CoordinateRing (C (p.eval x)) +
              algebraMap ℚ[X] CoordinateRing (C (q.eval x)) *
                algebraMap ℚ[X] CoordinateRing (C y)) := by ring
      _ = _ := by rw [hconstant, sub_zero]
  simp only [Algebra.smul_def, mul_one]
  rw [← hdecomp]
  exact hmem

/-- The kernel of rational-point evaluation is exactly `⟨X-x,Y-y⟩`. -/
theorem pointEval_ker
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    RingHom.ker (pointEval x y hcurve) = pointIdeal x y :=
  le_antisymm (pointEval_ker_le_pointIdeal x y hcurve)
    (pointIdeal_le_pointEval_ker x y hcurve)

/-- Rational-point evaluation is onto because it fixes constants. -/
theorem pointEval_surjective
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    Function.Surjective (pointEval x y hcurve) := by
  intro a
  refine ⟨algebraMap ℚ[X] CoordinateRing (C a), ?_⟩
  rw [pointEval_algebraMap]
  simp

/-- A rational affine point cuts out a maximal ideal. -/
theorem pointIdeal_isMaximal
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    (pointIdeal x y).IsMaximal := by
  rw [← pointEval_ker x y hcurve]
  exact RingHom.ker_isMaximal_of_surjective (pointEval x y hcurve)
    (pointEval_surjective x y hcurve)

/-- The residue field at a rational affine point is explicitly `ℚ`. -/
def pointIdealQuotientEquiv
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    CoordinateRing ⧸ pointIdeal x y ≃+* ℚ :=
  (Ideal.quotEquivOfEq (pointEval_ker x y hcurve).symm).trans
    ((pointEval x y hcurve).quotientKerEquivOfSurjective
      (pointEval_surjective x y hcurve))

@[simp] theorem pointIdealQuotientEquiv_mk
    (x y : ℚ) (hcurve : IsAffinePoint x y) (z : CoordinateRing) :
    pointIdealQuotientEquiv x y hcurve
        (Ideal.Quotient.mk (pointIdeal x y) z) =
      pointEval x y hcurve z := by
  rfl

/-- Equality of rational point ideals recovers both affine coordinates. -/
theorem pointIdeal_eq_iff
    {x y x' y' : ℚ}
    (_hcurve : IsAffinePoint x y) (hcurve' : IsAffinePoint x' y') :
    pointIdeal x y = pointIdeal x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro hideal
    have hxmem : xClass x ∈ pointIdeal x' y' := by
      rw [← hideal]
      exact Ideal.subset_span (by simp)
    have hymem : yClass y ∈ pointIdeal x' y' := by
      rw [← hideal]
      exact Ideal.subset_span (by simp)
    have hxzero : x' - x = 0 := by
      rw [← pointEval_xClass x' y' hcurve' x]
      exact RingHom.mem_ker.mp
        (pointIdeal_le_pointEval_ker x' y' hcurve' hxmem)
    have hyzero : y' - y = 0 := by
      rw [← pointEval_yClass x' y' hcurve' y]
      exact RingHom.mem_ker.mp
        (pointIdeal_le_pointEval_ker x' y' hcurve' hymem)
    exact ⟨sub_eq_zero.mp hxzero |>.symm, sub_eq_zero.mp hyzero |>.symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Rational affine points on the fixed model. -/
abbrev RationalAffinePoint :=
  {p : ℚ × ℚ // IsAffinePoint p.1 p.2}

/-- The maximal ideal attached to a rational affine point. -/
def rationalAffinePointIdeal (p : RationalAffinePoint) : Ideal CoordinateRing :=
  pointIdeal p.1.1 p.1.2

/-- The point-to-ideal map remembers the complete rational affine point. -/
theorem rationalAffinePointIdeal_injective :
    Function.Injective rationalAffinePointIdeal := by
  rintro ⟨⟨x, y⟩, hcurve⟩ ⟨⟨x', y'⟩, hcurve'⟩ hideal
  have hxy := (pointIdeal_eq_iff hcurve hcurve').mp hideal
  cases hxy.1
  cases hxy.2
  rfl

end CoordinateRing

end

end MazurTorsion.XOneThirteenPicard
