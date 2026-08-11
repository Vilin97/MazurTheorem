/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenHaoQuadraticShift

/-!
# Triviality of the affine cusp classes on `X₁(13)`

The three explicit Hao principal divisors give the relations

`A B = 1`, `A³ C = 1`, and `A C⁴ = 1`,

where `A`, `B`, and `C` are the affine Picard classes of `(0,1)`,
`(-1,1)`, and `(-1,-1)`.  Hyperelliptic conjugation also gives `C B = 1`.
Consequently `C=A`, while the two shifted Hao relations say both `A⁴=1`
and `A⁵=1`; hence all three classes are trivial.  The conjugate of `(0,1)`
is then trivial as well.

This is an explicit affine class-group consequence of the checked ideal
factorizations.  It does not assume a projective Jacobian group law.
-/

namespace MazurTorsion.XOneThirteenHaoCuspClasses

open XOneThirteenPicard
open XOneThirteenPicard.CoordinateRing
open XOneThirteenMumford
open XOneThirteenHaoFunctions
open XOneThirteenHaoShift
open XOneThirteenHaoQuadraticShift

noncomputable section

/-- The two cusps above `X=-1` give inverse affine Picard classes. -/
theorem cuspNegOneConjugateClass_mul_cuspNegOneClass :
    cuspNegOneConjugateClass * cuspNegOneClass = 1 := by
  have hcurve : IsAffinePoint (-1) 1 := by
    norm_num [IsAffinePoint, sexticPolynomial]
  simpa only [cuspNegOneConjugateClass, cuspNegOneClass] using
    (pointClass_neg_mul hcurve one_ne_zero)

/-- The classes of `(0,1)` and `(-1,-1)` coincide. -/
theorem cuspNegOneConjugateClass_eq_cuspZeroClass :
    cuspNegOneConjugateClass = cuspZeroClass := by
  apply mul_right_cancel (b := cuspNegOneClass)
  rw [cuspNegOneConjugateClass_mul_cuspNegOneClass,
    cuspZeroClass_mul_cuspNegOneClass_eq_one]

/-- The first shifted Hao divisor gives fourth-power triviality of the
class of `(0,1)`. -/
theorem cuspZeroClass_pow_four : cuspZeroClass ^ 4 = 1 := by
  simpa only [cuspNegOneConjugateClass_eq_cuspZeroClass, pow_succ] using
    cuspZeroClass_cube_mul_cuspNegOneConjugateClass

/-- The quadratically shifted Hao divisor gives fifth-power triviality of
the class of `(0,1)`. -/
theorem cuspZeroClass_pow_five : cuspZeroClass ^ 5 = 1 := by
  simpa only [cuspNegOneConjugateClass_eq_cuspZeroClass, pow_succ'] using
    cuspZeroClass_mul_cuspNegOneConjugateClass_fourth

/-- The affine Picard class of the cusp `(0,1)` is trivial. -/
theorem cuspZeroClass_eq_one : cuspZeroClass = 1 := by
  calc
    cuspZeroClass = 1 * cuspZeroClass := by simp
    _ = cuspZeroClass ^ 4 * cuspZeroClass := by
      rw [cuspZeroClass_pow_four]
    _ = cuspZeroClass ^ 5 := (pow_succ cuspZeroClass 4).symm
    _ = 1 := cuspZeroClass_pow_five

/-- The affine Picard class of the cusp `(-1,1)` is trivial. -/
theorem cuspNegOneClass_eq_one : cuspNegOneClass = 1 := by
  have h := cuspZeroClass_mul_cuspNegOneClass_eq_one
  rwa [cuspZeroClass_eq_one, one_mul] at h

/-- The affine Picard class of the cusp `(-1,-1)` is trivial. -/
theorem cuspNegOneConjugateClass_eq_one : cuspNegOneConjugateClass = 1 := by
  rw [cuspNegOneConjugateClass_eq_cuspZeroClass, cuspZeroClass_eq_one]

/-- The affine Picard class of the cusp `(0,-1)` is trivial. -/
theorem cuspZeroConjugateClass_eq_one : cuspZeroConjugateClass = 1 := by
  have h := cuspZeroConjugateClass_mul_cuspZeroClass
  rwa [cuspZeroClass_eq_one, mul_one] at h

/-- All four affine rational cusps have trivial affine Picard class. -/
theorem affine_cusp_classes_eq_one :
    cuspZeroClass = 1 ∧ cuspZeroConjugateClass = 1 ∧
      cuspNegOneClass = 1 ∧ cuspNegOneConjugateClass = 1 :=
  ⟨cuspZeroClass_eq_one, cuspZeroConjugateClass_eq_one,
    cuspNegOneClass_eq_one, cuspNegOneConjugateClass_eq_one⟩

end

end MazurTorsion.XOneThirteenHaoCuspClasses
