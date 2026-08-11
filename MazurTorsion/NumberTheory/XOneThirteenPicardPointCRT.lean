/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPicardPointEvaluation

/-!
# Chinese remaindering rational affine points of `X₁(13)`

Distinct rational affine points define distinct maximal ideals in the fixed
coordinate ring, hence comaximal ideals.  Combining this fact with the
point-evaluation residue-field calculation gives an explicit two-point
Chinese-remainder equivalence

`A / (m_P m_Q) ≃ ℚ × ℚ`.

The two components of the equivalence are proved to be evaluation at `P` and
`Q`.  A final specialization uses the conjugate cusp pair `(0,1)` and
`(0,-1)`.
-/

namespace MazurTorsion.XOneThirteenPicard

open Ideal Polynomial

open XOneThirteenMumford

noncomputable section

namespace CoordinateRing

/-- Distinct rational affine points define comaximal point ideals. -/
theorem pointIdeal_isCoprime_of_ne
    {x y x' y' : ℚ}
    (hcurve : IsAffinePoint x y) (hcurve' : IsAffinePoint x' y')
    (hne : (x, y) ≠ (x', y')) :
    IsCoprime (pointIdeal x y) (pointIdeal x' y') := by
  letI : (pointIdeal x y).IsMaximal :=
    pointIdeal_isMaximal x y hcurve
  letI : (pointIdeal x' y').IsMaximal :=
    pointIdeal_isMaximal x' y' hcurve'
  apply Ideal.isCoprime_of_isMaximal
  intro hideal
  apply hne
  have hxy := (pointIdeal_eq_iff hcurve hcurve').mp hideal
  exact Prod.ext hxy.1 hxy.2

/-- The point-ideal version of comaximality for bundled rational affine
points. -/
theorem rationalAffinePointIdeal_isCoprime
    {P Q : RationalAffinePoint} (hne : P ≠ Q) :
    IsCoprime (rationalAffinePointIdeal P) (rationalAffinePointIdeal Q) := by
  apply pointIdeal_isCoprime_of_ne P.2 Q.2
  intro hpq
  apply hne
  apply Subtype.ext
  exact hpq

/-- Chinese remaindering two distinct rational affine points, with both
residue fields identified with `ℚ` by evaluation. -/
def pointPairQuotientEquiv
    {x y x' y' : ℚ}
    (hcurve : IsAffinePoint x y) (hcurve' : IsAffinePoint x' y')
    (hne : (x, y) ≠ (x', y')) :
    CoordinateRing ⧸ (pointIdeal x y * pointIdeal x' y') ≃+* (ℚ × ℚ) :=
  (Ideal.quotientMulEquivQuotientProd
      (pointIdeal x y) (pointIdeal x' y')
      (pointIdeal_isCoprime_of_ne hcurve hcurve' hne)).trans
    (RingEquiv.prodCongr
      (pointIdealQuotientEquiv x y hcurve)
      (pointIdealQuotientEquiv x' y' hcurve'))

/-- On a coordinate-ring function, the two CRT components are exactly the
two rational-point evaluations. -/
@[simp] theorem pointPairQuotientEquiv_mk
    {x y x' y' : ℚ}
    (hcurve : IsAffinePoint x y) (hcurve' : IsAffinePoint x' y')
    (hne : (x, y) ≠ (x', y')) (z : CoordinateRing) :
    pointPairQuotientEquiv hcurve hcurve' hne
        (Ideal.Quotient.mk (pointIdeal x y * pointIdeal x' y') z) =
      (pointEval x y hcurve z, pointEval x' y' hcurve' z) := by
  apply Prod.ext
  · simp [pointPairQuotientEquiv]
  · simp [pointPairQuotientEquiv]

/-- The two evaluation maps annihilate the product of the two point ideals. -/
theorem pointIdeal_mul_le_evalProd_ker
    {x y x' y' : ℚ}
    (hcurve : IsAffinePoint x y) (hcurve' : IsAffinePoint x' y') :
    pointIdeal x y * pointIdeal x' y' ≤
      RingHom.ker ((pointEval x y hcurve).prod (pointEval x' y' hcurve')) := by
  intro z hz
  rw [RingHom.mem_ker]
  apply Prod.ext
  · exact RingHom.mem_ker.mp <| pointIdeal_le_pointEval_ker x y hcurve
      (mul_le_right hz)
  · exact RingHom.mem_ker.mp <| pointIdeal_le_pointEval_ker x' y' hcurve'
      (mul_le_left hz)

/-- For distinct points, the product ideal is exactly the kernel of paired
evaluation. -/
theorem evalProd_ker_eq_pointIdeal_mul
    {x y x' y' : ℚ}
    (hcurve : IsAffinePoint x y) (hcurve' : IsAffinePoint x' y')
    (hne : (x, y) ≠ (x', y')) :
    RingHom.ker ((pointEval x y hcurve).prod (pointEval x' y' hcurve')) =
      pointIdeal x y * pointIdeal x' y' := by
  apply le_antisymm
  · intro z hz
    rw [mul_eq_inf_of_isCoprime
      (pointIdeal_isCoprime_of_ne hcurve hcurve' hne)]
    have hzprod := RingHom.mem_ker.mp hz
    constructor
    · rw [← pointEval_ker x y hcurve]
      exact RingHom.mem_ker.mpr (congrArg Prod.fst hzprod)
    · rw [← pointEval_ker x' y' hcurve']
      exact RingHom.mem_ker.mpr (congrArg Prod.snd hzprod)
  · exact pointIdeal_mul_le_evalProd_ker hcurve hcurve'

/-! ## The conjugate cusp pair -/

theorem cuspZeroPositive_isAffinePoint : IsAffinePoint 0 1 := by
  norm_num [IsAffinePoint, sexticPolynomial]

theorem cuspZeroNegative_isAffinePoint : IsAffinePoint 0 (-1) := by
  norm_num [IsAffinePoint, sexticPolynomial]

private theorem cuspZeroPair_ne : ((0, 1) : ℚ × ℚ) ≠ (0, -1) := by
  norm_num

/-- The product of the two conjugate cusp ideals has residue algebra
`ℚ × ℚ`. -/
def cuspZeroPairQuotientEquiv :
    CoordinateRing ⧸ (pointIdeal 0 1 * pointIdeal 0 (-1)) ≃+* (ℚ × ℚ) :=
  pointPairQuotientEquiv cuspZeroPositive_isAffinePoint
    cuspZeroNegative_isAffinePoint cuspZeroPair_ne

@[simp] theorem cuspZeroPairQuotientEquiv_mk (z : CoordinateRing) :
    cuspZeroPairQuotientEquiv
        (Ideal.Quotient.mk (pointIdeal 0 1 * pointIdeal 0 (-1)) z) =
      (pointEval 0 1 cuspZeroPositive_isAffinePoint z,
        pointEval 0 (-1) cuspZeroNegative_isAffinePoint z) := by
  exact pointPairQuotientEquiv_mk cuspZeroPositive_isAffinePoint
    cuspZeroNegative_isAffinePoint cuspZeroPair_ne z

/-- The CRT image of `Y` separates the two conjugate cusps. -/
@[simp] theorem cuspZeroPairQuotientEquiv_yCoordinate :
    cuspZeroPairQuotientEquiv
        (Ideal.Quotient.mk (pointIdeal 0 1 * pointIdeal 0 (-1)) yCoordinate) =
      ((1, -1) : ℚ × ℚ) := by
  simp

/-- Both conjugate cusps have `X`-coordinate zero. -/
@[simp] theorem cuspZeroPairQuotientEquiv_xCoordinate :
    cuspZeroPairQuotientEquiv
        (Ideal.Quotient.mk (pointIdeal 0 1 * pointIdeal 0 (-1))
          (algebraMap ℚ[X] CoordinateRing X)) =
      ((0, 0) : ℚ × ℚ) := by
  simp

end CoordinateRing

end

end MazurTorsion.XOneThirteenPicard
