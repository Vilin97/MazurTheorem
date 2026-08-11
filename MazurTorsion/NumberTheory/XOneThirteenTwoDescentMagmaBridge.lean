/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentUnits

/-!
# An alternate sextic presentation for the `X₁(13)` two-descent field

This file checks the exact change of primitive element between the sextic
presentation used by the existing two-descent modules and the presentation
used by the independent Magma calculation.  Only polynomial identities and
explicit unit identities are asserted; no unit-group generation statement is
introduced.
-/

namespace MazurTorsion.XOneThirteenTwoDescentMagmaBridge

open Polynomial
open XOneThirteenTwoDescentSextic
open XOneThirteenTwoDescentUnits

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The integral sextic used by the independent Magma presentation. -/
def magmaSextic : ℤ[X] :=
  X ^ 6 - 2 * X ^ 5 + 3 * X ^ 4 - 4 * X ^ 3 +
    4 * X ^ 2 - 2 * X + 1

/-- The integral presentation is monic, so its six power coordinates are
canonical. -/
theorem magmaSextic_monic : magmaSextic.Monic := by
  simp only [magmaSextic]
  monicity!

/-- The polynomial obtained from `magmaSextic` by changing the sign of the
primitive element. -/
def magmaConjugateSextic : ℤ[X] :=
  X ^ 6 + 2 * X ^ 5 + 3 * X ^ 4 + 4 * X ^ 3 +
    4 * X ^ 2 + 2 * X + 1

/-- Integral norm identity behind the substitution `theta = a²`. -/
theorem magmaSextic_mul_conjugate :
    magmaSextic * magmaConjugateSextic = sextic.comp (X ^ 2) := by
  simp [magmaSextic, magmaConjugateSextic, sextic]
  ring

/-- The same alternate sextic over the rationals. -/
def magmaRationalSextic : ℚ[X] :=
  X ^ 6 - 2 * X ^ 5 + 3 * X ^ 4 - 4 * X ^ 3 +
    4 * X ^ 2 - 2 * X + 1

/-- Scalar extension of the integral Magma sextic. -/
theorem magmaRationalSextic_eq_map :
    magmaRationalSextic = magmaSextic.map (algebraMap ℤ ℚ) := by
  simp [magmaRationalSextic, magmaSextic]

/-- The alternate degree-six quotient algebra. -/
abbrev MagmaAlgebra := AdjoinRoot magmaRationalSextic

/-- Its distinguished primitive element. -/
def a : MagmaAlgebra :=
  AdjoinRoot.root magmaRationalSextic

/-- The defining equation for the alternate primitive element. -/
theorem a_spec :
    a ^ 6 - 2 * a ^ 5 + 3 * a ^ 4 - 4 * a ^ 3 +
      4 * a ^ 2 - 2 * a + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root magmaRationalSextic
  change Polynomial.eval₂ (AdjoinRoot.of magmaRationalSextic)
      (AdjoinRoot.root magmaRationalSextic)
      (X ^ 6 - 2 * X ^ 5 + 3 * X ^ 4 - 4 * X ^ 3 +
        4 * X ^ 2 - 2 * X + 1 : ℚ[X]) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one] at h
  simpa only [a] using h

/-- The old primitive element inside the alternate presentation. -/
def thetaValue : MagmaAlgebra := a ^ 2

@[simp]
theorem thetaValue_eq_a_sq : thetaValue = a ^ 2 := rfl

/-- Exact checked relation: `thetaValue = a²` satisfies the existing sextic. -/
theorem thetaValue_spec :
    thetaValue ^ 6 + 2 * thetaValue ^ 5 + thetaValue ^ 4 +
      2 * thetaValue ^ 3 + 6 * thetaValue ^ 2 +
      4 * thetaValue + 1 = 0 := by
  have h := a_spec
  simp only [thetaValue]
  calc
    (a ^ 2) ^ 6 + 2 * (a ^ 2) ^ 5 + (a ^ 2) ^ 4 +
          2 * (a ^ 2) ^ 3 + 6 * (a ^ 2) ^ 2 + 4 * a ^ 2 + 1 =
        (a ^ 6 - 2 * a ^ 5 + 3 * a ^ 4 - 4 * a ^ 3 +
          4 * a ^ 2 - 2 * a + 1) *
        (a ^ 6 + 2 * a ^ 5 + 3 * a ^ 4 + 4 * a ^ 3 +
          4 * a ^ 2 + 2 * a + 1) := by ring
    _ = 0 := by rw [h, zero_mul]

/-- The alternate primitive element is recovered exactly from `thetaValue`.
This is the denominator-cleared inverse change of primitive element. -/
theorem magmaRoot_from_thetaValue :
    thetaValue ^ 5 + 2 * thetaValue ^ 4 + 2 * thetaValue ^ 2 +
        7 * thetaValue + 3 = 2 * a := by
  have h := a_spec
  simp only [thetaValue]
  linear_combination
    (a ^ 4 + 2 * a ^ 3 + 3 * a ^ 2 + 4 * a + 3) * h

private theorem rationalSextic_eval_thetaValue :
    Polynomial.eval₂ (AdjoinRoot.of magmaRationalSextic) thetaValue
      rationalSextic = 0 := by
  simpa only [rationalSextic, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat,
    Polynomial.eval₂_one] using thetaValue_spec

/-- The checked algebra map implementing `theta ↦ a²`.  The recovery identity
`magmaRoot_from_thetaValue` records that no generator is lost. -/
noncomputable def oldToMagma : SexticField →ₐ[ℚ] MagmaAlgebra :=
  AdjoinRoot.liftAlgHom rationalSextic (Algebra.ofId ℚ MagmaAlgebra)
    thetaValue rationalSextic_eval_thetaValue

@[simp]
theorem oldToMagma_theta : oldToMagma theta = thetaValue := by
  change
    AdjoinRoot.liftAlgHom rationalSextic (Algebra.ofId ℚ MagmaAlgebra)
      thetaValue rationalSextic_eval_thetaValue
        (AdjoinRoot.root rationalSextic) = thetaValue
  apply AdjoinRoot.liftAlgHom_root

/-- The old-field expression whose image is the alternate primitive root. -/
def magmaRootPreimage : SexticField :=
  (1 / 2 : ℚ) •
    (theta ^ 5 + 2 * theta ^ 4 + 2 * theta ^ 2 + 7 * theta + 3)

@[simp]
theorem oldToMagma_magmaRootPreimage :
    oldToMagma magmaRootPreimage = a := by
  simp only [magmaRootPreimage, map_smul, map_add, map_mul, map_pow,
    map_ofNat, oldToMagma_theta]
  rw [magmaRoot_from_thetaValue]
  simp only [Algebra.smul_def]
  rw [← map_ofNat (algebraMap ℚ MagmaAlgebra) 2]
  rw [← mul_assoc, ← map_mul]
  norm_num

/-! ## The order-three `U0` action -/

/-- The image of `a` under the order-three automorphism denoted `U0` in the
independent calculation. -/
def uZeroValue : MagmaAlgebra :=
  a ^ 5 - 2 * a ^ 4 + 2 * a ^ 3 - 3 * a ^ 2 + 2 * a

/-- The displayed value is another root of the alternate sextic. -/
theorem uZeroValue_spec :
    uZeroValue ^ 6 - 2 * uZeroValue ^ 5 + 3 * uZeroValue ^ 4 -
        4 * uZeroValue ^ 3 + 4 * uZeroValue ^ 2 - 2 * uZeroValue + 1 = 0 := by
  have h := a_spec
  simp only [uZeroValue]
  linear_combination
    (a ^ 24 - 10 * a ^ 23 + 49 * a ^ 22 - 166 * a ^ 21 +
      449 * a ^ 20 - 1020 * a ^ 19 + 1991 * a ^ 18 -
      3414 * a ^ 17 + 5208 * a ^ 16 - 7098 * a ^ 15 +
      8690 * a ^ 14 - 9584 * a ^ 13 + 9494 * a ^ 12 -
      8430 * a ^ 11 + 6690 * a ^ 10 - 4698 * a ^ 9 +
      2890 * a ^ 8 - 1552 * a ^ 7 + 721 * a ^ 6 - 288 * a ^ 5 +
      109 * a ^ 4 - 44 * a ^ 3 + 14 * a ^ 2 - 2 * a + 1) * h

private theorem magmaRationalSextic_eval_uZeroValue :
    Polynomial.eval₂ (AdjoinRoot.of magmaRationalSextic) uZeroValue
      magmaRationalSextic = 0 := by
  change Polynomial.eval₂ (AdjoinRoot.of magmaRationalSextic) uZeroValue
      (X ^ 6 - 2 * X ^ 5 + 3 * X ^ 4 - 4 * X ^ 3 +
        4 * X ^ 2 - 2 * X + 1 : ℚ[X]) = 0
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one]
  exact uZeroValue_spec

/-- Magma's `U0` endomorphism, defined by its exact image of the primitive
element.  It is packaged as an automorphism below after checking order three. -/
noncomputable def uZero : MagmaAlgebra →ₐ[ℚ] MagmaAlgebra :=
  AdjoinRoot.liftAlgHom magmaRationalSextic (Algebra.ofId ℚ MagmaAlgebra)
    uZeroValue magmaRationalSextic_eval_uZeroValue

@[simp]
theorem uZero_a : uZero a = uZeroValue := by
  change
    AdjoinRoot.liftAlgHom magmaRationalSextic
      (Algebra.ofId ℚ MagmaAlgebra) uZeroValue
        magmaRationalSextic_eval_uZeroValue
          (AdjoinRoot.root magmaRationalSextic) = uZeroValue
  apply AdjoinRoot.liftAlgHom_root

/-- The reduced expression for the second iterate of `U0` on `a`. -/
def uZeroSquareValue : MagmaAlgebra :=
  -a ^ 5 + 2 * a ^ 4 - 2 * a ^ 3 + 3 * a ^ 2 - 3 * a + 1

/-- First checked iterate of the `U0` root substitution. -/
@[simp]
theorem uZero_uZeroValue : uZero uZeroValue = uZeroSquareValue := by
  have h := a_spec
  simp only [uZeroValue, uZeroSquareValue, map_sub, map_add, map_mul,
    map_pow, map_ofNat, uZero_a]
  linear_combination
    (a ^ 19 - 8 * a ^ 18 + 31 * a ^ 17 - 85 * a ^ 16 +
      191 * a ^ 15 - 359 * a ^ 14 + 574 * a ^ 13 -
      805 * a ^ 12 + 991 * a ^ 11 - 1066 * a ^ 10 +
      1012 * a ^ 9 - 839 * a ^ 8 + 595 * a ^ 7 - 358 * a ^ 6 +
      178 * a ^ 5 - 70 * a ^ 4 + 20 * a ^ 3 - 7 * a ^ 2 +
      5 * a - 1) * h

private theorem uZeroSquareValue_eq :
    uZeroSquareValue = 1 - a - uZeroValue := by
  simp only [uZeroSquareValue, uZeroValue]
  ring

/-- Second checked iterate: the third application returns the primitive
element. -/
@[simp]
theorem uZero_uZeroSquareValue : uZero uZeroSquareValue = a := by
  rw [uZeroSquareValue_eq]
  simp only [map_sub, map_one, uZero_a, uZero_uZeroValue]
  rw [uZeroSquareValue_eq]
  ring

private theorem uZero_comp_square :
    uZero.comp (uZero.comp uZero) = AlgHom.id ℚ MagmaAlgebra := by
  apply AdjoinRoot.algHom_ext
  change uZero (uZero (uZero a)) = a
  rw [uZero_a, uZero_uZeroValue, uZero_uZeroSquareValue]

private theorem uZero_square_comp :
    (uZero.comp uZero).comp uZero = AlgHom.id ℚ MagmaAlgebra := by
  apply AdjoinRoot.algHom_ext
  change uZero (uZero (uZero a)) = a
  rw [uZero_a, uZero_uZeroValue, uZero_uZeroSquareValue]

/-- The checked order-three endomorphism, packaged as a `ℚ`-algebra
automorphism. -/
noncomputable def uZeroAutomorphism : MagmaAlgebra ≃ₐ[ℚ] MagmaAlgebra :=
  AlgEquiv.ofAlgHom uZero (uZero.comp uZero)
    uZero_comp_square uZero_square_comp

@[simp]
theorem uZeroAutomorphism_a : uZeroAutomorphism a = uZeroValue :=
  uZero_a

/-- The automorphism has order dividing three on every element. -/
theorem uZeroAutomorphism_apply_three (z : MagmaAlgebra) :
    uZeroAutomorphism (uZeroAutomorphism (uZeroAutomorphism z)) = z := by
  exact DFunLike.congr_fun uZero_comp_square z

/-! ## Explicit roots of unity and units in the alternate presentation -/

/-- The reduced Magma-basis expression for the fourth root of unity. -/
def magmaI : MagmaAlgebra :=
  a ^ 5 - 2 * a ^ 4 + 3 * a ^ 3 - 3 * a ^ 2 + 3 * a - 1

/-- The reduced Magma-basis expression corresponding to `unitOneValue`. -/
def magmaUnitOne : MagmaAlgebra :=
  a ^ 5 - a ^ 4 + a ^ 3 - a ^ 2 + a + 1

/-- An explicit inverse of `magmaUnitOne`. -/
def magmaUnitOneInverse : MagmaAlgebra :=
  -a ^ 3 + a ^ 2 - a + 1

/-- The reduced Magma-basis expression corresponding to `unitTwoValue`. -/
def magmaUnitTwo : MagmaAlgebra :=
  a ^ 5 - 2 * a ^ 4 + 2 * a ^ 3 - 3 * a ^ 2 + 3 * a - 1

/-- An explicit inverse of `magmaUnitTwo`. -/
def magmaUnitTwoInverse : MagmaAlgebra :=
  a ^ 4 - a ^ 3 + 2 * a ^ 2 - 2 * a + 1

/-- The displayed `magmaI` is a square root of `-1`. -/
theorem magmaI_sq : magmaI ^ 2 = -1 := by
  have h := a_spec
  simp only [magmaI]
  linear_combination
    (a ^ 4 - 2 * a ^ 3 + 3 * a ^ 2 - 2 * a + 2) * h

/-- Checked inverse identity for the first displayed unit. -/
theorem magmaUnitOne_mul_inverse :
    magmaUnitOne * magmaUnitOneInverse = 1 := by
  have h := a_spec
  simp only [magmaUnitOne, magmaUnitOneInverse]
  linear_combination -a ^ 2 * h

/-- Checked inverse identity for the second displayed unit. -/
theorem magmaUnitTwo_mul_inverse :
    magmaUnitTwo * magmaUnitTwoInverse = 1 := by
  have h := a_spec
  simp only [magmaUnitTwo, magmaUnitTwoInverse]
  linear_combination (a ^ 3 - a ^ 2 + a - 2) * h

/-! ## Exact `U0` action on the displayed units -/

/-- Reduced expression for the `U0`-image of the first unit. -/
def uZeroUnitOneValue : MagmaAlgebra := magmaI - a ^ 2

/-- A useful low-degree identity relating the primitive element, the first
unit, and the fourth root of unity. -/
theorem a_mul_magmaUnitOne : a * magmaUnitOne = magmaI := by
  have h := a_spec
  simp only [magmaUnitOne, magmaI]
  linear_combination h

/-- Polynomial reduction of the first unit under `U0`. -/
theorem uZero_magmaUnitOne_reduced :
    uZero magmaUnitOne = uZeroUnitOneValue := by
  have h := a_spec
  simp only [magmaUnitOne, uZeroUnitOneValue, magmaI, map_sub, map_add,
    map_pow, map_one, uZero_a, uZeroValue]
  linear_combination
    (a ^ 19 - 8 * a ^ 18 + 31 * a ^ 17 - 85 * a ^ 16 +
      191 * a ^ 15 - 358 * a ^ 14 + 568 * a ^ 13 -
      788 * a ^ 12 + 955 * a ^ 11 - 1001 * a ^ 10 +
      919 * a ^ 9 - 729 * a ^ 8 + 480 * a ^ 7 - 262 * a ^ 6 +
      115 * a ^ 5 - 33 * a ^ 4 + 5 * a ^ 3 - 5 * a ^ 2 +
      3 * a + 2) * h

/-- The reduced image is exactly `u2 / u1`, expressed without division. -/
theorem uZeroUnitOneValue_eq_unitTwo_mul_inverse :
    uZeroUnitOneValue = magmaUnitTwo * magmaUnitOneInverse := by
  have h := a_spec
  simp only [uZeroUnitOneValue, magmaI, magmaUnitTwo,
    magmaUnitOneInverse]
  linear_combination (a ^ 2 - a) * h

/-- Exact first unit action: `U0(u1) = u2 / u1`. -/
theorem uZero_magmaUnitOne :
    uZero magmaUnitOne = magmaUnitTwo * magmaUnitOneInverse := by
  rw [uZero_magmaUnitOne_reduced,
    uZeroUnitOneValue_eq_unitTwo_mul_inverse]

/-- The order-three action fixes the displayed fourth root of unity. -/
@[simp]
theorem uZero_magmaI : uZero magmaI = magmaI := by
  calc
    uZero magmaI = uZero (a * magmaUnitOne) := by
      rw [a_mul_magmaUnitOne]
    _ = uZeroValue * uZeroUnitOneValue := by
      rw [map_mul, uZero_a, uZero_magmaUnitOne_reduced]
    _ = magmaI := by
      have h := a_spec
      simp only [uZeroValue, uZeroUnitOneValue, magmaI]
      linear_combination
        (a ^ 4 - 2 * a ^ 3 + 2 * a ^ 2 - 3 * a + 1) * h

private theorem magmaUnitTwo_eq_uZeroValue_add :
    magmaUnitTwo = uZeroValue + a - 1 := by
  simp only [magmaUnitTwo, uZeroValue]
  ring

/-- Polynomial reduction of the second unit under `U0`. -/
theorem uZero_magmaUnitTwo_reduced : uZero magmaUnitTwo = -a := by
  rw [magmaUnitTwo_eq_uZeroValue_add]
  simp only [map_sub, map_add, map_one, uZero_a, uZero_uZeroValue]
  rw [uZeroSquareValue_eq]
  ring

/-- Denominator-cleared form of the second expected unit action. -/
theorem neg_a_mul_magmaUnitOne_eq_magmaI_cube :
    (-a) * magmaUnitOne = magmaI ^ 3 := by
  rw [show (-a) * magmaUnitOne = -(a * magmaUnitOne) by ring,
    a_mul_magmaUnitOne]
  calc
    -magmaI = magmaI * (-1) := by ring
    _ = magmaI * magmaI ^ 2 := by rw [magmaI_sq]
    _ = magmaI ^ 3 := by ring

/-- The reduced second image is exactly `i³ / u1`. -/
theorem neg_a_eq_magmaI_cube_mul_unitOneInverse :
    -a = magmaI ^ 3 * magmaUnitOneInverse := by
  calc
    -a = (-a) * 1 := by ring
    _ = (-a) * (magmaUnitOne * magmaUnitOneInverse) := by
      rw [magmaUnitOne_mul_inverse]
    _ = ((-a) * magmaUnitOne) * magmaUnitOneInverse := by ring
    _ = magmaI ^ 3 * magmaUnitOneInverse := by
      rw [neg_a_mul_magmaUnitOne_eq_magmaI_cube]

/-- Exact second unit action: `U0(u2) = i³ / u1`. -/
theorem uZero_magmaUnitTwo :
    uZero magmaUnitTwo = magmaI ^ 3 * magmaUnitOneInverse := by
  rw [uZero_magmaUnitTwo_reduced,
    neg_a_eq_magmaI_cube_mul_unitOneInverse]

/-- The displayed fourth root of unity, packaged as an actual unit. -/
def magmaIUnit : MagmaAlgebraˣ :=
  Units.mkOfMulEqOne magmaI (-magmaI) (by
    rw [mul_neg, ← pow_two, magmaI_sq]
    norm_num)

/-- The first displayed element, packaged as an actual unit. -/
def magmaUnitOneUnit : MagmaAlgebraˣ :=
  Units.mkOfMulEqOne magmaUnitOne magmaUnitOneInverse
    magmaUnitOne_mul_inverse

/-- The second displayed element, packaged as an actual unit. -/
def magmaUnitTwoUnit : MagmaAlgebraˣ :=
  Units.mkOfMulEqOne magmaUnitTwo magmaUnitTwoInverse
    magmaUnitTwo_mul_inverse

@[simp] theorem magmaIUnit_coe : (magmaIUnit : MagmaAlgebra) = magmaI := rfl

@[simp] theorem magmaUnitOneUnit_coe :
    (magmaUnitOneUnit : MagmaAlgebra) = magmaUnitOne := rfl

@[simp] theorem magmaUnitTwoUnit_coe :
    (magmaUnitTwoUnit : MagmaAlgebra) = magmaUnitTwo := rfl

/-- `U0(i) = i`, as an equality of packaged units. -/
theorem uZero_magmaIUnit :
    Units.map uZero.toMonoidHom magmaIUnit = magmaIUnit := by
  apply Units.ext
  exact uZero_magmaI

/-- `U0(u1) = u2 / u1`, as an equality of packaged units. -/
theorem uZero_magmaUnitOneUnit :
    Units.map uZero.toMonoidHom magmaUnitOneUnit =
      magmaUnitTwoUnit * magmaUnitOneUnit⁻¹ := by
  apply Units.ext
  exact uZero_magmaUnitOne

/-- `U0(u2) = i³ / u1`, as an equality of packaged units. -/
theorem uZero_magmaUnitTwoUnit :
    Units.map uZero.toMonoidHom magmaUnitTwoUnit =
      magmaIUnit ^ 3 * magmaUnitOneUnit⁻¹ := by
  apply Units.ext
  exact uZero_magmaUnitTwo

/-! ## Integral order and genuine reduction modulo two -/

/-- The monogenic integral order `ℤ[a]/(g)`. -/
abbrev MagmaOrder := AdjoinRoot magmaSextic

/-- The integral primitive element. -/
def integralA : MagmaOrder := AdjoinRoot.root magmaSextic

/-- Its defining integral equation. -/
theorem integralA_spec :
    integralA ^ 6 - 2 * integralA ^ 5 + 3 * integralA ^ 4 -
        4 * integralA ^ 3 + 4 * integralA ^ 2 - 2 * integralA + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root magmaSextic
  change Polynomial.eval₂ (AdjoinRoot.of magmaSextic)
      (AdjoinRoot.root magmaSextic)
      (X ^ 6 - 2 * X ^ 5 + 3 * X ^ 4 - 4 * X ^ 3 +
        4 * X ^ 2 - 2 * X + 1 : ℤ[X]) = 0 at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one] at h
  simpa only [integralA] using h

/-- Integral representative of the displayed fourth root of unity. -/
def integralI : MagmaOrder :=
  integralA ^ 5 - 2 * integralA ^ 4 + 3 * integralA ^ 3 -
    3 * integralA ^ 2 + 3 * integralA - 1

/-- Integral representative of the first unit. -/
def integralUnitOne : MagmaOrder :=
  integralA ^ 5 - integralA ^ 4 + integralA ^ 3 -
    integralA ^ 2 + integralA + 1

/-- Integral inverse of the first unit. -/
def integralUnitOneInverse : MagmaOrder :=
  -integralA ^ 3 + integralA ^ 2 - integralA + 1

/-- Integral representative of the second unit. -/
def integralUnitTwo : MagmaOrder :=
  integralA ^ 5 - 2 * integralA ^ 4 + 2 * integralA ^ 3 -
    3 * integralA ^ 2 + 3 * integralA - 1

/-- Integral inverse of the second unit. -/
def integralUnitTwoInverse : MagmaOrder :=
  integralA ^ 4 - integralA ^ 3 + 2 * integralA ^ 2 -
    2 * integralA + 1

/-- Integral `U0`-image of the primitive element. -/
def integralUZeroValue : MagmaOrder :=
  integralA ^ 5 - 2 * integralA ^ 4 + 2 * integralA ^ 3 -
    3 * integralA ^ 2 + 2 * integralA

theorem integralUZeroValue_spec :
    integralUZeroValue ^ 6 - 2 * integralUZeroValue ^ 5 +
        3 * integralUZeroValue ^ 4 - 4 * integralUZeroValue ^ 3 +
        4 * integralUZeroValue ^ 2 - 2 * integralUZeroValue + 1 = 0 := by
  have h := integralA_spec
  simp only [integralUZeroValue]
  linear_combination
    (integralA ^ 24 - 10 * integralA ^ 23 + 49 * integralA ^ 22 -
      166 * integralA ^ 21 + 449 * integralA ^ 20 -
      1020 * integralA ^ 19 + 1991 * integralA ^ 18 -
      3414 * integralA ^ 17 + 5208 * integralA ^ 16 -
      7098 * integralA ^ 15 + 8690 * integralA ^ 14 -
      9584 * integralA ^ 13 + 9494 * integralA ^ 12 -
      8430 * integralA ^ 11 + 6690 * integralA ^ 10 -
      4698 * integralA ^ 9 + 2890 * integralA ^ 8 -
      1552 * integralA ^ 7 + 721 * integralA ^ 6 -
      288 * integralA ^ 5 + 109 * integralA ^ 4 -
      44 * integralA ^ 3 + 14 * integralA ^ 2 - 2 * integralA + 1) * h

private theorem magmaSextic_eval_integralUZeroValue :
    Polynomial.eval₂ (AdjoinRoot.of magmaSextic) integralUZeroValue
      magmaSextic = 0 := by
  change Polynomial.eval₂ (AdjoinRoot.of magmaSextic) integralUZeroValue
      (X ^ 6 - 2 * X ^ 5 + 3 * X ^ 4 - 4 * X ^ 3 +
        4 * X ^ 2 - 2 * X + 1 : ℤ[X]) = 0
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one]
  exact integralUZeroValue_spec

/-- The same `U0` action, now as an endomorphism of the integral order. -/
def integralUZero : MagmaOrder →ₐ[ℤ] MagmaOrder :=
  AdjoinRoot.liftAlgHom magmaSextic (Algebra.ofId ℤ MagmaOrder)
    integralUZeroValue magmaSextic_eval_integralUZeroValue

@[simp]
theorem integralUZero_integralA :
    integralUZero integralA = integralUZeroValue := by
  change
    AdjoinRoot.liftAlgHom magmaSextic (Algebra.ofId ℤ MagmaOrder)
      integralUZeroValue magmaSextic_eval_integralUZeroValue
        (AdjoinRoot.root magmaSextic) = integralUZeroValue
  apply AdjoinRoot.liftAlgHom_root

/-- Reduced second iterate in the integral order. -/
def integralUZeroSquareValue : MagmaOrder :=
  -integralA ^ 5 + 2 * integralA ^ 4 - 2 * integralA ^ 3 +
    3 * integralA ^ 2 - 3 * integralA + 1

@[simp]
theorem integralUZero_integralUZeroValue :
    integralUZero integralUZeroValue = integralUZeroSquareValue := by
  have h := integralA_spec
  simp only [integralUZeroValue, integralUZeroSquareValue, map_sub, map_add,
    map_mul, map_pow, map_ofNat, integralUZero_integralA]
  linear_combination
    (integralA ^ 19 - 8 * integralA ^ 18 + 31 * integralA ^ 17 -
      85 * integralA ^ 16 + 191 * integralA ^ 15 -
      359 * integralA ^ 14 + 574 * integralA ^ 13 -
      805 * integralA ^ 12 + 991 * integralA ^ 11 -
      1066 * integralA ^ 10 + 1012 * integralA ^ 9 -
      839 * integralA ^ 8 + 595 * integralA ^ 7 -
      358 * integralA ^ 6 + 178 * integralA ^ 5 -
      70 * integralA ^ 4 + 20 * integralA ^ 3 -
      7 * integralA ^ 2 + 5 * integralA - 1) * h

private theorem integralUZeroSquareValue_eq :
    integralUZeroSquareValue = 1 - integralA - integralUZeroValue := by
  simp only [integralUZeroSquareValue, integralUZeroValue]
  ring

@[simp]
theorem integralUZero_integralUZeroSquareValue :
    integralUZero integralUZeroSquareValue = integralA := by
  rw [integralUZeroSquareValue_eq]
  simp only [map_sub, map_one, integralUZero_integralA,
    integralUZero_integralUZeroValue]
  rw [integralUZeroSquareValue_eq]
  ring

private theorem integralUZero_comp_square :
    integralUZero.comp (integralUZero.comp integralUZero) =
      AlgHom.id ℤ MagmaOrder := by
  apply AdjoinRoot.algHom_ext
  change integralUZero (integralUZero (integralUZero integralA)) = integralA
  rw [integralUZero_integralA, integralUZero_integralUZeroValue,
    integralUZero_integralUZeroSquareValue]

private theorem integralUZero_square_comp :
    (integralUZero.comp integralUZero).comp integralUZero =
      AlgHom.id ℤ MagmaOrder := by
  apply AdjoinRoot.algHom_ext
  change integralUZero (integralUZero (integralUZero integralA)) = integralA
  rw [integralUZero_integralA, integralUZero_integralUZeroValue,
    integralUZero_integralUZeroSquareValue]

/-- `U0` as an automorphism of the integral order. -/
def integralUZeroAutomorphism : MagmaOrder ≃ₐ[ℤ] MagmaOrder :=
  AlgEquiv.ofAlgHom integralUZero (integralUZero.comp integralUZero)
    integralUZero_comp_square integralUZero_square_comp

theorem integralI_sq : integralI ^ 2 = -1 := by
  have h := integralA_spec
  simp only [integralI]
  linear_combination
    (integralA ^ 4 - 2 * integralA ^ 3 + 3 * integralA ^ 2 -
      2 * integralA + 2) * h

theorem integralUnitOne_mul_inverse :
    integralUnitOne * integralUnitOneInverse = 1 := by
  have h := integralA_spec
  simp only [integralUnitOne, integralUnitOneInverse]
  linear_combination -integralA ^ 2 * h

theorem integralUnitTwo_mul_inverse :
    integralUnitTwo * integralUnitTwoInverse = 1 := by
  have h := integralA_spec
  simp only [integralUnitTwo, integralUnitTwoInverse]
  linear_combination
    (integralA ^ 3 - integralA ^ 2 + integralA - 2) * h

/-- Reduced integral value of `U0(u1)`. -/
def integralUZeroUnitOneValue : MagmaOrder :=
  integralI - integralA ^ 2

theorem integralA_mul_integralUnitOne :
    integralA * integralUnitOne = integralI := by
  have h := integralA_spec
  simp only [integralUnitOne, integralI]
  linear_combination h

theorem integralUZero_integralUnitOne_reduced :
    integralUZero integralUnitOne = integralUZeroUnitOneValue := by
  have h := integralA_spec
  simp only [integralUnitOne, integralUZeroUnitOneValue, integralI,
    map_sub, map_add, map_pow, map_one, integralUZero_integralA,
    integralUZeroValue]
  linear_combination
    (integralA ^ 19 - 8 * integralA ^ 18 + 31 * integralA ^ 17 -
      85 * integralA ^ 16 + 191 * integralA ^ 15 -
      358 * integralA ^ 14 + 568 * integralA ^ 13 -
      788 * integralA ^ 12 + 955 * integralA ^ 11 -
      1001 * integralA ^ 10 + 919 * integralA ^ 9 -
      729 * integralA ^ 8 + 480 * integralA ^ 7 -
      262 * integralA ^ 6 + 115 * integralA ^ 5 -
      33 * integralA ^ 4 + 5 * integralA ^ 3 -
      5 * integralA ^ 2 + 3 * integralA + 2) * h

theorem integralUZeroUnitOneValue_eq :
    integralUZeroUnitOneValue =
      integralUnitTwo * integralUnitOneInverse := by
  have h := integralA_spec
  simp only [integralUZeroUnitOneValue, integralI, integralUnitTwo,
    integralUnitOneInverse]
  linear_combination (integralA ^ 2 - integralA) * h

/-- Integral identity `U0(u1) = u2 / u1`. -/
theorem integralUZero_integralUnitOne :
    integralUZero integralUnitOne =
      integralUnitTwo * integralUnitOneInverse := by
  rw [integralUZero_integralUnitOne_reduced,
    integralUZeroUnitOneValue_eq]

@[simp]
theorem integralUZero_integralI : integralUZero integralI = integralI := by
  calc
    integralUZero integralI =
        integralUZero (integralA * integralUnitOne) := by
      rw [integralA_mul_integralUnitOne]
    _ = integralUZeroValue * integralUZeroUnitOneValue := by
      rw [map_mul, integralUZero_integralA,
        integralUZero_integralUnitOne_reduced]
    _ = integralI := by
      have h := integralA_spec
      simp only [integralUZeroValue, integralUZeroUnitOneValue, integralI]
      linear_combination
        (integralA ^ 4 - 2 * integralA ^ 3 + 2 * integralA ^ 2 -
          3 * integralA + 1) * h

private theorem integralUnitTwo_eq_uZeroValue_add :
    integralUnitTwo = integralUZeroValue + integralA - 1 := by
  simp only [integralUnitTwo, integralUZeroValue]
  ring

theorem integralUZero_integralUnitTwo_reduced :
    integralUZero integralUnitTwo = -integralA := by
  rw [integralUnitTwo_eq_uZeroValue_add]
  simp only [map_sub, map_add, map_one, integralUZero_integralA,
    integralUZero_integralUZeroValue]
  rw [integralUZeroSquareValue_eq]
  ring

theorem neg_integralA_mul_unitOne_eq_i_cube :
    (-integralA) * integralUnitOne = integralI ^ 3 := by
  rw [show (-integralA) * integralUnitOne =
      -(integralA * integralUnitOne) by ring,
    integralA_mul_integralUnitOne]
  calc
    -integralI = integralI * (-1) := by ring
    _ = integralI * integralI ^ 2 := by rw [integralI_sq]
    _ = integralI ^ 3 := by ring

theorem neg_integralA_eq_i_cube_mul_unitOneInverse :
    -integralA = integralI ^ 3 * integralUnitOneInverse := by
  calc
    -integralA = (-integralA) * 1 := by ring
    _ = (-integralA) * (integralUnitOne * integralUnitOneInverse) := by
      rw [integralUnitOne_mul_inverse]
    _ = ((-integralA) * integralUnitOne) * integralUnitOneInverse := by ring
    _ = integralI ^ 3 * integralUnitOneInverse := by
      rw [neg_integralA_mul_unitOne_eq_i_cube]

/-- Integral identity `U0(u2) = i³ / u1`. -/
theorem integralUZero_integralUnitTwo :
    integralUZero integralUnitTwo =
      integralI ^ 3 * integralUnitOneInverse := by
  rw [integralUZero_integralUnitTwo_reduced,
    neg_integralA_eq_i_cube_mul_unitOneInverse]

/-- The fourth root of unity as a unit of the integral order. -/
def integralIUnit : MagmaOrderˣ :=
  Units.mkOfMulEqOne integralI (-integralI) (by
    rw [mul_neg, ← pow_two, integralI_sq]
    norm_num)

/-- The first unit as a unit of the integral order. -/
def integralUnitOneUnit : MagmaOrderˣ :=
  Units.mkOfMulEqOne integralUnitOne integralUnitOneInverse
    integralUnitOne_mul_inverse

/-- The second unit as a unit of the integral order. -/
def integralUnitTwoUnit : MagmaOrderˣ :=
  Units.mkOfMulEqOne integralUnitTwo integralUnitTwoInverse
    integralUnitTwo_mul_inverse

@[simp] theorem integralIUnit_coe :
    (integralIUnit : MagmaOrder) = integralI := rfl

@[simp] theorem integralUnitOneUnit_coe :
    (integralUnitOneUnit : MagmaOrder) = integralUnitOne := rfl

@[simp] theorem integralUnitTwoUnit_coe :
    (integralUnitTwoUnit : MagmaOrder) = integralUnitTwo := rfl

theorem integralUZero_integralIUnit :
    Units.map integralUZero.toMonoidHom integralIUnit = integralIUnit := by
  apply Units.ext
  exact integralUZero_integralI

theorem integralUZero_integralUnitOneUnit :
    Units.map integralUZero.toMonoidHom integralUnitOneUnit =
      integralUnitTwoUnit * integralUnitOneUnit⁻¹ := by
  apply Units.ext
  exact integralUZero_integralUnitOne

theorem integralUZero_integralUnitTwoUnit :
    Units.map integralUZero.toMonoidHom integralUnitTwoUnit =
      integralIUnit ^ 3 * integralUnitOneUnit⁻¹ := by
  apply Units.ext
  exact integralUZero_integralUnitTwo

/-- Base change from the integral order to the rational presentation used
above. -/
noncomputable def magmaOrderToAlgebra : MagmaOrder →+* MagmaAlgebra :=
  AdjoinRoot.map (algebraMap ℤ ℚ) magmaSextic magmaRationalSextic (by
    rw [magmaRationalSextic_eq_map])

@[simp]
theorem magmaOrderToAlgebra_integralA :
    magmaOrderToAlgebra integralA = a := by
  change
    AdjoinRoot.map (algebraMap ℤ ℚ) magmaSextic magmaRationalSextic _
      (AdjoinRoot.root magmaSextic) = AdjoinRoot.root magmaRationalSextic
  apply AdjoinRoot.map_root

@[simp]
theorem magmaOrderToAlgebra_integralI :
    magmaOrderToAlgebra integralI = magmaI := by
  simp only [integralI, magmaI, map_sub, map_add, map_mul, map_pow,
    map_ofNat, map_one, magmaOrderToAlgebra_integralA]

@[simp]
theorem magmaOrderToAlgebra_integralUnitOne :
    magmaOrderToAlgebra integralUnitOne = magmaUnitOne := by
  simp only [integralUnitOne, magmaUnitOne, map_sub, map_add, map_pow,
    map_one, magmaOrderToAlgebra_integralA]

@[simp]
theorem magmaOrderToAlgebra_integralUnitTwo :
    magmaOrderToAlgebra integralUnitTwo = magmaUnitTwo := by
  simp only [integralUnitTwo, magmaUnitTwo, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_one, magmaOrderToAlgebra_integralA]

theorem integralIUnit_toAlgebra :
    Units.map magmaOrderToAlgebra.toMonoidHom integralIUnit = magmaIUnit := by
  apply Units.ext
  exact magmaOrderToAlgebra_integralI

theorem integralUnitOneUnit_toAlgebra :
    Units.map magmaOrderToAlgebra.toMonoidHom integralUnitOneUnit =
      magmaUnitOneUnit := by
  apply Units.ext
  exact magmaOrderToAlgebra_integralUnitOne

theorem integralUnitTwoUnit_toAlgebra :
    Units.map magmaOrderToAlgebra.toMonoidHom integralUnitTwoUnit =
      magmaUnitTwoUnit := by
  apply Units.ext
  exact magmaOrderToAlgebra_integralUnitTwo

/-- The defining polynomial reduced modulo two. -/
def magmaSexticModTwo : (ZMod 2)[X] :=
  magmaSextic.map (Int.castRingHom (ZMod 2))

/-- Explicit reduced defining equation. -/
theorem magmaSexticModTwo_eq :
    magmaSexticModTwo = X ^ 6 + X ^ 4 + 1 := by
  simp [magmaSexticModTwo, magmaSextic]
  ring_nf
  reduce_mod_char

/-- The genuine quotient ring `𝔽₂[a]/(ḡ)`. -/
abbrev MagmaModTwo := AdjoinRoot magmaSexticModTwo

/-- Its distinguished residue-class root. -/
def modTwoA : MagmaModTwo := AdjoinRoot.root magmaSexticModTwo

/-- Genuine coefficient reduction from the integral order to the quotient
ring modulo two. -/
def magmaOrderToModTwo : MagmaOrder →+* MagmaModTwo :=
  AdjoinRoot.map (Int.castRingHom (ZMod 2)) magmaSextic magmaSexticModTwo (by
    simp only [magmaSexticModTwo]
    exact dvd_rfl)

@[simp]
theorem magmaOrderToModTwo_integralA :
    magmaOrderToModTwo integralA = modTwoA := by
  change
    AdjoinRoot.map (Int.castRingHom (ZMod 2)) magmaSextic magmaSexticModTwo _
      (AdjoinRoot.root magmaSextic) = AdjoinRoot.root magmaSexticModTwo
  apply AdjoinRoot.map_root

private theorem modTwo_two_eq_zero : (2 : MagmaModTwo) = 0 := by
  rw [← map_ofNat (AdjoinRoot.of magmaSexticModTwo) 2]
  rw [show (2 : ZMod 2) = 0 by decide, map_zero]

/-- Interpret six displayed coefficients in the power basis
`1,a,a²,…,a⁵` of the mod-two quotient. -/
def modTwoCoordinateValue
    (c₀ c₁ c₂ c₃ c₄ c₅ : ZMod 2) : MagmaModTwo :=
  AdjoinRoot.of magmaSexticModTwo c₀ +
    AdjoinRoot.of magmaSexticModTwo c₁ * modTwoA +
    AdjoinRoot.of magmaSexticModTwo c₂ * modTwoA ^ 2 +
    AdjoinRoot.of magmaSexticModTwo c₃ * modTwoA ^ 3 +
    AdjoinRoot.of magmaSexticModTwo c₄ * modTwoA ^ 4 +
    AdjoinRoot.of magmaSexticModTwo c₅ * modTwoA ^ 5

/-- Exact mod-two coefficient vector of `i`:
`[1, 1, 1, 1, 0, 1]`. -/
theorem integralI_modTwo_coordinates :
    magmaOrderToModTwo (integralIUnit : MagmaOrder) =
      modTwoCoordinateValue 1 1 1 1 0 1 := by
  simp only [integralIUnit_coe, integralI, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_one, magmaOrderToModTwo_integralA,
    modTwoCoordinateValue]
  simp only [map_zero, zero_mul, add_zero]
  linear_combination
    (-1 + modTwoA - 2 * modTwoA ^ 2 + modTwoA ^ 3 - modTwoA ^ 4) *
      modTwo_two_eq_zero

/-- Exact mod-two coefficient vector of `u1`:
`[1, 1, 1, 1, 1, 1]`. -/
theorem integralUnitOne_modTwo_coordinates :
    magmaOrderToModTwo (integralUnitOneUnit : MagmaOrder) =
      modTwoCoordinateValue 1 1 1 1 1 1 := by
  simp only [integralUnitOneUnit_coe, integralUnitOne, map_sub, map_add,
    map_pow, map_one, magmaOrderToModTwo_integralA, modTwoCoordinateValue]
  linear_combination
    (-modTwoA ^ 2 - modTwoA ^ 4) * modTwo_two_eq_zero

/-- Exact mod-two coefficient vector of `u2`:
`[1, 1, 1, 0, 0, 1]`. -/
theorem integralUnitTwo_modTwo_coordinates :
    magmaOrderToModTwo (integralUnitTwoUnit : MagmaOrder) =
      modTwoCoordinateValue 1 1 1 0 0 1 := by
  simp only [integralUnitTwoUnit_coe, integralUnitTwo, map_sub, map_add,
    map_mul, map_pow, map_ofNat, map_one, magmaOrderToModTwo_integralA,
    modTwoCoordinateValue]
  simp only [map_zero, zero_mul, add_zero]
  linear_combination
    (-1 + modTwoA - 2 * modTwoA ^ 2 + modTwoA ^ 3 - modTwoA ^ 4) *
      modTwo_two_eq_zero

/-- Denominator-cleared identity transporting the existing square root of
`-1` after the substitution `theta = a²`. -/
theorem magmaI_from_thetaValue :
    (4 * thetaValue ^ 5 + 6 * thetaValue ^ 4 +
        2 * thetaValue ^ 3 + 8 * thetaValue ^ 2 +
        22 * thetaValue + 9) - 1 = 4 * magmaI := by
  have h := a_spec
  simp only [thetaValue, magmaI]
  linear_combination
    (4 * a ^ 4 + 8 * a ^ 3 + 10 * a ^ 2 + 12 * a + 12) * h

/-- Denominator-cleared transport identity for `unitOneValue`. -/
theorem magmaUnitOne_from_thetaValue :
    thetaValue ^ 4 + thetaValue ^ 3 + 3 * thetaValue + 4 =
      2 * magmaUnitOne := by
  have h := a_spec
  simp only [thetaValue, magmaUnitOne]
  linear_combination (a ^ 2 + 2 * a + 2) * h

/-- Denominator-cleared transport identity for `unitTwoValue`. -/
theorem magmaUnitTwo_from_thetaValue :
    2 * thetaValue ^ 5 + 4 * thetaValue ^ 4 + thetaValue ^ 3 +
        3 * thetaValue ^ 2 + 12 * thetaValue + 5 =
      2 * magmaUnitTwo := by
  have h := a_spec
  simp only [thetaValue, magmaUnitTwo]
  linear_combination
    (2 * a ^ 4 + 4 * a ^ 3 + 6 * a ^ 2 + 8 * a + 7) * h

end

end MazurTorsion.XOneThirteenTwoDescentMagmaBridge
