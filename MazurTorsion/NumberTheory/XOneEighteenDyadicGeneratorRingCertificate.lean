/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MazurTorsion.NumberTheory.XOneEighteenDyadicGeneratorCertificate

/-!
# Ring realization of the dyadic generator certificate

The finite certificate in `XOneEighteenDyadicCubicCertificate` uses triples
with a custom multiplication.  This file identifies those triples with the
power basis of

`(ZMod 16)[T] / (T³ - 3T - 1)`

and transfers its nonsquare result to the ordinary ring-theoretic
`IsSquare` predicate.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate

noncomputable section

/-- The coefficient ring used throughout this finite certificate. -/
abbrev R := ZMod 16

/-- The cubic polynomial defining the finite dyadic coefficient ring. -/
def cubicPolynomial16 : Polynomial R :=
  X ^ 3 - 3 * X - 1

/-- The actual cubic residue ring modulo `16`. -/
abbrev CubicRing16 := AdjoinRoot cubicPolynomial16

/-- The distinguished root of `T³ - 3T - 1`. -/
def tau16 : CubicRing16 :=
  AdjoinRoot.root cubicPolynomial16

private theorem cubicPolynomial16_monic : cubicPolynomial16.Monic := by
  simp only [cubicPolynomial16]
  monicity <;> norm_num

private theorem cubicPolynomial16_natDegree :
    cubicPolynomial16.natDegree = 3 := by
  simp only [cubicPolynomial16]
  compute_degree!

/-- The canonical power basis of the cubic residue ring. -/
def cubicPowerBasis16 : PowerBasis R CubicRing16 :=
  AdjoinRoot.powerBasis' cubicPolynomial16_monic

/-- The canonical power basis, reindexed by the literal type `Fin 3`. -/
def cubicBasis16 : Basis (Fin 3) R CubicRing16 :=
  cubicPowerBasis16.basis.reindex
    (finCongr (by
      simpa only [cubicPowerBasis16, AdjoinRoot.powerBasis'_dim] using
        cubicPolynomial16_natDegree))

@[simp]
private theorem cubicBasis16_apply (i : Fin 3) :
    cubicBasis16 i = tau16 ^ (i : ℕ) := by
  rw [cubicBasis16, Basis.reindex_apply,
    cubicPowerBasis16.basis_eq_pow, finCongr_symm_apply_coe]
  rfl

/-- Coefficient vectors and the cubic residue ring are linearly equivalent
via the power basis `1, τ, τ²`. -/
def fromVec : (Fin 3 → R) ≃ₗ[R] CubicRing16 :=
  cubicBasis16.equivFun.symm

@[simp]
theorem fromVec_apply (v : Fin 3 → R) :
    fromVec v =
      algebraMap R CubicRing16 (v 0) +
        algebraMap R CubicRing16 (v 1) * tau16 +
          algebraMap R CubicRing16 (v 2) * tau16 ^ 2 := by
  simp only [fromVec, Basis.equivFun_symm_apply, Fin.sum_univ_three,
    cubicBasis16_apply, Algebra.smul_def]
  norm_num

/-- The defining relation in the cubic residue ring. -/
theorem tau16_cubic : tau16 ^ 3 = 3 * tau16 + 1 := by
  have h : AdjoinRoot.mk cubicPolynomial16 cubicPolynomial16 = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk cubicPolynomial16
    (X ^ 3 - 3 * X - 1 : Polynomial R) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_one,
    AdjoinRoot.mk_X] at h
  have h' : tau16 ^ 3 - 3 * tau16 - 1 = 0 := by
    simpa only [tau16] using h
  linear_combination h'

private theorem tau16_pow_four : tau16 ^ 4 = 3 * tau16 ^ 2 + tau16 := by
  calc
    tau16 ^ 4 = tau16 * tau16 ^ 3 := by ring
    _ = 3 * tau16 ^ 2 + tau16 := by rw [tau16_cubic]; ring

private theorem encoded_product
    (a b c d e f : R) :
    (algebraMap R CubicRing16 a + algebraMap R CubicRing16 b * tau16 +
        algebraMap R CubicRing16 c * tau16 ^ 2) *
      (algebraMap R CubicRing16 d + algebraMap R CubicRing16 e * tau16 +
        algebraMap R CubicRing16 f * tau16 ^ 2) =
      algebraMap R CubicRing16 (a * d + b * f + c * e) +
        algebraMap R CubicRing16
            (a * e + b * d + 3 * (b * f + c * e) + c * f) * tau16 +
          algebraMap R CubicRing16
              (a * f + b * e + c * d + 3 * c * f) * tau16 ^ 2 := by
  calc
    (algebraMap R CubicRing16 a + algebraMap R CubicRing16 b * tau16 +
          algebraMap R CubicRing16 c * tau16 ^ 2) *
        (algebraMap R CubicRing16 d + algebraMap R CubicRing16 e * tau16 +
          algebraMap R CubicRing16 f * tau16 ^ 2) =
        algebraMap R CubicRing16 a * algebraMap R CubicRing16 d +
          (algebraMap R CubicRing16 a * algebraMap R CubicRing16 e +
            algebraMap R CubicRing16 b * algebraMap R CubicRing16 d) * tau16 +
          (algebraMap R CubicRing16 a * algebraMap R CubicRing16 f +
            algebraMap R CubicRing16 b * algebraMap R CubicRing16 e +
            algebraMap R CubicRing16 c * algebraMap R CubicRing16 d) * tau16 ^ 2 +
          (algebraMap R CubicRing16 b * algebraMap R CubicRing16 f +
            algebraMap R CubicRing16 c * algebraMap R CubicRing16 e) * tau16 ^ 3 +
          algebraMap R CubicRing16 c * algebraMap R CubicRing16 f * tau16 ^ 4 := by
            ring
    _ = algebraMap R CubicRing16 (a * d + b * f + c * e) +
          algebraMap R CubicRing16
              (a * e + b * d + 3 * (b * f + c * e) + c * f) * tau16 +
            algebraMap R CubicRing16
                (a * f + b * e + c * d + 3 * c * f) * tau16 ^ 2 := by
      rw [tau16_cubic, tau16_pow_four]
      simp only [map_add, map_mul, map_ofNat]
      ring

/-- The power-basis equivalence turns the custom coefficient
multiplication into ordinary multiplication in the quotient ring. -/
theorem fromVec_mul (x y : Fin 3 → R) :
    fromVec
        (XOneEighteenDyadicCubicCertificate.mul x y) =
      fromVec x * fromVec y := by
  simp only [fromVec_apply]
  change
    algebraMap R CubicRing16 (x 0 * y 0 + x 1 * y 2 + x 2 * y 1) +
        algebraMap R CubicRing16
            (x 0 * y 1 + x 1 * y 0 + 3 * (x 1 * y 2 + x 2 * y 1) +
              x 2 * y 2) * tau16 +
          algebraMap R CubicRing16
              (x 0 * y 2 + x 1 * y 1 + x 2 * y 0 + 3 * x 2 * y 2) *
            tau16 ^ 2 =
      (algebraMap R CubicRing16 (x 0) +
          algebraMap R CubicRing16 (x 1) * tau16 +
            algebraMap R CubicRing16 (x 2) * tau16 ^ 2) *
        (algebraMap R CubicRing16 (y 0) +
          algebraMap R CubicRing16 (y 1) * tau16 +
            algebraMap R CubicRing16 (y 2) * tau16 ^ 2)
  exact (encoded_product (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)).symm

/-! ## The bounded normalized-relative-cubic certificate -/

/-- Evaluation of the normalized relative cubic on coefficient vectors.
The two coefficient vectors are respectively `τ² - 3` and
`-2τ² + τ + 4`. -/
def normalizedRelativeCubicValue (z : Fin 3 → R) : Fin 3 → R :=
  XOneEighteenDyadicCubicCertificate.mul
      (XOneEighteenDyadicCubicCertificate.mul z z) z +
    XOneEighteenDyadicCubicCertificate.mul ![-3, 0, 1]
      (XOneEighteenDyadicCubicCertificate.mul z z) +
    XOneEighteenDyadicCubicCertificate.mul ![4, 1, -2] z -
    XOneEighteenDyadicGeneratorCertificate.one

private theorem normalizedRelativeCubicValue_eq_zero_iff_coordinates :
    ∀ a b c : R,
      normalizedRelativeCubicValue ![a, b, c] = 0 ↔
        ![a, b, c] =
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  decide +kernel +revert

/-- The normalized relative cubic has exactly one root among the `16³`
coefficient vectors.  This is the complete bounded enumeration used by the
integral reduction bridge.  The three coordinates are enumerated separately
so that the kernel proof term does not traverse a `4096`-element function
enumeration at once. -/
theorem normalizedRelativeCubicValue_eq_zero_iff :
    ∀ z : Fin 3 → R,
      normalizedRelativeCubicValue z = 0 ↔
        z = XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  intro z
  have hz : ![z 0, z 1, z 2] = z := by
    funext i
    fin_cases i <;> rfl
  rw [← hz]
  exact normalizedRelativeCubicValue_eq_zero_iff_coordinates
    (z 0) (z 1) (z 2)

@[simp]
theorem fromVec_tau : fromVec ![0, 1, 0] = tau16 := by
  simp [fromVec_apply]

@[simp]
theorem fromVec_one :
    fromVec XOneEighteenDyadicGeneratorCertificate.one = 1 := by
  simp [XOneEighteenDyadicGeneratorCertificate.one, fromVec_apply]

/-- Custom powers of a coefficient vector become ordinary powers in the
quotient ring. -/
@[simp]
theorem fromVec_cubicPow (x : Fin 3 → R) (n : ℕ) :
    fromVec (XOneEighteenDyadicGeneratorCertificate.cubicPow x n) =
      fromVec x ^ n := by
  induction n with
  | zero =>
      simp only [XOneEighteenDyadicGeneratorCertificate.cubicPow,
        fromVec_one, pow_zero]
  | succ n ih =>
      rw [XOneEighteenDyadicGeneratorCertificate.cubicPow, fromVec_mul,
        ih, pow_succ]

@[simp]
private theorem fromVec_quadratic_coefficient :
    fromVec ![-3, 0, 1] = tau16 ^ 2 - 3 := by
  simp only [fromVec_apply, AdjoinRoot.algebraMap_eq, Fin.isValue,
    Matrix.cons_val_zero, map_neg, Matrix.cons_val_one, map_zero, zero_mul,
    add_zero, Matrix.cons_val, map_one, one_mul, map_ofNat]
  ring

@[simp]
private theorem fromVec_linear_coefficient :
    fromVec ![4, 1, -2] = -2 * tau16 ^ 2 + tau16 + 4 := by
  simp only [fromVec_apply, AdjoinRoot.algebraMap_eq, Fin.isValue,
    Matrix.cons_val_zero, map_neg, Matrix.cons_val_one, Matrix.cons_val,
    map_one, one_mul, map_ofNat]
  ring

/-- Evaluation of the vector cubic agrees with evaluation of the displayed
cubic in the actual quotient ring. -/
@[simp]
theorem fromVec_normalizedRelativeCubicValue (z : Fin 3 → R) :
    fromVec (normalizedRelativeCubicValue z) =
      fromVec z ^ 3 + (tau16 ^ 2 - 3) * fromVec z ^ 2 +
        (-2 * tau16 ^ 2 + tau16 + 4) * fromVec z - 1 := by
  simp only [normalizedRelativeCubicValue, map_sub, map_add, fromVec_mul,
    fromVec_quadratic_coefficient, fromVec_linear_coefficient,
    fromVec_one]
  ring

/-- The certified vector is indeed a root of the normalized relative
cubic in the actual quotient ring. -/
theorem normalizedRelativeCubic_normalizedGenerator_root :
    let z := fromVec
      XOneEighteenDyadicGeneratorCertificate.normalizedGenerator
    z ^ 3 + (tau16 ^ 2 - 3) * z ^ 2 +
        (-2 * tau16 ^ 2 + tau16 + 4) * z - 1 = 0 := by
  dsimp only
  have hv := (normalizedRelativeCubicValue_eq_zero_iff
    XOneEighteenDyadicGeneratorCertificate.normalizedGenerator).2 rfl
  have himage := congrArg fromVec hv
  simpa only [fromVec_normalizedRelativeCubicValue, map_zero] using himage

/-- Any root of the normalized relative cubic in the actual quotient ring
is the certified reduction `7 + 10τ + τ²`. -/
theorem normalizedRelativeCubic_root_eq (z : CubicRing16)
    (h : z ^ 3 + (tau16 ^ 2 - 3) * z ^ 2 +
      (-2 * tau16 ^ 2 + tau16 + 4) * z - 1 = 0) :
    z = fromVec
      XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  obtain ⟨v, rfl⟩ := fromVec.surjective z
  have himage :
      fromVec (normalizedRelativeCubicValue v) = fromVec 0 := by
    rw [fromVec_normalizedRelativeCubicValue, map_zero]
    exact h
  have hv : normalizedRelativeCubicValue v = 0 :=
    fromVec.injective himage
  exact congrArg fromVec
    ((normalizedRelativeCubicValue_eq_zero_iff v).mp hv)

/-- Exact uniqueness formulation for the root certificate. -/
theorem normalizedRelativeCubic_eq_zero_iff (z : CubicRing16) :
    z ^ 3 + (tau16 ^ 2 - 3) * z ^ 2 +
        (-2 * tau16 ^ 2 + tau16 + 4) * z - 1 = 0 ↔
      z = fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  constructor
  · exact normalizedRelativeCubic_root_eq z
  · intro hz
    rw [hz]
    exact normalizedRelativeCubic_normalizedGenerator_root

/-! ## Exact evaluations of the four generator polynomials -/

private theorem fromVec_mul_two (v : Fin 3 → R) :
    fromVec (v * 2) = fromVec v * 2 := by
  have h : v * 2 = (2 : R) • v := by
    ext i
    simp [smul_eq_mul, mul_comm]
  rw [h, map_smul, Algebra.smul_def, map_ofNat]
  ring

private theorem fromVec_mul_three (v : Fin 3 → R) :
    fromVec (v * 3) = fromVec v * 3 := by
  have h : v * 3 = (3 : R) • v := by
    ext i
    simp [smul_eq_mul, mul_comm]
  rw [h, map_smul, Algebra.smul_def, map_ofNat]
  ring

private theorem fromVec_mul_four (v : Fin 3 → R) :
    fromVec (v * 4) = fromVec v * 4 := by
  have h : v * 4 = (4 : R) • v := by
    ext i
    simp [smul_eq_mul, mul_comm]
  rw [h, map_smul, Algebra.smul_def, map_ofNat]
  ring

private theorem fromVec_mul_six (v : Fin 3 → R) :
    fromVec (v * 6) = fromVec v * 6 := by
  have h : v * 6 = (6 : R) • v := by
    ext i
    simp [smul_eq_mul, mul_comm]
  rw [h, map_smul, Algebra.smul_def, map_ofNat]
  ring

private theorem fromVec_mul_seven (v : Fin 3 → R) :
    fromVec (v * 7) = fromVec v * 7 := by
  have h : v * 7 = (7 : R) • v := by
    ext i
    simp [smul_eq_mul, mul_comm]
  rw [h, map_smul, Algebra.smul_def, map_ofNat]
  ring

private theorem fromVec_mul_eight (v : Fin 3 → R) :
    fromVec (v * 8) = fromVec v * 8 := by
  have h : v * 8 = (8 : R) • v := by
    ext i
    simp [smul_eq_mul, mul_comm]
  rw [h, map_smul, Algebra.smul_def, map_ofNat]
  ring

/-- The first certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_firstGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.firstGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -z ^ 8 + 3 * z ^ 7 - 8 * z ^ 5 + 6 * z ^ 4 +
        8 * z ^ 3 - 7 * z ^ 2 - 3 * z + 3 := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 8 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 7 -
        (8 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 5 +
        (6 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 4 +
        (8 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
        (7 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 -
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.one) = _
  simp only [map_add, map_sub, map_neg, map_smul, fromVec_cubicPow,
    fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]
  ring

/-- The second certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_secondGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.secondGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -z ^ 6 + 3 * z ^ 5 - z ^ 4 - 4 * z ^ 3 +
        3 * z ^ 2 + 3 * z - 1 := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 6 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 5 -
        XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 4 -
        (4 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator -
        XOneEighteenDyadicGeneratorCertificate.one) = _
  simp only [map_add, map_sub, map_neg, map_smul, fromVec_cubicPow,
    fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]

/-- The third certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_thirdGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.thirdGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -(z ^ 3 - z ^ 2 + 1) *
        (z ^ 5 - 3 * z ^ 4 + z ^ 3 + 4 * z ^ 2 - 3 * z - 4) := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicCubicCertificate.mul
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
          XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 +
          XOneEighteenDyadicGeneratorCertificate.one)
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 5 -
          (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 4 +
          XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 +
          (4 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 -
          (3 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator -
          (4 : R) • XOneEighteenDyadicGeneratorCertificate.one)) = _
  simp only [map_neg, fromVec_mul, map_add, map_sub, map_smul,
    fromVec_cubicPow, fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]
  ring

/-- The fourth certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_fourthGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.fourthGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -(z ^ 3 - 2 * z ^ 2 + z + 1) *
        (z ^ 3 - z ^ 2 - 2 * z - 1) := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicCubicCertificate.mul
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
          (2 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 +
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator +
          XOneEighteenDyadicGeneratorCertificate.one)
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
          XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 -
          (2 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator -
          XOneEighteenDyadicGeneratorCertificate.one)) = _
  simp only [map_neg, fromVec_mul, map_add, map_sub, map_smul,
    fromVec_cubicPow, fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]
  ring

/-- A square in the actual quotient ring gives a square coefficient triple
for the custom multiplication used by the finite certificate. -/
theorem certificate_isSquare_of_isSquare (v : Fin 3 → R)
    (hv : IsSquare (fromVec v)) :
    XOneEighteenDyadicCubicCertificate.IsSquare v := by
  rcases hv with ⟨z, hz⟩
  obtain ⟨w, rfl⟩ := fromVec.surjective z
  refine ⟨w 0, w 1, w 2, ?_⟩
  have hw : ![w 0, w 1, w 2] = w := by
    funext i
    fin_cases i <;> rfl
  rw [hw]
  apply fromVec.injective
  rw [fromVec_mul, hz]

/-- Every nonidentity product in the generator certificate is nonsquare in
the actual cubic residue ring modulo `16`. -/
theorem fromVec_maskedProduct_nonsquare (i : Fin 15) :
    ¬ IsSquare
      (fromVec
        (XOneEighteenDyadicGeneratorCertificate.maskedProduct
          (XOneEighteenDyadicGeneratorCertificate.nonzeroMask i))) := by
  intro h
  exact XOneEighteenDyadicGeneratorCertificate.maskedProduct_nonsquare i
    (certificate_isSquare_of_isSquare _ h)

end

end MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate
