/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionIntegralElements
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionExactSignature
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# A Minkowski bound for the `X₁(18)` two-division compositum

The normalized integral generator supplies an order of discriminant
`-272097792`.  Comparing its rational basis with an integral basis proves the
required upper bound on the absolute field discriminant; no maximal-order
claim is made.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionMinkowski

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionExactSignature

private def normalizedRootPowerBasis :
    PowerBasis ℚ (AdjoinRoot normalizedPolynomial) :=
  AdjoinRoot.powerBasis normalizedPolynomial_monic.ne_zero

private theorem normalizedPolynomial_derivative_natDegree :
    normalizedPolynomial.derivative.natDegree =
      normalizedPolynomial.natDegree - 1 := by
  have hderiv : normalizedPolynomial.derivative.natDegree = 8 := by
    simp only [normalizedPolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
      derivative_one, mul_one, Nat.cast_ofNat, zero_mul, sub_zero]
    compute_degree!
  rw [hderiv, normalizedPolynomial_natDegree]

private theorem normalizedRootPowerBasis_discriminant :
    Algebra.discr ℚ normalizedRootPowerBasis.basis =
      normalizedPolynomial.discr := by
  exact AdjoinRoot.discr_powerBasis_eq_discr normalizedPolynomial_monic
    normalizedPolynomial_derivative_natDegree

private def normalizedDiscriminantBasis :
    Basis (Fin normalizedRootPowerBasis.dim) ℚ M :=
  normalizedRootPowerBasis.basis.map normalizedAdjoinRootEquiv.toLinearEquiv

private theorem normalizedDiscriminantBasis_discriminant :
    Algebra.discr ℚ normalizedDiscriminantBasis = -272097792 := by
  rw [← normalizedPolynomial_discr,
    ← normalizedRootPowerBasis_discriminant]
  calc
    Algebra.discr ℚ normalizedDiscriminantBasis =
        Algebra.discr ℚ
          (normalizedAdjoinRootEquiv ∘ normalizedRootPowerBasis.basis) := by
            congr 1
    _ = Algebra.discr ℚ normalizedRootPowerBasis.basis :=
      (Algebra.discr_eq_discr_of_algEquiv normalizedRootPowerBasis.basis
        normalizedAdjoinRootEquiv).symm

private theorem normalizedDiscriminantBasis_isIntegral
    (i : Fin normalizedRootPowerBasis.dim) :
    IsIntegral ℤ (normalizedDiscriminantBasis i) := by
  rw [normalizedDiscriminantBasis, Basis.map_apply,
    normalizedRootPowerBasis.basis_eq_pow]
  change IsIntegral ℤ
    (normalizedAdjoinRootEquiv (normalizedRootPowerBasis.gen ^ (i : ℕ)))
  rw [map_pow, show normalizedRootPowerBasis.gen =
      AdjoinRoot.root normalizedPolynomial by rfl,
    normalizedAdjoinRootEquiv_root]
  exact normalizedElement_isIntegral_int.pow i

private def reindexedIntegralBasis :
    Basis (Fin normalizedRootPowerBasis.dim) ℚ M :=
  (integralBasis M).reindex
    ((integralBasis M).indexEquiv normalizedDiscriminantBasis)

private theorem reindexedIntegralBasis_discriminant :
    Algebra.discr ℚ reindexedIntegralBasis =
      (NumberField.discr M : ℚ) := by
  simp only [reindexedIntegralBasis, Basis.coe_reindex,
    Algebra.discr_reindex, NumberField.coe_discr]

private theorem changeMatrix_entry_isIntegral
    (i j : Fin normalizedRootPowerBasis.dim) :
    IsIntegral ℤ
      (reindexedIntegralBasis.toMatrix normalizedDiscriminantBasis i j) := by
  let x : NumberField.RingOfIntegers M :=
    ⟨normalizedDiscriminantBasis j,
      normalizedDiscriminantBasis_isIntegral j⟩
  let e := (integralBasis M).indexEquiv normalizedDiscriminantBasis
  have hrepr := NumberField.integralBasis_repr_apply (K := M) x (e.symm i)
  rw [Basis.toMatrix_apply]
  change IsIntegral ℤ (reindexedIntegralBasis.repr (x : M) i)
  rw [show reindexedIntegralBasis.repr (x : M) i =
      (integralBasis M).repr (x : M) (e.symm i) by
    simp only [reindexedIntegralBasis, Basis.repr_reindex_apply]
    rfl]
  rw [hrepr]
  exact isIntegral_algebraMap

/-- The absolute field discriminant is bounded by the discriminant of the
explicit normalized integral order. -/
theorem field_discriminant_natAbs_le :
    (NumberField.discr M).natAbs ≤ 272097792 := by
  have hchange :
      Algebra.discr ℚ normalizedDiscriminantBasis =
        (reindexedIntegralBasis.toMatrix normalizedDiscriminantBasis).det ^ 2 *
          Algebra.discr ℚ reindexedIntegralBasis := by
    nth_rw 1 [← reindexedIntegralBasis.toMatrix_map_vecMul
      normalizedDiscriminantBasis]
    rw [Algebra.discr_of_matrix_vecMul]
  rw [normalizedDiscriminantBasis_discriminant,
    reindexedIntegralBasis_discriminant] at hchange
  have hdet : IsIntegral ℤ
      (reindexedIntegralBasis.toMatrix normalizedDiscriminantBasis).det :=
    IsIntegral.det changeMatrix_entry_isIntegral
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdet
  rw [← hz] at hchange
  have hint : (-272097792 : ℤ) = z ^ 2 * NumberField.discr M := by
    apply Rat.intCast_inj.mp
    norm_num
    exact hchange
  have hdvd : NumberField.discr M ∣ (-272097792 : ℤ) := by
    exact ⟨z ^ 2, by rw [hint]; ring⟩
  simpa using Int.natAbs_le_of_dvd_ne_zero hdvd
    (by norm_num : (-272097792 : ℤ) ≠ 0)

/-- The classical Minkowski bound for the degree-nine compositum. -/
def minkowskiBound : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces M *
    (Nat.factorial (Module.finrank ℚ M) /
      (Module.finrank ℚ M) ^ (Module.finrank ℚ M) *
        Real.sqrt |NumberField.discr M|)

private theorem abs_discr_cast_le :
    (((|NumberField.discr M| : ℤ) : ℝ)) ≤ 272097792 := by
  have hInt : |NumberField.discr M| ≤ (272097792 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast field_discriminant_natAbs_le
  exact_mod_cast hInt

private theorem sqrt_abs_discr_lt :
    Real.sqrt (((|NumberField.discr M| : ℤ) : ℝ)) < 16500 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 16500)]
  nlinarith [abs_discr_cast_le]

/-- The exact Minkowski expression is strictly less than `32`. -/
theorem minkowskiBound_lt_thirtytwo : minkowskiBound < 32 := by
  rw [minkowskiBound, nrComplexPlaces_eq_three, finrank_M_over_rat]
  norm_num [Nat.factorial]
  rw [← Int.cast_abs]
  calc
    (4 / Real.pi) ^ 3 *
        (4480 / 4782969 *
          Real.sqrt (((|NumberField.discr M| : ℤ) : ℝ))) <
      (4 / (3.14 : ℝ)) ^ 3 * (4480 / 4782969 * 16500) := by
        gcongr
        · exact Real.pi_gt_d2
        · exact sqrt_abs_discr_lt
    _ < 32 := by norm_num

end

end MazurTorsion.XOneEighteenTwoDivisionMinkowski
