/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrimitive

/-!
# The sign of the `X₁(18)` two-division discriminant

This file gives a bounded Euclidean certificate for the sign of the
degree-nine primitive polynomial.  Each line of the remainder chain is a
polynomial identity checked by `ring`; the resultant identities then show
that the discriminant is negative.  Transporting the corresponding basis
discriminant to an integral basis proves that the number-field discriminant
is negative, and hence that the number of complex places is odd.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionDiscriminant

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive

private def p₀ : Polynomial ℚ := primitivePolynomial

private def p₁ : Polynomial ℚ :=
  X ^ 8 - 14 * X ^ 6 + 18 * X ^ 5 + 45 * X ^ 4 -
    36 * X ^ 3 + 135 * X ^ 2 + 81

private def p₂ : Polynomial ℚ :=
  -4 * X ^ 7 + 9 * X ^ 6 + 36 * X ^ 5 - 45 * X ^ 4 +
    270 * X ^ 3 + 648 * X + 729

private def p₃ : Polynomial ℚ :=
  X ^ 6 + 432 * X ^ 5 + 1395 * X ^ 4 + 1854 * X ^ 3 +
    4752 * X ^ 2 + 8748 * X + 7857

private def p₄ : Polynomial ℚ :=
  -862 * X ^ 5 - 2796 * X ^ 4 - 3705 * X ^ 3 -
    9513 * X ^ 2 - 17550 * X - 15795

private def p₅ : Polynomial ℚ :=
  -2563 * X ^ 4 + 13305 * X ^ 3 - 12276 * X ^ 2 +
    44037 * X + 75708

private def p₆ : Polynomial ℚ :=
  -439913 * X ^ 3 + 123783 * X ^ 2 - 1979568 * X - 2717793

private def p₇ : Polynomial ℚ :=
  1577 * X ^ 2 + 1829 * X - 1147

private def p₈ : Polynomial ℚ := -39 * X - 29

private def p₉ : Polynomial ℚ := -1

/-- One adjacent-degree Euclidean step for a resultant.  The explicit
remainder chains below always have degrees `k+2`, `k+1`, and `k` and a
linear quotient. -/
private theorem resultant_step {f g r q : Polynomial ℚ} {c : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : f = C c * r + g * q) :
    f.resultant g = g.leadingCoeff ^ 2 * c ^ (k + 1) * g.resultant r := by
  change resultant f g f.natDegree g.natDegree = _
  rw [hf, hg, hrel]
  rw [resultant_add_mul_left (f := C c * r) (g := g) (p := q)
    (m := k + 2) (n := k + 1)]
  · rw [show k + 2 = k + 2 by rfl]
    rw [resultant_add_left_deg (f := C c * r) (g := g)
      (m := k) (n := k + 1) (k := 2)]
    · rw [resultant_C_mul_left, resultant_comm]
      rw [Even.neg_one_pow (⟨k + 1, by omega⟩),
        Even.neg_one_pow (Nat.even_mul_succ_self k)]
      rw [← hg, coeff_natDegree]
      rw [← hr]
      simp only [one_mul]
      ring
    · exact (natDegree_C_mul_le c r).trans_eq hr
  · omega
  · omega

private theorem resultant_neg_iff_step {f g r q : Polynomial ℚ} {c : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : f = C c * r + g * q) (hc : 0 < c) :
    f.resultant g < 0 ↔ g.resultant r < 0 := by
  rw [resultant_step hf hg hr hq hrel]
  have hg₀ : g ≠ 0 := by
    intro hzero
    rw [hzero] at hg
    simp only [natDegree_zero] at hg
    omega
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg₀
  have hfactor : 0 < g.leadingCoeff ^ 2 * c ^ (k + 1) :=
    mul_pos (sq_pos_of_ne_zero hlc) (pow_pos hc _)
  constructor
  · intro hneg
    exact neg_of_mul_neg_right hneg hfactor.le
  · exact mul_neg_of_pos_of_neg hfactor

private theorem resultant_neg_iff_step_scaled
    {f g r q : Polynomial ℚ} {c d : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : C d * f = C c * r + g * q) (hc : 0 < c) (hd : 0 < d) :
    f.resultant g < 0 ↔ g.resultant r < 0 := by
  have hscaledDegree : (C d * f).natDegree = k + 2 := by
    rw [natDegree_C_mul hd.ne', hf]
  have hstep := resultant_neg_iff_step hscaledDegree hg hr hq hrel hc
  have hscaleResultant :
      (C d * f).resultant g = d ^ (k + 1) * f.resultant g := by
    change resultant (C d * f) g (C d * f).natDegree g.natDegree = _
    rw [natDegree_C_mul hd.ne', hf, hg, resultant_C_mul_left]
  rw [hscaleResultant] at hstep
  have hpow : 0 < d ^ (k + 1) := pow_pos hd _
  constructor
  · intro hneg
    exact hstep.mp (mul_neg_of_pos_of_neg hpow hneg)
  · intro hneg
    exact neg_of_mul_neg_right (hstep.mpr hneg) hpow.le

private theorem p₀_degree : p₀.natDegree = 9 := by
  exact primitivePolynomial_natDegree

private theorem p₁_degree : p₁.natDegree = 8 := by
  simp only [p₁]
  compute_degree!

private theorem p₂_degree : p₂.natDegree = 7 := by
  simp only [p₂]
  compute_degree!

private theorem p₃_degree : p₃.natDegree = 6 := by
  simp only [p₃]
  compute_degree!

private theorem p₄_degree : p₄.natDegree = 5 := by
  simp only [p₄]
  compute_degree!

private theorem p₅_degree : p₅.natDegree = 4 := by
  simp only [p₅]
  compute_degree!

private theorem p₆_degree : p₆.natDegree = 3 := by
  simp only [p₆]
  compute_degree!

private theorem p₇_degree : p₇.natDegree = 2 := by
  simp only [p₇]
  compute_degree!

private theorem p₈_degree : p₈.natDegree = 1 := by
  simp only [p₈]
  compute_degree!

private theorem p₉_degree : p₉.natDegree = 0 := by
  simp only [p₉]
  compute_degree!

private theorem p₀_resultant_neg_iff_p₁ :
    p₀.resultant p₁ < 0 ↔ p₁.resultant p₂ < 0 := by
  apply resultant_neg_iff_step (q := X) (c := 1) (k := 7)
  · simpa using p₀_degree
  · simpa using p₁_degree
  · simpa using p₂_degree
  · simp
  · simp only [p₀, p₁, p₂, primitivePolynomial]
    norm_num
    ring
  · norm_num

private theorem p₁_resultant_neg_iff_p₂ :
    p₁.resultant p₂ < 0 ↔ p₂.resultant p₃ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -4 * X - 9) (c := 1) (d := 16) (k := 6)
  · simpa using p₁_degree
  · simpa using p₂_degree
  · simpa using p₃_degree
  · compute_degree!
  · simp only [p₁, p₂, p₃]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₂_resultant_neg_iff_p₃ :
    p₂.resultant p₃ < 0 ↔ p₃.resultant p₄ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := 1737 - 4 * X) (c := 864) (d := 1) (k := 5)
  · simpa using p₂_degree
  · simpa using p₃_degree
  · simpa using p₄_degree
  · compute_degree!
  · simp only [p₂, p₃, p₄]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₃_resultant_neg_iff_p₄ :
    p₃.resultant p₄ < 0 ↔ p₄.resultant p₅ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -431 * X - 184794) (c := 3) (d := 371522) (k := 4)
  · simpa using p₃_degree
  · simpa using p₄_degree
  · simpa using p₅_degree
  · compute_degree!
  · simp only [p₃, p₄, p₅]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₄_resultant_neg_iff_p₅ :
    p₄.resultant p₅ < 0 ↔ p₅.resultant p₆ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := 2209306 * X + 18635058) (c := 557283)
    (d := 6568969) (k := 3)
  · simpa using p₄_degree
  · simpa using p₅_degree
  · simpa using p₆_degree
  · compute_degree!
  · simp only [p₄, p₅, p₆]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₅_resultant_neg_iff_p₆ :
    p₅.resultant p₆ < 0 ↔ p₆.resultant p₇ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := 1127497019 * X - 5535786636) (c := 343373147568)
    (d := 193523447569) (k := 2)
  · simpa using p₅_degree
  · simpa using p₆_degree
  · simpa using p₇_degree
  · compute_degree!
  · simp only [p₅, p₆, p₇]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₆_resultant_neg_iff_p₇ :
    p₆.resultant p₇ < 0 ↔ p₇.resultant p₈ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -693742801 * X + 999806668) (c := 193523447569)
    (d := 2486929) (k := 1)
  · simpa using p₆_degree
  · simpa using p₇_degree
  · simpa using p₈_degree
  · compute_degree!
  · simp only [p₆, p₇, p₈]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₇_resultant_neg_iff_p₈ :
    p₇.resultant p₈ < 0 ↔ p₈.resultant p₉ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -61503 * X - 25598) (c := 2486929) (d := 1521) (k := 0)
  · simpa using p₇_degree
  · simpa using p₈_degree
  · simpa using p₉_degree
  · compute_degree!
  · simp only [p₇, p₈, p₉]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₈_resultant_p₉_neg : p₈.resultant p₉ < 0 := by
  norm_num [p₉, resultant_C_right, p₈_degree]

private theorem p₀_resultant_p₁_neg : p₀.resultant p₁ < 0 := by
  exact p₀_resultant_neg_iff_p₁.mpr
    (p₁_resultant_neg_iff_p₂.mpr
      (p₂_resultant_neg_iff_p₃.mpr
        (p₃_resultant_neg_iff_p₄.mpr
          (p₄_resultant_neg_iff_p₅.mpr
            (p₅_resultant_neg_iff_p₆.mpr
              (p₆_resultant_neg_iff_p₇.mpr
                (p₇_resultant_neg_iff_p₈.mpr p₈_resultant_p₉_neg)))))))

private theorem primitivePolynomial_derivative :
    primitivePolynomial.derivative = C 9 * p₁ := by
  simp only [primitivePolynomial, p₁, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
    Nat.cast_ofNat, mul_one, zero_mul]
  simp only [Polynomial.C_ofNat]
  norm_num
  ring

private theorem primitivePolynomial_resultant_derivative_neg :
    resultant primitivePolynomial primitivePolynomial.derivative 9 8 < 0 := by
  rw [primitivePolynomial_derivative, resultant_C_mul_right]
  apply mul_neg_of_pos_of_neg
  · norm_num
  · simpa only [p₀, primitivePolynomial_natDegree, p₁_degree] using
      p₀_resultant_p₁_neg

/-- The degree-nine primitive polynomial has negative discriminant.  The
proof is the finite pseudo-remainder chain above, rather than an external
computer-algebra discriminant computation. -/
theorem primitivePolynomial_discr_neg : primitivePolynomial.discr < 0 := by
  have hdegree : 0 < primitivePolynomial.degree :=
    natDegree_pos_iff_degree_pos.mp (by rw [primitivePolynomial_natDegree]; norm_num)
  have hres := Polynomial.resultant_deriv (f := primitivePolynomial) hdegree
  rw [primitivePolynomial_natDegree,
    primitivePolynomial_monic.leadingCoeff] at hres
  norm_num at hres
  rw [← hres]
  exact primitivePolynomial_resultant_derivative_neg

private def rootPowerBasis : PowerBasis ℚ (AdjoinRoot primitivePolynomial) :=
  AdjoinRoot.powerBasis primitivePolynomial_monic.ne_zero

private theorem primitivePolynomial_derivative_natDegree :
    primitivePolynomial.derivative.natDegree =
      primitivePolynomial.natDegree - 1 := by
  rw [primitivePolynomial_derivative,
    natDegree_C_mul (by norm_num : (9 : ℚ) ≠ 0), p₁_degree,
    primitivePolynomial_natDegree]

private theorem rootPowerBasis_discriminant :
    Algebra.discr ℚ rootPowerBasis.basis = primitivePolynomial.discr := by
  exact AdjoinRoot.discr_powerBasis_eq_discr primitivePolynomial_monic
    primitivePolynomial_derivative_natDegree

private def primitiveDiscriminantBasis :
    Basis (Fin rootPowerBasis.dim) ℚ M :=
  rootPowerBasis.basis.map primitiveAdjoinRootEquiv.toLinearEquiv

private theorem primitiveDiscriminantBasis_discriminant :
    Algebra.discr ℚ primitiveDiscriminantBasis =
      primitivePolynomial.discr := by
  rw [← rootPowerBasis_discriminant]
  calc
    Algebra.discr ℚ primitiveDiscriminantBasis =
        Algebra.discr ℚ
          (primitiveAdjoinRootEquiv ∘ rootPowerBasis.basis) := by
            congr 1
    _ = Algebra.discr ℚ rootPowerBasis.basis :=
      (Algebra.discr_eq_discr_of_algEquiv rootPowerBasis.basis
        primitiveAdjoinRootEquiv).symm

private theorem primitiveDiscriminantBasis_discr_neg :
    Algebra.discr ℚ primitiveDiscriminantBasis < 0 := by
  rw [primitiveDiscriminantBasis_discriminant]
  exact primitivePolynomial_discr_neg

/-- The number-field discriminant of the two-division compositum is
negative. -/
theorem field_discriminant_neg : NumberField.discr M < 0 := by
  let integralBasis' : Basis (Fin rootPowerBasis.dim) ℚ M :=
    (integralBasis M).reindex
      ((integralBasis M).indexEquiv primitiveDiscriminantBasis)
  have hintegral :
      Algebra.discr ℚ integralBasis' = (NumberField.discr M : ℚ) := by
    dsimp only [integralBasis']
    rw [Basis.coe_reindex, Algebra.discr_reindex, ← NumberField.coe_discr]
  have hchange :
      Algebra.discr ℚ primitiveDiscriminantBasis =
        (integralBasis'.toMatrix primitiveDiscriminantBasis).det ^ 2 *
          Algebra.discr ℚ integralBasis' := by
    nth_rw 1 [← integralBasis'.toMatrix_map_vecMul primitiveDiscriminantBasis]
    rw [Algebra.discr_of_matrix_vecMul]
  rw [hintegral] at hchange
  have hcast : (NumberField.discr M : ℚ) < 0 := by
    nlinarith [sq_nonneg
      (integralBasis'.toMatrix primitiveDiscriminantBasis).det,
      primitiveDiscriminantBasis_discr_neg]
  exact_mod_cast hcast

/-- The degree-nine two-division compositum has an odd number of complex
places. -/
theorem nrComplexPlaces_odd :
    Odd (NumberField.InfinitePlace.nrComplexPlaces M) := by
  have hsign := NumberField.sign_discr M
  rw [Int.sign_eq_neg_one_of_neg field_discriminant_neg] at hsign
  exact (neg_one_pow_eq_neg_one_iff_odd (R := ℤ) (by norm_num)).mp hsign.symm

end

end MazurTorsion.XOneEighteenTwoDivisionDiscriminant
