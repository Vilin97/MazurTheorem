/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrimitive

/-!
# A small-discriminant model of the `X₁(18)` two-division compositum

Starting from the primitive element `u = t - s`, this file constructs a
second generator with a substantially smaller defining polynomial.  Both
changes of generator are checked by explicit bounded polynomial identities.

The resulting power basis is a power basis over `ℚ`.  No assertion is made
that its integral span is the full ring of integers.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive

/-- The normalized degree-nine polynomial. -/
def normalizedPolynomial : Polynomial ℚ :=
  X ^ 9 - 3 * X ^ 8 + 7 * X ^ 6 - 3 * X ^ 5 - 9 * X ^ 4 +
    3 * X ^ 3 + 6 * X ^ 2 - 1

theorem normalizedPolynomial_monic : normalizedPolynomial.Monic := by
  simp only [normalizedPolynomial]
  monicity <;> norm_num

theorem normalizedPolynomial_natDegree :
    normalizedPolynomial.natDegree = 9 := by
  simp only [normalizedPolynomial]
  compute_degree!

private def discrP₀ : Polynomial ℚ := normalizedPolynomial

private def discrP₁ : Polynomial ℚ :=
  9 * X ^ 8 - 24 * X ^ 7 + 42 * X ^ 5 - 15 * X ^ 4 -
    36 * X ^ 3 + 9 * X ^ 2 + 12 * X

private def discrP₂ : Polynomial ℚ :=
  8 * X ^ 7 - 21 * X ^ 6 - 2 * X ^ 5 + 50 * X ^ 4 -
    6 * X ^ 3 - 45 * X ^ 2 - 4 * X + 9

private def discrP₃ : Polynomial ℚ :=
  3 * X ^ 6 - 34 * X ^ 5 - 14 * X ^ 4 + 34 * X ^ 3 +
    27 * X ^ 2 + 4 * X + 1

private def discrP₄ : Polynomial ℚ :=
  58 * X ^ 5 + 20 * X ^ 4 - 61 * X ^ 3 - 48 * X ^ 2 - 7 * X - 1

private def discrP₅ : Polynomial ℚ :=
  231 * X ^ 4 - 68 * X ^ 3 - 305 * X ^ 2 - 33 * X + 74

private def discrP₆ : Polynomial ℚ :=
  1681 * X ^ 3 + 586 * X ^ 2 - 1287 * X - 817

private def discrP₇ : Polynomial ℚ :=
  337 * X ^ 2 + 152 * X - 8

private def discrP₈ : Polynomial ℚ := 47 * X + 33

private def discrP₉ : Polynomial ℚ := 1

private theorem discrP₀_degree : discrP₀.natDegree = 9 := by
  simpa only [discrP₀] using normalizedPolynomial_natDegree

private theorem discrP₁_degree : discrP₁.natDegree = 8 := by
  simp only [discrP₁]
  compute_degree!

private theorem discrP₂_degree : discrP₂.natDegree = 7 := by
  simp only [discrP₂]
  compute_degree!

private theorem discrP₃_degree : discrP₃.natDegree = 6 := by
  simp only [discrP₃]
  compute_degree!

private theorem discrP₄_degree : discrP₄.natDegree = 5 := by
  simp only [discrP₄]
  compute_degree!

private theorem discrP₅_degree : discrP₅.natDegree = 4 := by
  simp only [discrP₅]
  compute_degree!

private theorem discrP₆_degree : discrP₆.natDegree = 3 := by
  simp only [discrP₆]
  compute_degree!

private theorem discrP₇_degree : discrP₇.natDegree = 2 := by
  simp only [discrP₇]
  compute_degree!

private theorem discrP₈_degree : discrP₈.natDegree = 1 := by
  simp only [discrP₈]
  compute_degree!

private theorem discrP₉_degree : discrP₉.natDegree = 0 := by
  simp only [discrP₉, natDegree_one]

private theorem discrP₁_leadingCoeff : discrP₁.leadingCoeff = 9 := by
  rw [← coeff_natDegree, discrP₁_degree]
  norm_num [discrP₁]
  simp only [coeff_X]
  norm_num

private theorem discrP₂_leadingCoeff : discrP₂.leadingCoeff = 8 := by
  rw [← coeff_natDegree, discrP₂_degree]
  norm_num [discrP₂]
  simp only [coeff_X]
  norm_num

private theorem discrP₃_leadingCoeff : discrP₃.leadingCoeff = 3 := by
  rw [← coeff_natDegree, discrP₃_degree]
  norm_num [discrP₃]
  simp only [coeff_X, coeff_one]
  norm_num

private theorem discrP₄_leadingCoeff : discrP₄.leadingCoeff = 58 := by
  rw [← coeff_natDegree, discrP₄_degree]
  norm_num [discrP₄]
  simp only [coeff_X, coeff_one]
  norm_num

private theorem discrP₅_leadingCoeff : discrP₅.leadingCoeff = 231 := by
  rw [← coeff_natDegree, discrP₅_degree]
  norm_num [discrP₅]
  simp only [coeff_X]
  norm_num

private theorem discrP₆_leadingCoeff : discrP₆.leadingCoeff = 1681 := by
  rw [← coeff_natDegree, discrP₆_degree]
  norm_num [discrP₆]
  simp only [coeff_X]
  norm_num

private theorem discrP₇_leadingCoeff : discrP₇.leadingCoeff = 337 := by
  rw [← coeff_natDegree, discrP₇_degree]
  norm_num [discrP₇]
  simp only [coeff_X]
  norm_num

private theorem discrP₈_leadingCoeff : discrP₈.leadingCoeff = 47 := by
  rw [← coeff_natDegree, discrP₈_degree]
  norm_num [discrP₈]

private theorem resultant_step {f g r q : Polynomial ℚ} {c : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : f = C c * r + g * q) :
    f.resultant g =
      g.leadingCoeff ^ 2 * c ^ (k + 1) * g.resultant r := by
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

private theorem resultant_step_scaled {f g r q : Polynomial ℚ}
    {c d : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : C d * f = C c * r + g * q) (hd : d ≠ 0) :
    f.resultant g =
      g.leadingCoeff ^ 2 * (c / d) ^ (k + 1) * g.resultant r := by
  have hscaledDegree : (C d * f).natDegree = k + 2 := by
    rw [natDegree_C_mul hd, hf]
  have hstep := resultant_step hscaledDegree hg hr hq hrel
  have hscaleResultant :
      (C d * f).resultant g = d ^ (k + 1) * f.resultant g := by
    change resultant (C d * f) g (C d * f).natDegree g.natDegree = _
    rw [natDegree_C_mul hd, hf, hg, resultant_C_mul_left]
  rw [hscaleResultant] at hstep
  apply mul_left_cancel₀ (pow_ne_zero (k + 1) hd)
  calc
    d ^ (k + 1) * f.resultant g =
        g.leadingCoeff ^ 2 * c ^ (k + 1) * g.resultant r := hstep
    _ = d ^ (k + 1) *
        (g.leadingCoeff ^ 2 * (c / d) ^ (k + 1) *
          g.resultant r) := by
      rw [div_pow]
      field_simp [pow_ne_zero (k + 1) hd]

private theorem discrP₀_resultant_discrP₁ :
    discrP₀.resultant discrP₁ =
      discrP₁.leadingCoeff ^ 2 * ((-3 : ℚ) / 27) ^ 8 *
        discrP₁.resultant discrP₂ := by
  apply resultant_step_scaled
    (q := 3 * X - 1) (c := -3) (d := 27) (k := 7)
  · simpa using discrP₀_degree
  · simpa using discrP₁_degree
  · simpa using discrP₂_degree
  · compute_degree!
  · simp only [discrP₀, discrP₁, discrP₂,
      normalizedPolynomial]
    simp only [map_neg, Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₁_resultant_discrP₂ :
    discrP₁.resultant discrP₂ =
      discrP₂.leadingCoeff ^ 2 * ((27 : ℚ) / 64) ^ 7 *
        discrP₂.resultant discrP₃ := by
  apply resultant_step_scaled
    (q := 72 * X - 3) (c := 27) (d := 64) (k := 6)
  · simpa using discrP₁_degree
  · simpa using discrP₂_degree
  · simpa using discrP₃_degree
  · compute_degree!
  · simp only [discrP₁, discrP₂, discrP₃]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₂_resultant_discrP₃ :
    discrP₂.resultant discrP₃ =
      discrP₃.leadingCoeff ^ 2 * ((128 : ℚ) / 9) ^ 6 *
        discrP₃.resultant discrP₄ := by
  apply resultant_step_scaled
    (q := 24 * X + 209) (c := 128) (d := 9) (k := 5)
  · simpa using discrP₂_degree
  · simpa using discrP₃_degree
  · simpa using discrP₄_degree
  · compute_degree!
  · simp only [discrP₂, discrP₃, discrP₄]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₃_resultant_discrP₄ :
    discrP₃.resultant discrP₄ =
      discrP₄.leadingCoeff ^ 2 * ((9 : ℚ) / 1682) ^ 5 *
        discrP₄.resultant discrP₅ := by
  apply resultant_step_scaled
    (q := 87 * X - 1016) (c := 9) (d := 1682) (k := 4)
  · simpa using discrP₃_degree
  · simpa using discrP₄_degree
  · simpa using discrP₅_degree
  · compute_degree!
  · simp only [discrP₃, discrP₄, discrP₅]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₄_resultant_discrP₅ :
    discrP₄.resultant discrP₅ =
      discrP₅.leadingCoeff ^ 2 * ((841 : ℚ) / 53361) ^ 4 *
        discrP₅.resultant discrP₆ := by
  apply resultant_step_scaled
    (q := 13398 * X + 8564) (c := 841) (d := 53361) (k := 3)
  · simpa using discrP₄_degree
  · simpa using discrP₅_degree
  · simpa using discrP₆_degree
  · compute_degree!
  · simp only [discrP₄, discrP₅, discrP₆]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₅_resultant_discrP₆ :
    discrP₅.resultant discrP₆ =
      discrP₆.leadingCoeff ^ 2 * ((-640332 : ℚ) / 2825761) ^ 3 *
        discrP₆.resultant discrP₇ := by
  apply resultant_step_scaled
    (q := 388311 * X - 249674) (c := -640332) (d := 2825761)
      (k := 2)
  · simpa using discrP₅_degree
  · simpa using discrP₆_degree
  · simpa using discrP₇_degree
  · compute_degree!
  · simp only [discrP₅, discrP₆, discrP₇]
    simp only [map_neg, Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num

private theorem discrP₆_resultant_discrP₇ :
    discrP₆.resultant discrP₇ =
      discrP₇.leadingCoeff ^ 2 * ((-2825761 : ℚ) / 113569) ^ 2 *
        discrP₇.resultant discrP₈ := by
  apply resultant_step_scaled
    (q := 566497 * X - 58030) (c := -2825761) (d := 113569)
      (k := 1)
  · simpa using discrP₆_degree
  · simpa using discrP₇_degree
  · simpa using discrP₈_degree
  · compute_degree!
  · simp only [discrP₆, discrP₇, discrP₈]
    simp only [map_neg, Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num

private theorem discrP₇_resultant_discrP₈ :
    discrP₇.resultant discrP₈ =
      discrP₈.leadingCoeff ^ 2 * ((113569 : ℚ) / 2209) ^ 1 *
        discrP₈.resultant discrP₉ := by
  apply resultant_step_scaled
    (q := 15839 * X - 3977) (c := 113569) (d := 2209) (k := 0)
  · simpa using discrP₇_degree
  · simpa using discrP₈_degree
  · simpa using discrP₉_degree
  · compute_degree!
  · simp only [discrP₇, discrP₈, discrP₉]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num

private theorem normalizedPolynomial_derivative :
    normalizedPolynomial.derivative = discrP₁ := by
  simp only [normalizedPolynomial, discrP₁, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
    Nat.cast_ofNat, mul_one, zero_mul]
  simp only [Polynomial.C_ofNat]
  norm_num
  ring

private theorem discrP₀_resultant_discrP₁_exact :
    discrP₀.resultant discrP₁ = -272097792 := by
  rw [discrP₀_resultant_discrP₁, discrP₁_resultant_discrP₂,
    discrP₂_resultant_discrP₃, discrP₃_resultant_discrP₄,
    discrP₄_resultant_discrP₅, discrP₅_resultant_discrP₆,
    discrP₆_resultant_discrP₇, discrP₇_resultant_discrP₈]
  rw [discrP₁_leadingCoeff, discrP₂_leadingCoeff,
    discrP₃_leadingCoeff, discrP₄_leadingCoeff,
    discrP₅_leadingCoeff, discrP₆_leadingCoeff,
    discrP₇_leadingCoeff, discrP₈_leadingCoeff]
  norm_num [discrP₉, resultant_C_right, discrP₈_degree]

/-- The exact discriminant of the normalized rational power basis.  Its
factorization is `-2⁹·3¹²`. -/
theorem normalizedPolynomial_discr :
    normalizedPolynomial.discr = -272097792 := by
  have hdegree : 0 < normalizedPolynomial.degree :=
    natDegree_pos_iff_degree_pos.mp
      (by rw [normalizedPolynomial_natDegree]; norm_num)
  have hres := Polynomial.resultant_deriv
    (f := normalizedPolynomial) hdegree
  rw [normalizedPolynomial_natDegree,
    normalizedPolynomial_monic.leadingCoeff] at hres
  norm_num at hres
  rw [← hres, normalizedPolynomial_derivative]
  have hexact := discrP₀_resultant_discrP₁_exact
  change resultant discrP₀ discrP₁ discrP₀.natDegree
    discrP₁.natDegree = -272097792 at hexact
  rw [discrP₀_degree, discrP₁_degree] at hexact
  simpa only [discrP₀] using hexact

theorem normalizedPolynomial_discr_neg :
    normalizedPolynomial.discr < 0 := by
  rw [normalizedPolynomial_discr]
  norm_num

private def forwardNumerator : Polynomial ℚ :=
  X ^ 8 - 12 * X ^ 7 - 15 * X ^ 6 + 261 * X ^ 5 -
    243 * X ^ 4 - 1377 * X ^ 3 + 1377 * X ^ 2 - 3402 * X + 2673

/-- The forward change of generator, from `u` to the normalized generator. -/
def forwardPolynomial : Polynomial ℚ :=
  C (1 / 5346) * forwardNumerator

/-- The inverse change of generator. -/
def inversePolynomial : Polynomial ℚ :=
  -X ^ 6 + 4 * X ^ 5 - 4 * X ^ 4 - 4 * X ^ 3 +
    8 * X ^ 2 - 4

/-- The normalized generator in the degree-nine compositum. -/
def normalizedElement : M :=
  Polynomial.aeval primitiveElement forwardPolynomial

/-- The normalized generator in the coefficient-by-coefficient form used in
the elimination calculation. -/
theorem normalizedElement_formula :
    normalizedElement =
      (1 / 5346 : M) * primitiveElement ^ 8 -
        (2 / 891 : M) * primitiveElement ^ 7 -
        (5 / 1782 : M) * primitiveElement ^ 6 +
        (29 / 594 : M) * primitiveElement ^ 5 -
        (1 / 22 : M) * primitiveElement ^ 4 -
        (17 / 66 : M) * primitiveElement ^ 3 +
        (17 / 66 : M) * primitiveElement ^ 2 -
        (7 / 11 : M) * primitiveElement + (1 / 2 : M) := by
  simp only [normalizedElement, forwardPolynomial, forwardNumerator, map_mul,
    aeval_C, map_add, map_sub, map_pow, map_ofNat, aeval_X]
  rw [map_div₀, map_one, map_ofNat]
  field_simp
  ring

private def primitiveCertificateLeft : Polynomial ℚ :=
  X ^ 18 - 15 * X ^ 17 + 99 * X ^ 16 - 370 * X ^ 15 +
    822 * X ^ 14 - 951 * X ^ 13 - 38 * X ^ 12 + 1860 * X ^ 11 -
    2490 * X ^ 10 + 583 * X ^ 9 + 1911 * X ^ 8 - 2079 * X ^ 7 +
    325 * X ^ 6 + 729 * X ^ 5 - 417 * X ^ 4 - 18 * X ^ 3 +
    48 * X ^ 2 + 1

private def primitiveCertificateRight : Polynomial ℚ :=
  X ^ 27 - 18 * X ^ 26 + 144 * X ^ 25 - 648 * X ^ 24 +
    1632 * X ^ 23 - 1344 * X ^ 22 - 5118 * X ^ 21 +
    18660 * X ^ 20 - 19032 * X ^ 19 - 28109 * X ^ 18 +
    100284 * X ^ 17 - 69132 * X ^ 16 - 139269 * X ^ 15 +
    291906 * X ^ 14 - 44040 * X ^ 13 - 416277 * X ^ 12 +
    389016 * X ^ 11 + 236328 * X ^ 10 - 567261 * X ^ 9 +
    87198 * X ^ 8 + 428580 * X ^ 7 - 241218 * X ^ 6 -
    178008 * X ^ 5 + 178008 * X ^ 4 + 33333 * X ^ 3 -
    66666 * X ^ 2 + 11573

private def inverseCertificate : Polynomial ℚ :=
  X ^ 39 - 29 * X ^ 38 + 393 * X ^ 37 - 3276 * X ^ 36 +
    18538 * X ^ 35 - 73551 * X ^ 34 + 199718 * X ^ 33 -
    316038 * X ^ 32 - 9396 * X ^ 31 + 1492518 * X ^ 30 -
    3811884 * X ^ 29 + 3342246 * X ^ 28 + 5571187 * X ^ 27 -
    20469077 * X ^ 26 + 20282946 * X ^ 25 + 18324779 * X ^ 24 -
    72486147 * X ^ 23 + 59978295 * X ^ 22 + 62314925 * X ^ 21 -
    176704300 * X ^ 20 + 91592559 * X ^ 19 + 166289854 * X ^ 18 -
    278593602 * X ^ 17 + 39708081 * X ^ 16 + 278712309 * X ^ 15 -
    250996431 * X ^ 14 - 79815546 * X ^ 13 + 259471817 * X ^ 12 -
    96550462 * X ^ 11 - 117315852 * X ^ 10 + 114862674 * X ^ 9 +
    6336218 * X ^ 8 - 51676242 * X ^ 7 + 16470556 * X ^ 6 +
    9620757 * X ^ 5 - 6095061 * X ^ 4 - 229751 * X ^ 3 +
    551578 * X ^ 2 + 5346 * X + 2327

private abbrev NormalizedAdjoinRoot := AdjoinRoot normalizedPolynomial

private abbrev normalizedRoot : NormalizedAdjoinRoot :=
  AdjoinRoot.root normalizedPolynomial

private theorem normalizedRoot_root :
    Polynomial.aeval normalizedRoot normalizedPolynomial = 0 := by
  rw [aeval_def, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root normalizedPolynomial

private theorem primitive_change_identity :
    primitivePolynomial.comp inversePolynomial =
      -primitiveCertificateLeft * primitiveCertificateRight *
        normalizedPolynomial := by
  simp only [primitivePolynomial, inversePolynomial, primitiveCertificateLeft,
    primitiveCertificateRight, normalizedPolynomial, add_comp, sub_comp,
    mul_comp, pow_comp, X_comp, ofNat_comp]
  ring

private theorem inverse_change_identity :
    forwardPolynomial.comp inversePolynomial - X =
      C (1 / 5346) * inverseCertificate * normalizedPolynomial := by
  have hnumerator :
      forwardNumerator.comp inversePolynomial - 5346 * X =
        inverseCertificate * normalizedPolynomial := by
    simp only [forwardNumerator, inversePolynomial, inverseCertificate,
      normalizedPolynomial, add_comp, sub_comp, mul_comp, pow_comp, X_comp,
      ofNat_comp]
    ring
  have hc : C (1 / 5346 : ℚ) * (5346 : Polynomial ℚ) = 1 := by
    change C (1 / 5346 : ℚ) * C (5346 : ℚ) = C (1 : ℚ)
    rw [← C_mul]
    norm_num
  have hscaled := congrArg
    (fun p : Polynomial ℚ ↦ C (1 / 5346) * p) hnumerator
  rw [mul_sub, ← mul_assoc, hc, one_mul] at hscaled
  simpa only [forwardPolynomial, mul_comp, C_comp, mul_assoc] using hscaled

private theorem primitive_of_inverse_root :
    Polynomial.aeval (Polynomial.aeval normalizedRoot inversePolynomial)
      primitivePolynomial = 0 := by
  rw [← Polynomial.aeval_comp, primitive_change_identity]
  simp only [map_mul, normalizedRoot_root, mul_zero]

private theorem forward_of_inverse_root :
    Polynomial.aeval
      (Polynomial.aeval normalizedRoot inversePolynomial) forwardPolynomial =
        normalizedRoot := by
  have h := congrArg (Polynomial.aeval normalizedRoot) inverse_change_identity
  simp only [map_sub, Polynomial.aeval_comp, aeval_X, map_mul, aeval_C,
    normalizedRoot_root, mul_zero] at h
  exact sub_eq_zero.mp h

/-- The explicit old-to-normalized change of presentation. -/
def primitiveToNormalizedHom :
    AdjoinRoot primitivePolynomial →ₐ[ℚ] AdjoinRoot normalizedPolynomial :=
  AdjoinRoot.liftAlgHom primitivePolynomial
    (Algebra.ofId ℚ (AdjoinRoot normalizedPolynomial))
    (Polynomial.aeval normalizedRoot inversePolynomial) (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact primitive_of_inverse_root)

@[simp]
theorem primitiveToNormalizedHom_root :
    primitiveToNormalizedHom (AdjoinRoot.root primitivePolynomial) =
      Polynomial.aeval normalizedRoot inversePolynomial := by
  exact AdjoinRoot.liftAlgHom_root primitivePolynomial _ _ _

private theorem primitiveToNormalizedHom_forward :
    primitiveToNormalizedHom
        (Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
          forwardPolynomial) = normalizedRoot := by
  rw [← Polynomial.aeval_algHom_apply, primitiveToNormalizedHom_root]
  exact forward_of_inverse_root

private instance normalizedAdjoinRootNontrivial :
    Nontrivial (AdjoinRoot normalizedPolynomial) := by
  apply AdjoinRoot.nontrivial
  rw [degree_eq_natDegree normalizedPolynomial_monic.ne_zero,
    normalizedPolynomial_natDegree]
  norm_num

private theorem primitiveToNormalizedHom_injective :
    Function.Injective primitiveToNormalizedHom := by
  exact RingHom.injective primitiveToNormalizedHom.toRingHom

private theorem primitiveToNormalizedHom_surjective :
    Function.Surjective primitiveToNormalizedHom := by
  apply (AlgHom.range_eq_top primitiveToNormalizedHom).mp
  rw [← top_le_iff, ← AdjoinRoot.adjoinRoot_eq_top]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  exact (AlgHom.mem_range primitiveToNormalizedHom).2
    ⟨Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
      forwardPolynomial, primitiveToNormalizedHom_forward⟩

/-- The two explicit changes of generator give an equivalence between the
old and normalized quotient presentations. -/
def primitiveToNormalizedEquiv :
    AdjoinRoot primitivePolynomial ≃ₐ[ℚ] AdjoinRoot normalizedPolynomial :=
  AlgEquiv.ofBijective primitiveToNormalizedHom
    ⟨primitiveToNormalizedHom_injective,
      primitiveToNormalizedHom_surjective⟩

@[simp]
theorem primitiveToNormalizedEquiv_root :
    primitiveToNormalizedEquiv (AdjoinRoot.root primitivePolynomial) =
      Polynomial.aeval normalizedRoot inversePolynomial := by
  exact primitiveToNormalizedHom_root

private theorem primitiveToNormalizedEquiv_symm_root :
    primitiveToNormalizedEquiv.symm normalizedRoot =
      Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
        forwardPolynomial := by
  apply primitiveToNormalizedEquiv.injective
  rw [primitiveToNormalizedEquiv.apply_symm_apply]
  exact primitiveToNormalizedHom_forward.symm

private def primitivePresentationHom :
    AdjoinRoot primitivePolynomial →ₐ[ℚ] M :=
  AdjoinRoot.liftAlgHom primitivePolynomial (Algebra.ofId ℚ M)
    primitiveElement (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact primitiveElement_root)

@[simp]
private theorem primitivePresentationHom_root :
    primitivePresentationHom (AdjoinRoot.root primitivePolynomial) =
      primitiveElement := by
  exact AdjoinRoot.liftAlgHom_root primitivePolynomial _ _ _

private theorem primitivePresentationHom_injective :
    Function.Injective primitivePresentationHom := by
  exact RingHom.injective primitivePresentationHom.toRingHom

private theorem primitivePresentationHom_surjective :
    Function.Surjective primitivePresentationHom := by
  apply (AlgHom.range_eq_top primitivePresentationHom).mp
  rw [← top_le_iff, ← primitiveElement_adjoin_eq_top]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  exact (AlgHom.mem_range primitivePresentationHom).2
    ⟨AdjoinRoot.root primitivePolynomial, primitivePresentationHom_root⟩

private def primitivePresentationEquiv :
    AdjoinRoot primitivePolynomial ≃ₐ[ℚ] M :=
  AlgEquiv.ofBijective primitivePresentationHom
    ⟨primitivePresentationHom_injective,
      primitivePresentationHom_surjective⟩

@[simp]
private theorem primitivePresentationEquiv_root :
    primitivePresentationEquiv (AdjoinRoot.root primitivePolynomial) =
      primitiveElement := by
  exact primitivePresentationHom_root

/-- The normalized polynomial quotient is the original degree-nine
two-division compositum. -/
def normalizedAdjoinRootEquiv :
    AdjoinRoot normalizedPolynomial ≃ₐ[ℚ] M :=
  primitiveToNormalizedEquiv.symm.trans primitivePresentationEquiv

@[simp]
theorem normalizedAdjoinRootEquiv_root :
    normalizedAdjoinRootEquiv normalizedRoot = normalizedElement := by
  rw [normalizedAdjoinRootEquiv, AlgEquiv.trans_apply,
    primitiveToNormalizedEquiv_symm_root]
  rw [← Polynomial.aeval_algHom_apply, primitivePresentationEquiv_root]
  rfl

/-- The normalized generator satisfies the advertised small polynomial. -/
theorem normalizedElement_root :
    Polynomial.aeval normalizedElement normalizedPolynomial = 0 := by
  rw [← normalizedAdjoinRootEquiv_root,
    Polynomial.aeval_algHom_apply, normalizedRoot_root, map_zero]

/-- The inverse polynomial recovers `u = t - s` from the normalized
generator. -/
theorem normalizedElement_reconstruction :
    Polynomial.aeval normalizedElement inversePolynomial =
      primitiveElement := by
  rw [← normalizedAdjoinRootEquiv_root,
    Polynomial.aeval_algHom_apply]
  change primitivePresentationEquiv
      (primitiveToNormalizedEquiv.symm
        (Polynomial.aeval normalizedRoot inversePolynomial)) =
    primitiveElement
  rw [← primitiveToNormalizedEquiv_root,
    primitiveToNormalizedEquiv.symm_apply_apply,
    primitivePresentationEquiv_root]

theorem primitiveElement_mem_normalized_adjoin :
    primitiveElement ∈
      Algebra.adjoin ℚ ({normalizedElement} : Set M) := by
  rw [← normalizedElement_reconstruction]
  exact Polynomial.aeval_mem_adjoin_singleton ℚ normalizedElement

/-- The normalized element still generates the full compositum over `ℚ`. -/
theorem normalizedElement_adjoin_eq_top :
    Algebra.adjoin ℚ ({normalizedElement} : Set M) = ⊤ := by
  apply le_antisymm le_top
  rw [← primitiveElement_adjoin_eq_top]
  exact Algebra.adjoin_le
    (Set.singleton_subset_iff.mpr primitiveElement_mem_normalized_adjoin)

theorem normalizedElement_isIntegral :
    IsIntegral ℚ normalizedElement :=
  ⟨normalizedPolynomial, normalizedPolynomial_monic,
    normalizedElement_root⟩

/-- The rational power basis generated by the normalized element.  This is
not asserted to be an integral basis over `ℤ`. -/
def normalizedPowerBasis : PowerBasis ℚ M :=
  PowerBasis.ofAdjoinEqTop normalizedElement_isIntegral
    normalizedElement_adjoin_eq_top

@[simp]
theorem normalizedPowerBasis_gen :
    normalizedPowerBasis.gen = normalizedElement := by
  rw [normalizedPowerBasis, PowerBasis.ofAdjoinEqTop_gen]

theorem normalizedElement_minpoly_natDegree :
    (minpoly ℚ normalizedElement).natDegree = 9 := by
  calc
    (minpoly ℚ normalizedElement).natDegree = normalizedPowerBasis.dim := by
      simpa only [normalizedPowerBasis_gen] using
        normalizedPowerBasis.natDegree_minpoly
    _ = Module.finrank ℚ M := normalizedPowerBasis.finrank.symm
    _ = 9 := finrank_M_over_rat

/-- The normalized polynomial is exactly the minimal polynomial. -/
theorem normalizedElement_minpoly :
    minpoly ℚ normalizedElement = normalizedPolynomial := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic normalizedElement_isIntegral)
    normalizedPolynomial_monic
    (minpoly.dvd ℚ normalizedElement normalizedElement_root)
    (by rw [normalizedPolynomial_natDegree,
      normalizedElement_minpoly_natDegree])).symm

theorem normalizedPolynomial_irreducible :
    Irreducible normalizedPolynomial := by
  rw [← normalizedElement_minpoly]
  exact minpoly.irreducible normalizedElement_isIntegral

instance normalizedPolynomial_irreducibleFact :
    Fact (Irreducible normalizedPolynomial) :=
  ⟨normalizedPolynomial_irreducible⟩

end

end MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
