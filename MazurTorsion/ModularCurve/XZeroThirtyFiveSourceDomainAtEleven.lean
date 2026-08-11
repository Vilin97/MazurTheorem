/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.IntervalCases

/-!
# Integrality of the level-35 hyperelliptic chart in characteristic eleven

The affine source equation used by the explicit level-35 quotient calculation
is

`Y² = P(X)`.

Over `F₁₁[X]`, the polynomial `Y² - P(X)` is Eisenstein at the prime
`(X - 3)`: the value `P(3)` vanishes, while `P'(3) = 10` is nonzero.  Hence
the equation is prime in `F₁₁[X][Y]`.  Transport through Mathlib's bivariate
polynomial equivalence proves that the checked two-variable hypersurface
coordinate ring is a domain.  Its open chart and every prime localization,
in particular the selected cusp local ring, inherit this fact.

The numerical assertions are verified in Lean over `ZMod 11`; no external
factorization or computer-algebra certificate is retained.
-/

noncomputable section

namespace MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven

open MvPolynomial Polynomial
open scoped Polynomial.Bivariate

local instance primeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The hyperelliptic polynomial as an element of `F₁₁[X]`. -/
def sourcePolynomialUnivariate : Polynomial ResidueField :=
  X ^ 8 - 4 * X ^ 7 - 6 * X ^ 6 - 4 * X ^ 5 - 9 * X ^ 4 +
    4 * X ^ 3 - 6 * X ^ 2 + 4 * X + 1

/-- The source equation, now viewed as a polynomial in `Y` over
`F₁₁[X]`. -/
def sourceEquationBivariate : Polynomial (Polynomial ResidueField) :=
  X ^ 2 - C sourcePolynomialUnivariate

/-- The simple root used for the Eisenstein prime. -/
theorem sourcePolynomialUnivariate_eval_three :
    sourcePolynomialUnivariate.eval 3 = 0 := by
  norm_num [sourcePolynomialUnivariate]

/-- The chosen root is simple in characteristic eleven. -/
theorem sourcePolynomialUnivariate_derivative_eval_three :
    sourcePolynomialUnivariate.derivative.eval 3 = 10 := by
  norm_num [sourcePolynomialUnivariate]

/-- The constant coefficient of `Y²-P(X)` belongs to `(X-3)`. -/
theorem neg_sourcePolynomialUnivariate_mem_span_X_sub_three :
    -sourcePolynomialUnivariate ∈
      Ideal.span ({X - C (3 : ResidueField)} : Set (Polynomial ResidueField)) := by
  rw [Ideal.mem_span_singleton]
  apply dvd_neg.mpr
  rw [Polynomial.dvd_iff_isRoot]
  exact sourcePolynomialUnivariate_eval_three

/-- The constant coefficient is not divisible by `(X-3)²`, because the
derivative at the chosen root is nonzero. -/
theorem neg_sourcePolynomialUnivariate_not_mem_span_X_sub_three_sq :
    -sourcePolynomialUnivariate ∉
      Ideal.span ({X - C (3 : ResidueField)} : Set (Polynomial ResidueField)) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro hsq
  have hsq' : (X - C (3 : ResidueField)) ^ 2 ∣ sourcePolynomialUnivariate :=
    dvd_neg.mp hsq
  have hderivative : X - C (3 : ResidueField) ∣
      sourcePolynomialUnivariate.derivative := by
    simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hsq'
  have hzero : sourcePolynomialUnivariate.derivative.eval 3 = 0 := by
    exact Polynomial.dvd_iff_isRoot.mp hderivative
  rw [sourcePolynomialUnivariate_derivative_eval_three] at hzero
  norm_num at hzero

/-- The bivariate source equation is monic in `Y`. -/
theorem sourceEquationBivariate_monic : sourceEquationBivariate.Monic := by
  exact Polynomial.monic_X_pow_sub_C sourcePolynomialUnivariate (by norm_num)

/-- The bivariate equation is Eisenstein at the simple factor `(X-3)`. -/
theorem sourceEquationBivariate_isEisenstein :
    sourceEquationBivariate.IsEisensteinAt
      (Ideal.span ({X - C (3 : ResidueField)} :
        Set (Polynomial ResidueField))) := by
  apply sourceEquationBivariate_monic.isEisensteinAt_of_mem_of_notMem
  · exact (Ideal.isPrime_span_singleton_of_prime
      (Polynomial.prime_X_sub_C (3 : ResidueField))).ne_top
  · intro n hn
    rw [show sourceEquationBivariate.natDegree = 2 by
      simpa [sourceEquationBivariate] using
        (Polynomial.natDegree_X_pow_sub_C
          (r := sourcePolynomialUnivariate) (n := 2))] at hn
    interval_cases n
    · simpa [sourceEquationBivariate] using
        neg_sourcePolynomialUnivariate_mem_span_X_sub_three
    · simp [sourceEquationBivariate]
  · simpa [sourceEquationBivariate] using
      neg_sourcePolynomialUnivariate_not_mem_span_X_sub_three_sq

/-- The bivariate hyperelliptic equation is irreducible. -/
theorem sourceEquationBivariate_irreducible :
    Irreducible sourceEquationBivariate :=
  sourceEquationBivariate_isEisenstein.irreducible
    (Ideal.isPrime_span_singleton_of_prime
      (Polynomial.prime_X_sub_C (3 : ResidueField)))
    sourceEquationBivariate_monic.isPrimitive
    (by simp [sourceEquationBivariate])

/-- The bivariate hyperelliptic equation is prime. -/
theorem sourceEquationBivariate_prime : Prime sourceEquationBivariate :=
  sourceEquationBivariate_irreducible.prime

/-- Mathlib's bivariate equivalence sends the iterated-polynomial equation
to the two-variable equation used by the explicit quotient chart. -/
theorem bivariateEquiv_sourceEquation :
    Polynomial.Bivariate.equivMvPolynomial ResidueField
        sourceEquationBivariate = sourceEquation := by
  simp [sourceEquationBivariate, sourcePolynomialUnivariate, sourceEquation,
    sourcePolynomial]

/-- The checked source ideal is the transport of the prime bivariate
equation ideal. -/
theorem sourceIdeal_eq_map_bivariate :
    sourceIdeal =
      Ideal.map (Polynomial.Bivariate.equivMvPolynomial ResidueField)
        (Ideal.span ({sourceEquationBivariate} :
          Set (Polynomial (Polynomial ResidueField)))) := by
  rw [sourceIdeal, ← bivariateEquiv_sourceEquation]
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

/-- The defining ideal of the checked source hypersurface is prime. -/
instance sourceIdeal_isPrime : sourceIdeal.IsPrime := by
  rw [sourceIdeal_eq_map_bivariate]
  haveI : (Ideal.span ({sourceEquationBivariate} :
      Set (Polynomial (Polynomial ResidueField)))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime sourceEquationBivariate_prime
  infer_instance

/-- The checked affine hyperelliptic source coordinate ring is a domain. -/
instance sourceCoordinateRing_isDomain : IsDomain SourceCoordinateRing :=
  inferInstance

/-- Coordinates of the selected cusp, used only to certify that the open-chart
denominator is nonzero before localization. -/
private def denominatorWitnessCoordinates : Fin 2 → ResidueField :=
  Fin.cases 0 (Fin.cases 1 Fin.elim0)

/-- Evaluation at `(0,1)` on the ambient polynomial ring. -/
private def denominatorWitnessEvaluation :
    MvPolynomial (Fin 2) ResidueField →+* ResidueField :=
  MvPolynomial.eval₂Hom (RingHom.id ResidueField)
    denominatorWitnessCoordinates

private theorem denominatorWitnessEvaluation_sourceEquation :
    denominatorWitnessEvaluation sourceEquation = 0 := by
  simp [denominatorWitnessEvaluation, denominatorWitnessCoordinates,
    sourceEquation, sourcePolynomial]

/-- Evaluation at `(0,1)` descends to the integral source hypersurface. -/
private def denominatorWitnessRetraction :
    SourceCoordinateRing →+* ResidueField :=
  Ideal.Quotient.lift sourceIdeal denominatorWitnessEvaluation (by
    intro P hP
    have hle : sourceIdeal ≤ RingHom.ker denominatorWitnessEvaluation := by
      rw [sourceIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact denominatorWitnessEvaluation_sourceEquation
    exact RingHom.mem_ker.mp (hle hP))

@[simp]
private theorem denominatorWitnessRetraction_sourceMk
    (P : MvPolynomial (Fin 2) ResidueField) :
    denominatorWitnessRetraction (sourceMk P) =
      denominatorWitnessEvaluation P := by
  simp [denominatorWitnessRetraction, sourceMk]

/-- The denominator defining the quotient-map chart survives in the integral
source coordinate ring: at the selected cusp it has value `-1`. -/
theorem sourceDenominator_ne_zero : sourceDenominator ≠ 0 := by
  intro hzero
  have h := congrArg denominatorWitnessRetraction hzero
  have hvalue : denominatorWitnessRetraction sourceDenominator = -1 := by
    simp [sourceDenominator, sourceX, denominatorWitnessEvaluation,
      denominatorWitnessCoordinates]
  rw [hvalue, map_zero] at h
  norm_num at h

/-- The open chart on which the quotient formulas are regular is a domain. -/
instance sourceChart_isDomain : IsDomain SourceChart :=
  Localization.Away.isDomain sourceDenominator_ne_zero

end MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven
