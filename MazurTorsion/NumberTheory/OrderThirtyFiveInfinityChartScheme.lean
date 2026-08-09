/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The integral infinity chart of the level-35 quotient map

At either point at infinity of the standard hyperelliptic model, put
`t = 1/x` and `s = y/x⁴`.  The resulting integral chart is

`s² = (1+t-t²)(1-5t-9t³-5t⁵-t⁶)`.

On the principal open where `d = 1+t-t²` is invertible, the quotient
coordinates are

`W = (1-6t-t²)/d` and `R = 7s/d²`.

This file checks the formula over every commutative base ring and constructs
the induced morphism of affine schemes to

`R² = 4W³ + 4W² + 36W + 5`.

The cusp `(t,s) = (0,1)` is retained as an actual affine structural section,
and the exact identity `W-1 = (-7/d)t` is proved in the source coordinate
ring.  These are the represented inputs for the characteristic-eleven
first-order formal-immersion calculation; no modular interpretation or
formal-immersion conclusion is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace MazurTorsion.OrderThirtyFive.InfinityChartScheme

universe u

section UniversalIdentity

variable {R : Type u} [CommRing R]

/-- The integral hyperelliptic polynomial on the infinity chart. -/
def sourcePolynomialValue (t : R) : R :=
  t ^ 8 + 4 * t ^ 7 - 6 * t ^ 6 + 4 * t ^ 5 - 9 * t ^ 4 -
    4 * t ^ 3 - 6 * t ^ 2 - 4 * t + 1

/-- The denominator inverted on the quotient chart. -/
def quotientDenominator (t : R) : R :=
  1 + t - t ^ 2

/-- The numerator of the quotient abscissa. -/
def quotientWNumerator (t : R) : R :=
  1 - 6 * t - t ^ 2

/-- The quotient abscissa after a chosen inverse of the denominator. -/
def quotientWValue (t denominatorInverse : R) : R :=
  quotientWNumerator t * denominatorInverse

/-- The denominator-free quotient ordinate. -/
def quotientRValue (s denominatorInverse : R) : R :=
  7 * s * denominatorInverse ^ 2

/-- The infinity-chart quotient formulas satisfy the target equation over
every commutative ring. -/
theorem quotientValues_equation {t s denominatorInverse : R}
    (hsource : s ^ 2 = sourcePolynomialValue t)
    (hdenominator :
      denominatorInverse * quotientDenominator t = 1) :
    quotientRValue s denominatorInverse ^ 2 =
      4 * quotientWValue t denominatorInverse ^ 3 +
        4 * quotientWValue t denominatorInverse ^ 2 +
          36 * quotientWValue t denominatorInverse + 5 := by
  dsimp only [sourcePolynomialValue, quotientDenominator,
    quotientWNumerator, quotientWValue, quotientRValue] at hsource hdenominator ⊢
  linear_combination
    (49 * denominatorInverse ^ 4) * hsource +
      (-49 * t ^ 6 * denominatorInverse ^ 3 -
          245 * t ^ 5 * denominatorInverse ^ 3 +
          45 * t ^ 4 * denominatorInverse ^ 2 -
          441 * t ^ 3 * denominatorInverse ^ 3 +
          218 * t ^ 3 * denominatorInverse ^ 2 -
          157 * t ^ 2 * denominatorInverse ^ 2 -
          41 * t ^ 2 * denominatorInverse -
          245 * t * denominatorInverse ^ 3 -
          218 * t * denominatorInverse ^ 2 -
          211 * t * denominatorInverse +
          49 * denominatorInverse ^ 3 +
          45 * denominatorInverse ^ 2 +
          41 * denominatorInverse + 5) * hdenominator

/-- The first-order quotient coordinate has the exact integral factorization
used at the cusp. -/
theorem quotientWValue_sub_one {t denominatorInverse : R}
    (hdenominator :
      denominatorInverse * quotientDenominator t = 1) :
    quotientWValue t denominatorInverse - 1 =
      (-7 * denominatorInverse) * t := by
  dsimp only [quotientWValue, quotientWNumerator,
    quotientDenominator] at hdenominator ⊢
  linear_combination hdenominator

end UniversalIdentity

variable (R : Type u) [CommRing R]

/-- The polynomial in the infinity-chart parameter `t`. -/
def sourcePolynomial : Polynomial R :=
  X ^ 8 + 4 * X ^ 7 - 6 * X ^ 6 + 4 * X ^ 5 - 9 * X ^ 4 -
    4 * X ^ 3 - 6 * X ^ 2 - 4 * X + 1

/-- The monic quadratic equation defining the infinity chart. -/
def sourceEquation : Polynomial (Polynomial R) :=
  X ^ 2 - C (sourcePolynomial R)

/-- Coordinate ring of the integral infinity chart. -/
abbrev SourceRing := AdjoinRoot (sourceEquation R)

/-- The infinity parameter `t`. -/
def sourceT : SourceRing R :=
  AdjoinRoot.of (sourceEquation R) X

/-- The rescaled hyperelliptic ordinate `s`. -/
def sourceS : SourceRing R :=
  AdjoinRoot.root (sourceEquation R)

private theorem of_sourcePolynomial_eq_aeval :
    AdjoinRoot.of (sourceEquation R) (sourcePolynomial R) =
      aeval (sourceT R) (sourcePolynomial R) := by
  have hhom :
      AdjoinRoot.ofAlgHom R (sourceEquation R) =
        aeval (sourceT R) := by
    apply Polynomial.algHom_ext
    simp [sourceT]
  exact DFunLike.congr_fun hhom (sourcePolynomial R)

/-- The two coordinate functions satisfy the infinity-chart equation. -/
theorem sourceS_sq :
    sourceS R ^ 2 = sourcePolynomialValue (sourceT R) := by
  rw [show sourcePolynomialValue (sourceT R) =
      aeval (sourceT R) (sourcePolynomial R) by
    simp [sourcePolynomialValue, sourcePolynomial, Polynomial.aeval_def]]
  rw [← of_sourcePolynomial_eq_aeval]
  change AdjoinRoot.mk (sourceEquation R) (X ^ 2) =
    AdjoinRoot.mk (sourceEquation R) (C (sourcePolynomial R))
  rw [AdjoinRoot.mk_eq_mk]
  refine ⟨1, ?_⟩
  simp [sourceEquation]

/-- The element inverted on the quotient chart. -/
def sourceDenominator : SourceRing R :=
  quotientDenominator (sourceT R)

/-- Coordinate ring of the principal open `D(1+t-t²)`. -/
abbrev SourceOpenRing := Localization.Away (sourceDenominator R)

/-- The source parameter on the principal open. -/
def openT : SourceOpenRing R :=
  algebraMap (SourceRing R) (SourceOpenRing R) (sourceT R)

/-- The source ordinate on the principal open. -/
def openS : SourceOpenRing R :=
  algebraMap (SourceRing R) (SourceOpenRing R) (sourceS R)

/-- The canonical denominator unit on its principal open. -/
def denominatorUnit : Units (SourceOpenRing R) :=
  (IsLocalization.Away.algebraMap_isUnit (sourceDenominator R)).unit

/-- The canonical inverse of `1+t-t²`. -/
def denominatorInverse : SourceOpenRing R :=
  ((denominatorUnit R)⁻¹ : Units (SourceOpenRing R))

theorem quotientDenominator_openT :
    quotientDenominator (openT R) =
      (denominatorUnit R : SourceOpenRing R) := by
  change quotientDenominator
      (algebraMap (SourceRing R) (SourceOpenRing R) (sourceT R)) =
    algebraMap (SourceRing R) (SourceOpenRing R) (sourceDenominator R)
  simp [quotientDenominator, sourceDenominator]

theorem denominatorInverse_mul :
    denominatorInverse R * quotientDenominator (openT R) = 1 := by
  rw [quotientDenominator_openT]
  exact Units.inv_mul (denominatorUnit R)

/-- The source equation after restricting to the principal open. -/
theorem open_source_equation :
    openS R ^ 2 = sourcePolynomialValue (openT R) := by
  simpa only [openS, openT, sourcePolynomialValue, map_add, map_sub,
    map_mul, map_pow, map_ofNat, map_one] using
      congrArg (algebraMap (SourceRing R) (SourceOpenRing R))
        (sourceS_sq R)

/-- The represented quotient abscissa. -/
def openQuotientW : SourceOpenRing R :=
  quotientWValue (openT R) (denominatorInverse R)

/-- The represented denominator-free quotient ordinate. -/
def openQuotientR : SourceOpenRing R :=
  quotientRValue (openS R) (denominatorInverse R)

/-- The represented coordinates satisfy the quotient equation. -/
theorem open_quotient_equation :
    openQuotientR R ^ 2 =
      4 * openQuotientW R ^ 3 + 4 * openQuotientW R ^ 2 +
        36 * openQuotientW R + 5 :=
  quotientValues_equation (open_source_equation R)
    (denominatorInverse_mul R)

/-- Exact first-order identity for the quotient abscissa at the cusp. -/
theorem openQuotientW_sub_one :
    openQuotientW R - 1 =
      (-7 * denominatorInverse R) * openT R :=
  quotientWValue_sub_one (denominatorInverse_mul R)

/-- The target cubic in the quotient abscissa. -/
def targetPolynomial : Polynomial R :=
  4 * X ^ 3 + 4 * X ^ 2 + 36 * X + 5

/-- The monic quadratic equation defining the quotient chart. -/
def targetEquation : Polynomial (Polynomial R) :=
  X ^ 2 - C (targetPolynomial R)

/-- Coordinate ring of `R² = 4W³+4W²+36W+5`. -/
abbrev TargetRing := AdjoinRoot (targetEquation R)

/-- The quotient abscissa coordinate. -/
def targetW : TargetRing R :=
  AdjoinRoot.of (targetEquation R) X

/-- The quotient ordinate coordinate. -/
def targetR : TargetRing R :=
  AdjoinRoot.root (targetEquation R)

/-- The contravariant algebra map defined by the quotient formulas. -/
def targetToOpenRing : TargetRing R →ₐ[R] SourceOpenRing R :=
  AdjoinRoot.liftAlgHom (targetEquation R) (aeval (openQuotientW R))
    (openQuotientR R) (by
      have hpoly : aeval (openQuotientW R) (targetPolynomial R) =
          4 * openQuotientW R ^ 3 + 4 * openQuotientW R ^ 2 +
            36 * openQuotientW R + 5 := by
        simp only [targetPolynomial, map_add, map_mul, map_pow, aeval_X,
          map_ofNat]
      simpa [targetEquation, hpoly] using
        sub_eq_zero.mpr (open_quotient_equation R))

@[simp]
theorem targetToOpenRing_w :
    targetToOpenRing R (targetW R) = openQuotientW R := by
  simp [targetToOpenRing, targetW]

@[simp]
theorem targetToOpenRing_r :
    targetToOpenRing R (targetR R) = openQuotientR R := by
  simp [targetToOpenRing, targetR]

/-- The genuine affine-scheme morphism induced by the infinity-chart
quotient formulas. -/
def quotientMorphism :
    Spec (.of (SourceOpenRing R)) ⟶ Spec (.of (TargetRing R)) :=
  Spec.map (CommRingCat.ofHom (targetToOpenRing R).toRingHom)

/-- The represented morphism has the checked quotient algebra map as its
affine comorphism. -/
theorem quotientMorphism_preimage :
    Spec.preimage (quotientMorphism R) =
      CommRingCat.ofHom (targetToOpenRing R).toRingHom := by
  rw [quotientMorphism, Spec.preimage_map]

/-- Evaluation of the source chart at the integral cusp `(t,s)=(0,1)`. -/
def sourceCuspEvaluation : SourceRing R →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (sourceEquation R) (aeval (0 : R)) 1 (by
    simp [sourceEquation, sourcePolynomial])

@[simp]
theorem sourceCuspEvaluation_t :
    sourceCuspEvaluation R (sourceT R) = 0 := by
  simp [sourceCuspEvaluation, sourceT]

@[simp]
theorem sourceCuspEvaluation_s :
    sourceCuspEvaluation R (sourceS R) = 1 := by
  simp [sourceCuspEvaluation, sourceS]

theorem sourceCuspEvaluation_denominator :
    sourceCuspEvaluation R (sourceDenominator R) = 1 := by
  simp [sourceDenominator, quotientDenominator]

/-- The integral cusp extends over the principal open because its denominator
evaluates to one. -/
def cuspRetraction : SourceOpenRing R →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (sourceDenominator R)
    (f := sourceCuspEvaluation R) (by
      rw [sourceCuspEvaluation_denominator]
      exact isUnit_one)

@[simp]
theorem cuspRetraction_algebraMap (a : SourceRing R) :
    cuspRetraction R
        (algebraMap (SourceRing R) (SourceOpenRing R) a) =
      sourceCuspEvaluation R a := by
  simp [cuspRetraction, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

@[simp]
theorem cuspRetraction_openT : cuspRetraction R (openT R) = 0 := by
  simp [openT]

@[simp]
theorem cuspRetraction_openS : cuspRetraction R (openS R) = 1 := by
  simp [openS]

@[simp]
theorem cuspRetraction_denominatorInverse :
    cuspRetraction R (denominatorInverse R) = 1 := by
  simpa [quotientDenominator] using
    congrArg (cuspRetraction R) (denominatorInverse_mul R)

@[simp]
theorem cuspRetraction_openQuotientW :
    cuspRetraction R (openQuotientW R) = 1 := by
  simp [openQuotientW, quotientWValue, quotientWNumerator]

@[simp]
theorem cuspRetraction_openQuotientR :
    cuspRetraction R (openQuotientR R) = 7 := by
  simp [openQuotientR, quotientRValue, map_ofNat]

/-- The integral cusp as an actual section of the affine structural
morphism. -/
def cuspSection :
    Spec (.of R) ⟶ Spec (.of (SourceOpenRing R)) :=
  Spec.map (CommRingCat.ofHom (cuspRetraction R).toRingHom)

/-- The represented cusp is a section of the source chart over the base. -/
theorem cuspSection_isSection :
    cuspSection R ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (SourceOpenRing R))) =
      𝟙 (Spec (.of R)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (.of R)
  ext r
  exact (cuspRetraction R).commutes r

end MazurTorsion.OrderThirtyFive.InfinityChartScheme
