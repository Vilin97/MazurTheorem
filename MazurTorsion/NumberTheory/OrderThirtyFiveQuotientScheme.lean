/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveQuotientMap
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The affine scheme map underlying the level-35 quotient formulas

The pointwise quotient formulas on the standard affine model of `X₀(35)`
simplify after putting

`a = x² + x - 1`, `w = (x² - 6x - 1) / a`, and
`r = 2z + 1 = 7y / a²`.

This file checks the resulting identity over every commutative ring, constructs
the induced morphism from the principal open `D(a)` of the displayed affine
level-35 model to the affine curve

`r² = 4w³ + 4w² + 36w + 5`,

and records its effect on both coordinate functions.  Over `ℚ`, the target is
the affine chart of the already checked rank-zero Weierstrass quotient under
`r = 2z + 1`.

This is a represented morphism between the two explicit affine models.  It
does not identify the source with the modular curve `X₀(35)`; that moduli
comparison remains a separate geometric obligation.
-/

noncomputable section

open AlgebraicGeometry

namespace MazurTorsion.OrderThirtyFive.QuotientScheme

universe u

section UniversalIdentity

variable {R : Type u} [CommRing R]

/-- The level-35 source polynomial evaluated in a commutative ring. -/
def sourcePolynomialValue (x : R) : R :=
  x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 +
    4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1

/-- The denominator of the regular quotient coordinates. -/
def quotientDenominator (x : R) : R :=
  x ^ 2 + x - 1

/-- The quotient abscissa when `t` is the inverse of `x²+x-1`. -/
def quotientWValue (x t : R) : R :=
  (x ^ 2 - 6 * x - 1) * t

/-- The denominator-free ordinate `r = 2z+1` on the quotient model. -/
def quotientRValue (y t : R) : R :=
  7 * y * t ^ 2

/-- The simplified quotient formulas satisfy the target equation over every
commutative ring.  This is the universal polynomial identity used to factor
the coordinate-ring map through the two curve equations. -/
theorem quotientValues_equation {x y t : R}
    (hxy : y ^ 2 = sourcePolynomialValue x)
    (ht : t * quotientDenominator x = 1) :
    quotientRValue y t ^ 2 =
      4 * quotientWValue x t ^ 3 + 4 * quotientWValue x t ^ 2 +
        36 * quotientWValue x t + 5 := by
  dsimp only [sourcePolynomialValue, quotientDenominator,
    quotientWValue, quotientRValue] at hxy ht ⊢
  linear_combination
    (49 * t ^ 4) * hxy +
      (49 * t ^ 3 * x ^ 6 - 245 * t ^ 3 * x ^ 5 -
          441 * t ^ 3 * x ^ 3 - 245 * t ^ 3 * x - 49 * t ^ 3 +
          45 * t ^ 2 * x ^ 4 - 218 * t ^ 2 * x ^ 3 -
          157 * t ^ 2 * x ^ 2 + 218 * t ^ 2 * x + 45 * t ^ 2 +
          41 * t * x ^ 2 - 211 * t * x - 41 * t + 5) * ht

end UniversalIdentity

/-- The simplified quotient denominator has no rational zero. -/
theorem quotientDenominator_ne_zero (x : ℚ) :
    quotientDenominator x ≠ 0 := by
  by_cases hx : x = 0
  · simp [quotientDenominator, hx]
  intro hden
  apply quotientU_add_one_ne_zero x
  rw [show quotientU x + 1 = quotientDenominator x / x by
    simp only [quotientU, quotientDenominator]
    field_simp [hx]
    ring]
  rw [hden]
  simp

/-- On the original rational-function domain, the represented abscissa is the
previously checked pointwise quotient coordinate. -/
theorem quotientWValue_inv_eq_quotientW {x : ℚ} (hx : x ≠ 0) :
    quotientWValue x (quotientDenominator x)⁻¹ = quotientW x := by
  unfold quotientWValue quotientDenominator quotientW quotientU
  field_simp [hx, quotientDenominator_ne_zero x]
  ring

/-- On the original rational-function domain, the denominator-free ordinate
is `2z+1` for the previously checked pointwise quotient coordinate. -/
theorem quotientRValue_inv_eq_two_mul_quotientZ_add_one {x y : ℚ}
    (hx : x ≠ 0) :
    quotientRValue y (quotientDenominator x)⁻¹ =
      2 * quotientZ x y + 1 := by
  have hden := quotientDenominator_ne_zero x
  have hu := quotientU_add_one_ne_zero x
  have hu2 := quotientU_sq_add_two_ne_zero x
  unfold quotientRValue quotientDenominator quotientZ quotientV quotientU
  field_simp [hx, hden, hu, hu2]
  ring

abbrev PolynomialRing := MvPolynomial (Fin 2) ℚ

/-- The polynomial cutting out the displayed affine level-35 model, with
coordinates `(x,y) = (X 0, X 1)`. -/
def sourcePolynomial : PolynomialRing :=
  MvPolynomial.X 1 ^ 2 -
    (MvPolynomial.X 0 ^ 8 - 4 * MvPolynomial.X 0 ^ 7 -
      6 * MvPolynomial.X 0 ^ 6 - 4 * MvPolynomial.X 0 ^ 5 -
      9 * MvPolynomial.X 0 ^ 4 + 4 * MvPolynomial.X 0 ^ 3 -
      6 * MvPolynomial.X 0 ^ 2 + 4 * MvPolynomial.X 0 + 1)

/-- The principal ideal cutting out the displayed affine source model. -/
def sourceIdeal : Ideal PolynomialRing :=
  Ideal.span ({sourcePolynomial} : Set PolynomialRing)

/-- The affine source coordinate ring. -/
abbrev SourceRing := PolynomialRing ⧸ sourceIdeal

/-- The source abscissa. -/
def sourceX : SourceRing :=
  Ideal.Quotient.mk sourceIdeal (MvPolynomial.X 0)

/-- The source ordinate. -/
def sourceY : SourceRing :=
  Ideal.Quotient.mk sourceIdeal (MvPolynomial.X 1)

/-- The element whose principal open supports the affine quotient chart. -/
def sourceDenominator : SourceRing :=
  sourceX ^ 2 + sourceX - 1

/-- The coordinate ring of the principal source open `D(x²+x-1)`. -/
abbrev SourceOpenRing := Localization.Away sourceDenominator

/-- The source abscissa on the principal open. -/
def openX : SourceOpenRing :=
  algebraMap SourceRing SourceOpenRing sourceX

/-- The source ordinate on the principal open. -/
def openY : SourceOpenRing :=
  algebraMap SourceRing SourceOpenRing sourceY

/-- The canonical unit represented by `x²+x-1` on its principal open. -/
def denominatorUnit : Units SourceOpenRing :=
  (IsLocalization.Away.algebraMap_isUnit sourceDenominator).unit

/-- The canonical inverse of `x²+x-1` on the principal open. -/
def denominatorInverse : SourceOpenRing :=
  (denominatorUnit⁻¹ : Units SourceOpenRing)

theorem quotientDenominator_openX :
    quotientDenominator openX = (denominatorUnit : SourceOpenRing) := by
  change quotientDenominator
      (algebraMap SourceRing SourceOpenRing sourceX) =
    algebraMap SourceRing SourceOpenRing sourceDenominator
  simp [quotientDenominator, sourceDenominator]

theorem denominatorInverse_mul :
    denominatorInverse * quotientDenominator openX = 1 := by
  rw [quotientDenominator_openX]
  exact Units.inv_mul denominatorUnit

theorem open_source_equation :
    openY ^ 2 = sourcePolynomialValue openX := by
  have hsource :
      (Ideal.Quotient.mk
          sourceIdeal
          sourcePolynomial : SourceRing) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton sourcePolynomial)
  have hsource' : sourceY ^ 2 = sourcePolynomialValue sourceX := by
    rw [sourcePolynomial, map_sub] at hsource
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one] at hsource
    change sourceY ^ 2 - sourcePolynomialValue sourceX = 0 at hsource
    exact sub_eq_zero.mp hsource
  simpa only [openX, openY, sourcePolynomialValue, map_sub, map_add,
    map_mul, map_pow, map_ofNat, map_one] using
    congrArg (algebraMap SourceRing SourceOpenRing) hsource'

/-- The represented quotient abscissa on the source open. -/
def openQuotientW : SourceOpenRing :=
  quotientWValue openX denominatorInverse

/-- The represented denominator-free quotient ordinate on the source open. -/
def openQuotientR : SourceOpenRing :=
  quotientRValue openY denominatorInverse

theorem open_quotient_equation :
    openQuotientR ^ 2 =
      4 * openQuotientW ^ 3 + 4 * openQuotientW ^ 2 +
        36 * openQuotientW + 5 :=
  quotientValues_equation open_source_equation denominatorInverse_mul

/-- The affine target polynomial, in coordinates `(w,r) = (X 0, X 1)`. -/
def targetPolynomial : PolynomialRing :=
  MvPolynomial.X 1 ^ 2 -
    (4 * MvPolynomial.X 0 ^ 3 + 4 * MvPolynomial.X 0 ^ 2 +
      36 * MvPolynomial.X 0 + 5)

/-- The principal ideal cutting out the affine quotient model
`r² = 4w³+4w²+36w+5`. -/
def targetIdeal : Ideal PolynomialRing :=
  Ideal.span ({targetPolynomial} : Set PolynomialRing)

/-- The affine coordinate ring of the quotient model. -/
abbrev TargetRing := PolynomialRing ⧸ targetIdeal

private def targetPolynomialEvaluation : PolynomialRing →+* SourceOpenRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ SourceOpenRing)
    (fun i ↦ if i = 0 then openQuotientW else openQuotientR)

private theorem targetPolynomialEvaluation_eq_zero :
    targetPolynomialEvaluation targetPolynomial = 0 := by
  simpa [targetPolynomialEvaluation, targetPolynomial] using
    sub_eq_zero.mpr open_quotient_equation

/-- The contravariant coordinate-ring map defining the explicit quotient
morphism on the principal source open. -/
def targetToOpenRing : TargetRing →+* SourceOpenRing :=
  Ideal.Quotient.lift targetIdeal
    targetPolynomialEvaluation (by
      intro p hp
      change p ∈ RingHom.ker targetPolynomialEvaluation
      apply (show targetIdeal ≤ RingHom.ker targetPolynomialEvaluation by
        rw [targetIdeal]
        apply Ideal.span_le.mpr
        intro q hq
        change targetPolynomialEvaluation q = 0
        rw [Set.mem_singleton_iff.mp hq]
        exact targetPolynomialEvaluation_eq_zero) hp
      )

theorem targetToOpenRing_w :
    targetToOpenRing
        (Ideal.Quotient.mk targetIdeal (MvPolynomial.X 0)) = openQuotientW := by
  simp [targetToOpenRing, targetPolynomialEvaluation]

theorem targetToOpenRing_r :
    targetToOpenRing
        (Ideal.Quotient.mk targetIdeal (MvPolynomial.X 1)) = openQuotientR := by
  simp [targetToOpenRing, targetPolynomialEvaluation]

/-- The genuine affine-scheme morphism induced by the checked quotient
coordinate formulas. -/
def quotientMorphism :
    Spec (.of SourceOpenRing) ⟶ Spec (.of TargetRing) :=
  Spec.map (CommRingCat.ofHom targetToOpenRing)

/-- The actual scheme morphism has the checked coordinate-ring map as its
affine comorphism. -/
theorem quotientMorphism_preimage :
    Spec.preimage quotientMorphism = CommRingCat.ofHom targetToOpenRing := by
  rw [quotientMorphism, Spec.preimage_map]

end MazurTorsion.OrderThirtyFive.QuotientScheme
