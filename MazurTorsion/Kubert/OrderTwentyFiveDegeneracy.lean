/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveFiveDivisionFactorization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Degeneracy parameters for the order-twenty-five quintic

Forgetting the generator of the marked order-five subgroup identifies the
order-five Tate parameter `c` with the standard `X₀(5)` parameter

`(c² - 11c - 1) / c`.

The two parameters on the oriented five-division quintic satisfy the explicit
degree-five degeneracy equation for `X₀(25)`.  The final definitions record
the rational Hauptmodul parametrization of that equation and its Fricke
symmetry.
-/

namespace MazurTorsion.Kubert

/-- The standard `X₀(5)` parameter obtained by forgetting the generator of
the order-five Tate point. -/
def orderFiveXZeroParameter (c : ℚ) : ℚ :=
  (c ^ 2 - 11 * c - 1) / c

/-- Numerator in the source `j`-map on `X₀(5)`. -/
def orderFiveXZeroJNumerator (t : ℚ) : ℚ :=
  t ^ 2 + 10 * t + 5

/-- Numerator in the quotient `j`-map on `X₀(5)`. -/
def orderFiveXZeroQuotientJNumerator (t : ℚ) : ℚ :=
  t ^ 2 + 250 * t + 3125

/-- The order-five Tate curve has the standard source `X₀(5)` invariant
identity. -/
theorem orderFiveCurve_xZeroParameter_identity
    (c : ℚ) (hc : c ≠ 0) :
    orderFiveXZeroJNumerator (orderFiveXZeroParameter c) ^ 3 *
        (orderFiveCurve c).Δ =
      (orderFiveCurve c).c₄ ^ 3 * orderFiveXZeroParameter c := by
  rw [orderFiveCurve_discriminant, orderFiveCurve_c₄]
  simp only [orderFiveXZeroParameter, orderFiveXZeroJNumerator,
    orderFiveC4Polynomial]
  field_simp [hc]
  ring

/-- The explicit Vélu target has the standard quotient `X₀(5)` invariant
identity for the same parameter. -/
theorem orderFiveVeluTarget_xZeroParameter_identity
    (c : ℚ) (hc : c ≠ 0) :
    orderFiveXZeroQuotientJNumerator (orderFiveXZeroParameter c) ^ 3 *
        (orderFiveVeluTarget c).Δ =
      (orderFiveVeluTarget c).c₄ ^ 3 *
        orderFiveXZeroParameter c ^ 5 := by
  rw [orderFiveVeluTarget_discriminant, orderFiveVeluTarget_c₄]
  simp only [orderFiveXZeroParameter,
    orderFiveXZeroQuotientJNumerator,
    orderFiveVeluTargetC4Polynomial]
  field_simp [hc]
  ring

/-- The degree-five relation between the two `X₀(5)` degeneracy parameters
on `X₀(25)`. -/
def orderTwentyFiveDegeneracyRelation (t s : ℚ) : ℚ :=
  s ^ 5 - s ^ 4 * t ^ 5 - 30 * s ^ 4 * t ^ 4 -
    315 * s ^ 4 * t ^ 3 - 1300 * s ^ 4 * t ^ 2 -
    1575 * s ^ 4 * t - 125 * s ^ 3 * t ^ 4 -
    3750 * s ^ 3 * t ^ 3 - 39375 * s ^ 3 * t ^ 2 -
    162500 * s ^ 3 * t - 15625 * s ^ 2 * t ^ 3 -
    468750 * s ^ 2 * t ^ 2 - 4921875 * s ^ 2 * t -
    1953125 * s * t ^ 2 - 58593750 * s * t -
    244140625 * t

/-- Clearing the two generator-forgetting denominators factors the
degeneracy relation as the product of the two oriented quintics. -/
theorem orderTwentyFiveDegeneracyRelation_cleared
    (c d : ℚ) (hc : c ≠ 0) (hd : d ≠ 0) :
    c ^ 5 * d ^ 5 *
        orderTwentyFiveDegeneracyRelation
          (orderFiveXZeroParameter d) (orderFiveXZeroParameter c) =
      orderTwentyFiveFiveDivisionFactor c d *
        orderTwentyFiveFiveDivisionReverseFactor c d := by
  simp only [orderTwentyFiveDegeneracyRelation,
    orderFiveXZeroParameter,
    orderTwentyFiveFiveDivisionFactor,
    orderTwentyFiveFiveDivisionReverseFactor]
  field_simp [hc, hd]
  ring

/-- Every point on the fixed oriented five-division quintic maps to the
degree-five `X₀(25)` degeneracy relation. -/
theorem orderTwentyFiveDegeneracyRelation_eq_zero_of_fiveDivisionFactor
    {c d : ℚ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hfactor : orderTwentyFiveFiveDivisionFactor c d = 0) :
    orderTwentyFiveDegeneracyRelation
      (orderFiveXZeroParameter d) (orderFiveXZeroParameter c) = 0 := by
  have hcleared :=
    orderTwentyFiveDegeneracyRelation_cleared c d hc hd
  rw [hfactor, zero_mul] at hcleared
  exact (mul_eq_zero.mp hcleared).resolve_left
    (mul_ne_zero (pow_ne_zero 5 hc) (pow_ne_zero 5 hd))

/-- Denominator polynomial in the rational Hauptmodul parametrization of
the degeneracy relation. -/
def orderTwentyFiveHauptmodulDenominator (n : ℚ) : ℚ :=
  n ^ 4 + 5 * n ^ 3 + 15 * n ^ 2 + 25 * n + 25

/-- The Hauptmodul denominator never vanishes over the rationals. -/
theorem orderTwentyFiveHauptmodulDenominator_ne_zero (n : ℚ) :
    orderTwentyFiveHauptmodulDenominator n ≠ 0 := by
  intro hzero
  by_cases hn : n = 0
  · subst n
    norm_num [orderTwentyFiveHauptmodulDenominator] at hzero
  · have hsquare :
        (2 * n ^ 2 + 5 * n + 10) ^ 2 = 5 * n ^ 2 := by
      dsimp only [orderTwentyFiveHauptmodulDenominator] at hzero
      nlinarith
    have hfive : ¬ IsSquare (5 : ℚ) := by
      intro h
      exact (by decide : Nat.Prime 5).not_isSquare
        (Rat.isSquare_natCast_iff.mp h)
    apply hfive
    refine ⟨(2 * n ^ 2 + 5 * n + 10) / n, ?_⟩
    field_simp [hn]
    nlinarith [hsquare]

/-- The first `X₀(5)` degeneracy parameter in terms of the
`X₀(25)` Hauptmodul. -/
def orderTwentyFiveFirstDegeneracyParameter (n : ℚ) : ℚ :=
  n ^ 5 / orderTwentyFiveHauptmodulDenominator n

/-- The second `X₀(5)` degeneracy parameter in terms of the
`X₀(25)` Hauptmodul. -/
def orderTwentyFiveSecondDegeneracyParameter (n : ℚ) : ℚ :=
  n * orderTwentyFiveHauptmodulDenominator n

/-- The Hauptmodul formulas satisfy the degree-five degeneracy equation. -/
theorem orderTwentyFiveDegeneracyRelation_parametrized (n : ℚ) :
    orderTwentyFiveDegeneracyRelation
      (orderTwentyFiveFirstDegeneracyParameter n)
      (orderTwentyFiveSecondDegeneracyParameter n) = 0 := by
  simp only [orderTwentyFiveDegeneracyRelation,
    orderTwentyFiveFirstDegeneracyParameter,
    orderTwentyFiveSecondDegeneracyParameter]
  field_simp [orderTwentyFiveHauptmodulDenominator_ne_zero n]
  simp only [orderTwentyFiveHauptmodulDenominator]
  ring

/-- Denominator of the rational inverse to the two degeneracy maps. -/
def orderTwentyFiveHauptmodulRecoveryDenominator (t s : ℚ) : ℚ :=
  (s ^ 2 + 250 * s + 3125) *
    (s * t + 5 * s + 125 * t + 125)

/-- Numerator of the rational inverse to the two degeneracy maps. -/
def orderTwentyFiveHauptmodulRecoveryNumerator (t s : ℚ) : ℚ :=
  s ^ 3 * t ^ 2 + 10 * s ^ 3 * t + 15 * s ^ 3 -
    50 * s ^ 2 * t ^ 3 - 750 * s ^ 2 * t ^ 2 -
    3000 * s ^ 2 * t + 1250 * s ^ 2 - 3125 * s * t ^ 2 -
    93750 * s * t + 15625 * s - 781250 * t

/-- The `X₀(25)` Hauptmodul recovered from its two `X₀(5)` degeneracy
parameters. -/
def orderTwentyFiveHauptmodulAt (t s : ℚ) : ℚ :=
  orderTwentyFiveHauptmodulRecoveryNumerator t s /
    orderTwentyFiveHauptmodulRecoveryDenominator t s

private theorem five_not_isSquare : ¬ IsSquare (5 : ℚ) := by
  intro h
  exact (by decide : Nat.Prime 5).not_isSquare
    (Rat.isSquare_natCast_iff.mp h)

private theorem orderTwentyFiveRecoveryFirstFactor_ne_zero (s : ℚ) :
    s ^ 2 + 250 * s + 3125 ≠ 0 := by
  intro hzero
  apply five_not_isSquare
  refine ⟨(s + 125) / 50, ?_⟩
  field_simp
  nlinarith

private theorem orderTwentyFiveRecoveryQuadraticOne_ne_zero (t : ℚ) :
    t ^ 2 + 4 * t - 1 ≠ 0 := by
  intro hzero
  apply five_not_isSquare
  exact ⟨t + 2, by nlinarith⟩

private theorem orderTwentyFiveRecoveryQuadraticTwo_ne_zero (t : ℚ) :
    t ^ 2 + 10 * t + 5 ≠ 0 := by
  intro hzero
  apply five_not_isSquare
  refine ⟨(t + 5) / 2, ?_⟩
  field_simp
  nlinarith

/-- Substitution certificate used to exclude the second recovery
denominator on the degeneracy curve. -/
private theorem orderTwentyFiveDegeneracyRelation_linear_certificate
    (t : ℚ) (ht : t + 5 ≠ 0) :
    (t + 5) ^ 5 *
        orderTwentyFiveDegeneracyRelation t
          (-125 * (t + 1) / (t + 5)) =
      -244140625 * (t ^ 2 + 4 * t - 1) ^ 2 *
        (t ^ 2 + 10 * t + 5) ^ 3 := by
  simp only [orderTwentyFiveDegeneracyRelation]
  field_simp [ht]
  ring

/-- The rational inverse has no pole at a rational point of the degeneracy
curve. -/
theorem orderTwentyFiveHauptmodulRecoveryDenominator_ne_zero
    {t s : ℚ} (hrelation : orderTwentyFiveDegeneracyRelation t s = 0) :
    orderTwentyFiveHauptmodulRecoveryDenominator t s ≠ 0 := by
  apply mul_ne_zero (orderTwentyFiveRecoveryFirstFactor_ne_zero s)
  intro hlinear
  have ht : t + 5 ≠ 0 := by
    intro htzero
    have htvalue : t = -5 := by linarith
    rw [htvalue] at hlinear
    linarith
  have hs : s = -125 * (t + 1) / (t + 5) := by
    apply (eq_div_iff ht).2
    linear_combination hlinear
  have hcertificate :=
    orderTwentyFiveDegeneracyRelation_linear_certificate t ht
  rw [← hs, hrelation, mul_zero] at hcertificate
  have hright :
      -244140625 * (t ^ 2 + 4 * t - 1) ^ 2 *
          (t ^ 2 + 10 * t + 5) ^ 3 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num)
        (pow_ne_zero 2
          (orderTwentyFiveRecoveryQuadraticOne_ne_zero t)))
      (pow_ne_zero 3
        (orderTwentyFiveRecoveryQuadraticTwo_ne_zero t))
  exact hright hcertificate.symm

/-- The recovered Hauptmodul reproduces both degeneracy parameters. -/
theorem orderTwentyFiveHauptmodulAt_spec
    {t s : ℚ} (hrelation : orderTwentyFiveDegeneracyRelation t s = 0) :
    orderTwentyFiveFirstDegeneracyParameter
        (orderTwentyFiveHauptmodulAt t s) = t ∧
      orderTwentyFiveSecondDegeneracyParameter
        (orderTwentyFiveHauptmodulAt t s) = s := by
  let N := orderTwentyFiveHauptmodulRecoveryNumerator t s
  let C := orderTwentyFiveHauptmodulRecoveryDenominator t s
  let n := N / C
  have hC : C ≠ 0 :=
    orderTwentyFiveHauptmodulRecoveryDenominator_ne_zero hrelation
  have hn : orderTwentyFiveHauptmodulAt t s = n := rfl
  have hmain := hrelation
  simp only [orderTwentyFiveDegeneracyRelation] at hmain
  constructor
  · rw [hn, orderTwentyFiveFirstDegeneracyParameter,
      div_eq_iff (orderTwentyFiveHauptmodulDenominator_ne_zero
        n)]
    simp only [orderTwentyFiveHauptmodulDenominator]
    dsimp only [n]
    field_simp [hC]
    simp only [N, C, orderTwentyFiveHauptmodulRecoveryNumerator,
      orderTwentyFiveHauptmodulRecoveryDenominator]
    grobner
  · rw [hn]
    simp only [orderTwentyFiveSecondDegeneracyParameter,
      orderTwentyFiveHauptmodulDenominator]
    dsimp only [n]
    field_simp [hC]
    simp only [N, C, orderTwentyFiveHauptmodulRecoveryNumerator,
      orderTwentyFiveHauptmodulRecoveryDenominator]
    grobner

/-- Fricke inversion exchanges the first degeneracy parameter with the
reciprocal of the second. -/
theorem orderTwentyFiveFirstDegeneracyParameter_fricke
    (n : ℚ) (hn : n ≠ 0) :
    orderTwentyFiveFirstDegeneracyParameter (5 / n) =
      125 / orderTwentyFiveSecondDegeneracyParameter n := by
  rw [orderTwentyFiveFirstDegeneracyParameter,
    orderTwentyFiveSecondDegeneracyParameter]
  field_simp [hn, orderTwentyFiveHauptmodulDenominator_ne_zero n,
    orderTwentyFiveHauptmodulDenominator_ne_zero (5 / n)]
  simp only [orderTwentyFiveHauptmodulDenominator]
  field_simp [hn]
  ring

/-- Fricke inversion exchanges the second degeneracy parameter with the
reciprocal of the first. -/
theorem orderTwentyFiveSecondDegeneracyParameter_fricke
    (n : ℚ) (hn : n ≠ 0) :
    orderTwentyFiveSecondDegeneracyParameter (5 / n) =
      125 / orderTwentyFiveFirstDegeneracyParameter n := by
  rw [orderTwentyFiveFirstDegeneracyParameter,
    orderTwentyFiveSecondDegeneracyParameter]
  field_simp [hn, orderTwentyFiveHauptmodulDenominator_ne_zero n,
    orderTwentyFiveHauptmodulDenominator_ne_zero (5 / n)]
  simp only [orderTwentyFiveHauptmodulDenominator]
  field_simp [hn]
  ring

/-- An exact rational order-twenty-five point reaches the rational
`X₀(25)` Hauptmodul together with both nonzero degeneracy parameters and the
original invariant scales. -/
theorem orderTwentyFive_degeneracyHauptmodul_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h25 : addOrderOf P = 25) :
    ∃ (c d u n : ℚ),
      c ≠ 0 ∧ c ^ 2 - 11 * c - 1 ≠ 0 ∧
        d ≠ 0 ∧ d ^ 2 - 11 * d - 1 ≠ 0 ∧ u ≠ 0 ∧ n ≠ 0 ∧
        orderTwentyFiveFiveDivisionFactor c d = 0 ∧
        orderTwentyFiveFirstDegeneracyParameter n =
          orderFiveXZeroParameter d ∧
        orderTwentyFiveSecondDegeneracyParameter n =
          orderFiveXZeroParameter c ∧
        u ^ 12 * E.Δ = (orderFiveCurve c).Δ ∧
        u ^ 4 * E.c₄ = (orderFiveCurve c).c₄ := by
  obtain ⟨c, d, u, hc, hcfactor, hd, hdfactor, hu,
      hfiveDivision, hdisc, hc₄⟩ :=
    orderTwentyFive_fiveDivisionFactor_package E P h25
  have hrelation :
      orderTwentyFiveDegeneracyRelation
          (orderFiveXZeroParameter d) (orderFiveXZeroParameter c) = 0 :=
    orderTwentyFiveDegeneracyRelation_eq_zero_of_fiveDivisionFactor
      hc hd hfiveDivision
  let n := orderTwentyFiveHauptmodulAt
    (orderFiveXZeroParameter d) (orderFiveXZeroParameter c)
  obtain ⟨hfirst, hsecond⟩ :=
    orderTwentyFiveHauptmodulAt_spec hrelation
  have hs : orderFiveXZeroParameter c ≠ 0 :=
    div_ne_zero hcfactor hc
  have hn : n ≠ 0 := by
    intro hnzero
    apply hs
    rw [← hsecond]
    simp [n, hnzero, orderTwentyFiveSecondDegeneracyParameter]
  exact ⟨c, d, u, n, hc, hcfactor, hd, hdfactor, hu, hn,
    hfiveDivision, hfirst, hsecond, hdisc, hc₄⟩

/-- At an exact rational order-twenty-five point, Fricke inversion exchanges
the two recovered `X₀(5)` degeneracy parameters, with the standard reciprocal
factor `125`. -/
theorem orderTwentyFive_degeneracyFricke_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h25 : addOrderOf P = 25) :
    ∃ (c d u n : ℚ),
      c ≠ 0 ∧ c ^ 2 - 11 * c - 1 ≠ 0 ∧
        d ≠ 0 ∧ d ^ 2 - 11 * d - 1 ≠ 0 ∧ u ≠ 0 ∧ n ≠ 0 ∧
        orderTwentyFiveFiveDivisionFactor c d = 0 ∧
        orderTwentyFiveFirstDegeneracyParameter n =
          orderFiveXZeroParameter d ∧
        orderTwentyFiveSecondDegeneracyParameter n =
          orderFiveXZeroParameter c ∧
        orderTwentyFiveFirstDegeneracyParameter (5 / n) =
          125 / orderFiveXZeroParameter c ∧
        orderTwentyFiveSecondDegeneracyParameter (5 / n) =
          125 / orderFiveXZeroParameter d ∧
        u ^ 12 * E.Δ = (orderFiveCurve c).Δ ∧
        u ^ 4 * E.c₄ = (orderFiveCurve c).c₄ := by
  obtain ⟨c, d, u, n, hc, hcfactor, hd, hdfactor, hu, hn,
      hfiveDivision, hfirst, hsecond, hdisc, hc₄⟩ :=
    orderTwentyFive_degeneracyHauptmodul_package E P h25
  have hfrickeFirst :=
    orderTwentyFiveFirstDegeneracyParameter_fricke n hn
  have hfrickeSecond :=
    orderTwentyFiveSecondDegeneracyParameter_fricke n hn
  rw [hsecond] at hfrickeFirst
  rw [hfirst] at hfrickeSecond
  exact ⟨c, d, u, n, hc, hcfactor, hd, hdfactor, hu, hn,
    hfiveDivision, hfirst, hsecond, hfrickeFirst, hfrickeSecond,
    hdisc, hc₄⟩

end MazurTorsion.Kubert
