/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenMumfordTangent

/-!
# Explicit quartic-support reduction for `X₁(13)` Mumford data

This file implements the coefficient algebra needed after coprime composition
of two quadratic supports.  Write

* `U = X⁴ + u₃X³ + u₂X² + u₁X + u₀`, and
* `V = v₃X³ + v₂X² + v₁X + v₀`.

Division of the fixed sextic minus `V²` by `U` has an explicit quadratic
quotient and four explicit remainder coefficients.  Their vanishing is a
finite coefficient certificate for `U ∣ f - V²`.

The quotient has leading coefficient `δ = 1 - v₃²`.  When `δ ≠ 0`, it is
normalized to a monic quadratic `U'`.  An explicit linear polynomial `V'` is
congruent to `-V` modulo `U'`; consequently `U' ∣ f - V'²`.  The result is
packaged in the existing normalized `AffineMumford` coordinate type.

This is polynomial reduction only.  It does not assert that the input arose
from a particular divisor-class composition, nor does it define or claim a
Jacobian group law.
-/

namespace MazurTorsion.XOneThirteenMumford

open Polynomial

noncomputable section

namespace AffineMumford

/-! ## Quartic division by coefficients -/

/-- A monic quartic support in coefficient coordinates. -/
def monicQuartic (u₀ u₁ u₂ u₃ : ℚ) : ℚ[X] :=
  X ^ 4 + C u₃ * X ^ 3 + C u₂ * X ^ 2 + C u₁ * X + C u₀

/-- A cubic-or-lower ordinate in coefficient coordinates. -/
def cubicPolynomial (v₀ v₁ v₂ v₃ : ℚ) : ℚ[X] :=
  C v₃ * X ^ 3 + C v₂ * X ^ 2 + C v₁ * X + C v₀

/-- Leading coefficient of the quadratic quotient. -/
def quarticQuotientLeading (v₃ : ℚ) : ℚ :=
  1 - v₃ ^ 2

/-- Linear coefficient of the quadratic quotient. -/
def quarticQuotientLinear (u₃ v₂ v₃ : ℚ) : ℚ :=
  2 - 2 * v₂ * v₃ - u₃ * quarticQuotientLeading v₃

/-- Constant coefficient of the quadratic quotient. -/
def quarticQuotientConstant (u₂ u₃ v₁ v₂ v₃ : ℚ) : ℚ :=
  1 - v₂ ^ 2 - 2 * v₁ * v₃ -
    u₃ * quarticQuotientLinear u₃ v₂ v₃ -
    u₂ * quarticQuotientLeading v₃

/-- The explicit quotient in degree-four support division. -/
def quarticQuotient (u₂ u₃ v₁ v₂ v₃ : ℚ) : ℚ[X] :=
  C (quarticQuotientLeading v₃) * X ^ 2 +
    C (quarticQuotientLinear u₃ v₂ v₃) * X +
    C (quarticQuotientConstant u₂ u₃ v₁ v₂ v₃)

/-- Constant remainder coefficient in quartic support division. -/
def quarticRemainderZero
    (u₀ _u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) : ℚ :=
  1 - v₀ ^ 2 -
    u₀ * quarticQuotientConstant u₂ u₃ v₁ v₂ v₃

/-- Linear remainder coefficient in quartic support division. -/
def quarticRemainderOne
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) : ℚ :=
  4 - 2 * v₀ * v₁ -
    (u₀ * quarticQuotientLinear u₃ v₂ v₃ +
      u₁ * quarticQuotientConstant u₂ u₃ v₁ v₂ v₃)

/-- Quadratic remainder coefficient in quartic support division. -/
def quarticRemainderTwo
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) : ℚ :=
  6 - v₁ ^ 2 - 2 * v₀ * v₂ -
    (u₀ * quarticQuotientLeading v₃ +
      u₁ * quarticQuotientLinear u₃ v₂ v₃ +
      u₂ * quarticQuotientConstant u₂ u₃ v₁ v₂ v₃)

/-- Cubic remainder coefficient in quartic support division. -/
def quarticRemainderThree
    (_u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) : ℚ :=
  2 - 2 * v₀ * v₃ - 2 * v₁ * v₂ -
    (u₁ * quarticQuotientLeading v₃ +
      u₂ * quarticQuotientLinear u₃ v₂ v₃ +
      u₃ * quarticQuotientConstant u₂ u₃ v₁ v₂ v₃)

/-- Exact symbolic division by the monic quartic.  The four displayed scalar
remainders are the complete low-degree obstruction to divisibility. -/
theorem quartic_division_certificate
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) :
    sexticPolynomial - cubicPolynomial v₀ v₁ v₂ v₃ ^ 2 =
      monicQuartic u₀ u₁ u₂ u₃ * quarticQuotient u₂ u₃ v₁ v₂ v₃ +
        C (quarticRemainderZero u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) +
        C (quarticRemainderOne u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X +
        C (quarticRemainderTwo u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X ^ 2 +
        C (quarticRemainderThree u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X ^ 3 := by
  apply Polynomial.funext
  intro z
  simp only [sexticPolynomial, cubicPolynomial, monicQuartic,
    quarticQuotient, quarticQuotientLeading, quarticQuotientLinear,
    quarticQuotientConstant, quarticRemainderZero, quarticRemainderOne,
    quarticRemainderTwo, quarticRemainderThree, eval_sub, eval_add,
    eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, eval_one]
  ring

/-- Fixed-curve validity condition for a monic quartic support and a
cubic-or-lower ordinate. -/
def IsQuarticMumfordPair
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) : Prop :=
  monicQuartic u₀ u₁ u₂ u₃ ∣
    sexticPolynomial - cubicPolynomial v₀ v₁ v₂ v₃ ^ 2

/-- Vanishing of the four scalar remainders is a sufficient checked
certificate for quartic divisibility. -/
theorem isQuarticMumfordPair_of_remainders_eq_zero
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ)
    (h₀ : quarticRemainderZero u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0)
    (h₁ : quarticRemainderOne u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0)
    (h₂ : quarticRemainderTwo u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0)
    (h₃ : quarticRemainderThree u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0) :
    IsQuarticMumfordPair u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ := by
  refine ⟨quarticQuotient u₂ u₃ v₁ v₂ v₃, ?_⟩
  rw [quartic_division_certificate, h₀, h₁, h₂, h₃]
  simp

/-- Genuine divisibility by the monic quartic forces all four displayed
scalar remainders to vanish. -/
theorem remainders_eq_zero_of_isQuarticMumfordPair
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ)
    (hpair : IsQuarticMumfordPair u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) :
    quarticRemainderZero u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 ∧
      quarticRemainderOne u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 ∧
      quarticRemainderTwo u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 ∧
      quarticRemainderThree u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 := by
  have hu : (monicQuartic u₀ u₁ u₂ u₃).Monic := by
    simp only [monicQuartic]
    monicity <;> norm_num
  let rem : ℚ[X] :=
    C (quarticRemainderZero u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) +
      C (quarticRemainderOne u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X +
      C (quarticRemainderTwo u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X ^ 2 +
      C (quarticRemainderThree u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X ^ 3
  have hsub : monicQuartic u₀ u₁ u₂ u₃ ∣
      (sexticPolynomial - cubicPolynomial v₀ v₁ v₂ v₃ ^ 2) - rem := by
    refine ⟨quarticQuotient u₂ u₃ v₁ v₂ v₃, ?_⟩
    calc
      (sexticPolynomial - cubicPolynomial v₀ v₁ v₂ v₃ ^ 2) - rem =
          (monicQuartic u₀ u₁ u₂ u₃ * quarticQuotient u₂ u₃ v₁ v₂ v₃ +
            C (quarticRemainderZero u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) +
            C (quarticRemainderOne u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X +
            C (quarticRemainderTwo u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X ^ 2 +
            C (quarticRemainderThree u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃) * X ^ 3) - rem := by
              rw [quartic_division_certificate]
      _ = monicQuartic u₀ u₁ u₂ u₃ * quarticQuotient u₂ u₃ v₁ v₂ v₃ := by
        simp only [rem]
        ring
  have hmod := modByMonic_eq_of_dvd_sub hu hsub
  have hpmod :
      (sexticPolynomial - cubicPolynomial v₀ v₁ v₂ v₃ ^ 2) %ₘ
          monicQuartic u₀ u₁ u₂ u₃ = 0 :=
    (modByMonic_eq_zero_iff_dvd hu).2 hpair
  have hrdeg : rem.degree < (monicQuartic u₀ u₁ u₂ u₃).degree := by
    have huDegree : (monicQuartic u₀ u₁ u₂ u₃).degree = 4 := by
      simp only [monicQuartic]
      compute_degree <;> norm_num
    rw [huDegree]
    dsimp only [rem]
    compute_degree
    all_goals norm_num
  have hrmod : rem %ₘ monicQuartic u₀ u₁ u₂ u₃ = rem :=
    (modByMonic_eq_self_iff hu).2 hrdeg
  rw [hpmod, hrmod] at hmod
  have hz : rem = 0 := hmod.symm
  constructor
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 0) hz
    simpa [rem] using hc
  constructor
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hz
    simpa [rem] using hc
  constructor
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 2) hz
    simpa [rem] using hc
  · have hc := congrArg (fun p : ℚ[X] => p.coeff 3) hz
    simpa [rem] using hc

/-- The four scalar equations are exactly the quartic divisibility condition
over `ℚ`. -/
theorem isQuarticMumfordPair_iff_remainders_eq_zero
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) :
    IsQuarticMumfordPair u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ ↔
      quarticRemainderZero u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 ∧
      quarticRemainderOne u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 ∧
      quarticRemainderTwo u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 ∧
      quarticRemainderThree u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0 := by
  constructor
  · exact remainders_eq_zero_of_isQuarticMumfordPair
      u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    exact isQuarticMumfordPair_of_remainders_eq_zero
      u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ h₀ h₁ h₂ h₃

/-! ## Monic quotient normalization and ordinate reduction -/

/-- Constant coefficient of the normalized quadratic quotient. -/
def reducedSupportConstant (u₂ u₃ v₁ v₂ v₃ : ℚ) : ℚ :=
  quarticQuotientConstant u₂ u₃ v₁ v₂ v₃ /
    quarticQuotientLeading v₃

/-- Linear coefficient of the normalized quadratic quotient. -/
def reducedSupportLinear (u₃ v₂ v₃ : ℚ) : ℚ :=
  quarticQuotientLinear u₃ v₂ v₃ / quarticQuotientLeading v₃

/-- The monic quadratic obtained from the quartic quotient. -/
def reducedSupport (u₂ u₃ v₁ v₂ v₃ : ℚ) : ℚ[X] :=
  monicQuadratic (reducedSupportConstant u₂ u₃ v₁ v₂ v₃)
    (reducedSupportLinear u₃ v₂ v₃)

/-- Constant coefficient of `-V mod U'`. -/
def reducedOrdinateConstant
    (u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) : ℚ :=
  let s₀ := reducedSupportConstant u₂ u₃ v₁ v₂ v₃;
  let s₁ := reducedSupportLinear u₃ v₂ v₃;
  -v₀ + v₂ * s₀ - v₃ * s₀ * s₁

/-- Linear coefficient of `-V mod U'`. -/
def reducedOrdinateLinear
    (u₂ u₃ _v₀ v₁ v₂ v₃ : ℚ) : ℚ :=
  let s₀ := reducedSupportConstant u₂ u₃ v₁ v₂ v₃;
  let s₁ := reducedSupportLinear u₃ v₂ v₃;
  -v₁ + v₂ * s₁ - v₃ * s₁ ^ 2 + v₃ * s₀

/-- The explicit reduced ordinate `-V mod U'`. -/
def reducedOrdinate
    (u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) : ℚ[X] :=
  linearPolynomial (reducedOrdinateConstant u₂ u₃ v₀ v₁ v₂ v₃)
    (reducedOrdinateLinear u₂ u₃ v₀ v₁ v₂ v₃)

/-- Normalizing the quotient by its nonzero leading coefficient gives the
displayed monic quadratic. -/
theorem quarticQuotient_eq_leading_mul_reducedSupport
    (u₂ u₃ v₁ v₂ v₃ : ℚ)
    (hδ : quarticQuotientLeading v₃ ≠ 0) :
    quarticQuotient u₂ u₃ v₁ v₂ v₃ =
      C (quarticQuotientLeading v₃) *
        reducedSupport u₂ u₃ v₁ v₂ v₃ := by
  apply Polynomial.funext
  intro z
  simp only [quarticQuotient, reducedSupport, monicQuadratic,
    reducedSupportConstant, reducedSupportLinear, eval_add, eval_mul,
    eval_pow, eval_X, eval_C]
  field_simp [hδ]

/-- Explicit congruence identity showing that the reduced ordinate is
`-V` modulo the normalized quotient. -/
theorem cubic_add_reducedOrdinate_identity
    (u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) :
    cubicPolynomial v₀ v₁ v₂ v₃ +
        reducedOrdinate u₂ u₃ v₀ v₁ v₂ v₃ =
      reducedSupport u₂ u₃ v₁ v₂ v₃ *
        linearPolynomial
          (v₂ - v₃ * reducedSupportLinear u₃ v₂ v₃) v₃ := by
  apply Polynomial.funext
  intro z
  simp only [cubicPolynomial, reducedOrdinate, reducedOrdinateConstant,
    reducedOrdinateLinear, reducedSupport, monicQuadratic,
    linearPolynomial, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- Reduce a valid quartic coefficient certificate to normalized quadratic
Mumford coordinates.

The four remainder equalities expose all divisibility premises.  The sole
denominator premise is `1 - v₃² ≠ 0`, exactly the condition that the quotient
really has degree two and can be made monic. -/
def reduceQuartic
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ)
    (hδ : quarticQuotientLeading v₃ ≠ 0)
    (h₀ : quarticRemainderZero u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0)
    (h₁ : quarticRemainderOne u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0)
    (h₂ : quarticRemainderTwo u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0)
    (h₃ : quarticRemainderThree u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ = 0) :
    AffineMumford where
  u := reducedSupport u₂ u₃ v₁ v₂ v₃
  v := reducedOrdinate u₂ u₃ v₀ v₁ v₂ v₃
  u_monic := by
    simp only [reducedSupport, monicQuadratic]
    monicity <;> norm_num
  u_natDegree_le := by
    simp only [reducedSupport, monicQuadratic]
    compute_degree
  v_degree_lt := by
    have huDegree : (reducedSupport u₂ u₃ v₁ v₂ v₃).degree = 2 := by
      simp only [reducedSupport, monicQuadratic]
      compute_degree <;> norm_num
    rw [huDegree]
    simp only [reducedOrdinate, linearPolynomial]
    compute_degree
    all_goals norm_num
  equation_mod_u := by
    let U := monicQuartic u₀ u₁ u₂ u₃
    let V := cubicPolynomial v₀ v₁ v₂ v₃
    let Q := quarticQuotient u₂ u₃ v₁ v₂ v₃
    let U' := reducedSupport u₂ u₃ v₁ v₂ v₃
    let V' := reducedOrdinate u₂ u₃ v₀ v₁ v₂ v₃
    have hfactor : sexticPolynomial - V ^ 2 = U * Q := by
      dsimp only [U, V, Q]
      rw [quartic_division_certificate, h₀, h₁, h₂, h₃]
      simp
    have hnormalize : Q = C (quarticQuotientLeading v₃) * U' := by
      exact quarticQuotient_eq_leading_mul_reducedSupport
        u₂ u₃ v₁ v₂ v₃ hδ
    have hOld : U' ∣ sexticPolynomial - V ^ 2 := by
      refine ⟨U * C (quarticQuotientLeading v₃), ?_⟩
      rw [hfactor, hnormalize]
      ring
    have hcongruence : U' ∣ V + V' := by
      refine ⟨linearPolynomial
        (v₂ - v₃ * reducedSupportLinear u₃ v₂ v₃) v₃, ?_⟩
      exact cubic_add_reducedOrdinate_identity u₂ u₃ v₀ v₁ v₂ v₃
    have hsquares : U' ∣ V' ^ 2 - V ^ 2 := by
      obtain ⟨q, hq⟩ := hcongruence
      refine ⟨q * (V' - V), ?_⟩
      calc
        V' ^ 2 - V ^ 2 = (V + V') * (V' - V) := by ring
        _ = (U' * q) * (V' - V) := by rw [hq]
        _ = U' * (q * (V' - V)) := by ring
    have htarget : U' ∣ sexticPolynomial - V' ^ 2 := by
      convert hOld.sub hsquares using 1
      ring
    exact htarget

@[simp]
theorem reduceQuartic_u
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) (hδ h₀ h₁ h₂ h₃) :
    (reduceQuartic u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃
      hδ h₀ h₁ h₂ h₃).u = reducedSupport u₂ u₃ v₁ v₂ v₃ := rfl

@[simp]
theorem reduceQuartic_v
    (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℚ) (hδ h₀ h₁ h₂ h₃) :
    (reduceQuartic u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃
      hδ h₀ h₁ h₂ h₃).v =
        reducedOrdinate u₂ u₃ v₀ v₁ v₂ v₃ := rfl

/-! ## A concrete complementary-quartic reduction -/

private theorem complementaryQuartic_delta :
    quarticQuotientLeading 0 ≠ 0 := by
  norm_num [quarticQuotientLeading]

private theorem complementaryQuartic_remainders :
    quarticRemainderZero 4 2 0 1 1 0 0 0 = 0 ∧
      quarticRemainderOne 4 2 0 1 1 0 0 0 = 0 ∧
      quarticRemainderTwo 4 2 0 1 1 0 0 0 = 0 ∧
      quarticRemainderThree 4 2 0 1 1 0 0 0 = 0 := by
  norm_num [quarticRemainderZero, quarticRemainderOne,
    quarticRemainderTwo, quarticRemainderThree,
    quarticQuotientLeading, quarticQuotientLinear,
    quarticQuotientConstant]

/-- The exact quartic certificate

`f - 1 = (X⁴ + X³ + 2X + 4)(X² + X)`.

It is a compact concrete input to the generic reduction verifier. -/
theorem complementaryQuartic_division :
    sexticPolynomial - cubicPolynomial 1 0 0 0 ^ 2 =
      monicQuartic 4 2 0 1 * quarticQuotient 0 1 0 0 0 := by
  rw [quartic_division_certificate,
    complementaryQuartic_remainders.1,
    complementaryQuartic_remainders.2.1,
    complementaryQuartic_remainders.2.2.1,
    complementaryQuartic_remainders.2.2.2]
  simp

/-- Reduction of the complementary quartic with constant ordinate `1`. -/
def complementaryQuarticReduction : AffineMumford :=
  reduceQuartic 4 2 0 1 1 0 0 0 complementaryQuartic_delta
    complementaryQuartic_remainders.1
    complementaryQuartic_remainders.2.1
    complementaryQuartic_remainders.2.2.1
    complementaryQuartic_remainders.2.2.2

/-- The normalized quotient is the two-cusp support `X² + X`. -/
@[simp]
theorem complementaryQuarticReduction_u :
    complementaryQuarticReduction.u = monicQuadratic 0 1 := by
  rw [complementaryQuarticReduction, reduceQuartic_u]
  norm_num [reducedSupport, reducedSupportConstant, reducedSupportLinear,
    quarticQuotientLeading, quarticQuotientLinear,
    quarticQuotientConstant]

/-- Reduction changes the constant ordinate `1` to its negative. -/
@[simp]
theorem complementaryQuarticReduction_v :
    complementaryQuarticReduction.v = linearPolynomial (-1) 0 := by
  rw [complementaryQuarticReduction, reduceQuartic_v]
  norm_num [reducedOrdinate, reducedOrdinateConstant,
    reducedOrdinateLinear, reducedSupportConstant, reducedSupportLinear,
    quarticQuotientLeading, quarticQuotientLinear,
    quarticQuotientConstant]

/-- The concrete quartic reduction recovers the hyperelliptic conjugate of
the existing two-affine-cusp coordinate record.  This is equality of checked
Mumford coordinates, not a claim about divisor classes. -/
theorem complementaryQuarticReduction_eq_neg_cuspComposition :
    complementaryQuarticReduction = neg cuspComposition := by
  apply AffineMumford.ext <;>
    simp [linearPolynomial]

end AffineMumford

/-! ## Reduction of the concrete output modulo `5` -/

open XOneThirteenRationalMumfordReduction
open XOneThirteenFiniteMumfordFive

local instance : NeZero 5 := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Denominator-one integer coefficients of the reduced complementary
quartic. -/
def complementaryQuarticReducedCleared : ClearedDegreeTwo where
  u₀Numerator := 0
  u₁Numerator := 1
  v₀Numerator := -1
  v₁Numerator := 0
  denominator := 1
  denominator_ne_zero := by norm_num
  cleared_constant := by
    norm_num [clearedRemainderConstant]
  cleared_linear := by
    norm_num [clearedRemainderLinear]

/-- The cleared coefficients recover the polynomial reduction over `ℚ`. -/
theorem complementaryQuarticReducedCleared_toAffineMumford :
    complementaryQuarticReducedCleared.toAffineMumford =
      AffineMumford.complementaryQuarticReduction := by
  apply AffineMumford.ext <;>
    simp [complementaryQuarticReducedCleared,
      ClearedDegreeTwo.toAffineMumford, ClearedDegreeTwo.u₀,
      ClearedDegreeTwo.u₁, ClearedDegreeTwo.v₀, ClearedDegreeTwo.v₁,
      linearPolynomial]

/-- The reduced quartic certificate viewed through the existing cleared-data
sum. -/
def complementaryQuarticReducedMumford : ClearedMumford :=
  .inr complementaryQuarticReducedCleared

private theorem complementaryQuartic_denominator_good_F5 :
    ¬(5 : ℤ) ∣ complementaryQuarticReducedMumford.denominator := by
  norm_num [complementaryQuarticReducedMumford,
    ClearedMumford.denominator, complementaryQuarticReducedCleared]

/-- Existing coefficientwise reduction sends the quartic output into the
balanced record set modulo `5`. -/
def complementaryQuarticReductionF5 : BalancedMumfordF5 :=
  complementaryQuarticReducedMumford.reduceF5
    complementaryQuartic_denominator_good_F5

/-- The reduced value is the coefficient tuple `(0,1,-1,0)` modulo `5`. -/
theorem complementaryQuarticReductionF5_value :
    complementaryQuarticReductionF5.1 = rawDegreeTwoF5 0 1 (-1) 0 := by
  simp [complementaryQuarticReductionF5,
    complementaryQuarticReducedMumford,
    complementaryQuarticReducedCleared, ClearedMumford.reduceF5,
    ClearedMumford.reduceRawF5, ClearedMumford.degreeTwoRawF5,
    ClearedMumford.fractionF5]

/-- The concrete reduction is entry four of the existing exhaustive
eight-element degree-two table modulo `5`. -/
theorem complementaryQuarticReductionF5_table_entry :
    (degreeTwoRecordOfIndexF5 4).1 = (0, 1, 4, 0) ∧
      complementaryQuarticReductionF5.1 = rawDegreeTwoF5 0 1 4 0 := by
  constructor
  · rfl
  · rw [complementaryQuarticReductionF5_value]
    have h : (-1 : F5) = 4 := by decide
    rw [h]

/-- The existing finite verifier supplies reducedness and polynomial
divisibility for the concrete quartic reduction modulo `5`. -/
theorem complementaryQuarticReductionF5_spec :
    IsReducedEncodingF5 complementaryQuarticReductionF5.1 ∧
      recordUF5 complementaryQuarticReductionF5.1 ∣
        sexticF5 - recordVF5 complementaryQuarticReductionF5.1 ^ 2 :=
  balancedMumfordF5_spec complementaryQuarticReductionF5

end


end MazurTorsion.XOneThirteenMumford
