/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenFiniteField
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Quotient and arithmetic descent identities for `X₁(18)`

The order-three automorphism of the order-eighteen sextic has invariant
functions

`u = (x³ - 3x + 1)/(x(x-1))`,
`v = y/(x(x-1))`,

which satisfy

`v² = u² - 4u + 12`.

This file parameterizes that rational conic, identifies the degree-three
fiber as the cyclic cubic

`z³ - uz² + (u-3)z + 1`,

and records its orbit factorization and square discriminant.  After the
conic parameter is introduced, the cleared cubic has discriminant

`(t²+3)²(7t²+6t+3)²`.

The two quadratic factors are explicit norms in Eisenstein coordinates.
Writing `ω²+ω+1=0`, the second is

`N((3+ω)m + (1-ω)n) = 7m²+6mn+3n²`,

and `N(3+ω)=7`.  We prove these norm identities, multiplicativity, two
primitive-form Bézout identities, and the fact that the two norm forms
cannot both be divisible by `7` for coprime integer parameters.

For a rational root, comparison of all three coefficients of the cyclic
cubic gives two binary quadratic--cubic identities.  Their resultant is
`16`; a mod-`2` and mod-`16` calculation then proves that the remaining
integer quotient is one of `-8`, `-4`, `4`, or `8`.  The final boundary is
therefore a four-case primitive integral obstruction.

These are algebraic and local prerequisites for the classical
`π = 3+ω` descent.  They do not construct the induced endomorphism of the
Jacobian, prove `π`-surjectivity on its Mordell--Weil group, determine its
torsion, or solve the four remaining integral cases.
-/

namespace MazurTorsion.XOneEighteenDescent

open MazurTorsion.XOneEighteenFiniteField

/-! ## The rational conic quotient -/

/-- The conic abscissa obtained from a line through `(u,v)=(1,3)`. -/
def conicU (t : ℚ) : ℚ :=
  (t ^ 2 - 6 * t - 3) / (t ^ 2 - 1)

/-- The conic ordinate obtained from the same line. -/
def conicV (t : ℚ) : ℚ :=
  -(3 * t ^ 2 + 2 * t + 3) / (t ^ 2 - 1)

/-- The displayed parametrization lies on the invariant conic. -/
theorem conic_parameter_equation
    (t : ℚ) (ht : t ^ 2 ≠ 1) :
    conicV t ^ 2 = conicU t ^ 2 - 4 * conicU t + 12 := by
  simp only [conicU, conicV]
  field_simp [sub_ne_zero.mpr ht]
  ring

/-- The slope used to recover the conic parameter away from `u=1`. -/
def conicSlope (u v : ℚ) : ℚ :=
  (v - 3) / (u - 1)

private lemma conicSlope_sq_ne_one
    (u v : ℚ) (hu : u ≠ 1)
    (hconic : v ^ 2 = u ^ 2 - 4 * u + 12) :
    conicSlope u v ^ 2 ≠ 1 := by
  intro ht
  have hden : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hfactor :
      (conicSlope u v - 1) * (conicSlope u v + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with htpos | htneg
  · have hslope : conicSlope u v = 1 := by linarith
    simp only [conicSlope] at hslope
    field_simp [hden] at hslope
    have : u = 1 := by nlinarith
    exact hu this
  · have hslope : conicSlope u v = -1 := by linarith
    simp only [conicSlope] at hslope
    field_simp [hden] at hslope
    have : u = 1 := by nlinarith
    exact hu this

/-- Away from the base point's vertical fiber, the slope construction
recovers both conic coordinates. -/
theorem conic_parameter_inverse
    (u v : ℚ) (hu : u ≠ 1)
    (hconic : v ^ 2 = u ^ 2 - 4 * u + 12) :
    let t := conicSlope u v
    t ^ 2 ≠ 1 ∧ conicU t = u ∧ conicV t = v := by
  let t := conicSlope u v
  have ht : t ^ 2 ≠ 1 :=
    conicSlope_sq_ne_one u v hu hconic
  have huden : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hteq : t = (v - 3) / (u - 1) := rfl
  have hraw : (v - 3) ^ 2 - (u - 1) ^ 2 ≠ 0 := by
    intro hzero
    apply ht
    rw [hteq]
    field_simp [huden]
    nlinarith
  have hU : conicU t = u := by
    simp only [conicU]
    rw [hteq]
    field_simp [huden, hraw]
    nlinarith
  have hV : conicV t = v := by
    simp only [conicV]
    rw [hteq]
    field_simp [huden, hraw]
    nlinarith
  exact ⟨ht, hU, hV⟩

/-- The exceptional affine conic fiber `u=1` consists of `v=±3`. -/
theorem conic_at_one_iff (v : ℚ) :
    v ^ 2 = (1 : ℚ) ^ 2 - 4 * 1 + 12 ↔
      v = 3 ∨ v = -3 := by
  constructor
  · intro h
    have hfac : (v - 3) * (v + 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with hpos | hneg
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Every rational affine point on the invariant conic is either one of
the two exceptional points over `u=1`, or comes from the displayed
one-parameter family. -/
theorem conic_rational_parameterization
    (u v : ℚ)
    (hconic : v ^ 2 = u ^ 2 - 4 * u + 12) :
    (u = 1 ∧ (v = 3 ∨ v = -3)) ∨
      ∃ t : ℚ,
        t ^ 2 ≠ 1 ∧ conicU t = u ∧ conicV t = v := by
  by_cases hu : u = 1
  · left
    subst u
    exact ⟨rfl, (conic_at_one_iff v).mp hconic⟩
  · right
    exact ⟨conicSlope u v,
      conic_parameter_inverse u v hu hconic⟩

/-! ## The cyclic cubic fiber -/

/-- The degree-three fiber above a quotient abscissa `u`. -/
def fiberCubic (u z : ℚ) : ℚ :=
  z ^ 3 - u * z ^ 2 + (u - 3) * z + 1

private noncomputable def exceptionalFiberPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 3 -
    Polynomial.X ^ 2 -
    Polynomial.C 2 * Polynomial.X +
    Polynomial.C 1

private lemma exceptionalFiberPolynomial_monic :
    Polynomial.Monic exceptionalFiberPolynomial := by
  unfold exceptionalFiberPolynomial
  monicity!

private lemma exceptionalFiberPolynomial_no_root_mod_two :
    ∀ z : ZMod 2, z ^ 3 - z ^ 2 - 2 * z + 1 ≠ 0 := by
  decide

/-- The exceptional quotient fiber `u=1` has no rational abscissa. -/
theorem fiberCubic_one_ne_zero (x : ℚ) :
    fiberCubic 1 x ≠ 0 := by
  intro hx
  simp only [fiberCubic] at hx
  have hroot :
      Polynomial.aeval x exceptionalFiberPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [exceptionalFiberPolynomial]
    linear_combination hx
  obtain ⟨z, hxz, -⟩ :=
    exists_integer_of_is_root_of_monic
      exceptionalFiberPolynomial_monic hroot
  have hzrat :
      (z : ℚ) ^ 3 - (z : ℚ) ^ 2 -
          2 * (z : ℚ) + 1 = 0 := by
    have hzcast : (z : ℚ) = x := by
      simpa using hxz.symm
    rw [hzcast]
    linear_combination hx
  have hzint :
      z ^ 3 - z ^ 2 - 2 * z + 1 = 0 := by
    exact_mod_cast hzrat
  apply exceptionalFiberPolynomial_no_root_mod_two (z : ZMod 2)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 2)) hzint

/-- The invariant abscissa of a noncuspidal point satisfies its cubic
fiber equation. -/
theorem fiberCubic_invariantX
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    fiberCubic (invariantX x) x = 0 := by
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [fiberCubic, invariantX]
  field_simp [hx0, hxsub]
  ring

/-- A noncuspidal rational abscissa never lies over the exceptional
quotient value `u=1`. -/
theorem invariantX_ne_one
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    invariantX x ≠ 1 := by
  intro hu
  have hroot := fiberCubic_invariantX x hx0 hx1
  rw [hu] at hroot
  exact fiberCubic_one_ne_zero x hroot

/-- Product over the three-element Möbius orbit, viewed as a degree-three
norm polynomial. -/
def orbitNorm (x z : ℚ) : ℚ :=
  (z - x) *
    (z - orderThreeX x) *
    (z - orderThreeX (orderThreeX x))

/-- The orbit norm is exactly the cyclic cubic fiber polynomial. -/
theorem orbitNorm_eq_fiberCubic
    (x z : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    orbitNorm x z = fiberCubic (invariantX x) z := by
  simp only [orbitNorm]
  rw [orderThreeX_sq x hx0 hx1]
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [fiberCubic, invariantX, orderThreeX]
  field_simp [hden, hx0, hxsub]
  ring

/-- The standard discriminant formula for a cubic
`a z³ + b z² + c z + d`. -/
def cubicDiscriminant (a b c d : ℚ) : ℚ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d -
    27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- The cyclic cubic fiber has square discriminant. -/
theorem fiberCubic_discriminant (u : ℚ) :
    cubicDiscriminant 1 (-u) (u - 3) 1 =
      (u ^ 2 - 3 * u + 9) ^ 2 := by
  simp only [cubicDiscriminant]
  ring

/-- The conic-parameterized cubic with its sole denominator cleared. -/
def clearedFiber (t z : ℚ) : ℚ :=
  (t ^ 2 - 1) * z ^ 3 -
    (t ^ 2 - 6 * t - 3) * z ^ 2 +
    (-2 * t ^ 2 - 6 * t) * z +
    (t ^ 2 - 1)

/-- Clearing the conic denominator gives `clearedFiber`. -/
theorem clearedFiber_eq_mul_fiberCubic
    (t z : ℚ) (ht : t ^ 2 ≠ 1) :
    clearedFiber t z =
      (t ^ 2 - 1) * fiberCubic (conicU t) z := by
  simp only [clearedFiber, fiberCubic, conicU]
  field_simp [sub_ne_zero.mpr ht]
  ring

/-- A root of the parameterized fiber gives a root of the cleared cubic. -/
theorem clearedFiber_eq_zero
    (t z : ℚ) (ht : t ^ 2 ≠ 1)
    (hroot : fiberCubic (conicU t) z = 0) :
    clearedFiber t z = 0 := by
  rw [clearedFiber_eq_mul_fiberCubic t z ht, hroot, mul_zero]

/-- The homogeneous cubic obtained by writing the conic parameter as
`t=m/n`. -/
def homogeneousFiber (m n z : ℚ) : ℚ :=
  (m ^ 2 - n ^ 2) * z ^ 3 -
    (m ^ 2 - 6 * m * n - 3 * n ^ 2) * z ^ 2 +
    (-2 * m ^ 2 - 6 * m * n) * z +
    (m ^ 2 - n ^ 2)

/-- Substitution `t=m/n` turns the cleared cubic into its homogeneous
form after multiplication by `n²`. -/
theorem homogeneousFiber_eq_den_sq_mul
    (m n z : ℚ) (hn : n ≠ 0) :
    homogeneousFiber m n z =
      n ^ 2 * clearedFiber (m / n) z := by
  simp only [homogeneousFiber, clearedFiber]
  field_simp [hn]

/-- A root of the cleared rational-parameter cubic is a root of the
primitive homogeneous cubic attached to its canonical fraction. -/
theorem homogeneousFiber_eq_zero_of_clearedFiber
    (t z : ℚ) (hroot : clearedFiber t z = 0) :
    homogeneousFiber (t.num : ℚ) (t.den : ℚ) z = 0 := by
  have hn : (t.den : ℚ) ≠ 0 := by
    exact_mod_cast t.den_ne_zero
  rw [homogeneousFiber_eq_den_sq_mul
    (t.num : ℚ) (t.den : ℚ) z hn, Rat.num_div_den t,
    hroot, mul_zero]

/-- The homogeneous cubic discriminant is the product of the squares of
the two quadratic norm forms. -/
theorem homogeneousFiber_discriminant (m n : ℚ) :
    cubicDiscriminant
        (m ^ 2 - n ^ 2)
        (-(m ^ 2 - 6 * m * n - 3 * n ^ 2))
        (-2 * m ^ 2 - 6 * m * n)
        (m ^ 2 - n ^ 2) =
      (m ^ 2 + 3 * n ^ 2) ^ 2 *
        (7 * m ^ 2 + 6 * m * n + 3 * n ^ 2) ^ 2 := by
  simp only [cubicDiscriminant]
  ring

/-- Every rational noncuspidal point on the sextic admits the explicit
conic parameter and is a root of the resulting denominator-free cubic. -/
theorem noncuspidal_curve_parameterization
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    ∃ t : ℚ,
      t ^ 2 ≠ 1 ∧
      conicU t = invariantX x ∧
      conicV t = invariantY x y ∧
      clearedFiber t x = 0 := by
  have hconic :=
    invariant_conic_equation x y hx0 hx1 hcurve
  have hu : invariantX x ≠ 1 :=
    invariantX_ne_one x hx0 hx1
  let t := conicSlope (invariantX x) (invariantY x y)
  obtain ⟨ht, hU, hV⟩ :=
    conic_parameter_inverse
      (invariantX x) (invariantY x y) hu hconic
  refine ⟨t, ht, hU, hV, ?_⟩
  apply clearedFiber_eq_zero t x ht
  rw [hU]
  exact fiberCubic_invariantX x hx0 hx1

/-- Canonical numerator-denominator coordinates sharpen the preceding
statement to primitive integer parameters. -/
theorem noncuspidal_curve_primitive_parameterization
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    ∃ m n : ℤ,
      0 < n ∧
      IsCoprime m n ∧
      ((m : ℚ) / (n : ℚ)) ^ 2 ≠ 1 ∧
      conicU ((m : ℚ) / (n : ℚ)) = invariantX x ∧
      conicV ((m : ℚ) / (n : ℚ)) = invariantY x y ∧
      homogeneousFiber (m : ℚ) (n : ℚ) x = 0 := by
  obtain ⟨t, ht, hU, hV, hroot⟩ :=
    noncuspidal_curve_parameterization x y hx0 hx1 hcurve
  refine ⟨t.num, (t.den : ℤ), ?_, Rat.isCoprime_num_den t,
    ?_, ?_, ?_, ?_⟩
  · exact_mod_cast t.den_pos
  · simpa only [Int.cast_natCast, Rat.num_div_den] using ht
  · simpa only [Int.cast_natCast, Rat.num_div_den] using hU
  · simpa only [Int.cast_natCast, Rat.num_div_den] using hV
  · exact homogeneousFiber_eq_zero_of_clearedFiber t x hroot

/-- The coefficient discriminant of the cleared cubic factors into two
squared quadratic forms. -/
theorem clearedFiber_discriminant (t : ℚ) :
    cubicDiscriminant
        (t ^ 2 - 1)
        (-(t ^ 2 - 6 * t - 3))
        (-2 * t ^ 2 - 6 * t)
        (t ^ 2 - 1) =
      (t ^ 2 + 3) ^ 2 * (7 * t ^ 2 + 6 * t + 3) ^ 2 := by
  simp only [cubicDiscriminant]
  ring

/-- The square root of the fiber discriminant before clearing
denominators factors as displayed. -/
theorem fiber_discriminant_parameter_factorization
    (t : ℚ) (ht : t ^ 2 ≠ 1) :
    conicU t ^ 2 - 3 * conicU t + 9 =
      (t ^ 2 + 3) * (7 * t ^ 2 + 6 * t + 3) /
        (t ^ 2 - 1) ^ 2 := by
  simp only [conicU]
  field_simp [sub_ne_zero.mpr ht]
  ring

/-! ## Eisenstein-coordinate norm identities -/

/-- Multiplication in coordinates `a+bω`, where `ω²+ω+1=0`. -/
def eisensteinMul (z w : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 * w.1 - z.2 * w.2,
    z.1 * w.2 + z.2 * w.1 - z.2 * w.2)

/-- The norm of the Eisenstein coordinate pair `a+bω`. -/
def eisensteinNorm (z : ℤ × ℤ) : ℤ :=
  z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2

/-- The coordinate norm is multiplicative. -/
theorem eisensteinNorm_mul (z w : ℤ × ℤ) :
    eisensteinNorm (eisensteinMul z w) =
      eisensteinNorm z * eisensteinNorm w := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  simp only [eisensteinNorm, eisensteinMul]
  ring

/-- Complex conjugation in coordinates `a+bω`, using
`conj(ω)=ω²=-1-ω`. -/
def eisensteinConj (z : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 - z.2, -z.2)

/-- Multiplication by the conjugate gives the rational integer norm. -/
theorem eisensteinMul_conj (z : ℤ × ℤ) :
    eisensteinMul z (eisensteinConj z) =
      (eisensteinNorm z, 0) := by
  rcases z with ⟨a, b⟩
  simp only [eisensteinMul, eisensteinConj, eisensteinNorm]
  ext <;> simp <;> ring

/-- Conjugation preserves the Eisenstein norm. -/
theorem eisensteinNorm_conj (z : ℤ × ℤ) :
    eisensteinNorm (eisensteinConj z) = eisensteinNorm z := by
  rcases z with ⟨a, b⟩
  simp only [eisensteinNorm, eisensteinConj]
  ring

/-- The Eisenstein prime above `7`, represented by `π=3+ω`. -/
def eisensteinPi : ℤ × ℤ :=
  (3, 1)

/-- The norm of `π=3+ω` is `7`. -/
theorem eisensteinNorm_pi :
    eisensteinNorm eisensteinPi = 7 := by
  norm_num [eisensteinNorm, eisensteinPi]

/-- The conjugate prime is `conj(π)=2-ω`. -/
theorem eisensteinConj_pi :
    eisensteinConj eisensteinPi = (2, -1) := by
  norm_num [eisensteinConj, eisensteinPi]

/-- The coordinate factorization of the rational prime `7` as
`π·conj(π)`. -/
theorem seven_eq_pi_mul_conj :
    eisensteinMul eisensteinPi (eisensteinConj eisensteinPi) =
      (7, 0) := by
  rw [eisensteinMul_conj, eisensteinNorm_pi]

/-- Divisibility by `π` in the coordinate ring. -/
def EisensteinPiDivides (z : ℤ × ℤ) : Prop :=
  ∃ w : ℤ × ℤ, eisensteinMul eisensteinPi w = z

/-- The index-seven lattice cut out by multiplication by `π` has the
single congruence `2a+b ≡ 0 mod 7`. -/
theorem eisensteinPiDivides_iff (a b : ℤ) :
    EisensteinPiDivides (a, b) ↔
      (7 : ℤ) ∣ 2 * a + b := by
  constructor
  · rintro ⟨⟨c, d⟩, h⟩
    have ha : 3 * c - d = a := by
      simpa [eisensteinMul, eisensteinPi] using congrArg Prod.fst h
    have hb : 3 * d + c - d = b := by
      simpa [eisensteinMul, eisensteinPi] using congrArg Prod.snd h
    refine ⟨c, ?_⟩
    nlinarith
  · rintro ⟨c, hc⟩
    refine ⟨(c, 3 * c - a), ?_⟩
    ext
    · simp only [eisensteinMul, eisensteinPi]
      ring
    · simp only [eisensteinMul, eisensteinPi]
      nlinarith

/-- A factor of `π` forces a factor of `7` in the norm. -/
theorem seven_dvd_eisensteinNorm_of_piDivides
    (z : ℤ × ℤ) (hz : EisensteinPiDivides z) :
    (7 : ℤ) ∣ eisensteinNorm z := by
  obtain ⟨w, rfl⟩ := hz
  rw [eisensteinNorm_mul, eisensteinNorm_pi]
  exact ⟨eisensteinNorm w, by ring⟩

/-- The first quadratic factor is an Eisenstein norm after clearing a
rational parameter `t=m/n`. -/
theorem first_parameter_form_is_norm (m n : ℤ) :
    eisensteinNorm (m + n, 2 * n) = m ^ 2 + 3 * n ^ 2 := by
  simp only [eisensteinNorm]
  ring

/-- The second quadratic factor is the norm of
`πm + (1-ω)n`. -/
theorem pi_parameter_form_is_norm (m n : ℤ) :
    eisensteinNorm (3 * m + n, m - n) =
      7 * m ^ 2 + 6 * m * n + 3 * n ^ 2 := by
  simp only [eisensteinNorm]
  ring

/-- Coordinate identity behind
`(3+ω)m + (1-ω)n = (3m+n) + (m-n)ω`. -/
theorem pi_parameter_coordinates (m n : ℤ) :
    eisensteinMul eisensteinPi (m, 0) + (n, -n) =
      (3 * m + n, m - n) := by
  ext
  · simp [eisensteinMul, eisensteinPi]
  · simp [eisensteinMul, eisensteinPi]
    ring

/-- The second norm argument is divisible by `π` exactly when the
denominator parameter is divisible by `7`. -/
theorem piDivides_second_parameter_iff (m n : ℤ) :
    EisensteinPiDivides (3 * m + n, m - n) ↔
      (7 : ℤ) ∣ n := by
  rw [eisensteinPiDivides_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - m, ?_⟩
    nlinarith
  · rintro ⟨k, hk⟩
    refine ⟨m + k, ?_⟩
    nlinarith

/-- The two primitive quadratic norm forms. -/
def firstParameterForm (m n : ℤ) : ℤ :=
  m ^ 2 + 3 * n ^ 2

/-- The norm form associated to the Eisenstein prime above seven. -/
def piParameterForm (m n : ℤ) : ℤ :=
  7 * m ^ 2 + 6 * m * n + 3 * n ^ 2

/-- For integer homogeneous parameters, the two factors in the cubic
discriminant are exactly the two named norm forms. -/
theorem homogeneousFiber_discriminant_integer (m n : ℤ) :
    cubicDiscriminant
        ((m : ℚ) ^ 2 - (n : ℚ) ^ 2)
        (-((m : ℚ) ^ 2 -
          6 * (m : ℚ) * (n : ℚ) - 3 * (n : ℚ) ^ 2))
        (-2 * (m : ℚ) ^ 2 - 6 * (m : ℚ) * (n : ℚ))
        ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) =
      (firstParameterForm m n : ℚ) ^ 2 *
        (piParameterForm m n : ℚ) ^ 2 := by
  simpa [firstParameterForm, piParameterForm] using
    homogeneousFiber_discriminant (m : ℚ) (n : ℚ)

/-- A Bézout-style identity eliminating the denominator parameter. -/
theorem parameter_forms_m_identity (m n : ℤ) :
    (m + n) * firstParameterForm m n +
        (m - n) * piParameterForm m n =
      8 * m ^ 3 := by
  simp only [firstParameterForm, piParameterForm]
  ring

/-- A complementary Bézout-style identity eliminating the numerator
parameter. -/
theorem parameter_forms_n_identity (m n : ℤ) :
    (7 * m + 27 * n) * firstParameterForm m n -
        (m + 3 * n) * piParameterForm m n =
      72 * n ^ 3 := by
  simp only [firstParameterForm, piParameterForm]
  ring

private lemma common_zero_mod_seven :
    ∀ m n : ZMod 7,
      m ^ 2 + 3 * n ^ 2 = 0 →
      7 * m ^ 2 + 6 * m * n + 3 * n ^ 2 = 0 →
      m = 0 ∧ n = 0 := by
  decide

/-- For primitive integer parameters, the two Eisenstein norm forms
cannot both be divisible by the rational prime below `π`. -/
theorem seven_not_common_divisor
    (m n : ℤ) (hcoprime : IsCoprime m n) :
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) := by
  rintro ⟨hfirst, hpi⟩
  have hfirstMod :
      ((m : ZMod 7) ^ 2 + 3 * (n : ZMod 7) ^ 2) = 0 := by
    have hcast :
        ((firstParameterForm m n : ℤ) : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (firstParameterForm m n) 7).2 hfirst
    simpa [firstParameterForm] using hcast
  have hpiMod :
      7 * (m : ZMod 7) ^ 2 +
          6 * (m : ZMod 7) * (n : ZMod 7) +
          3 * (n : ZMod 7) ^ 2 = 0 := by
    have hcast :
        ((piParameterForm m n : ℤ) : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (piParameterForm m n) 7).2 hpi
    simpa [piParameterForm] using hcast
  obtain ⟨hmMod, hnMod⟩ :=
    common_zero_mod_seven (m : ZMod 7) (n : ZMod 7)
      hfirstMod hpiMod
  have hm : (7 : ℤ) ∣ m :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd m 7).mp hmMod
  have hn : (7 : ℤ) ∣ n :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd n 7).mp hnMod
  have hunit : IsUnit (7 : ℤ) :=
    hcoprime.isUnit_of_dvd' hm hn
  norm_num [Int.isUnit_iff] at hunit

/-! ## Rational-root divisibility -/

/-- The integer obtained by clearing the denominator of a rational root
of the homogeneous cyclic cubic. -/
private def rootNumeratorEquation (m n a b : ℤ) : ℤ :=
  (m ^ 2 - n ^ 2) * a ^ 3 -
    (m ^ 2 - 6 * m * n - 3 * n ^ 2) * a ^ 2 * b +
    (-2 * m ^ 2 - 6 * m * n) * a * b ^ 2 +
    (m ^ 2 - n ^ 2) * b ^ 3

private lemma rootNumeratorEquation_eq_zero
    (m n a b : ℤ) (hb : b ≠ 0)
    (hroot :
      homogeneousFiber (m : ℚ) (n : ℚ) ((a : ℚ) / (b : ℚ)) = 0) :
    rootNumeratorEquation m n a b = 0 := by
  simp only [homogeneousFiber] at hroot
  field_simp [Int.cast_ne_zero.mpr hb] at hroot
  have hcast :
      (rootNumeratorEquation m n a b : ℚ) = 0 := by
    simp only [rootNumeratorEquation, Int.cast_add, Int.cast_sub,
      Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_neg]
    linear_combination hroot
  exact_mod_cast hcast

private lemma root_num_dvd_leadingCoefficient
    (m n a b : ℤ) (hab : IsCoprime a b)
    (hroot : rootNumeratorEquation m n a b = 0) :
    a ∣ m ^ 2 - n ^ 2 := by
  have hdiv : a ∣ (m ^ 2 - n ^ 2) * b ^ 3 := by
    refine ⟨
      -(m ^ 2 - n ^ 2) * a ^ 2 +
        (m ^ 2 - 6 * m * n - 3 * n ^ 2) * a * b -
        (-2 * m ^ 2 - 6 * m * n) * b ^ 2,
      ?_⟩
    unfold rootNumeratorEquation at hroot
    linear_combination hroot
  exact hab.pow_right.dvd_of_dvd_mul_right hdiv

private lemma root_den_dvd_leadingCoefficient
    (m n a b : ℤ) (hab : IsCoprime a b)
    (hroot : rootNumeratorEquation m n a b = 0) :
    b ∣ m ^ 2 - n ^ 2 := by
  have hdiv : b ∣ (m ^ 2 - n ^ 2) * a ^ 3 := by
    refine ⟨
      (m ^ 2 - 6 * m * n - 3 * n ^ 2) * a ^ 2 -
        (-2 * m ^ 2 - 6 * m * n) * a * b -
        (m ^ 2 - n ^ 2) * b ^ 2,
      ?_⟩
    unfold rootNumeratorEquation at hroot
    linear_combination hroot
  exact hab.symm.pow_right.dvd_of_dvd_mul_right hdiv

private lemma root_difference_dvd_leadingCoefficient
    (m n a b : ℤ) (hab : IsCoprime a b)
    (hroot : rootNumeratorEquation m n a b = 0) :
    a - b ∣ m ^ 2 - n ^ 2 := by
  have hdifference : IsCoprime (a - b) b := by
    simpa [sub_eq_add_neg, add_comm] using
      (hab.add_mul_left_left (-1 : ℤ))
  have hdiv : a - b ∣ (m ^ 2 - n ^ 2) * b ^ 3 := by
    refine ⟨
      a ^ 2 * m ^ 2 - a ^ 2 * n ^ 2 + 6 * a * b * m * n +
        2 * a * b * n ^ 2 - 2 * b ^ 2 * m ^ 2 +
        2 * b ^ 2 * n ^ 2,
      ?_⟩
    unfold rootNumeratorEquation at hroot
    linear_combination -hroot
  exact hdifference.pow_right.dvd_of_dvd_mul_right hdiv

/-- If a primitive rational number `a/b` is a root of the homogeneous
cyclic cubic, then the three pairwise-coprime cusp factors of its
Möbius orbit divide the leading coefficient together. -/
theorem root_orbit_product_dvd_leadingCoefficient
    (m n a b : ℤ) (hab : IsCoprime a b)
    (hroot :
      homogeneousFiber (m : ℚ) (n : ℚ) ((a : ℚ) / (b : ℚ)) = 0)
    (hb : b ≠ 0) :
    a * b * (a - b) ∣ m ^ 2 - n ^ 2 := by
  have hrootInt :=
    rootNumeratorEquation_eq_zero m n a b hb hroot
  have ha :=
    root_num_dvd_leadingCoefficient m n a b hab hrootInt
  have hbdiv :=
    root_den_dvd_leadingCoefficient m n a b hab hrootInt
  have hdifference :=
    root_difference_dvd_leadingCoefficient m n a b hab hrootInt
  have habDifference : IsCoprime (a * b) (a - b) := by
    have haDifference : IsCoprime a (a - b) := by
      simpa [sub_eq_add_neg, add_comm] using
        (hab.add_mul_right_right (-1 : ℤ)).neg_right
    have hbDifference : IsCoprime b (a - b) := by
      simpa [sub_eq_add_neg] using
        hab.symm.add_mul_right_right (-1 : ℤ)
    exact haDifference.mul_left hbDifference
  exact habDifference.mul_dvd (hab.mul_dvd ha hbdiv) hdifference

private lemma invariantX_discriminant_factorization
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    invariantX x ^ 2 - 3 * invariantX x + 9 =
      (x ^ 2 - x + 1) ^ 3 / (x ^ 2 * (x - 1) ^ 2) := by
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [invariantX]
  field_simp [hx0, hxsub]
  ring

/-- Equating the two presentations of the cyclic-cubic discriminant
gives an integral norm equation for primitive quotient and root
coordinates. -/
theorem parameter_forms_mul_orbitNorm_sq
    (m n a b : ℤ) (hn : n ≠ 0) (hb : b ≠ 0)
    (ha : a ≠ 0) (hab : a ≠ b)
    (ht : ((m : ℚ) / (n : ℚ)) ^ 2 ≠ 1)
    (hU :
      conicU ((m : ℚ) / (n : ℚ)) =
        invariantX ((a : ℚ) / (b : ℚ))) :
    firstParameterForm m n * piParameterForm m n *
        (a * b * (a - b)) ^ 2 =
      (m ^ 2 - n ^ 2) ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 := by
  have hnq : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hx0 : (a : ℚ) / (b : ℚ) ≠ 0 :=
    div_ne_zero (Int.cast_ne_zero.mpr ha) hbq
  have hx1 : (a : ℚ) / (b : ℚ) ≠ 1 := by
    intro hx
    have habq : (a : ℚ) = (b : ℚ) :=
      (div_eq_one_iff_eq hbq).mp hx
    exact hab (by exact_mod_cast habq)
  have hparameterDenominator :
      (m : ℚ) ^ 2 - (n : ℚ) ^ 2 ≠ 0 := by
    intro hzero
    apply ht
    field_simp [hnq]
    linear_combination hzero
  have hrootDenominator : (a : ℚ) - (b : ℚ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hab)
  have hparameter :=
    fiber_discriminant_parameter_factorization
      ((m : ℚ) / (n : ℚ)) ht
  have hroot :=
    invariantX_discriminant_factorization
      ((a : ℚ) / (b : ℚ)) hx0 hx1
  have heq :
      ((((m : ℚ) / (n : ℚ)) ^ 2 + 3) *
          (7 * ((m : ℚ) / (n : ℚ)) ^ 2 +
            6 * ((m : ℚ) / (n : ℚ)) + 3) /
        (((m : ℚ) / (n : ℚ)) ^ 2 - 1) ^ 2) =
        ((((a : ℚ) / (b : ℚ)) ^ 2 -
              (a : ℚ) / (b : ℚ) + 1) ^ 3 /
          (((a : ℚ) / (b : ℚ)) ^ 2 *
            ((a : ℚ) / (b : ℚ) - 1) ^ 2)) := by
    rw [← hparameter, ← hroot, hU]
  field_simp [hnq, hbq, hparameterDenominator,
    hrootDenominator] at heq
  have hcast :
      ((firstParameterForm m n * piParameterForm m n *
          (a * b * (a - b)) ^ 2 : ℤ) : ℚ) =
        (((m ^ 2 - n ^ 2) ^ 2 *
          (a ^ 2 - a * b + b ^ 2) ^ 3 : ℤ) : ℚ) := by
    simp only [firstParameterForm, piParameterForm, Int.cast_mul,
      Int.cast_pow, Int.cast_sub, Int.cast_add, Int.cast_ofNat]
    linear_combination heq
  exact_mod_cast hcast

/-- After dividing by the nonzero product of the three cusp factors,
the discriminant identity becomes a square times the cube of the
Eisenstein orbit norm. -/
theorem exists_root_leadingCoefficient_quotient
    (m n a b : ℤ) (hn : n ≠ 0) (hb : b ≠ 0)
    (ha : a ≠ 0) (hab : a ≠ b)
    (ht : ((m : ℚ) / (n : ℚ)) ^ 2 ≠ 1)
    (hU :
      conicU ((m : ℚ) / (n : ℚ)) =
        invariantX ((a : ℚ) / (b : ℚ)))
    (hdvd : a * b * (a - b) ∣ m ^ 2 - n ^ 2) :
    ∃ k : ℤ,
      m ^ 2 - n ^ 2 = k * (a * b * (a - b)) ∧
      firstParameterForm m n * piParameterForm m n =
        k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 := by
  obtain ⟨k, hk⟩ := hdvd
  have hnorm :=
    parameter_forms_mul_orbitNorm_sq
      m n a b hn hb ha hab ht hU
  have hproduct : a * b * (a - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha hb) (sub_ne_zero.mpr hab)
  refine ⟨k, by simpa [mul_comm] using hk, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hproduct)
  calc
    (a * b * (a - b)) ^ 2 *
          (firstParameterForm m n * piParameterForm m n) =
        firstParameterForm m n * piParameterForm m n *
          (a * b * (a - b)) ^ 2 := by ring
    _ = (m ^ 2 - n ^ 2) ^ 2 *
          (a ^ 2 - a * b + b ^ 2) ^ 3 := hnorm
    _ = (a * b * (a - b)) ^ 2 *
          (k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3) := by
      rw [hk]
      ring

/-- Once the quotient parameter and a primitive rational root are both
cleared, equality of the two invariant presentations determines the other
two coefficients of the split cyclic cubic. -/
theorem root_split_coefficient_identities
    (m n a b k : ℤ) (hn : n ≠ 0) (hb : b ≠ 0)
    (ha : a ≠ 0) (hab : a ≠ b)
    (ht : ((m : ℚ) / (n : ℚ)) ^ 2 ≠ 1)
    (hU :
      conicU ((m : ℚ) / (n : ℚ)) =
        invariantX ((a : ℚ) / (b : ℚ)))
    (hk : m ^ 2 - n ^ 2 = k * (a * b * (a - b))) :
    m ^ 2 - 6 * m * n - 3 * n ^ 2 =
        k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) ∧
      -2 * m ^ 2 - 6 * m * n =
        k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3) := by
  have hnq : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have habq : (a : ℚ) - (b : ℚ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab
  have hparameterDenominator :
      (m : ℚ) ^ 2 - (n : ℚ) ^ 2 ≠ 0 := by
    intro hzero
    apply ht
    field_simp [hnq]
    linear_combination hzero
  have hrootProduct : a * b * (a - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha hb) (sub_ne_zero.mpr hab)
  have hcross :
      (m ^ 2 - 6 * m * n - 3 * n ^ 2) *
          (a * b * (a - b)) =
        (m ^ 2 - n ^ 2) *
          (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) := by
    have hU' := hU
    simp only [conicU, invariantX] at hU'
    field_simp [hnq, hbq, habq, hparameterDenominator] at hU'
    have hcrossQ :
        (((m ^ 2 - 6 * m * n - 3 * n ^ 2) *
            (a * b * (a - b)) : ℤ) : ℚ) =
          (((m ^ 2 - n ^ 2) *
            (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) : ℤ) : ℚ) := by
      push_cast
      linear_combination hU'
    exact_mod_cast hcrossQ
  have hfirst :
      m ^ 2 - 6 * m * n - 3 * n ^ 2 =
        k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) := by
    apply mul_right_cancel₀ hrootProduct
    calc
      (m ^ 2 - 6 * m * n - 3 * n ^ 2) *
            (a * b * (a - b)) =
          (m ^ 2 - n ^ 2) *
            (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) := hcross
      _ = (k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3)) *
            (a * b * (a - b)) := by rw [hk]; ring
  exact ⟨hfirst, by
    linear_combination hfirst - 3 * hk
    ⟩

private lemma primitive_split_mod_two :
    ∀ m n a b k : ZMod 2,
      (m ≠ 0 ∨ n ≠ 0) →
      (a ≠ 0 ∨ b ≠ 0) →
      m ^ 2 - n ^ 2 = k * (a * b * (a - b)) →
      m ^ 2 - 6 * m * n - 3 * n ^ 2 =
        k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) →
      -2 * m ^ 2 - 6 * m * n =
        k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3) →
      m = 1 ∧ n = 1 ∧ k = 0 := by
  decide

/-- A primitive split fiber can only occur in the odd-odd parameter
class.  Opposite parity would give the rootless cubic
`z³ + z² + 1` modulo two. -/
theorem split_parameters_odd
    (m n a b k : ℤ)
    (hmn : IsCoprime m n) (hab : IsCoprime a b)
    (hk : m ^ 2 - n ^ 2 = k * (a * b * (a - b)))
    (htrace :
      m ^ 2 - 6 * m * n - 3 * n ^ 2 =
        k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3))
    (hpair :
      -2 * m ^ 2 - 6 * m * n =
        k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3)) :
    Odd m ∧ Odd n := by
  have hmnMod :
      IsCoprime (m : ZMod 2) (n : ZMod 2) :=
    hmn.intCast
  have habMod :
      IsCoprime (a : ZMod 2) (b : ZMod 2) :=
    hab.intCast
  have hkMod :
      (m : ZMod 2) ^ 2 - (n : ZMod 2) ^ 2 =
        (k : ZMod 2) *
          ((a : ZMod 2) * (b : ZMod 2) *
            ((a : ZMod 2) - (b : ZMod 2))) := by
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul,
      Int.cast_ofNat] using
      congrArg (fun z : ℤ ↦ (z : ZMod 2)) hk
  have htraceMod :
      (m : ZMod 2) ^ 2 - 6 * (m : ZMod 2) * (n : ZMod 2) -
          3 * (n : ZMod 2) ^ 2 =
        (k : ZMod 2) *
          ((a : ZMod 2) ^ 3 -
            3 * (a : ZMod 2) * (b : ZMod 2) ^ 2 +
            (b : ZMod 2) ^ 3) := by
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul,
      Int.cast_add, Int.cast_ofNat] using
      congrArg (fun z : ℤ ↦ (z : ZMod 2)) htrace
  have hpairMod :
      -2 * (m : ZMod 2) ^ 2 -
          6 * (m : ZMod 2) * (n : ZMod 2) =
        (k : ZMod 2) *
          ((a : ZMod 2) ^ 3 -
            3 * (a : ZMod 2) ^ 2 * (b : ZMod 2) +
            (b : ZMod 2) ^ 3) := by
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul,
      Int.cast_add, Int.cast_ofNat, Int.cast_neg] using
      congrArg (fun z : ℤ ↦ (z : ZMod 2)) hpair
  obtain ⟨hmMod, hnMod, -⟩ :=
    primitive_split_mod_two
      (m : ZMod 2) (n : ZMod 2) (a : ZMod 2) (b : ZMod 2)
      (k : ZMod 2) hmnMod.ne_zero_or_ne_zero
      habMod.ne_zero_or_ne_zero hkMod htraceMod hpairMod
  have hmNotEven : ¬Even m := by
    rw [even_iff_two_dvd]
    intro hm
    have hmZero : (m : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 2).2 hm
    rw [hmMod] at hmZero
    norm_num at hmZero
  have hnNotEven : ¬Even n := by
    rw [even_iff_two_dvd]
    intro hn
    have hnZero : (n : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).2 hn
    rw [hnMod] at hnZero
    norm_num at hnZero
  exact ⟨Int.not_even_iff_odd.mp hmNotEven,
    Int.not_even_iff_odd.mp hnNotEven⟩

/-- The two independent split-fiber coefficients have resultant sixteen
as binary quadratic forms in the primitive conic parameters. -/
theorem split_parameter_resultant_identities (m n : ℤ) :
    (15 * m + 9 * n) * (m ^ 2 - n ^ 2) +
        (m - 3 * n) * (m ^ 2 - 6 * m * n - 3 * n ^ 2) =
      16 * m ^ 3 ∧
    (3 * m - 19 * n) * (m ^ 2 - n ^ 2) +
        (-3 * m + n) * (m ^ 2 - 6 * m * n - 3 * n ^ 2) =
      16 * n ^ 3 := by
  constructor <;> ring

private lemma primitive_trace_mod_two :
    ∀ a b : ZMod 2,
      (a ≠ 0 ∨ b ≠ 0) →
      a ^ 3 - 3 * a * b ^ 2 + b ^ 3 = 1 := by
  decide

private lemma primitive_root_trace_odd
    (a b : ℤ) (hab : IsCoprime a b) :
    Odd (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) := by
  have habMod :
      IsCoprime (a : ZMod 2) (b : ZMod 2) :=
    hab.intCast
  have htraceMod :
      ((a ^ 3 - 3 * a * b ^ 2 + b ^ 3 : ℤ) : ZMod 2) = 1 := by
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul,
      Int.cast_add, Int.cast_ofNat] using
      primitive_trace_mod_two (a : ZMod 2) (b : ZMod 2)
        habMod.ne_zero_or_ne_zero
  apply Int.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro htwo
  have hzero :
      ((a ^ 3 - 3 * a * b ^ 2 + b ^ 3 : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) 2).2 htwo
  rw [htraceMod] at hzero
  norm_num at hzero

private lemma odd_traceCoefficient_ne_zero_mod_sixteen :
    ∀ m n : ZMod 16,
      (ZMod.cast m : ZMod 2) = 1 →
      (ZMod.cast n : ZMod 2) = 1 →
      m ^ 2 - 6 * m * n - 3 * n ^ 2 ≠ 0 := by
  decide

private lemma odd_intCast_mod_two_eq_one
    (z : ℤ) (hz : Odd z) : (z : ZMod 2) = 1 := by
  obtain ⟨r, rfl⟩ := hz
  push_cast
  simp [show (2 : ZMod 2) = 0 by decide]

private lemma four_dvd_traceCoefficient_of_odd
    (m n : ℤ) (hm : Odd m) (hn : Odd n) :
    (4 : ℤ) ∣ m ^ 2 - 6 * m * n - 3 * n ^ 2 := by
  obtain ⟨r, hr⟩ := hm
  obtain ⟨s, hs⟩ := hn
  refine ⟨r ^ 2 - 6 * r * s - 2 * r - 3 * s ^ 2 - 6 * s - 2, ?_⟩
  rw [hr, hs]
  ring

private lemma sixteen_not_dvd_traceCoefficient_of_odd
    (m n : ℤ) (hm : Odd m) (hn : Odd n) :
    ¬(16 : ℤ) ∣ m ^ 2 - 6 * m * n - 3 * n ^ 2 := by
  have hmReduce :
      (ZMod.cast (m : ZMod 16) : ZMod 2) = 1 := by
    rw [ZMod.cast_intCast (R := ZMod 2)
      (by norm_num : 2 ∣ 16) m]
    exact odd_intCast_mod_two_eq_one m hm
  have hnReduce :
      (ZMod.cast (n : ZMod 16) : ZMod 2) = 1 := by
    rw [ZMod.cast_intCast (R := ZMod 2)
      (by norm_num : 2 ∣ 16) n]
    exact odd_intCast_mod_two_eq_one n hn
  have hnonzero :
      (m : ZMod 16) ^ 2 -
          6 * (m : ZMod 16) * (n : ZMod 16) -
          3 * (n : ZMod 16) ^ 2 ≠ 0 :=
    odd_traceCoefficient_ne_zero_mod_sixteen
      (m : ZMod 16) (n : ZMod 16) hmReduce hnReduce
  intro hdvd
  apply hnonzero
  have hcast :
      ((m ^ 2 - 6 * m * n - 3 * n ^ 2 : ℤ) : ZMod 16) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (m ^ 2 - 6 * m * n - 3 * n ^ 2) 16).2 hdvd
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul,
    Int.cast_ofNat] using hcast

/-- Primitivity and the split coefficient identities make the apparent
quotient `k` a divisor of sixteen with exact two-adic order two or three.
In particular, the remaining arithmetic boundary has only four possible
signed values for `k`. -/
theorem split_quotient_divisibility
    (m n a b k : ℤ)
    (hmn : IsCoprime m n) (hab : IsCoprime a b)
    (hk : m ^ 2 - n ^ 2 = k * (a * b * (a - b)))
    (htrace :
      m ^ 2 - 6 * m * n - 3 * n ^ 2 =
        k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3))
    (hpair :
      -2 * m ^ 2 - 6 * m * n =
        k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3)) :
    Odd m ∧ Odd n ∧
      (4 : ℤ) ∣ k ∧ ¬(16 : ℤ) ∣ k ∧ k ∣ 16 := by
  obtain ⟨hmOdd, hnOdd⟩ :=
    split_parameters_odd m n a b k hmn hab hk htrace hpair
  let trace := a ^ 3 - 3 * a * b ^ 2 + b ^ 3
  have htraceOdd : Odd trace :=
    primitive_root_trace_odd a b hab
  have hDfour :
      (4 : ℤ) ∣ m ^ 2 - 6 * m * n - 3 * n ^ 2 :=
    four_dvd_traceCoefficient_of_odd m n hmOdd hnOdd
  have hDnotSixteen :
      ¬(16 : ℤ) ∣ m ^ 2 - 6 * m * n - 3 * n ^ 2 :=
    sixteen_not_dvd_traceCoefficient_of_odd m n hmOdd hnOdd
  have htwoCoprime : IsCoprime (2 : ℤ) trace := by
    obtain ⟨r, hr⟩ := htraceOdd
    exact ⟨-r, 1, by simp only [one_mul]; rw [hr]; ring⟩
  have hfourCoprime : IsCoprime (4 : ℤ) trace := by
    simpa using htwoCoprime.pow_left (m := 2)
  have hkFour : (4 : ℤ) ∣ k := by
    apply hfourCoprime.dvd_of_dvd_mul_right
    rw [← htrace]
    exact hDfour
  have hkNotSixteen : ¬(16 : ℤ) ∣ k := by
    intro hkSixteen
    apply hDnotSixteen
    rw [htrace]
    exact hkSixteen.mul_right trace
  have hkA : k ∣ m ^ 2 - n ^ 2 := ⟨a * b * (a - b), hk⟩
  have hkD :
      k ∣ m ^ 2 - 6 * m * n - 3 * n ^ 2 :=
    ⟨trace, htrace⟩
  obtain ⟨hmResultant, hnResultant⟩ :=
    split_parameter_resultant_identities m n
  have hkMCube : k ∣ 16 * m ^ 3 := by
    rw [← hmResultant]
    exact dvd_add (hkA.mul_left (15 * m + 9 * n))
      (hkD.mul_left (m - 3 * n))
  have hkNCube : k ∣ 16 * n ^ 3 := by
    rw [← hnResultant]
    exact dvd_add (hkA.mul_left (3 * m - 19 * n))
      (hkD.mul_left (-3 * m + n))
  have hmnCubes : IsCoprime (m ^ 3) (n ^ 3) :=
    hmn.pow_left.pow_right
  obtain ⟨u, v, huv⟩ := hmnCubes
  have hkSixteen : k ∣ 16 := by
    have hsum :
        k ∣ u * (16 * m ^ 3) + v * (16 * n ^ 3) :=
      dvd_add (hkMCube.mul_left u) (hkNCube.mul_left v)
    have hsumEq :
        u * (16 * m ^ 3) + v * (16 * n ^ 3) = 16 := by
      calc
        u * (16 * m ^ 3) + v * (16 * n ^ 3) =
            16 * (u * m ^ 3 + v * n ^ 3) := by ring
        _ = 16 := by rw [huv]; ring
    rw [hsumEq] at hsum
    exact hsum
  exact ⟨hmOdd, hnOdd, hkFour, hkNotSixteen, hkSixteen⟩

/-- The quotient in a primitive split cyclic cubic is one of the four
signed integers of two-adic order two or three. -/
theorem split_quotient_eq_neg_eight_or_neg_four_or_four_or_eight
    (m n a b k : ℤ)
    (hmn : IsCoprime m n) (hab : IsCoprime a b)
    (hk : m ^ 2 - n ^ 2 = k * (a * b * (a - b)))
    (htrace :
      m ^ 2 - 6 * m * n - 3 * n ^ 2 =
        k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3))
    (hpair :
      -2 * m ^ 2 - 6 * m * n =
        k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3)) :
    k = -8 ∨ k = -4 ∨ k = 4 ∨ k = 8 := by
  obtain ⟨-, -, hkFour, hkNotSixteen, hkSixteen⟩ :=
    split_quotient_divisibility
      m n a b k hmn hab hk htrace hpair
  have hkNe : k ≠ 0 := by
    intro hkZero
    subst k
    exact hkNotSixteen (dvd_zero 16)
  have hkAbsFour : 4 ∣ k.natAbs :=
    Int.natCast_dvd.mp hkFour
  have hkAbsSixteen : k.natAbs ∣ 16 :=
    Int.dvd_natCast.mp hkSixteen
  have hkAbsPos : 0 < k.natAbs :=
    Int.natAbs_pos.mpr hkNe
  have hkAbsLower : 4 ≤ k.natAbs :=
    Nat.le_of_dvd hkAbsPos hkAbsFour
  have hkAbsUpper : k.natAbs ≤ 16 :=
    Nat.le_of_dvd (by norm_num) hkAbsSixteen
  have hkAbsNotSixteen : k.natAbs ≠ 16 := by
    intro hkAbs
    apply hkNotSixteen
    apply Int.natCast_dvd.mpr
    rw [hkAbs]
  have hkAbs : k.natAbs = 4 ∨ k.natAbs = 8 := by
    interval_cases h : k.natAbs
    all_goals norm_num at *
  obtain hkAbs | hkAbs := hkAbs
  · obtain hkPos | hkNeg := Int.natAbs_eq k
    · right; right; left
      omega
    · right; left
      omega
  · obtain hkPos | hkNeg := Int.natAbs_eq k
    · right; right; right
      omega
    · left
      omega

/-- The complete elementary descent package obtained here from a
noncuspidal rational point.  Besides primitive quotient and root
coordinates, it supplies the exact quotient of the cubic's leading
coefficient by the three cusp factors and the resulting square-times-cube
Eisenstein norm equation. -/
theorem noncuspidal_curve_primitive_descent_data
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    ∃ m n a b k : ℤ,
      0 < n ∧
      0 < b ∧
      IsCoprime m n ∧
      IsCoprime a b ∧
      (a : ℚ) / (b : ℚ) = x ∧
      a ≠ 0 ∧
      a ≠ b ∧
      ((m : ℚ) / (n : ℚ)) ^ 2 ≠ 1 ∧
      conicU ((m : ℚ) / (n : ℚ)) =
        invariantX ((a : ℚ) / (b : ℚ)) ∧
      conicV ((m : ℚ) / (n : ℚ)) = invariantY x y ∧
      homogeneousFiber (m : ℚ) (n : ℚ)
          ((a : ℚ) / (b : ℚ)) = 0 ∧
      m ^ 2 - n ^ 2 = k * (a * b * (a - b)) ∧
      firstParameterForm m n * piParameterForm m n =
        k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 ∧
      ¬((7 : ℤ) ∣ firstParameterForm m n ∧
        (7 : ℤ) ∣ piParameterForm m n) := by
  obtain ⟨m, n, hn, hcoprime, ht, hU, hV, hroot⟩ :=
    noncuspidal_curve_primitive_parameterization
      x y hx0 hx1 hcurve
  let a : ℤ := x.num
  let b : ℤ := x.den
  have hbpos : 0 < b := by
    simpa [b] using (show (0 : ℤ) < (x.den : ℤ) by
      exact_mod_cast x.den_pos)
  have hb : b ≠ 0 := ne_of_gt hbpos
  have habCoprime : IsCoprime a b := by
    simpa [a, b] using Rat.isCoprime_num_den x
  have hxrepr : (a : ℚ) / (b : ℚ) = x := by
    simpa [a, b] using Rat.num_div_den x
  have ha : a ≠ 0 := by
    simpa [a] using (Rat.num_ne_zero.mpr hx0)
  have hab : a ≠ b := by
    intro heq
    apply hx1
    rw [← hxrepr, heq]
    exact div_self (Int.cast_ne_zero.mpr hb)
  have hUab :
      conicU ((m : ℚ) / (n : ℚ)) =
        invariantX ((a : ℚ) / (b : ℚ)) := by
    rw [hxrepr]
    exact hU
  have hrootab :
      homogeneousFiber (m : ℚ) (n : ℚ)
          ((a : ℚ) / (b : ℚ)) = 0 := by
    rw [hxrepr]
    exact hroot
  have hdvd :=
    root_orbit_product_dvd_leadingCoefficient
      m n a b habCoprime hrootab hb
  obtain ⟨k, hk, hnorm⟩ :=
    exists_root_leadingCoefficient_quotient
      m n a b (ne_of_gt hn) hb ha hab ht hUab hdvd
  exact ⟨m, n, a, b, k, hn, hbpos, hcoprime, habCoprime,
    hxrepr, ha, hab, ht, hUab, hV, hrootab, hk, hnorm,
    seven_not_common_divisor m n hcoprime⟩

/-- The remaining arithmetic statement after the checked quotient and
rational-root descent.  It rules out primitive integral parameters for which
the cyclic cubic has a rational root and satisfies the resulting
square-times-cube norm equation.

This predicate is deliberately narrower than the original rational-point
classification: all coordinate changes, denominator conditions, and norm
identities needed to reach it are proved above. -/
def PrimitiveCyclicCubicObstruction : Prop :=
  ∀ m n a b k : ℤ,
    0 < n →
    0 < b →
    IsCoprime m n →
    IsCoprime a b →
    a ≠ 0 →
    a ≠ b →
    ((m : ℚ) / (n : ℚ)) ^ 2 ≠ 1 →
    conicU ((m : ℚ) / (n : ℚ)) =
      invariantX ((a : ℚ) / (b : ℚ)) →
    homogeneousFiber (m : ℚ) (n : ℚ)
        ((a : ℚ) / (b : ℚ)) = 0 →
    m ^ 2 - n ^ 2 = k * (a * b * (a - b)) →
    firstParameterForm m n * piParameterForm m n =
      k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 →
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) →
    False

/-- The finite integral boundary left after comparing all three
coefficients of the split cyclic cubic.  The quotient is restricted to
`-8`, `-4`, `4`, or `8`; no rational functions or denominator conditions
remain in the statement. -/
def FiniteSplitCyclicCubicObstruction : Prop :=
  ∀ m n a b k : ℤ,
    0 < n →
    0 < b →
    IsCoprime m n →
    IsCoprime a b →
    a ≠ 0 →
    a ≠ b →
    Odd m →
    Odd n →
    m ^ 2 - n ^ 2 = k * (a * b * (a - b)) →
    m ^ 2 - 6 * m * n - 3 * n ^ 2 =
      k * (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) →
    -2 * m ^ 2 - 6 * m * n =
      k * (a ^ 3 - 3 * a ^ 2 * b + b ^ 3) →
    (k = -8 ∨ k = -4 ∨ k = 4 ∨ k = 8) →
    firstParameterForm m n * piParameterForm m n =
      k ^ 2 * (a ^ 2 - a * b + b ^ 2) ^ 3 →
    ¬((7 : ℤ) ∣ firstParameterForm m n ∧
      (7 : ℤ) ∣ piParameterForm m n) →
    False

/-- The finite split-coefficient boundary implies the earlier primitive
rational-root obstruction. -/
theorem primitiveCyclicCubicObstruction_of_finiteSplit
    (hfinite : FiniteSplitCyclicCubicObstruction) :
    PrimitiveCyclicCubicObstruction := by
  intro m n a b k hn hb hmn hab ha habne ht hU _hroot hk hnorm
    hseven
  obtain ⟨htrace, hpair⟩ :=
    root_split_coefficient_identities m n a b k
      (ne_of_gt hn) (ne_of_gt hb) ha habne ht hU hk
  obtain ⟨hmOdd, hnOdd⟩ :=
    split_parameters_odd m n a b k hmn hab hk htrace hpair
  have hkCases :=
    split_quotient_eq_neg_eight_or_neg_four_or_four_or_eight
      m n a b k hmn hab hk htrace hpair
  exact hfinite m n a b k hn hb hmn hab ha habne hmOdd hnOdd hk
    htrace hpair hkCases hnorm hseven

/-- The primitive cyclic-cubic obstruction consumes the complete descent
package and rules out a noncuspidal rational point on the `X₁(18)` model. -/
theorem no_noncuspidal_point_of_primitiveCyclicCubicObstruction
    (hobs : PrimitiveCyclicCubicObstruction)
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False := by
  obtain ⟨m, n, a, b, k, hn, hb, hmn, hab, _hx,
    ha, habne, ht, hU, _hV, hroot, hk, hnorm, hseven⟩ :=
    noncuspidal_curve_primitive_descent_data
      x y hx0 hx1 hcurve
  exact hobs m n a b k hn hb hmn hab ha habne ht hU hroot hk
    hnorm hseven

/-- A proof of the explicit primitive cyclic-cubic obstruction excludes
exact rational order eighteen through the already checked Tate-normal-form
and genus-two reduction. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_primitiveCyclicCubicObstruction
    (hobs : PrimitiveCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 := by
  apply
    MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint
      E Q
  intro x y hx0 hx1 hcurve
  exact no_noncuspidal_point_of_primitiveCyclicCubicObstruction
    hobs x y hx0 hx1 hcurve

/-- The four-case integral split obstruction excludes exact rational
order eighteen through the checked primitive descent. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_finiteSplitCyclicCubicObstruction
    (hfinite : FiniteSplitCyclicCubicObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_primitiveCyclicCubicObstruction
    (primitiveCyclicCubicObstruction_of_finiteSplit hfinite) E Q

end MazurTorsion.XOneEighteenDescent
