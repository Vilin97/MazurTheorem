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

These are algebraic and local prerequisites for the classical
`π = 3+ω` descent.  They do not construct the induced endomorphism of the
Jacobian, prove `π`-surjectivity on its Mordell--Weil group, determine its
torsion, or classify rational points.
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
`ω̄=ω²=-1-ω`. -/
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

/-- The conjugate prime is `π̄=2-ω`. -/
theorem eisensteinConj_pi :
    eisensteinConj eisensteinPi = (2, -1) := by
  norm_num [eisensteinConj, eisensteinPi]

/-- The coordinate factorization of the rational prime `7` as
`ππ̄`. -/
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

/-- The complete elementary descent package obtained here from a
noncuspidal rational point: primitive homogeneous parameters, the
homogeneous cubic equation, and the local exclusion of a simultaneous
factor of `7` in its two Eisenstein norm factors. -/
theorem noncuspidal_curve_primitive_descent_data
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
      homogeneousFiber (m : ℚ) (n : ℚ) x = 0 ∧
      ¬((7 : ℤ) ∣ firstParameterForm m n ∧
        (7 : ℤ) ∣ piParameterForm m n) := by
  obtain ⟨m, n, hn, hcoprime, ht, hU, hV, hroot⟩ :=
    noncuspidal_curve_primitive_parameterization
      x y hx0 hx1 hcurve
  exact ⟨m, n, hn, hcoprime, ht, hU, hV, hroot,
    seven_not_common_divisor m n hcoprime⟩

end MazurTorsion.XOneEighteenDescent
