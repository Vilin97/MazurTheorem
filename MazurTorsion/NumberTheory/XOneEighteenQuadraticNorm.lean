/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenCubeCorrespondence

/-!
# A quadratic norm factorization for the `X₁(18)` descent

The anti-diagonal quotient of the surviving cubic correspondence has the
genus-two model

`z² = 33w⁶ + 18w⁵ + 15w⁴ - 20w³ + 15w² + 2w + 1`.

Its sextic admits a useful factorization over `ℚ(√-2)`.  In homogeneous
coordinates, put

`A = r³ + 9r²s - rs² - s³`,
`B = -4r(r²-s²)`.

We prove the exact identity `A² + 2B² = F`, where `F` is the homogeneous
sextic.  More strongly, for coprime `r,s` the common divisor of `A` and `B`
divides eight.  Thus after removing the forced parity factor the two
conjugate factors are coprime away from the ramified prime above two.  These
are unconditional inputs to the fixed imaginary-quadratic descent, not a
rational-point classification.
-/

namespace MazurTorsion.XOneEighteenDescent

open MazurTorsion.XOneEighteenFiniteField

/-- The sextic on the anti-diagonal order-three quotient. -/
def antiDiagonalSextic (w : ℚ) : ℚ :=
  33 * w ^ 6 + 18 * w ^ 5 + 15 * w ^ 4 - 20 * w ^ 3 +
    15 * w ^ 2 + 2 * w + 1

/-- The degree-six homogeneous form attached to `antiDiagonalSextic`. -/
def antiDiagonalSexticHom (r s : ℤ) : ℤ :=
  33 * r ^ 6 + 18 * r ^ 5 * s + 15 * r ^ 4 * s ^ 2 -
    20 * r ^ 3 * s ^ 3 + 15 * r ^ 2 * s ^ 4 +
    2 * r * s ^ 5 + s ^ 6

/-- The real coefficient in the split quadratic norm. -/
def antiDiagonalNormReal (r s : ℤ) : ℤ :=
  r ^ 3 + 9 * r ^ 2 * s - r * s ^ 2 - s ^ 3

/-- The `√-2` coefficient in the split quadratic norm. -/
def antiDiagonalNormSqrtNegTwo (r s : ℤ) : ℤ :=
  -4 * r * (r ^ 2 - s ^ 2)

/-! ## The anti-diagonal quotient map -/

/-- The denominator of the anti-diagonal invariant on the cubic
correspondence. -/
def antiDiagonalDen (p q : ℚ) : ℚ :=
  2 * p * q - p - q - 1

/-- The anti-diagonal quotient coordinate. -/
def antiDiagonalW (p q : ℚ) : ℚ :=
  -(p + q - 1) / antiDiagonalDen p q

/-- The quadratic coefficient of the quotient equation. -/
def antiDiagonalQuadA (w : ℚ) : ℚ :=
  -4 * w ^ 3 + 4 * w

/-- The linear coefficient of the quotient equation. -/
def antiDiagonalQuadB (w : ℚ) : ℚ :=
  21 * w ^ 3 - 27 * w ^ 2 - 21 * w + 3

/-- The constant coefficient of the quotient equation. -/
def antiDiagonalQuadC (w : ℚ) : ℚ :=
  -9 * w ^ 3 + 81 * w ^ 2 + 9 * w - 9

/-- The square-root coordinate obtained from the discriminant of the
quadratic quotient equation. -/
def antiDiagonalZ (p q : ℚ) : ℚ :=
  let w := antiDiagonalW p q
  (2 * antiDiagonalQuadA w * invariantX q + antiDiagonalQuadB w) / 3

/-- The exceptional polynomial forced by a zero quotient denominator. -/
def antiDiagonalExceptionalPolynomial (q : ℚ) : ℚ :=
  4 * q ^ 6 - 21 * q ^ 5 + 6 * q ^ 4 + 53 * q ^ 3 -
    39 * q ^ 2 - 3 * q + 4

/-- The homogeneous exceptional polynomial. -/
def antiDiagonalExceptionalPolynomialHom (m n : ℤ) : ℤ :=
  4 * m ^ 6 - 21 * m ^ 5 * n + 6 * m ^ 4 * n ^ 2 +
    53 * m ^ 3 * n ^ 3 - 39 * m ^ 2 * n ^ 4 -
    3 * m * n ^ 5 + 4 * n ^ 6

private theorem antiDiagonalExceptionalPolynomialHom_dehomogenize
    (m n : ℤ) (hn : n ≠ 0) :
    ((antiDiagonalExceptionalPolynomialHom m n : ℤ) : ℚ) =
      (n : ℚ) ^ 6 *
        antiDiagonalExceptionalPolynomial ((m : ℚ) / (n : ℚ)) := by
  simp only [antiDiagonalExceptionalPolynomialHom,
    antiDiagonalExceptionalPolynomial]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnQ]
  push_cast
  ring

private theorem antiDiagonalExceptionalPolynomialHom_mod_five
    (m n : ZMod 5) (hprimitive : m ≠ 0 ∨ n ≠ 0) :
    4 * m ^ 6 - 21 * m ^ 5 * n + 6 * m ^ 4 * n ^ 2 +
        53 * m ^ 3 * n ^ 3 - 39 * m ^ 2 * n ^ 4 -
      3 * m * n ^ 5 + 4 * n ^ 6 ≠ 0 := by
  revert m n
  decide

/-- The exceptional quotient-denominator polynomial has no rational root;
the certificate is complete projective enumeration modulo five. -/
theorem antiDiagonalExceptionalPolynomial_ne_zero (q : ℚ) :
    antiDiagonalExceptionalPolynomial q ≠ 0 := by
  intro hroot
  let m : ℤ := q.num
  let n : ℤ := q.den
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast q.den_ne_zero
  have hq : q = (m : ℚ) / (n : ℚ) := by
    simpa only [m, n, Int.cast_natCast] using (Rat.num_div_den q).symm
  have hzeroQ :
      ((antiDiagonalExceptionalPolynomialHom m n : ℤ) : ℚ) = 0 := by
    rw [antiDiagonalExceptionalPolynomialHom_dehomogenize m n hn,
      ← hq, hroot, mul_zero]
  have hzero : antiDiagonalExceptionalPolynomialHom m n = 0 := by
    exact_mod_cast hzeroQ
  have hmn : IsCoprime m n := by
    simpa only [m, n] using Rat.isCoprime_num_den q
  have hprimitive : (m : ZMod 5) ≠ 0 ∨ (n : ZMod 5) ≠ 0 := by
    by_contra h
    push Not at h
    have hm : (5 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 5).mp h.1
    have hnFive : (5 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mp h.2
    have hunit : IsUnit (5 : ℤ) := hmn.isRelPrime hm hnFive
    exact (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 5)).not_unit
      hunit
  have hnonzero := antiDiagonalExceptionalPolynomialHom_mod_five
    (m : ZMod 5) (n : ZMod 5) hprimitive
  apply hnonzero
  have hcast := congrArg (fun z : ℤ => (z : ZMod 5)) hzero
  norm_num [antiDiagonalExceptionalPolynomialHom] at hcast ⊢
  exact hcast

private theorem invariantX_div
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    invariantX (a / b) =
      (a ^ 3 - 3 * a * b ^ 2 + b ^ 3) /
        (a * b * (a - b)) := by
  simp only [invariantX]
  have habSub : a - b ≠ 0 := sub_ne_zero.mpr hab
  field_simp [ha, hb, habSub]

/-- The exceptional denominator cannot vanish on a noncuspidal rational
point of the cubic correspondence. -/
theorem antiDiagonalDen_ne_zero_of_invariantX_relation
    (p q : ℚ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hrelation : invariantX p = 2 * invariantX q - 6) :
    antiDiagonalDen p q ≠ 0 := by
  intro hden
  have hdenRaw : 2 * p * q - p - q - 1 = 0 := by
    simpa only [antiDiagonalDen] using hden
  have htwoQ : 2 * q - 1 ≠ 0 := by
    intro hzero
    have hqHalf : q = 1 / 2 := by linarith
    rw [hqHalf] at hdenRaw
    ring_nf at hdenRaw
    norm_num at hdenRaw
  have hqNegOne : q + 1 ≠ 0 := by
    intro hzero
    have hqValue : q = -1 := by linarith
    rw [hqValue] at hdenRaw
    have : p = 0 := by linarith
    exact hp0 this
  have hqTwo : q - 2 ≠ 0 := by
    intro hzero
    have hqValue : q = 2 := by linarith
    rw [hqValue] at hdenRaw
    have : p = 1 := by linarith
    exact hp1 this
  have hpFormula : p = (q + 1) / (2 * q - 1) := by
    apply (eq_div_iff htwoQ).2
    linear_combination hdenRaw
  have hqSub : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hqPlus : q + 1 ≠ 0 := hqNegOne
  have hnumDen : q + 1 ≠ 2 * q - 1 := by
    intro h
    apply hqTwo
    linarith
  have hquad : -2 + q * 5 - q ^ 2 * 2 ≠ 0 := by
    rw [show -2 + q * 5 - q ^ 2 * 2 =
      -(2 * q - 1) * (q - 2) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr htwoQ) hqTwo
  have hpoly : antiDiagonalExceptionalPolynomial q = 0 := by
    rw [hpFormula] at hrelation
    rw [invariantX_div (q + 1) (2 * q - 1) hqPlus htwoQ hnumDen]
      at hrelation
    simp only [invariantX] at hrelation
    field_simp [hq0, hqSub, htwoQ, hqNegOne, hqTwo] at hrelation
    have hrelationMul := congrArg
      (fun z : ℚ => (-2 + q * 5 - q ^ 2 * 2) * z) hrelation
    field_simp [hquad] at hrelationMul
    simp only [antiDiagonalExceptionalPolynomial]
    have hproduct :
        (q - 2) * (2 * q - 1) *
          (4 * q ^ 6 - 21 * q ^ 5 + 6 * q ^ 4 + 53 * q ^ 3 -
            39 * q ^ 2 - 3 * q + 4) = 0 := by
      linear_combination -hrelationMul
    exact (mul_eq_zero.mp hproduct).resolve_left
      (mul_ne_zero hqTwo htwoQ)
  exact antiDiagonalExceptionalPolynomial_ne_zero q hpoly

/-- The discriminant of the quotient quadratic is nine times the
anti-diagonal sextic. -/
theorem antiDiagonal_discriminant_identity (w : ℚ) :
    antiDiagonalQuadB w ^ 2 -
        4 * antiDiagonalQuadA w * antiDiagonalQuadC w =
      9 * antiDiagonalSextic w := by
  simp only [antiDiagonalQuadA, antiDiagonalQuadB, antiDiagonalQuadC,
    antiDiagonalSextic]
  ring

/-- Exact rational-function identity producing the anti-diagonal quotient
of the surviving cubic correspondence. -/
theorem antiDiagonal_quadratic_relation_identity
    (p q : ℚ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hden : antiDiagonalDen p q ≠ 0) :
    let w := antiDiagonalW p q
    let V := invariantX q
    antiDiagonalQuadA w * V ^ 2 + antiDiagonalQuadB w * V +
        antiDiagonalQuadC w =
      (invariantX p - 2 * invariantX q + 6) *
        (8 * p * (p - 1) * (q ^ 2 - q + 1) ^ 3 /
          (q * (q - 1) * antiDiagonalDen p q ^ 3)) := by
  have hpSub : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  have hqSub : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  simp only [antiDiagonalW, antiDiagonalQuadA,
    antiDiagonalQuadB, antiDiagonalQuadC, invariantX]
  field_simp [hp0, hpSub, hq0, hqSub, hden]
  simp only [antiDiagonalDen]
  ring

/-- A nondegenerate point of the cubic correspondence maps to the
anti-diagonal genus-two curve. -/
theorem antiDiagonalZ_sq
    (p q : ℚ) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hden : antiDiagonalDen p q ≠ 0)
    (hcorrespondence : invariantX p = 2 * invariantX q - 6) :
    antiDiagonalZ p q ^ 2 = antiDiagonalSextic (antiDiagonalW p q) := by
  let w := antiDiagonalW p q
  let V := invariantX q
  have hrelation :
      antiDiagonalQuadA w * V ^ 2 + antiDiagonalQuadB w * V +
        antiDiagonalQuadC w = 0 := by
    rw [antiDiagonal_quadratic_relation_identity p q hp0 hp1 hq0 hq1
      hden]
    rw [hcorrespondence]
    ring
  have hdisc := antiDiagonal_discriminant_identity w
  simp only [antiDiagonalZ, w, V] at hrelation hdisc ⊢
  linear_combination
    (4 * antiDiagonalQuadA (antiDiagonalW p q) / 9) * hrelation +
      (1 / 9) * hdisc

/-- The cyclic-cubic invariant of an integral cube root is the ratio of
its two Eisenstein cube coordinates. -/
theorem invariantX_intRatio
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    invariantX ((x : ℚ) / (y : ℚ)) =
      3 * (eisensteinCubeReal x y : ℚ) /
        (eisensteinCubeEta x y : ℚ) := by
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hxyQ : (x : ℚ) - (y : ℚ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hxy
  simp only [invariantX, eisensteinCubeReal, eisensteinCubeEta]
  push_cast
  field_simp [hxQ, hyQ, hxyQ]

/-- The four-scalar cube correspondence is exactly the rational
anti-diagonal relation between the two cyclic-cubic invariants. -/
theorem invariantX_relation_of_fourScalarCorrespondence
    {x y u v : ℤ}
    (hetaNonzero : eisensteinCubeEta x y ≠ 0)
    (hcorrespondence : FourScalarEisensteinCubeCorrespondence x y u v) :
    invariantX ((x : ℚ) / (y : ℚ)) =
      2 * invariantX ((u : ℚ) / (v : ℚ)) - 6 := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp [eisensteinCubeEta] at hetaNonzero
  have hxy : x ≠ y := by
    intro hxy
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hetaSecond : eisensteinCubeEta u v ≠ 0 := by
    rw [hcorrespondence.1]
    exact mul_ne_zero (by norm_num) hetaNonzero
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  have hv : v ≠ 0 := by
    intro hv
    subst v
    simp [eisensteinCubeEta] at hetaSecond
  have huv : u ≠ v := by
    intro huv
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  rw [invariantX_intRatio x y hx hy hxy,
    invariantX_intRatio u v hu hv huv]
  have hetaQ := congrArg (fun z : ℤ => (z : ℚ)) hcorrespondence.1
  have hrealQ := congrArg (fun z : ℤ => (z : ℚ)) hcorrespondence.2
  norm_num at hetaQ hrealQ
  rw [hetaQ, hrealQ]
  have hetaNonzeroQ : (eisensteinCubeEta x y : ℚ) ≠ 0 := by
    exact_mod_cast hetaNonzero
  field_simp [hetaNonzeroQ]
  ring

/-- The quotient curve is a genuine consumer of the surviving four-scalar
cube correspondence. -/
theorem antiDiagonalZ_sq_of_fourScalarCorrespondence
    {x y u v : ℤ}
    (hetaNonzero : eisensteinCubeEta x y ≠ 0)
    (hcorrespondence : FourScalarEisensteinCubeCorrespondence x y u v) :
    antiDiagonalZ ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ)) ^ 2 =
      antiDiagonalSextic
        (antiDiagonalW ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ))) := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp [eisensteinCubeEta] at hetaNonzero
  have hxy : x ≠ y := by
    intro hxy
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hetaSecond : eisensteinCubeEta u v ≠ 0 := by
    rw [hcorrespondence.1]
    exact mul_ne_zero (by norm_num) hetaNonzero
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  have hv : v ≠ 0 := by
    intro hv
    subst v
    simp [eisensteinCubeEta] at hetaSecond
  have huv : u ≠ v := by
    intro huv
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  have hp0 : (x : ℚ) / (y : ℚ) ≠ 0 := div_ne_zero
    (by exact_mod_cast hx) (by exact_mod_cast hy)
  have hp1 : (x : ℚ) / (y : ℚ) ≠ 1 := by
    intro hp
    have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
    have hcast : (x : ℚ) = (y : ℚ) :=
      (div_eq_one_iff_eq hyQ).mp hp
    exact hxy (by exact_mod_cast hcast)
  have hq0 : (u : ℚ) / (v : ℚ) ≠ 0 := div_ne_zero
    (by exact_mod_cast hu) (by exact_mod_cast hv)
  have hq1 : (u : ℚ) / (v : ℚ) ≠ 1 := by
    intro hq
    have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv
    have hcast : (u : ℚ) = (v : ℚ) :=
      (div_eq_one_iff_eq hvQ).mp hq
    exact huv (by exact_mod_cast hcast)
  have hrelation := invariantX_relation_of_fourScalarCorrespondence
    hetaNonzero hcorrespondence
  have hden := antiDiagonalDen_ne_zero_of_invariantX_relation
    ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ))
    hp0 hp1 hq0 hq1 hrelation
  exact antiDiagonalZ_sq
    ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ))
    hp0 hp1 hq0 hq1 hden hrelation

/-- The anti-diagonal model is birational to the order-eighteen sextic
already used by the Tate-normal-form consumer. -/
theorem antiDiagonalSextic_birational_identity (w : ℚ)
    (hw : w ≠ 1) :
    (1 - w) ^ 6 *
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial
          ((1 + w) / (1 - w)) =
      antiDiagonalSextic w := by
  simp only [antiDiagonalSextic,
    MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial]
  have hden : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  field_simp [hden]
  ring

/-- The exact norm identity over `ℤ[√-2]`. -/
theorem antiDiagonal_quadraticNorm_identity (r s : ℤ) :
    antiDiagonalNormReal r s ^ 2 +
        2 * antiDiagonalNormSqrtNegTwo r s ^ 2 =
      antiDiagonalSexticHom r s := by
  simp only [antiDiagonalNormReal, antiDiagonalNormSqrtNegTwo,
    antiDiagonalSexticHom]
  ring

/-- Homogenizing at the canonical denominator recovers the integral sextic
form. -/
theorem antiDiagonalSexticHom_dehomogenize
    (r s : ℤ) (hs : s ≠ 0) :
    ((antiDiagonalSexticHom r s : ℤ) : ℚ) =
      (s : ℚ) ^ 6 * antiDiagonalSextic ((r : ℚ) / (s : ℚ)) := by
  simp only [antiDiagonalSexticHom, antiDiagonalSextic]
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  field_simp [hsQ]
  push_cast
  ring

/-- First small Bézout identity for the two norm coefficients. -/
theorem antiDiagonalNorm_bezout_num (r s : ℤ) :
    (4 * r * s) * antiDiagonalNormReal r s +
        (s ^ 2 + r * s - 8 * r ^ 2) *
          antiDiagonalNormSqrtNegTwo r s =
      32 * r ^ 5 := by
  simp only [antiDiagonalNormReal, antiDiagonalNormSqrtNegTwo]
  ring

/-- Second small Bézout identity for the two norm coefficients. -/
theorem antiDiagonalNorm_bezout_den (r s : ℤ) :
    (36 * r ^ 2 - 32 * s ^ 2) * antiDiagonalNormReal r s +
        (9 * r ^ 2 + 81 * r * s - 8 * s ^ 2) *
          antiDiagonalNormSqrtNegTwo r s =
      32 * s ^ 5 := by
  simp only [antiDiagonalNormReal, antiDiagonalNormSqrtNegTwo]
  ring

private theorem common_divisor_antiDiagonalNorm_dvd_32
    {r s d : ℤ} (hrs : IsCoprime r s)
    (hreal : d ∣ antiDiagonalNormReal r s)
    (himag : d ∣ antiDiagonalNormSqrtNegTwo r s) :
    d ∣ 32 := by
  obtain ⟨realPart, hrealPart⟩ := hreal
  obtain ⟨imagPart, himagPart⟩ := himag
  have hnum : d ∣ 32 * r ^ 5 := by
    refine ⟨(4 * r * s) * realPart +
      (s ^ 2 + r * s - 8 * r ^ 2) * imagPart, ?_⟩
    rw [← antiDiagonalNorm_bezout_num r s, hrealPart, himagPart]
    ring
  have hden : d ∣ 32 * s ^ 5 := by
    refine ⟨(36 * r ^ 2 - 32 * s ^ 2) * realPart +
      (9 * r ^ 2 + 81 * r * s - 8 * s ^ 2) * imagPart, ?_⟩
    rw [← antiDiagonalNorm_bezout_den r s, hrealPart, himagPart]
    ring
  obtain ⟨numPart, hnumPart⟩ := hnum
  obtain ⟨denPart, hdenPart⟩ := hden
  obtain ⟨a, b, hab⟩ := hrs.pow (m := 5) (n := 5)
  refine ⟨a * numPart + b * denPart, ?_⟩
  calc
    32 = 32 * (a * r ^ 5 + b * s ^ 5) := by rw [hab]; ring
    _ = d * (a * numPart + b * denPart) := by
      calc
        32 * (a * r ^ 5 + b * s ^ 5) =
            a * (32 * r ^ 5) + b * (32 * s ^ 5) := by ring
        _ = a * (d * numPart) + b * (d * denPart) := by
          rw [hnumPart, hdenPart]
        _ = d * (a * numPart + b * denPart) := by ring

private theorem antiDiagonalNormReal_mod_sixteen
    (r s : ZMod 16)
    (hprimitive :
      (ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)) r ≠ 0 ∨
        (ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)) s ≠ 0) :
    r ^ 3 + 9 * r ^ 2 * s - r * s ^ 2 - s ^ 3 ≠ 0 := by
  revert r s
  decide

private theorem primitive_parity
    {r s : ℤ} (hrs : IsCoprime r s) :
    (r : ZMod 2) ≠ 0 ∨ (s : ZMod 2) ≠ 0 := by
  by_contra h
  push Not at h
  have hr : (2 : ℤ) ∣ r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp h.1
  have hs : (2 : ℤ) ∣ s :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd s 2).mp h.2
  have hunit : IsUnit (2 : ℤ) := hrs.isRelPrime hr hs
  exact (Nat.prime_iff_prime_int.mp Nat.prime_two).not_unit hunit

private theorem sixteen_not_dvd_antiDiagonalNormReal
    {r s : ℤ} (hrs : IsCoprime r s) :
    ¬(16 : ℤ) ∣ antiDiagonalNormReal r s := by
  have hprimitive := primitive_parity hrs
  have hnonzero := antiDiagonalNormReal_mod_sixteen
    (r : ZMod 16) (s : ZMod 16) (by
      simpa [ZMod.castHom_apply] using hprimitive)
  intro hdvd
  have hzero : ((antiDiagonalNormReal r s : ℤ) : ZMod 16) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (antiDiagonalNormReal r s) 16).mpr hdvd
  apply hnonzero
  norm_num [antiDiagonalNormReal] at hzero ⊢
  exact hzero

/-- For primitive homogeneous coordinates, the two coefficients of the
quadratic norm have common divisor dividing eight. -/
theorem gcd_antiDiagonalNorm_dvd_eight
    {r s : ℤ} (hrs : IsCoprime r s) :
    (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) ∣ 8 := by
  let g : ℤ := GCDMonoid.gcd (antiDiagonalNormReal r s)
    (antiDiagonalNormSqrtNegTwo r s)
  have hg32 : g ∣ 32 :=
    common_divisor_antiDiagonalNorm_dvd_32 hrs
      (GCDMonoid.gcd_dvd_left _ _) (GCDMonoid.gcd_dvd_right _ _)
  have hgNonneg : 0 ≤ g := Int.gcd_nonneg _ _
  have hgAbs : g.natAbs ∣ 32 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hg32
  have hgLeNat : g.natAbs ≤ 32 := Nat.le_of_dvd (by norm_num) hgAbs
  have hgLe : g ≤ 32 := by
    have : (g.natAbs : ℤ) ≤ 32 := by exact_mod_cast hgLeNat
    simpa [Int.natCast_natAbs, abs_of_nonneg hgNonneg] using this
  have hsixteen : ¬(16 : ℤ) ∣ g := by
    intro hdiv
    apply sixteen_not_dvd_antiDiagonalNormReal hrs
    exact hdiv.trans (GCDMonoid.gcd_dvd_left _ _)
  change g ∣ 8
  interval_cases g
  all_goals norm_num at *

private theorem antiDiagonalNormReal_mod_two_of_parity_ne
    (r s : ZMod 2) (hparity : r ≠ s) :
    r ^ 3 + 9 * r ^ 2 * s - r * s ^ 2 - s ^ 3 ≠ 0 := by
  revert r s
  decide

private theorem antiDiagonalNorm_mod_eight_of_odd
    (r s : ZMod 8)
    (hr : (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) r ≠ 0)
    (hs : (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) s ≠ 0) :
    r ^ 3 + 9 * r ^ 2 * s - r * s ^ 2 - s ^ 3 = 0 ∧
      -4 * r * (r ^ 2 - s ^ 2) = 0 := by
  revert r s
  decide

/-- The common divisor is exactly one for opposite parities and exactly
eight for two odd primitive coordinates. -/
theorem gcd_antiDiagonalNorm_eq_one_or_eight
    {r s : ℤ} (hrs : IsCoprime r s) :
    (GCDMonoid.gcd (antiDiagonalNormReal r s)
        (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1 ∨
      (GCDMonoid.gcd (antiDiagonalNormReal r s)
        (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8 := by
  let g : ℤ := GCDMonoid.gcd (antiDiagonalNormReal r s)
    (antiDiagonalNormSqrtNegTwo r s)
  have hgEight : g ∣ 8 := gcd_antiDiagonalNorm_dvd_eight hrs
  have hgNonneg : 0 ≤ g := Int.gcd_nonneg _ _
  have hgAbs : g.natAbs ∣ 8 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgEight
  have hgLeNat : g.natAbs ≤ 8 := Nat.le_of_dvd (by norm_num) hgAbs
  have hgLe : g ≤ 8 := by
    have : (g.natAbs : ℤ) ≤ 8 := by exact_mod_cast hgLeNat
    simpa [Int.natCast_natAbs, abs_of_nonneg hgNonneg] using this
  by_cases hparity : (r : ZMod 2) = (s : ZMod 2)
  · have hprimitive := primitive_parity hrs
    have hr : (r : ZMod 2) ≠ 0 := by
      rcases hprimitive with hr | hs
      · exact hr
      · rwa [hparity]
    have hs : (s : ZMod 2) ≠ 0 := by rwa [← hparity]
    have hmod := antiDiagonalNorm_mod_eight_of_odd
      (r : ZMod 8) (s : ZMod 8) (by
        simpa [ZMod.castHom_apply] using hr) (by
        simpa [ZMod.castHom_apply] using hs)
    have hrealEight : (8 : ℤ) ∣ antiDiagonalNormReal r s := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd
        (antiDiagonalNormReal r s) 8).mp
      norm_num [antiDiagonalNormReal] at hmod ⊢
      exact hmod.1
    have himagEight :
        (8 : ℤ) ∣ antiDiagonalNormSqrtNegTwo r s := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd
        (antiDiagonalNormSqrtNegTwo r s) 8).mp
      norm_num [antiDiagonalNormSqrtNegTwo] at hmod ⊢
      exact hmod.2
    have hEightG : (8 : ℤ) ∣ g :=
      GCDMonoid.dvd_gcd hrealEight himagEight
    right
    change g = 8
    interval_cases g
    all_goals norm_num at *
  · have hrealNonzero :
        ((antiDiagonalNormReal r s : ℤ) : ZMod 2) ≠ 0 := by
      have hmod := antiDiagonalNormReal_mod_two_of_parity_ne
        (r : ZMod 2) (s : ZMod 2) hparity
      norm_num [antiDiagonalNormReal] at hmod ⊢
      exact hmod
    have htwoNotReal : ¬(2 : ℤ) ∣ antiDiagonalNormReal r s := by
      intro hdiv
      exact hrealNonzero
        ((ZMod.intCast_zmod_eq_zero_iff_dvd
          (antiDiagonalNormReal r s) 2).mpr hdiv)
    have htwoNotG : ¬(2 : ℤ) ∣ g := by
      intro hdiv
      apply htwoNotReal
      exact hdiv.trans (GCDMonoid.gcd_dvd_left _ _)
    left
    change g = 1
    interval_cases g
    all_goals norm_num at *

/-- A primitive integral point on the anti-diagonal sextic supplies a
quadratic norm equation whose two coefficients have gcd one or eight.
This is the checked consumer of the factorization and support bound. -/
theorem antiDiagonal_primitive_quadraticNormDatum
    {r s z : ℤ} (hrs : IsCoprime r s)
    (hcurve : z ^ 2 = antiDiagonalSexticHom r s) :
      antiDiagonalNormReal r s ^ 2 +
          2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = z ^ 2 ∧
      ((GCDMonoid.gcd (antiDiagonalNormReal r s)
            (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1 ∨
        (GCDMonoid.gcd (antiDiagonalNormReal r s)
            (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8) := by
  constructor
  · rw [antiDiagonal_quadraticNorm_identity, hcurve]
  · exact gcd_antiDiagonalNorm_eq_one_or_eight hrs

/-- Every rational point on the anti-diagonal sextic has canonical
primitive homogeneous coordinates satisfying the supported quadratic norm
equation.  This is the rational-point consumer used by the subsequent
fixed-field square-class allocation. -/
theorem exists_primitive_quadraticNormDatum_of_antiDiagonal_point
    {w z : ℚ} (hcurve : z ^ 2 = antiDiagonalSextic w) :
    ∃ r s c : ℤ,
      0 < s ∧
      IsCoprime r s ∧
      w = (r : ℚ) / (s : ℚ) ∧
      c ^ 2 = antiDiagonalSexticHom r s ∧
      antiDiagonalNormReal r s ^ 2 +
            2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2 ∧
        ((GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1 ∨
          (GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8) := by
  let r : ℤ := w.num
  let s : ℤ := w.den
  have hs : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast w.den_ne_zero
  have hw : w = (r : ℚ) / (s : ℚ) := by
    simpa only [r, s, Int.cast_natCast] using (Rat.num_div_den w).symm
  have hscaled :
      (z * (s : ℚ) ^ 3) ^ 2 =
        ((antiDiagonalSexticHom r s : ℤ) : ℚ) := by
    rw [antiDiagonalSexticHom_dehomogenize r s hs, ← hw, ← hcurve]
    ring
  have hsquare :
      IsSquare ((antiDiagonalSexticHom r s : ℤ) : ℚ) :=
    ⟨z * (s : ℚ) ^ 3, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hc⟩ := Rat.isSquare_intCast_iff.mp hsquare
  have hc' : c ^ 2 = antiDiagonalSexticHom r s := by
    simpa [pow_two] using hc.symm
  have hrs : IsCoprime r s := by
    simpa only [r, s] using Rat.isCoprime_num_den w
  obtain ⟨hnorm, hgcd⟩ :=
    antiDiagonal_primitive_quadraticNormDatum hrs hc'
  refine ⟨r, s, c, ?_, hrs, hw, hc', hnorm, hgcd⟩
  dsimp [s]
  exact_mod_cast w.den_pos

/-- The primitive quadratic norm datum is the final checked consumer of
the surviving four-scalar cube correspondence. -/
theorem exists_primitive_quadraticNormDatum_of_fourScalarCorrespondence
    {x y u v : ℤ}
    (hetaNonzero : eisensteinCubeEta x y ≠ 0)
    (hcorrespondence : FourScalarEisensteinCubeCorrespondence x y u v) :
    ∃ r s c : ℤ,
      0 < s ∧
      IsCoprime r s ∧
      antiDiagonalW ((x : ℚ) / (y : ℚ))
          ((u : ℚ) / (v : ℚ)) = (r : ℚ) / (s : ℚ) ∧
      c ^ 2 = antiDiagonalSexticHom r s ∧
      antiDiagonalNormReal r s ^ 2 +
            2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2 ∧
        ((GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1 ∨
          (GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8) := by
  have hcurve := antiDiagonalZ_sq_of_fourScalarCorrespondence
    hetaNonzero hcorrespondence
  exact exists_primitive_quadraticNormDatum_of_antiDiagonal_point hcurve

end MazurTorsion.XOneEighteenDescent
