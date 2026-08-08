/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuadraticNormBase

/-!
# A global conic parameter in the `X₁(18)` quadratic-norm descent

The anti-diagonal sextic factorization gives an integral equation

`A² + 2 B² = C²`.

This file takes the next global descent step.  Projection from the rational
point `(-1,0)` on the normalized conic gives the parameter

`lambda = B / (C + A)`.

For a noncuspidal point on the order-eighteen curve, the denominator cannot
vanish: otherwise `B = 0`, and the explicit factorization of `B` forces the
anti-diagonal abscissa to be `0`, `1`, or `-1`, hence the original abscissa is
a cusp.  Clearing the canonical numerator and denominator of `lambda` then
produces three integral equations with coprime parameter coordinates.  This
is a global parametrization of the quadratic norm equation, not a local
solubility certificate and not a rational-point classification.
-/

namespace MazurTorsion.XOneEighteenDescent

/-- The slope obtained by projecting the quadratic-norm conic from its
distinguished rational point. -/
def quadraticNormSlope (a b c : ℚ) : ℚ :=
  b / (c + a)

/-- Projection from the distinguished point parametrizes every point of
`a² + 2b² = c²` away from the tangent `c + a = 0`. -/
theorem quadraticNormSlope_relations
    (a b c : ℚ) (hden : c + a ≠ 0)
    (hnorm : a ^ 2 + 2 * b ^ 2 = c ^ 2) :
    2 * a = (c + a) * (1 - 2 * quadraticNormSlope a b c ^ 2) ∧
      2 * c = (c + a) * (1 + 2 * quadraticNormSlope a b c ^ 2) ∧
      b = quadraticNormSlope a b c * (c + a) := by
  simp only [quadraticNormSlope]
  constructor
  · field_simp [hden]
    nlinarith [hnorm]
  constructor
  · field_simp [hden]
    nlinarith [hnorm]
  · field_simp [hden]

/-- Clearing the canonical reduced fraction of the conic slope gives a
primitive integral parametrization. -/
theorem exists_primitive_parameter_of_int_quadraticNorm
    (a b c : ℤ) (hden : c + a ≠ 0)
    (hnorm : a ^ 2 + 2 * b ^ 2 = c ^ 2) :
    ∃ p q : ℤ,
      0 < q ∧
      IsCoprime p q ∧
      b * q = p * (c + a) ∧
      2 * a * q ^ 2 = (c + a) * (q ^ 2 - 2 * p ^ 2) ∧
      2 * c * q ^ 2 = (c + a) * (q ^ 2 + 2 * p ^ 2) := by
  have hdenQ : (c : ℚ) + a ≠ 0 := by
    exact_mod_cast hden
  have hnormQ : (a : ℚ) ^ 2 + 2 * (b : ℚ) ^ 2 = (c : ℚ) ^ 2 := by
    exact_mod_cast hnorm
  let slope : ℚ := quadraticNormSlope a b c
  let p : ℤ := slope.num
  let q : ℤ := slope.den
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast slope.den_ne_zero
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hslope : slope = (p : ℚ) / (q : ℚ) := by
    simpa only [p, q, Int.cast_natCast] using (Rat.num_div_den slope).symm
  obtain ⟨hfirst, hsecond, hlinear⟩ :=
    quadraticNormSlope_relations (a : ℚ) (b : ℚ) (c : ℚ)
      hdenQ hnormQ
  change slope = _ at hslope
  change _ = _ * (1 - 2 * slope ^ 2) at hfirst
  change _ = _ * (1 + 2 * slope ^ 2) at hsecond
  change _ = slope * _ at hlinear
  rw [hslope] at hfirst hsecond hlinear
  have hlinear' : b * q = p * (c + a) := by
    field_simp [hqQ] at hlinear
    exact_mod_cast hlinear
  have hfirst' :
      2 * a * q ^ 2 = (c + a) * (q ^ 2 - 2 * p ^ 2) := by
    field_simp [hqQ] at hfirst
    exact_mod_cast hfirst
  have hsecond' :
      2 * c * q ^ 2 = (c + a) * (q ^ 2 + 2 * p ^ 2) := by
    field_simp [hqQ] at hsecond
    exact_mod_cast hsecond
  refine ⟨p, q, ?_, ?_, hlinear', hfirst', hsecond'⟩
  · dsimp [q]
    exact_mod_cast slope.den_pos
  · simpa only [p, q] using Rat.isCoprime_num_den slope

/-! ## Excluding the tangent and consuming an order-eighteen point -/

/-- The imaginary norm coefficient cannot vanish on the primitive
homogeneous coordinates of a noncuspidal point.  The exact factorization
`B = -4 r (r - s) (r + s)` shows that its three zero factors give precisely
the anti-diagonal abscissas `0`, `1`, and `-1`. -/
theorem antiDiagonalNormSqrtNegTwo_ne_zero_of_noncuspidal
    {x w : ℚ} {r s : ℤ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hw1 : w ≠ 1)
    (hs : s ≠ 0)
    (hw : w = (r : ℚ) / (s : ℚ))
    (hinverse : (1 + w) / (1 - w) = x) :
    antiDiagonalNormSqrtNegTwo r s ≠ 0 := by
  intro himag
  have hfactor : r * (r ^ 2 - s ^ 2) = 0 := by
    simpa only [antiDiagonalNormSqrtNegTwo, neg_mul, neg_eq_zero,
      Int.reduceNeg, Int.reduceOfNat, mul_eq_zero, OfNat.ofNat_ne_zero,
      false_or] using himag
  rcases mul_eq_zero.mp hfactor with hr | hrs
  · have hw0 : w = 0 := by
      rw [hw, hr]
      simp
    rw [hw0] at hinverse
    norm_num at hinverse
    exact hx1 hinverse.symm
  · have hsplit : (r - s) * (r + s) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hsplit with hrsEq | hrsNeg
    · have hrEq : r = s := by linarith
      apply hw1
      rw [hw, hrEq]
      exact div_self (by exact_mod_cast hs)
    · have hrNeg : r = -s := by linarith
      have hwNeg : w = -1 := by
        rw [hw, hrNeg]
        push_cast
        field_simp [by exact_mod_cast hs]
      rw [hwNeg] at hinverse
      norm_num at hinverse
      exact hx0 hinverse.symm

/-- On a noncuspidal order-eighteen point, the integral quadratic-norm
datum never lies on the exceptional tangent used by the conic projection. -/
theorem antiDiagonal_norm_tangent_ne_zero_of_noncuspidal
    {x w : ℚ} {r s c : ℤ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hw1 : w ≠ 1)
    (hs : s ≠ 0)
    (hw : w = (r : ℚ) / (s : ℚ))
    (hinverse : (1 + w) / (1 - w) = x)
    (hnorm : antiDiagonalNormReal r s ^ 2 +
        2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2) :
    c + antiDiagonalNormReal r s ≠ 0 := by
  have himag := antiDiagonalNormSqrtNegTwo_ne_zero_of_noncuspidal
    hx0 hx1 hw1 hs hw hinverse
  intro htangent
  have hc : c = -antiDiagonalNormReal r s := by
    linarith
  have himagSq : antiDiagonalNormSqrtNegTwo r s ^ 2 = 0 := by
    rw [hc] at hnorm
    nlinarith
  exact himag ((sq_eq_zero_iff).mp himagSq)

/-- Every noncuspidal rational point on the order-eighteen sextic reaches a
single primitive integral Diophantine system obtained by globally
parametrizing the quadratic norm conic. -/
theorem exists_primitive_normParameter_of_orderEighteen_noncuspidal_point
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    ∃ r s c p q : ℤ,
      0 < s ∧
      IsCoprime r s ∧
      (1 + (r : ℚ) / (s : ℚ)) /
          (1 - (r : ℚ) / (s : ℚ)) = x ∧
      c ^ 2 = antiDiagonalSexticHom r s ∧
      antiDiagonalNormReal r s ^ 2 +
          2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2 ∧
      ((GCDMonoid.gcd (antiDiagonalNormReal r s)
            (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1 ∨
        (GCDMonoid.gcd (antiDiagonalNormReal r s)
            (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8) ∧
      antiDiagonalNormSqrtNegTwo r s ≠ 0 ∧
      c + antiDiagonalNormReal r s ≠ 0 ∧
      0 < q ∧
      p ≠ 0 ∧
      IsCoprime p q ∧
      antiDiagonalNormSqrtNegTwo r s * q =
        p * (c + antiDiagonalNormReal r s) ∧
      2 * antiDiagonalNormReal r s * q ^ 2 =
        (c + antiDiagonalNormReal r s) * (q ^ 2 - 2 * p ^ 2) ∧
      2 * c * q ^ 2 =
        (c + antiDiagonalNormReal r s) * (q ^ 2 + 2 * p ^ 2) := by
  obtain ⟨w, z, hw1, hanti, hinverse⟩ :=
    exists_antiDiagonal_point_of_orderEighteen_point x y hcurve
  obtain ⟨r, s, c, hs, hrs, hw, hc, hnorm, hgcd⟩ :=
    exists_primitive_quadraticNormDatum_of_antiDiagonal_point hanti
  have hs0 : s ≠ 0 := ne_of_gt hs
  have himag : antiDiagonalNormSqrtNegTwo r s ≠ 0 :=
    antiDiagonalNormSqrtNegTwo_ne_zero_of_noncuspidal
      hx0 hx1 hw1 hs0 hw hinverse
  have htangent : c + antiDiagonalNormReal r s ≠ 0 :=
    antiDiagonal_norm_tangent_ne_zero_of_noncuspidal
      hx0 hx1 hw1 hs0 hw hinverse hnorm
  obtain ⟨p, q, hq, hpq, hlinear, hfirst, hsecond⟩ :=
    exists_primitive_parameter_of_int_quadraticNorm
      (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) c htangent hnorm
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hlinear
    exact himag ((mul_eq_zero.mp hlinear).resolve_right (ne_of_gt hq))
  refine ⟨r, s, c, p, q, hs, hrs, ?_, hc, hnorm, hgcd,
    himag, htangent, hq, hp0, hpq, hlinear, hfirst, hsecond⟩
  rw [← hw]
  exact hinverse

/-- A point of exact order eighteen on a rational elliptic curve supplies
the globally parametrized primitive quadratic-norm system.  This is the
downstream consumer of the new conic interface; no unproved point
classification is assumed. -/
theorem exists_primitive_normParameter_of_exact_order_eighteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = 18) :
    ∃ x y : ℚ, x ≠ 0 ∧ x ≠ 1 ∧
      y ^ 2 = MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x ∧
      ∃ r s c p q : ℤ,
        0 < s ∧
        IsCoprime r s ∧
        (1 + (r : ℚ) / (s : ℚ)) /
            (1 - (r : ℚ) / (s : ℚ)) = x ∧
        c ^ 2 = antiDiagonalSexticHom r s ∧
        antiDiagonalNormReal r s ^ 2 +
            2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2 ∧
        ((GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1 ∨
          (GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8) ∧
        antiDiagonalNormSqrtNegTwo r s ≠ 0 ∧
        c + antiDiagonalNormReal r s ≠ 0 ∧
        0 < q ∧
        p ≠ 0 ∧
        IsCoprime p q ∧
        antiDiagonalNormSqrtNegTwo r s * q =
          p * (c + antiDiagonalNormReal r s) ∧
        2 * antiDiagonalNormReal r s * q ^ 2 =
          (c + antiDiagonalNormReal r s) * (q ^ 2 - 2 * p ^ 2) ∧
        2 * c * q ^ 2 =
          (c + antiDiagonalNormReal r s) * (q ^ 2 + 2 * p ^ 2) := by
  obtain ⟨b, c₀, u, r₀, d, t, _hu, _hb, _hc, _hbc, _hr,
    _hdEq, _hd0, _hd1, _hcparam, _hbparam, _htEq, _hnine, _htwo,
    _haux, _hden, hx0, hx1, hcurve, _hdisc⟩ :=
    MazurTorsion.Kubert.exists_orderEighteen_genusTwo_certificate E Q hQ
  refine ⟨MazurTorsion.Kubert.orderEighteenModelX d t,
    MazurTorsion.Kubert.orderEighteenModelY d t, hx0, hx1, hcurve, ?_⟩
  exact exists_primitive_normParameter_of_orderEighteen_noncuspidal_point
    (MazurTorsion.Kubert.orderEighteenModelX d t)
    (MazurTorsion.Kubert.orderEighteenModelY d t) hx0 hx1 hcurve

end MazurTorsion.XOneEighteenDescent
