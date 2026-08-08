/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuadraticNormParametrization

/-!
# The finite scalar refinement of the gcd-eight `X₁(18)` norm cover

In the gcd-eight branch, write the two quadratic-norm coefficients as
`A = 8a` and `B = 8b`.  The square root is then also exactly divisible by
eight, say `c = 8e`.  Comparing the reduced conic slope with the normalized
primitive norm equation leaves one integral scalar `k`:

`4a = k(q² - 2p²)`, `2b = kpq`, and
`4e = k(q² + 2p²)`.

Primitivity forces `k ∣ 4`.  The exact parity of the original cubic
coefficients removes the unit cases: `k = ±4` has `q` odd and `p` even,
whereas `k = ±2` has `p` odd and `4 ∣ q`.  Thus this file replaces the
unbounded factor split in the gcd-eight branch by four explicit integral
covers.  It does not assert that those four covers have no noncuspidal
points; that final classification is a separate arithmetic step.
-/

namespace MazurTorsion.XOneEighteenDescent

private lemma primitive_real_zero_mod_two_forces_odd :
    ∀ r s : ZMod 2,
      r ^ 3 + 9 * r ^ 2 * s - r * s ^ 2 - s ^ 3 = 0 →
      (r ≠ 0 ∨ s ≠ 0) →
      r = 1 ∧ s = 1 := by
  decide

private lemma odd_cubic_difference_zero_mod_eight :
    ∀ r s : ZMod 8,
      (ZMod.cast r : ZMod 2) = 1 →
      (ZMod.cast s : ZMod 2) = 1 →
      r * (r ^ 2 - s ^ 2) = 0 := by
  decide

private lemma primitive_pell_factor_ne_zero_mod_four :
    ∀ p q : ZMod 4,
      ((ZMod.cast p : ZMod 2) ≠ 0 ∨
        (ZMod.cast q : ZMod 2) ≠ 0) →
      q ^ 2 - 2 * p ^ 2 ≠ 0 := by
  decide

private theorem odd_parameters_of_eight_gcd
    (r s : ℤ) (hrs : IsCoprime r s)
    (hgcd : (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8) :
    Odd r ∧ Odd s := by
  have hrealEight : (8 : ℤ) ∣ antiDiagonalNormReal r s := by
    rw [← hgcd]
    exact GCDMonoid.gcd_dvd_left _ _
  have hrealTwo : (2 : ℤ) ∣ antiDiagonalNormReal r s :=
    (by norm_num : (2 : ℤ) ∣ 8).trans hrealEight
  have hrealZero :
      ((antiDiagonalNormReal r s : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (antiDiagonalNormReal r s) 2).2 hrealTwo
  have hrsMod : IsCoprime (r : ZMod 2) (s : ZMod 2) := hrs.intCast
  have hlocal := primitive_real_zero_mod_two_forces_odd
    (r : ZMod 2) (s : ZMod 2) (by
      norm_num [antiDiagonalNormReal] at hrealZero ⊢
      exact hrealZero) hrsMod.ne_zero_or_ne_zero
  exact ⟨ZMod.intCast_eq_one_iff_odd.mp hlocal.1,
    ZMod.intCast_eq_one_iff_odd.mp hlocal.2⟩

private theorem four_dvd_normalized_imaginary_coefficient
    (r s b : ℤ) (hr : Odd r) (hs : Odd s)
    (hD : r * (r ^ 2 - s ^ 2) = -2 * b) :
    (4 : ℤ) ∣ b := by
  have hrEight :
      (ZMod.cast (r : ZMod 8) : ZMod 2) = 1 := by
    rw [ZMod.cast_intCast (R := ZMod 2)
      (by norm_num : 2 ∣ 8) r]
    exact ZMod.intCast_eq_one_iff_odd.2 hr
  have hsEight :
      (ZMod.cast (s : ZMod 8) : ZMod 2) = 1 := by
    rw [ZMod.cast_intCast (R := ZMod 2)
      (by norm_num : 2 ∣ 8) s]
    exact ZMod.intCast_eq_one_iff_odd.2 hs
  have hzero := odd_cubic_difference_zero_mod_eight
    (r : ZMod 8) (s : ZMod 8) hrEight hsEight
  have hDvd : (8 : ℤ) ∣ r * (r ^ 2 - s ^ 2) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (r * (r ^ 2 - s ^ 2)) 8).1
    norm_num at hzero ⊢
    exact hzero
  obtain ⟨v, hv⟩ := hDvd
  refine ⟨-v, ?_⟩
  omega

private theorem odd_of_isCoprime_of_four_dvd_right
    (a b : ℤ) (hab : IsCoprime a b) (hb : (4 : ℤ) ∣ b) :
    Odd a := by
  apply Int.not_even_iff_odd.mp
  intro ha
  have htwoA : (2 : ℤ) ∣ a := ha.two_dvd
  have htwoB : (2 : ℤ) ∣ b :=
    (by norm_num : (2 : ℤ) ∣ 4).trans hb
  obtain ⟨x, hx⟩ := htwoA
  obtain ⟨y, hy⟩ := htwoB
  obtain ⟨u, v, huv⟩ := hab
  have htwoOne : (2 : ℤ) ∣ 1 := by
    refine ⟨u * x + v * y, ?_⟩
    calc
      1 = u * a + v * b := huv.symm
      _ = 2 * (u * x + v * y) := by rw [hx, hy]; ring
  norm_num at htwoOne

private theorem odd_left_of_isCoprime_of_even_right
    (a b : ℤ) (hab : IsCoprime a b) (hb : Even b) :
    Odd a := by
  apply Int.not_even_iff_odd.mp
  intro ha
  obtain ⟨x, hx⟩ := ha.two_dvd
  obtain ⟨y, hy⟩ := hb.two_dvd
  obtain ⟨u, v, huv⟩ := hab
  have htwoOne : (2 : ℤ) ∣ 1 := by
    refine ⟨u * x + v * y, ?_⟩
    calc
      1 = u * a + v * b := huv.symm
      _ = 2 * (u * x + v * y) := by rw [hx, hy]; ring
  norm_num at htwoOne

private theorem pell_factor_not_dvd_four_of_coprime
    (p q : ℤ) (hpq : IsCoprime p q) :
    ¬(4 : ℤ) ∣ q ^ 2 - 2 * p ^ 2 := by
  have hpqMod : IsCoprime (p : ZMod 2) (q : ZMod 2) := hpq.intCast
  have hprimitive :
      (ZMod.cast (p : ZMod 4) : ZMod 2) ≠ 0 ∨
        (ZMod.cast (q : ZMod 4) : ZMod 2) ≠ 0 := by
    rw [ZMod.cast_intCast (R := ZMod 2)
        (by norm_num : 2 ∣ 4) p,
      ZMod.cast_intCast (R := ZMod 2)
        (by norm_num : 2 ∣ 4) q]
    exact hpqMod.ne_zero_or_ne_zero
  have hnonzero := primitive_pell_factor_ne_zero_mod_four
    (p : ZMod 4) (q : ZMod 4) hprimitive
  intro hdvd
  apply hnonzero
  have hzero :
      ((q ^ 2 - 2 * p ^ 2 : ℤ) : ZMod 4) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (q ^ 2 - 2 * p ^ 2) 4).2 hdvd
  norm_num at hzero ⊢
  exact hzero

private theorem odd_second_of_odd_pell_factor
    (p q : ℤ) (hodd : Odd (q ^ 2 - 2 * p ^ 2)) :
    Odd q := by
  have htwoTerm : Even (2 * p ^ 2) := even_two.mul_right _
  have hqSquare : Odd (q ^ 2) :=
    (Int.odd_sub.mp hodd).mpr htwoTerm
  exact (Int.odd_pow' (by norm_num : (2 : ℕ) ≠ 0)).mp hqSquare

private theorem even_second_of_even_pell_factor
    (p q : ℤ) (heven : Even (q ^ 2 - 2 * p ^ 2)) :
    Even q := by
  have htwoTerm : Even (2 * p ^ 2) := even_two.mul_right _
  have hqSquare : Even (q ^ 2) :=
    (Int.even_sub.mp heven).mpr htwoTerm
  exact (Int.even_pow' (by norm_num : (2 : ℕ) ≠ 0)).mp hqSquare

private theorem signed_nonzero_divisor_four
    (k : ℤ) (hk0 : k ≠ 0) (hk : k ∣ 4) :
    k = -4 ∨ k = -2 ∨ k = -1 ∨
      k = 1 ∨ k = 2 ∨ k = 4 := by
  have hkAbsDvd : k.natAbs ∣ 4 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hk
  have hkAbsPos : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
  have hkAbsUpper : k.natAbs ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hkAbsDvd
  have hkAbs :
      k.natAbs = 1 ∨ k.natAbs = 2 ∨ k.natAbs = 4 := by
    interval_cases h : k.natAbs <;> norm_num at *
  rcases hkAbs with hkAbs | hkAbs | hkAbs
  · obtain hkPos | hkNeg := Int.natAbs_eq k
    · right; right; right; left
      omega
    · right; right; left
      omega
  · obtain hkPos | hkNeg := Int.natAbs_eq k
    · right; right; right; right; left
      omega
    · right; left
      omega
  · obtain hkPos | hkNeg := Int.natAbs_eq k
    · right; right; right; right; right
      omega
    · left
      omega

/-- If both quadratic-norm coefficients have exact common factor eight,
then the square-root coordinate has a concrete factor eight as well. -/
theorem exists_eight_normalized_antiDiagonal_squareRoot
    (r s c : ℤ)
    (hgcd : (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8)
    (hnorm : antiDiagonalNormReal r s ^ 2 +
      2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2) :
    ∃ e : ℤ, c = 8 * e := by
  have hreal : (8 : ℤ) ∣ antiDiagonalNormReal r s := by
    rw [← hgcd]
    exact GCDMonoid.gcd_dvd_left _ _
  have himag : (8 : ℤ) ∣ antiDiagonalNormSqrtNegTwo r s := by
    rw [← hgcd]
    exact GCDMonoid.gcd_dvd_right _ _
  obtain ⟨a, ha⟩ := hreal
  obtain ⟨b, hb⟩ := himag
  have hsquare : (8 : ℤ) ^ 2 ∣ c ^ 2 := by
    refine ⟨a ^ 2 + 2 * b ^ 2, ?_⟩
    rw [← hnorm, ha, hb]
    ring
  exact (Int.pow_dvd_pow_iff two_ne_zero).1 hsquare

/-- The gcd-eight branch of the primitive conic parametrization is one of
four explicit scalar covers.  The statement retains the primitive
homogeneous coordinates, the non-tangent condition, and all three conic
projection identities; in particular no denominator or exceptional-point
hypothesis is lost when the finite scalar is extracted. -/
theorem antiDiagonalNormParametric_eight_finite_scalar_cover
    (r s c p q : ℤ)
    (hrs : IsCoprime r s)
    (hq : 0 < q) (hp : p ≠ 0) (hpq : IsCoprime p q)
    (htangent : c + antiDiagonalNormReal r s ≠ 0)
    (hgcd : (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8)
    (hnorm : antiDiagonalNormReal r s ^ 2 +
      2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2)
    (hlinear : antiDiagonalNormSqrtNegTwo r s * q =
      p * (c + antiDiagonalNormReal r s))
    (hfirst : 2 * antiDiagonalNormReal r s * q ^ 2 =
      (c + antiDiagonalNormReal r s) * (q ^ 2 - 2 * p ^ 2))
    (hsecond : 2 * c * q ^ 2 =
      (c + antiDiagonalNormReal r s) * (q ^ 2 + 2 * p ^ 2)) :
    ∃ a b e k : ℤ,
      antiDiagonalNormReal r s = 8 * a ∧
      antiDiagonalNormSqrtNegTwo r s = 8 * b ∧
      c = 8 * e ∧
      IsCoprime a b ∧
      r * (r ^ 2 - s ^ 2) = -2 * b ∧
      4 * a = k * (q ^ 2 - 2 * p ^ 2) ∧
      2 * b = k * p * q ∧
      4 * e = k * (q ^ 2 + 2 * p ^ 2) ∧
      k ∣ 4 ∧
      ((k = -4 ∧ Odd q ∧ Even p) ∨
        (k = -2 ∧ Odd p ∧ (4 : ℤ) ∣ q) ∨
        (k = 2 ∧ Odd p ∧ (4 : ℤ) ∣ q) ∨
        (k = 4 ∧ Odd q ∧ Even p)) := by
  have hform : antiDiagonalNormParametricBidegreeForm r s p q = 0 :=
    antiDiagonalNormParametricBidegreeForm_eq_zero
      r s c p q (ne_of_gt hq) hlinear hfirst
  obtain ⟨a, b, _d₁, _d₂, hA, hB, hab, hD, _haPell,
    _hd₁, _hd₂, _hsplit, _hcommon⟩ :=
    antiDiagonalNormParametric_eight_cover
      r s p q hpq hgcd hform
  obtain ⟨e, hc⟩ :=
    exists_eight_normalized_antiDiagonal_squareRoot
      r s c hgcd hnorm
  have hB0 : antiDiagonalNormSqrtNegTwo r s ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hlinear
    have hproduct : p * (c + antiDiagonalNormReal r s) = 0 :=
      hlinear.symm
    exact htangent ((mul_eq_zero.mp hproduct).resolve_left hp)
  have hb0 : b ≠ 0 := by
    intro hb
    apply hB0
    rw [hB, hb]
    norm_num
  have hlinearNormalized : b * q = p * (e + a) := by
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    calc
      8 * (b * q) = (8 * b) * q := by ring
      _ = p * (8 * e + 8 * a) := by rw [← hB, ← hc, ← hA]; exact hlinear
      _ = 8 * (p * (e + a)) := by ring
  have hfirstScaled := hfirst
  rw [hA, hc] at hfirstScaled
  have hfirstNormalized :
      2 * a * q ^ 2 = (e + a) * (q ^ 2 - 2 * p ^ 2) := by
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    calc
      8 * (2 * a * q ^ 2) = 2 * (8 * a) * q ^ 2 := by ring
      _ = (8 * e + 8 * a) * (q ^ 2 - 2 * p ^ 2) := hfirstScaled
      _ = 8 * ((e + a) * (q ^ 2 - 2 * p ^ 2)) := by ring
  have hsecondScaled := hsecond
  rw [hA, hc] at hsecondScaled
  have hsecondNormalized :
      2 * e * q ^ 2 = (e + a) * (q ^ 2 + 2 * p ^ 2) := by
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    calc
      8 * (2 * e * q ^ 2) = 2 * (8 * e) * q ^ 2 := by ring
      _ = (8 * e + 8 * a) * (q ^ 2 + 2 * p ^ 2) := hsecondScaled
      _ = 8 * ((e + a) * (q ^ 2 + 2 * p ^ 2)) := by ring
  have hpDivB : p ∣ b := by
    apply hpq.dvd_of_dvd_mul_right
    exact ⟨e + a, hlinearNormalized⟩
  obtain ⟨t, ht⟩ := hpDivB
  have hsum : e + a = q * t := by
    apply mul_left_cancel₀ hp
    calc
      p * (e + a) = b * q := hlinearNormalized.symm
      _ = p * (q * t) := by rw [ht]; ring
  have hfirstScalar :
      2 * a * q = t * (q ^ 2 - 2 * p ^ 2) := by
    apply mul_right_cancel₀ (ne_of_gt hq)
    calc
      (2 * a * q) * q = 2 * a * q ^ 2 := by ring
      _ = (e + a) * (q ^ 2 - 2 * p ^ 2) := hfirstNormalized
      _ = (t * (q ^ 2 - 2 * p ^ 2)) * q := by rw [hsum]; ring
  have hqDiv : q ∣ (2 * t) * p ^ 2 := by
    refine ⟨t * q - 2 * a, ?_⟩
    linear_combination hfirstScalar
  have hqCoprimePSquare : IsCoprime q (p ^ 2) :=
    hpq.symm.pow_right
  have hqDivTwoT : q ∣ 2 * t :=
    hqCoprimePSquare.dvd_of_dvd_mul_right hqDiv
  obtain ⟨k, hk⟩ := hqDivTwoT
  have haScalar : 4 * a = k * (q ^ 2 - 2 * p ^ 2) := by
    apply mul_right_cancel₀ (ne_of_gt hq)
    calc
      (4 * a) * q = 2 * (2 * a * q) := by ring
      _ = 2 * (t * (q ^ 2 - 2 * p ^ 2)) := by rw [hfirstScalar]
      _ = (2 * t) * (q ^ 2 - 2 * p ^ 2) := by ring
      _ = (q * k) * (q ^ 2 - 2 * p ^ 2) := by rw [hk]
      _ = (k * (q ^ 2 - 2 * p ^ 2)) * q := by ring
  have hbScalar : 2 * b = k * p * q := by
    calc
      2 * b = 2 * (p * t) := by rw [ht]
      _ = p * (2 * t) := by ring
      _ = p * (q * k) := by rw [hk]
      _ = k * p * q := by ring
  have heScalar : 4 * e = k * (q ^ 2 + 2 * p ^ 2) := by
    apply mul_right_cancel₀ (ne_of_gt hq)
    calc
      (4 * e) * q = 2 * (2 * e * q) := by ring
      _ = 2 * (t * (q ^ 2 + 2 * p ^ 2)) := by
        congr 1
        apply mul_right_cancel₀ (ne_of_gt hq)
        calc
          (2 * e * q) * q = 2 * e * q ^ 2 := by ring
          _ = (e + a) * (q ^ 2 + 2 * p ^ 2) := hsecondNormalized
          _ = (t * (q ^ 2 + 2 * p ^ 2)) * q := by rw [hsum]; ring
      _ = (2 * t) * (q ^ 2 + 2 * p ^ 2) := by ring
      _ = (q * k) * (q ^ 2 + 2 * p ^ 2) := by rw [hk]
      _ = (k * (q ^ 2 + 2 * p ^ 2)) * q := by ring
  have hkFourA : k ∣ 4 * a := ⟨q ^ 2 - 2 * p ^ 2, haScalar⟩
  have hkTwoB : k ∣ 2 * b := ⟨p * q, by simpa [mul_assoc] using hbScalar⟩
  have hkFourB : k ∣ 4 * b := by
    obtain ⟨z, hz⟩ := hkTwoB
    refine ⟨2 * z, ?_⟩
    calc
      4 * b = 2 * (2 * b) := by ring
      _ = 2 * (k * z) := by rw [hz]
      _ = k * (2 * z) := by ring
  have hab' : IsCoprime a b := hab
  obtain ⟨u, v, huv⟩ := hab'
  have hkFour : k ∣ 4 := by
    obtain ⟨x, hx⟩ := hkFourA
    obtain ⟨y, hy⟩ := hkFourB
    refine ⟨u * x + v * y, ?_⟩
    calc
      4 = 4 * (u * a + v * b) := by rw [huv]; ring
      _ = u * (4 * a) + v * (4 * b) := by ring
      _ = k * (u * x + v * y) := by rw [hx, hy]; ring
  have hk0 : k ≠ 0 := by
    intro hkZero
    rw [hkZero, zero_mul, zero_mul] at hbScalar
    exact hb0 (by omega)
  obtain ⟨hrOdd, hsOdd⟩ := odd_parameters_of_eight_gcd r s hrs hgcd
  have hbFour : (4 : ℤ) ∣ b :=
    four_dvd_normalized_imaginary_coefficient r s b hrOdd hsOdd hD
  have haOdd : Odd a :=
    odd_of_isCoprime_of_four_dvd_right a b hab hbFour
  have hkCases := signed_nonzero_divisor_four k hk0 hkFour
  have hPellNotFour := pell_factor_not_dvd_four_of_coprime p q hpq
  have hcases :
      (k = -4 ∧ Odd q ∧ Even p) ∨
        (k = -2 ∧ Odd p ∧ (4 : ℤ) ∣ q) ∨
        (k = 2 ∧ Odd p ∧ (4 : ℤ) ∣ q) ∨
        (k = 4 ∧ Odd q ∧ Even p) := by
    rcases hkCases with hkNegFour | hkNegTwo | hkNegOne |
      hkOne | hkTwo | hkFourCase
    · have haEq : a = -(q ^ 2 - 2 * p ^ 2) := by
        apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
        calc
          4 * a = k * (q ^ 2 - 2 * p ^ 2) := haScalar
          _ = 4 * (-(q ^ 2 - 2 * p ^ 2)) := by rw [hkNegFour]; ring
      have hPellOdd : Odd (q ^ 2 - 2 * p ^ 2) := by
        rw [haEq] at haOdd
        simpa only [odd_neg] using haOdd
      have hqOdd := odd_second_of_odd_pell_factor p q hPellOdd
      have hbEq : b = -2 * (p * q) := by
        apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
        calc
          2 * b = k * p * q := hbScalar
          _ = 2 * (-2 * (p * q)) := by rw [hkNegFour]; ring
      have hpqEven : Even (p * q) := by
        obtain ⟨w, hw⟩ := hbFour
        refine ⟨-w, ?_⟩
        rw [hbEq] at hw
        omega
      have hpEven : Even p := by
        rcases (Int.even_mul.mp hpqEven) with hpEven | hqEven
        · exact hpEven
        · exact (Int.not_even_iff_odd.2 hqOdd hqEven).elim
      exact Or.inl ⟨hkNegFour, hqOdd, hpEven⟩
    · have htwoAEq : 2 * a = -(q ^ 2 - 2 * p ^ 2) := by
        apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
        calc
          2 * (2 * a) = 4 * a := by ring
          _ = k * (q ^ 2 - 2 * p ^ 2) := haScalar
          _ = 2 * (-(q ^ 2 - 2 * p ^ 2)) := by rw [hkNegTwo]; ring
      have hPellEven : Even (q ^ 2 - 2 * p ^ 2) := by
        refine ⟨-a, ?_⟩
        omega
      have hqEven := even_second_of_even_pell_factor p q hPellEven
      have hpOdd : Odd p :=
        odd_left_of_isCoprime_of_even_right p q hpq hqEven
      have hbEq : b = -(p * q) := by
        apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
        calc
          2 * b = k * p * q := hbScalar
          _ = 2 * (-(p * q)) := by rw [hkNegTwo]; ring
      have hfourProd : (4 : ℤ) ∣ p * q := by
        rw [hbEq] at hbFour
        simpa only [dvd_neg] using hbFour
      have hpOdd' : Odd p := hpOdd
      obtain ⟨w, hw⟩ := hpOdd'
      have htwoCoprimeP : IsCoprime (2 : ℤ) p := by
        refine ⟨-w, 1, ?_⟩
        rw [hw]
        ring
      have hfourCoprimeP : IsCoprime (4 : ℤ) p := by
        simpa using htwoCoprimeP.pow_left (m := 2)
      have hfourQ : (4 : ℤ) ∣ q :=
        hfourCoprimeP.dvd_of_dvd_mul_left hfourProd
      exact Or.inr (Or.inl ⟨hkNegTwo, hpOdd, hfourQ⟩)
    · exfalso
      apply hPellNotFour
      refine ⟨-a, ?_⟩
      rw [hkNegOne] at haScalar
      linear_combination haScalar
    · exfalso
      apply hPellNotFour
      exact ⟨a, by rw [hkOne] at haScalar; simpa using haScalar.symm⟩
    · have htwoAEq : 2 * a = q ^ 2 - 2 * p ^ 2 := by
        apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
        calc
          2 * (2 * a) = 4 * a := by ring
          _ = k * (q ^ 2 - 2 * p ^ 2) := haScalar
          _ = 2 * (q ^ 2 - 2 * p ^ 2) := by rw [hkTwo]
      have hPellEven : Even (q ^ 2 - 2 * p ^ 2) := by
        refine ⟨a, ?_⟩
        omega
      have hqEven := even_second_of_even_pell_factor p q hPellEven
      have hpOdd : Odd p :=
        odd_left_of_isCoprime_of_even_right p q hpq hqEven
      have hbEq : b = p * q := by
        apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
        calc
          2 * b = k * p * q := hbScalar
          _ = 2 * (p * q) := by rw [hkTwo]; ring
      have hfourProd : (4 : ℤ) ∣ p * q := by
        simpa [hbEq] using hbFour
      have hpOdd' : Odd p := hpOdd
      obtain ⟨w, hw⟩ := hpOdd'
      have htwoCoprimeP : IsCoprime (2 : ℤ) p := by
        refine ⟨-w, 1, ?_⟩
        rw [hw]
        ring
      have hfourCoprimeP : IsCoprime (4 : ℤ) p := by
        simpa using htwoCoprimeP.pow_left (m := 2)
      have hfourQ : (4 : ℤ) ∣ q :=
        hfourCoprimeP.dvd_of_dvd_mul_left hfourProd
      exact Or.inr (Or.inr (Or.inl ⟨hkTwo, hpOdd, hfourQ⟩))
    · have haEq : a = q ^ 2 - 2 * p ^ 2 := by
        apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
        calc
          4 * a = k * (q ^ 2 - 2 * p ^ 2) := haScalar
          _ = 4 * (q ^ 2 - 2 * p ^ 2) := by rw [hkFourCase]
      have hPellOdd : Odd (q ^ 2 - 2 * p ^ 2) := by
        rwa [← haEq]
      have hqOdd := odd_second_of_odd_pell_factor p q hPellOdd
      have hbEq : b = 2 * (p * q) := by
        apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
        calc
          2 * b = k * p * q := hbScalar
          _ = 2 * (2 * (p * q)) := by rw [hkFourCase]; ring
      have hpqEven : Even (p * q) := by
        obtain ⟨w, hw⟩ := hbFour
        refine ⟨w, ?_⟩
        rw [hbEq] at hw
        omega
      have hpEven : Even p := by
        rcases (Int.even_mul.mp hpqEven) with hpEven | hqEven
        · exact hpEven
        · exact (Int.not_even_iff_odd.2 hqOdd hqEven).elim
      exact Or.inr (Or.inr (Or.inr ⟨hkFourCase, hqOdd, hpEven⟩))
  exact ⟨a, b, e, k, hA, hB, hc, hab, hD, haScalar, hbScalar,
    heScalar, hkFour, hcases⟩

end MazurTorsion.XOneEighteenDescent
