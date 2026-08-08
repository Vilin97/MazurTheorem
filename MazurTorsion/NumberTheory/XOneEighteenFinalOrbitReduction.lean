/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuadraticNormParametrization

/-!
# The order-three orbit reduction for the final `X₁(18)` norm covers

The order-three automorphism becomes the homogeneous transformations

`(r,s,c) ↦ (-r-s, 3r-s, 8c)` and
`(r,s,c) ↦ (s-r, -3r-s, 8c)`

on the anti-diagonal sextic.  Both norm coefficients are multiplied by
eight, while the sextic is multiplied by sixty-four.  Primitive coordinates
therefore move through one opposite-parity representative and two odd
representatives in every orbit.

This file uses that covariance to reduce the gcd-eight branch to a genuine
gcd-one datum.  It keeps the sign of the square-root coordinate and the same
conic parameters `p,q`, including all three cleared conic identities.  It
does not classify the remaining gcd-one cover.
-/

namespace MazurTorsion.XOneEighteenDescent

/-! ## Homogeneous covariance -/

/-- The real norm coefficient has weight three under the first
order-three translate. -/
theorem antiDiagonalNormReal_orderThree_covariance (r s : ℤ) :
    antiDiagonalNormReal (-r - s) (3 * r - s) =
      8 * antiDiagonalNormReal r s := by
  simp only [antiDiagonalNormReal]
  ring

/-- The `√-2` norm coefficient has weight three under the first
order-three translate. -/
theorem antiDiagonalNormSqrtNegTwo_orderThree_covariance (r s : ℤ) :
    antiDiagonalNormSqrtNegTwo (-r - s) (3 * r - s) =
      8 * antiDiagonalNormSqrtNegTwo r s := by
  simp only [antiDiagonalNormSqrtNegTwo]
  ring

/-- The anti-diagonal sextic has weight six under the first order-three
translate. -/
theorem antiDiagonalSexticHom_orderThree_covariance (r s : ℤ) :
    antiDiagonalSexticHom (-r - s) (3 * r - s) =
      64 * antiDiagonalSexticHom r s := by
  simp only [antiDiagonalSexticHom]
  ring

/-- The cubic cusp product is multiplied by eight under the first
order-three translate. -/
theorem antiDiagonalCuspProduct_orderThree_covariance (r s : ℤ) :
    (-r - s) * ((-r - s) ^ 2 - (3 * r - s) ^ 2) =
      8 * (r * (r ^ 2 - s ^ 2)) := by
  ring

/-- A sign-compatible primitive representative of the second translate
also multiplies the real norm coefficient by eight. -/
theorem antiDiagonalNormReal_orderThree_sq_covariance (r s : ℤ) :
    antiDiagonalNormReal (s - r) (-3 * r - s) =
      8 * antiDiagonalNormReal r s := by
  simp only [antiDiagonalNormReal]
  ring

/-- A sign-compatible primitive representative of the second translate
also multiplies the `√-2` coefficient by eight. -/
theorem antiDiagonalNormSqrtNegTwo_orderThree_sq_covariance (r s : ℤ) :
    antiDiagonalNormSqrtNegTwo (s - r) (-3 * r - s) =
      8 * antiDiagonalNormSqrtNegTwo r s := by
  simp only [antiDiagonalNormSqrtNegTwo]
  ring

/-- The anti-diagonal sextic is multiplied by sixty-four under the second
translate. -/
theorem antiDiagonalSexticHom_orderThree_sq_covariance (r s : ℤ) :
    antiDiagonalSexticHom (s - r) (-3 * r - s) =
      64 * antiDiagonalSexticHom r s := by
  simp only [antiDiagonalSexticHom]
  ring

/-- The cubic cusp product is multiplied by eight under the second
translate. -/
theorem antiDiagonalCuspProduct_orderThree_sq_covariance (r s : ℤ) :
    (s - r) * ((s - r) ^ 2 - (-3 * r - s) ^ 2) =
      8 * (r * (r ^ 2 - s ^ 2)) := by
  ring

private theorem antiDiagonalNormReal_scale_four (r s : ℤ) :
    antiDiagonalNormReal (4 * r) (4 * s) =
      64 * antiDiagonalNormReal r s := by
  simp only [antiDiagonalNormReal]
  ring

private theorem antiDiagonalNormSqrtNegTwo_scale_four (r s : ℤ) :
    antiDiagonalNormSqrtNegTwo (4 * r) (4 * s) =
      64 * antiDiagonalNormSqrtNegTwo r s := by
  simp only [antiDiagonalNormSqrtNegTwo]
  ring

/-! ## Primitive normalization -/

private lemma primitive_even_real_forces_both_odd_mod_two :
    ∀ r s : ZMod 2,
      r ^ 3 + 9 * r ^ 2 * s - r * s ^ 2 - s ^ 3 = 0 →
      (r ≠ 0 ∨ s ≠ 0) →
      r = 1 ∧ s = 1 := by
  decide

private theorem odd_parameters_of_exact_eight_gcd
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
  have hlocal := primitive_even_real_forces_both_odd_mod_two
    (r : ZMod 2) (s : ZMod 2) (by
      norm_num [antiDiagonalNormReal] at hrealZero ⊢
      exact hrealZero) hrsMod.ne_zero_or_ne_zero
  exact ⟨ZMod.intCast_eq_one_iff_odd.mp hlocal.1,
    ZMod.intCast_eq_one_iff_odd.mp hlocal.2⟩

private lemma odd_unequal_neg_sum_zero_mod_four :
    ∀ r s : ZMod 4,
      (ZMod.cast r : ZMod 2) = 1 →
      (ZMod.cast s : ZMod 2) = 1 →
      r ≠ s →
      -r - s = 0 := by
  decide

private theorem exists_eight_factor_of_exact_eight_norm
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

private theorem scaled_conic_reduction
    {r s c p q R S C : ℤ}
    (hgcd : (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8)
    (hA : antiDiagonalNormReal r s =
      8 * antiDiagonalNormReal R S)
    (hB : antiDiagonalNormSqrtNegTwo r s =
      8 * antiDiagonalNormSqrtNegTwo R S)
    (hc : c = 8 * C)
    (htangent : c + antiDiagonalNormReal r s ≠ 0)
    (hnorm : antiDiagonalNormReal r s ^ 2 +
      2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2)
    (hlinear : antiDiagonalNormSqrtNegTwo r s * q =
      p * (c + antiDiagonalNormReal r s))
    (hfirst : 2 * antiDiagonalNormReal r s * q ^ 2 =
      (c + antiDiagonalNormReal r s) * (q ^ 2 - 2 * p ^ 2))
    (hsecond : 2 * c * q ^ 2 =
      (c + antiDiagonalNormReal r s) * (q ^ 2 + 2 * p ^ 2)) :
    (GCDMonoid.gcd (antiDiagonalNormReal R S)
        (antiDiagonalNormSqrtNegTwo R S) : ℤ) = 1 ∧
      C + antiDiagonalNormReal R S ≠ 0 ∧
      antiDiagonalNormReal R S ^ 2 +
        2 * antiDiagonalNormSqrtNegTwo R S ^ 2 = C ^ 2 ∧
      antiDiagonalNormSqrtNegTwo R S * q =
        p * (C + antiDiagonalNormReal R S) ∧
      2 * antiDiagonalNormReal R S * q ^ 2 =
        (C + antiDiagonalNormReal R S) * (q ^ 2 - 2 * p ^ 2) ∧
      2 * C * q ^ 2 =
        (C + antiDiagonalNormReal R S) * (q ^ 2 + 2 * p ^ 2) := by
  have hgcdScaled := hgcd
  rw [hA, hB, gcd_mul_left] at hgcdScaled
  have hgcdOne :
      (GCDMonoid.gcd (antiDiagonalNormReal R S)
        (antiDiagonalNormSqrtNegTwo R S) : ℤ) = 1 := by
    rw [Int.normalize_of_nonneg (by norm_num : (0 : ℤ) ≤ 8)] at hgcdScaled
    omega
  have htangent' : C + antiDiagonalNormReal R S ≠ 0 := by
    intro hzero
    apply htangent
    rw [hA, hc]
    linear_combination 8 * hzero
  have hnorm' : antiDiagonalNormReal R S ^ 2 +
      2 * antiDiagonalNormSqrtNegTwo R S ^ 2 = C ^ 2 := by
    rw [hA, hB, hc] at hnorm
    nlinarith
  have hlinear' : antiDiagonalNormSqrtNegTwo R S * q =
      p * (C + antiDiagonalNormReal R S) := by
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    calc
      8 * (antiDiagonalNormSqrtNegTwo R S * q) =
          (8 * antiDiagonalNormSqrtNegTwo R S) * q := by ring
      _ = p * (8 * C + 8 * antiDiagonalNormReal R S) := by
        rw [← hB, ← hc, ← hA]
        exact hlinear
      _ = 8 * (p * (C + antiDiagonalNormReal R S)) := by ring
  have hfirst' : 2 * antiDiagonalNormReal R S * q ^ 2 =
      (C + antiDiagonalNormReal R S) * (q ^ 2 - 2 * p ^ 2) := by
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    calc
      8 * (2 * antiDiagonalNormReal R S * q ^ 2) =
          2 * (8 * antiDiagonalNormReal R S) * q ^ 2 := by ring
      _ = (8 * C + 8 * antiDiagonalNormReal R S) *
          (q ^ 2 - 2 * p ^ 2) := by
        rw [← hA, ← hc]
        exact hfirst
      _ = 8 * ((C + antiDiagonalNormReal R S) *
          (q ^ 2 - 2 * p ^ 2)) := by ring
  have hsecond' : 2 * C * q ^ 2 =
      (C + antiDiagonalNormReal R S) * (q ^ 2 + 2 * p ^ 2) := by
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    calc
      8 * (2 * C * q ^ 2) = 2 * (8 * C) * q ^ 2 := by ring
      _ = (8 * C + 8 * antiDiagonalNormReal R S) *
          (q ^ 2 + 2 * p ^ 2) := by
        rw [← hc, ← hA]
        exact hsecond
      _ = 8 * ((C + antiDiagonalNormReal R S) *
          (q ^ 2 + 2 * p ^ 2)) := by ring
  exact ⟨hgcdOne, htangent', hnorm', hlinear', hfirst', hsecond'⟩

/-! ## The gcd-eight-to-gcd-one orbit reduction -/

/-- Every primitive gcd-eight norm datum has a primitive gcd-one
order-three translate.  The branch certificate records whether the first
or second translate was divided by four.  The square root is divided by
eight with its sign preserved, and the same primitive conic coordinates
`p,q` satisfy all three cleared identities on the reduced datum.

This is an equivalence between the two integral models of the remaining
cover, not a classification of that cover. -/
theorem exists_coprime_orderThreeOrbit_of_eight
    (r s c p q : ℤ)
    (hrs : IsCoprime r s)
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
    ∃ R S C : ℤ,
      IsCoprime R S ∧
      (((r : ZMod 4) = (s : ZMod 4) ∧
          s - r = 4 * R ∧ -3 * r - s = 4 * S) ∨
        ((r : ZMod 4) ≠ (s : ZMod 4) ∧
          -r - s = 4 * R ∧ 3 * r - s = 4 * S)) ∧
      antiDiagonalNormReal r s = 8 * antiDiagonalNormReal R S ∧
      antiDiagonalNormSqrtNegTwo r s =
        8 * antiDiagonalNormSqrtNegTwo R S ∧
      c = 8 * C ∧
      (GCDMonoid.gcd (antiDiagonalNormReal R S)
          (antiDiagonalNormSqrtNegTwo R S) : ℤ) = 1 ∧
      C + antiDiagonalNormReal R S ≠ 0 ∧
      antiDiagonalNormReal R S ^ 2 +
        2 * antiDiagonalNormSqrtNegTwo R S ^ 2 = C ^ 2 ∧
      antiDiagonalNormSqrtNegTwo R S * q =
        p * (C + antiDiagonalNormReal R S) ∧
      2 * antiDiagonalNormReal R S * q ^ 2 =
        (C + antiDiagonalNormReal R S) * (q ^ 2 - 2 * p ^ 2) ∧
      2 * C * q ^ 2 =
        (C + antiDiagonalNormReal R S) * (q ^ 2 + 2 * p ^ 2) := by
  obtain ⟨hrOdd, hsOdd⟩ :=
    odd_parameters_of_exact_eight_gcd r s hrs hgcd
  obtain ⟨C, hc⟩ :=
    exists_eight_factor_of_exact_eight_norm r s c hgcd hnorm
  by_cases hmod : (r : ZMod 4) = (s : ZMod 4)
  · have hfour : (4 : ℤ) ∣ s - r :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub r s 4).mp hmod
    obtain ⟨R, hR⟩ := hfour
    let S : ℤ := -r - R
    have hS : -3 * r - s = 4 * S := by
      dsimp [S]
      omega
    have hrInv : r = -R - S := by
      dsimp [S]
      ring
    have hsInv : s = 3 * R - S := by
      dsimp [S]
      omega
    have hRS : IsCoprime R S := by
      obtain ⟨u, v, huv⟩ := hrs
      refine ⟨-u + 3 * v, -u - v, ?_⟩
      rw [hrInv, hsInv] at huv
      linear_combination huv
    have hcovA := antiDiagonalNormReal_orderThree_sq_covariance r s
    rw [hR, hS, antiDiagonalNormReal_scale_four] at hcovA
    have hA : antiDiagonalNormReal r s =
        8 * antiDiagonalNormReal R S := by
      omega
    have hcovB := antiDiagonalNormSqrtNegTwo_orderThree_sq_covariance r s
    rw [hR, hS, antiDiagonalNormSqrtNegTwo_scale_four] at hcovB
    have hB : antiDiagonalNormSqrtNegTwo r s =
        8 * antiDiagonalNormSqrtNegTwo R S := by
      omega
    obtain ⟨hgcdOne, htangent', hnorm', hlinear', hfirst', hsecond'⟩ :=
      scaled_conic_reduction hgcd hA hB hc htangent hnorm
        hlinear hfirst hsecond
    exact ⟨R, S, C, hRS, Or.inl ⟨hmod, hR, hS⟩,
      hA, hB, hc, hgcdOne, htangent', hnorm', hlinear', hfirst', hsecond'⟩
  · have hrFour :
        (ZMod.cast (r : ZMod 4) : ZMod 2) = 1 := by
      rw [ZMod.cast_intCast (R := ZMod 2)
        (by norm_num : 2 ∣ 4) r]
      exact ZMod.intCast_eq_one_iff_odd.2 hrOdd
    have hsFour :
        (ZMod.cast (s : ZMod 4) : ZMod 2) = 1 := by
      rw [ZMod.cast_intCast (R := ZMod 2)
        (by norm_num : 2 ∣ 4) s]
      exact ZMod.intCast_eq_one_iff_odd.2 hsOdd
    have hzero := odd_unequal_neg_sum_zero_mod_four
      (r : ZMod 4) (s : ZMod 4) hrFour hsFour hmod
    have hfour : (4 : ℤ) ∣ -r - s := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (-r - s) 4).mp
      norm_num at hzero ⊢
      exact hzero
    obtain ⟨R, hR⟩ := hfour
    let S : ℤ := r + R
    have hS : 3 * r - s = 4 * S := by
      dsimp [S]
      omega
    have hrInv : r = S - R := by
      dsimp [S]
      ring
    have hsInv : s = -S - 3 * R := by
      dsimp [S]
      omega
    have hRS : IsCoprime R S := by
      obtain ⟨u, v, huv⟩ := hrs
      refine ⟨-u - 3 * v, u - v, ?_⟩
      rw [hrInv, hsInv] at huv
      linear_combination huv
    have hcovA := antiDiagonalNormReal_orderThree_covariance r s
    rw [hR, hS, antiDiagonalNormReal_scale_four] at hcovA
    have hA : antiDiagonalNormReal r s =
        8 * antiDiagonalNormReal R S := by
      omega
    have hcovB := antiDiagonalNormSqrtNegTwo_orderThree_covariance r s
    rw [hR, hS, antiDiagonalNormSqrtNegTwo_scale_four] at hcovB
    have hB : antiDiagonalNormSqrtNegTwo r s =
        8 * antiDiagonalNormSqrtNegTwo R S := by
      omega
    obtain ⟨hgcdOne, htangent', hnorm', hlinear', hfirst', hsecond'⟩ :=
      scaled_conic_reduction hgcd hA hB hc htangent hnorm
        hlinear hfirst hsecond
    exact ⟨R, S, C, hRS, Or.inr ⟨hmod, hR, hS⟩,
      hA, hB, hc, hgcdOne, htangent', hnorm', hlinear', hfirst', hsecond'⟩

end MazurTorsion.XOneEighteenDescent
