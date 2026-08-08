/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuadraticNormParametrization

/-!
# The finite-scalar gcd-one cover for `X₁(18)`

In the gcd-one branch of the quadratic-norm parametrization, the cubic
coefficient

`D = r * (r ^ 2 - s ^ 2)`

splits as `d₁ * d₂`, with `d₁` supported on `p` and `d₂` supported
on `q`.  Writing `p = d₁ * u` and `q = d₂ * v` and cancelling the
nonzero coefficient `D` gives one normalized quadratic equation.  The
primitivity of `p,q` then forces the residual scalars to satisfy `u ∣ 2`
and `v ∣ 4`.

This is a finite-scalar reduction of the gcd-one cover.  It does not by
itself classify the remaining integral points.
-/

namespace MazurTorsion.XOneEighteenDescent

private theorem signed_nonzero_divisor_two
    (k : ℤ) (hk0 : k ≠ 0) (hk : k ∣ 2) :
    k = -2 ∨ k = -1 ∨ k = 1 ∨ k = 2 := by
  have hkAbsDvd : k.natAbs ∣ 2 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hk
  have hkAbsPos : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
  have hkAbsUpper : k.natAbs ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hkAbsDvd
  have hkAbs : k.natAbs = 1 ∨ k.natAbs = 2 := by
    interval_cases h : k.natAbs <;> norm_num at *
  rcases hkAbs with hkAbs | hkAbs
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

/-- The gcd-one norm branch has only a divisor of two and a divisor of four
left after its two coprime support factors are removed.

The two displayed coprimality statements are retained in the output because
they are the exact facts used to remove the square factors in the proof and
are useful to downstream refinements of the finite cover. -/
theorem antiDiagonalNormParametric_coprime_finiteScalarCover
    (r s p q : ℤ) (hpq : IsCoprime p q)
    (hgcd : (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1)
    (hform : antiDiagonalNormParametricBidegreeForm r s p q = 0)
    (hD : r * (r ^ 2 - s ^ 2) ≠ 0) :
    ∃ d₁ d₂ u v : ℤ,
      p = d₁ * u ∧
      q = d₂ * v ∧
      r * (r ^ 2 - s ^ 2) = d₁ * d₂ ∧
      IsCoprime d₁ d₂ ∧
      IsCoprime u (d₂ * v) ∧
      IsCoprime v (d₁ * u) ∧
      antiDiagonalNormReal r s * u * v +
          2 * d₂ ^ 2 * v ^ 2 - 4 * d₁ ^ 2 * u ^ 2 = 0 ∧
      u ∣ 2 ∧
      v ∣ 4 := by
  obtain ⟨_, d₁, d₂, hd₁, hd₂, hsplit, hd₁d₂⟩ :=
    antiDiagonalNormParametric_coprime_cover
      r s p q hpq hgcd hform
  obtain ⟨u, hp⟩ := hd₁
  obtain ⟨v, hq⟩ := hd₂
  have huP : u ∣ p := by
    refine ⟨d₁, ?_⟩
    rw [hp]
    ring
  have hvQ : v ∣ q := by
    refine ⟨d₂, ?_⟩
    rw [hq]
    ring
  have huCoprime : IsCoprime u (d₂ * v) := by
    apply hpq.mono huP
    simp [hq]
  have hvCoprime : IsCoprime v (d₁ * u) := by
    apply hpq.symm.mono hvQ
    simp [hp]
  have hd₁d₂Ne : d₁ * d₂ ≠ 0 := by
    rw [← hsplit]
    exact hD
  have hnormalized :
      antiDiagonalNormReal r s * u * v +
          2 * d₂ ^ 2 * v ^ 2 - 4 * d₁ ^ 2 * u ^ 2 = 0 := by
    apply mul_left_cancel₀ hd₁d₂Ne
    simp only [mul_zero]
    simp only [antiDiagonalNormParametricBidegreeForm] at hform
    rw [hp, hq, show 2 * r * (r ^ 2 - s ^ 2) =
      2 * (d₁ * d₂) by rw [← hsplit]; ring] at hform
    linear_combination hform
  have huDiv : u ∣ 2 * (d₂ * v) ^ 2 := by
    refine ⟨4 * d₁ ^ 2 * u - antiDiagonalNormReal r s * v, ?_⟩
    linear_combination hnormalized
  have hvDiv : v ∣ 4 * (d₁ * u) ^ 2 := by
    refine ⟨antiDiagonalNormReal r s * u + 2 * d₂ ^ 2 * v, ?_⟩
    linear_combination -hnormalized
  have huTwo : u ∣ 2 :=
    huCoprime.pow_right.dvd_of_dvd_mul_right huDiv
  have hvFour : v ∣ 4 :=
    hvCoprime.pow_right.dvd_of_dvd_mul_right hvDiv
  exact ⟨d₁, d₂, u, v, hp, hq, hsplit, hd₁d₂,
    huCoprime, hvCoprime, hnormalized, huTwo, hvFour⟩

/-- In the gcd-one branch the residual divisors are not merely bounded:
their absolute values are exactly `(2,1)` or `(1,4)`.  Keeping their signs
gives one of two signed Pell-type covers.  The equations `u * v = -2 * ε`
and `u * v = 4 * ε` record, without a hidden choice of signs, which of the
two signs occurs in the corresponding Pell equation. -/
theorem antiDiagonalNormParametric_coprime_signedPellCover
    (r s p q : ℤ) (hpq : IsCoprime p q)
    (hgcd : (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1)
    (hform : antiDiagonalNormParametricBidegreeForm r s p q = 0)
    (hD : r * (r ^ 2 - s ^ 2) ≠ 0) :
    ∃ d₁ d₂ u v ε : ℤ,
      p = d₁ * u ∧
      q = d₂ * v ∧
      r * (r ^ 2 - s ^ 2) = d₁ * d₂ ∧
      IsCoprime d₁ d₂ ∧
      IsCoprime u (d₂ * v) ∧
      IsCoprime v (d₁ * u) ∧
      (ε = -1 ∨ ε = 1) ∧
      (((u = -2 ∨ u = 2) ∧
          (v = -1 ∨ v = 1) ∧
          u * v = -2 * ε ∧
          d₂ ^ 2 - 8 * d₁ ^ 2 = ε * antiDiagonalNormReal r s) ∨
        ((u = -1 ∨ u = 1) ∧
          (v = -4 ∨ v = 4) ∧
          u * v = 4 * ε ∧
          d₁ ^ 2 - 8 * d₂ ^ 2 = ε * antiDiagonalNormReal r s)) := by
  obtain ⟨d₁, d₂, u, v, hp, hq, hsplit, hd₁d₂,
      huCoprime, hvCoprime, hnormalized, huTwo, hvFour⟩ :=
    antiDiagonalNormParametric_coprime_finiteScalarCover
      r s p q hpq hgcd hform hD
  have huNe : u ≠ 0 := by
    intro hu
    subst u
    norm_num at huTwo
  have hvNe : v ≠ 0 := by
    intro hv
    subst v
    norm_num at hvFour
  have hcoprimeAB :
      IsCoprime (antiDiagonalNormReal r s)
        (antiDiagonalNormSqrtNegTwo r s) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    have h := congrArg Int.natAbs hgcd
    simpa only [Int.natAbs_gcd, Int.natAbs_one] using h
  have htwoDvdB : (2 : ℤ) ∣ antiDiagonalNormSqrtNegTwo r s := by
    refine ⟨-2 * r * (r ^ 2 - s ^ 2), ?_⟩
    simp only [antiDiagonalNormSqrtNegTwo]
    ring
  have hrealCoprimeTwo : IsCoprime (antiDiagonalNormReal r s) (2 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right hcoprimeAB htwoDvdB
  have hrealOdd : Odd (antiDiagonalNormReal r s) :=
    Int.isCoprime_two_right.mp hrealCoprimeTwo
  have hrealProductEven :
      Even (antiDiagonalNormReal r s * (u * v)) := by
    refine ⟨2 * d₁ ^ 2 * u ^ 2 - d₂ ^ 2 * v ^ 2, ?_⟩
    linear_combination hnormalized
  have huvEven : Even (u * v) := by
    by_contra huvNotEven
    have huvOdd : Odd (u * v) :=
      Int.not_even_iff_odd.mp huvNotEven
    have hproductOdd : Odd (antiDiagonalNormReal r s * (u * v)) :=
      Int.odd_mul.mpr ⟨hrealOdd, huvOdd⟩
    exact Int.not_even_iff_odd.mpr hproductOdd hrealProductEven
  have huvCoprime : IsCoprime u v :=
    IsCoprime.of_isCoprime_of_dvd_right huCoprime (dvd_mul_left v d₂)
  have huvNotBothEven : ¬(Even u ∧ Even v) := by
    rintro ⟨huEven, hvEven⟩
    have hunit : IsUnit (2 : ℤ) :=
      huvCoprime.isUnit_of_dvd'
        (even_iff_two_dvd.mp huEven) (even_iff_two_dvd.mp hvEven)
    exact absurd (Int.isUnit_iff.mp hunit) (by norm_num)
  have huCases := signed_nonzero_divisor_two u huNe huTwo
  have hvCases := signed_nonzero_divisor_four v hvNe hvFour
  obtain ⟨realHalf, hrealEq⟩ := hrealOdd
  have hscalars :
      (((u = -2 ∨ u = 2) ∧ (v = -1 ∨ v = 1)) ∨
        ((u = -1 ∨ u = 1) ∧ (v = -4 ∨ v = 4))) := by
    rcases huCases with rfl | rfl | rfl | rfl <;>
      rcases hvCases with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num at hnormalized
    all_goals norm_num at huvEven
    all_goals norm_num at huvNotBothEven
    all_goals norm_num
    all_goals omega
  rcases hscalars with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · refine ⟨d₁, d₂, -2, -1, -1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inl ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega
    · refine ⟨d₁, d₂, -2, 1, 1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inl ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega
    · refine ⟨d₁, d₂, 2, -1, 1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inl ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega
    · refine ⟨d₁, d₂, 2, 1, -1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inl ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega
  · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · refine ⟨d₁, d₂, -1, -4, 1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inr ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega
    · refine ⟨d₁, d₂, -1, 4, -1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inr ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega
    · refine ⟨d₁, d₂, 1, -4, -1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inr ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega
    · refine ⟨d₁, d₂, 1, 4, 1, hp, hq, hsplit, hd₁d₂,
        huCoprime, hvCoprime, by norm_num, Or.inr ?_⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      norm_num at hnormalized ⊢
      omega

/-- Forgetting which conic coordinate received which factor, every gcd-one
point lies on one of the two signed Pell equations `a² - 8b² = ±A`, with
the cubic coefficient still split as the coprime product `a*b`. -/
theorem antiDiagonalNormParametric_coprime_signedPellCover_compressed
    (r s p q : ℤ) (hpq : IsCoprime p q)
    (hgcd : (GCDMonoid.gcd (antiDiagonalNormReal r s)
      (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1)
    (hform : antiDiagonalNormParametricBidegreeForm r s p q = 0)
    (hD : r * (r ^ 2 - s ^ 2) ≠ 0) :
    ∃ a b ε : ℤ,
      IsCoprime a b ∧
      r * (r ^ 2 - s ^ 2) = a * b ∧
      (ε = -1 ∨ ε = 1) ∧
      a ^ 2 - 8 * b ^ 2 = ε * antiDiagonalNormReal r s := by
  obtain ⟨d₁, d₂, u, v, ε, -, -, hsplit, hd₁d₂, -, -, hε,
      hfirst | hsecond⟩ :=
    antiDiagonalNormParametric_coprime_signedPellCover
      r s p q hpq hgcd hform hD
  · exact ⟨d₂, d₁, ε, hd₁d₂.symm, by simpa [mul_comm] using hsplit,
      hε, hfirst.2.2.2⟩
  · exact ⟨d₁, d₂, ε, hd₁d₂, hsplit, hε, hsecond.2.2.2⟩

end MazurTorsion.XOneEighteenDescent
