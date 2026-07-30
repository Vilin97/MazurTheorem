/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import MazurTorsion.Foundations.FullFourTorsion
import MazurTorsion.GroupTheory.ForbiddenEmbeddings
import MazurTorsion.Kubert.TateNormalForm
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The direct two-by-ten obstruction

This file carries the exceptional subgroup `ZMod 2 × ZMod 10` from the group law on a rational
elliptic curve to one explicit Diophantine endpoint.  A point of order five is put into Tate normal
form

`y² + (1-c)xy - cy = x³ - cx²`.

Full rational two-torsion makes the Weierstrass discriminant a square.  Since the Tate-form
discriminant is `c⁵(c² - 11c - 1)`, clearing denominators reduces the obstruction to the quartic

`e² = X⁴ - 11X²Y² - Y⁴`

for coprime nonzero integers `X` and `Y`.  The public predicate `NoExceptionalQuartic` states
precisely this remaining infinite-descent input.  The final theorem proves the forbidden embedding
conditionally on that single arithmetic statement; all geometric, group-theoretic, denominator,
sign, and coprimality reductions are completed here.

The Tate-normal-form formulas are the classical Kubert formulas.  The coordinate-change and
three-root cubic infrastructure used below is supplied by the project's Apache-licensed elliptic
curve foundations.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion
namespace ExceptionalTwoTen

/-- The order-five diagonal in the Tate-normal-form family. -/
def tateFiveCurve (c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalCurve c c

@[simp] lemma tateFiveCurve_a₁ (c : ℚ) : (tateFiveCurve c).a₁ = 1 - c := rfl
@[simp] lemma tateFiveCurve_a₂ (c : ℚ) : (tateFiveCurve c).a₂ = -c := rfl
@[simp] lemma tateFiveCurve_a₃ (c : ℚ) : (tateFiveCurve c).a₃ = -c := rfl
@[simp] lemma tateFiveCurve_a₄ (c : ℚ) : (tateFiveCurve c).a₄ = 0 := rfl
@[simp] lemma tateFiveCurve_a₆ (c : ℚ) : (tateFiveCurve c).a₆ = 0 := rfl

/-- The cubic whose roots are the abscissae of the nonzero two-torsion. -/
def twoDivisionCubic (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

/-- Explicit two-division cubic of the order-five Tate family. -/
lemma twoDivisionCubic_tateFiveCurve (c x : ℚ) :
    twoDivisionCubic (tateFiveCurve c) x =
      4 * x ^ 3 + (c ^ 2 - 6 * c + 1) * x ^ 2 +
        2 * (c ^ 2 - c) * x + c ^ 2 := by
  simp only [twoDivisionCubic, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, tateFiveCurve_a₁, tateFiveCurve_a₂,
    tateFiveCurve_a₃, tateFiveCurve_a₄, tateFiveCurve_a₆]
  ring

/-- Discriminant of the order-five Tate family. -/
lemma tateFiveCurve_discriminant (c : ℚ) :
    (tateFiveCurve c).Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  simp only [tateFiveCurve, tateNormalCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Exact order five forces the two Tate parameters to coincide. -/
lemma tateNormalCurve_parameters_eq_of_order_five
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5) :
    b = c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  obtain ⟨hns₂, hdouble⟩ := two_mul_origin_coordinates b c hb h00
  obtain ⟨hns₃, htriple⟩ := three_mul_origin_coordinates b c hb h00
  have hfive : (5 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hsum : P + P + P + (P + P) = 0 := by
    rw [← hfive]
    abel
  rw [htriple, hdouble, add_eq_zero_iff_eq_neg,
    WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hsum
  exact hsum.1.symm

/-- A rational point of exact order five produces a nonzero diagonal Tate
parameter and an explicit twelfth-power discriminant scaling. -/
theorem exists_tateFive_discriminant_of_order_five
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 5) :
    ∃ c u : ℚ, u ≠ 0 ∧ c ≠ 0 ∧
      u ^ 12 * E.Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  have hQ3 : Q + Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        have hthree : (3 : ℕ) • Q = Q + Q + Q := by abel
        rw [hthree]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) Q hQ2 hQ3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hbc : b = c :=
    tateNormalCurve_parameters_eq_of_order_five b c hb h00 hmarked
  subst c
  refine ⟨b, u, hu, hb, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rw [← hbase, hdisc]
  exact tateFiveCurve_discriminant b

/-- The single Diophantine leaf needed by the direct exceptional
`ZMod 2 × ZMod 10` obstruction. -/
def NoExceptionalQuartic : Prop :=
  ∀ {X Y e : ℤ}, IsCoprime X Y → X ≠ 0 → Y ≠ 0 →
    e ^ 2 ≠ X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4

/-- Assuming the quartic leaf, a coprime product in the conductor-twenty
two-descent cannot be a square. -/
theorem not_isSquare_coprime_product
    (hquartic : NoExceptionalQuartic) {m n : ℤ}
    (hmn : IsCoprime m n) (hm : m ≠ 0) (hn : 0 < n) :
    ¬ IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2)) := by
  intro hsq
  set k : ℤ := m ^ 2 - 11 * m * n - n ^ 2 with hkdef
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hkdef] at hk
    have hA : (2 * m - 11 * n) ^ 2 = 125 * n ^ 2 := by
      linear_combination 4 * hk
    obtain ⟨A₁, hA₁⟩ : (5 : ℤ) ∣ (2 * m - 11 * n) := by
      apply Int.Prime.dvd_pow' (k := 2) (by decide : Nat.Prime 5)
      refine ⟨25 * n ^ 2, ?_⟩
      push_cast
      linear_combination hA
    have hA₁sq : A₁ ^ 2 = 5 * n ^ 2 := by
      have h25 : (25 : ℤ) * A₁ ^ 2 = 25 * (5 * n ^ 2) := by
        linear_combination hA - (2 * m - 11 * n + 5 * A₁) * hA₁
      linarith
    obtain ⟨A₂, hA₂⟩ : (5 : ℤ) ∣ A₁ := by
      apply Int.Prime.dvd_pow' (k := 2) (by decide : Nat.Prime 5)
      refine ⟨n ^ 2, ?_⟩
      push_cast
      linear_combination hA₁sq
    have hnsq : n ^ 2 = 5 * A₂ ^ 2 := by
      have h5 : (5 : ℤ) * n ^ 2 = 5 * (5 * A₂ ^ 2) := by
        linear_combination -hA₁sq + (A₁ + 5 * A₂) * hA₂
      linarith
    have hfive_n : (5 : ℤ) ∣ n := by
      apply Int.Prime.dvd_pow' (k := 2) (by decide : Nat.Prime 5)
      refine ⟨A₂ ^ 2, ?_⟩
      push_cast
      linear_combination hnsq
    obtain ⟨n₁, hn₁⟩ := id hfive_n
    have hm5 : (5 : ℤ) ∣ m := by
      have h2m : (5 : ℤ) ∣ 2 * m :=
        ⟨A₁ + 11 * n₁, by linear_combination hA₁ + 11 * hn₁⟩
      rcases Int.Prime.dvd_mul' (by decide : Nat.Prime 5) h2m with h5two | h5m
      · norm_num at h5two
      · push_cast at h5m
        exact h5m
    exact absurd (Int.isUnit_iff.mp (hmn.isUnit_of_dvd' hm5 hfive_n)) (by norm_num)
  have hmk : IsCoprime m k := by
    have h := ((hmn.pow_right (n := 2)).neg_right).add_mul_left_right (m - 11 * n)
    have heq : -n ^ 2 + m * (m - 11 * n) = k := by
      rw [hkdef]
      ring
    rwa [heq] at h
  have hnk : IsCoprime n k := by
    have h := (hmn.symm.pow_right (n := 2)).add_mul_left_right (-(11 * m) - n)
    have heq : m ^ 2 + n * (-(11 * m) - n) = k := by
      rw [hkdef]
      ring
    rwa [heq] at h
  obtain ⟨s, hs⟩ := hsq
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b ^ 2 ∨ n = -b ^ 2 :=
    Int.sq_of_isCoprime (hmn.symm.mul_right hnk) (c := s)
      (by linear_combination hs)
  obtain ⟨a, ha⟩ : ∃ a : ℤ, m = a ^ 2 ∨ m = -a ^ 2 :=
    Int.sq_of_isCoprime (hmn.mul_right hmk) (c := s)
      (by linear_combination hs)
  obtain ⟨e, he⟩ : ∃ e : ℤ, k = e ^ 2 ∨ k = -e ^ 2 :=
    Int.sq_of_isCoprime (hmk.symm.mul_right hnk.symm) (c := s)
      (by linear_combination hs)
  have hbn : n = b ^ 2 := by
    rcases hb with hb | hb
    · exact hb
    · exfalso
      linarith [sq_nonneg b]
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb] at hbn
    norm_num at hbn
    linarith
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    apply hm
    rcases ha with ha | ha <;> simpa using ha
  have hprod : 0 < m * n * k := by
    refine lt_of_le_of_ne ?_ (Ne.symm (mul_ne_zero (mul_ne_zero hm hn.ne') hk0))
    rw [hs]
    exact mul_self_nonneg s
  have hmkpos : 0 < m * k := by
    by_contra h
    have hnonpos : m * k ≤ 0 := not_lt.mp h
    have : m * k * n ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hnonpos, hn.le⟩)
    linarith
  have hab : IsCoprime a b := by
    have hsquares : IsCoprime (a ^ 2) (b ^ 2) := by
      rcases ha with ha | ha
      · rw [← ha, ← hbn]
        exact hmn
      · have hneg : IsCoprime (-(a ^ 2)) (b ^ 2) := by
          rw [← ha, ← hbn]
          exact hmn
        simpa using hneg.neg_left
    have ha_dvd : a ∣ a ^ 2 := dvd_pow_self a (by norm_num)
    have hb_dvd : b ∣ b ^ 2 := dvd_pow_self b (by norm_num)
    have hba_sq : IsCoprime (b ^ 2) a :=
      (hsquares.of_isCoprime_of_dvd_left ha_dvd).symm
    have hba : IsCoprime b a := hba_sq.of_isCoprime_of_dvd_left hb_dvd
    exact hba.symm
  rcases ha with hma | hma <;> rcases he with hke | hke
  · have hq : e ^ 2 = a ^ 4 - 11 * a ^ 2 * b ^ 2 - b ^ 4 := by
      rw [← hke, hkdef, hma, hbn]
      ring
    exact hquartic hab ha0 hb0 hq
  · rw [hma, hke] at hmkpos
    nlinarith [sq_nonneg a, sq_nonneg e]
  · rw [hma, hke] at hmkpos
    nlinarith [sq_nonneg a, sq_nonneg e]
  · have hq0 : -e ^ 2 = a ^ 4 + 11 * a ^ 2 * b ^ 2 - b ^ 4 := by
      rw [← hke, hkdef, hma, hbn]
      ring
    have hq : e ^ 2 = b ^ 4 - 11 * b ^ 2 * a ^ 2 - a ^ 4 := by
      linarith
    exact hquartic hab.symm hb0 ha0 hq

/-- Clearing denominators turns a nonzero rational point on
`v² = c³ - 11c² - c` into the integral product certificate. -/
lemma integral_certificate_of_rational_solution
    {c v : ℚ} (hcurve : v ^ 2 = c ^ 3 - 11 * c ^ 2 - c) :
    IsSquare
      (c.num * (c.den : ℤ) *
        (c.num ^ 2 - 11 * c.num * (c.den : ℤ) - (c.den : ℤ) ^ 2)) := by
  rw [← Rat.isSquare_intCast_iff]
  refine ⟨v * (c.den : ℚ) ^ 2, ?_⟩
  have hden : ((c.den : ℚ)) ≠ 0 := by
    exact_mod_cast c.den_ne_zero
  have hnum : (c.num : ℚ) = c * (c.den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den c)
  push_cast
  rw [hnum]
  linear_combination -((c.den : ℚ)) ^ 4 * hcurve

/-- The exceptional quartic leaf rules out all nonzero rational points on
the conductor-twenty curve. -/
theorem no_rational_solution
    (hquartic : NoExceptionalQuartic) {c v : ℚ} (hc : c ≠ 0) :
    v ^ 2 ≠ c ^ 3 - 11 * c ^ 2 - c := by
  intro hcurve
  have hcoprime : IsCoprime c.num (c.den : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using c.reduced)
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  have hden : (0 : ℤ) < (c.den : ℤ) := by
    exact_mod_cast c.den_pos
  exact not_isSquare_coprime_product hquartic hcoprime hnum hden
    (integral_certificate_of_rational_solution hcurve)

/-- Combining a square discriminant with the order-five Tate discriminant
produces a rational point on the conductor-twenty curve. -/
lemma conductorTwenty_solution_of_discriminants
    {c u D t : ℚ} (hc : c ≠ 0)
    (htate : u ^ 12 * D = c ^ 5 * (c ^ 2 - 11 * c - 1))
    (hsquare : D = t ^ 2) :
    (u ^ 6 * t / c ^ 2) ^ 2 = c ^ 3 - 11 * c ^ 2 - c := by
  rw [div_pow, div_eq_iff (pow_ne_zero 2 (pow_ne_zero 2 hc))]
  linear_combination htate - u ^ 12 * hsquare

/-- A nonzero point killed by two has affine coordinates in which its
ordinate is determined by its abscissa. -/
lemma exists_two_torsion_coordinates
    {W : WeierstrassCurve.Affine ℚ} (T : W.Point)
    (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ x y : ℚ,
      (∃ hns : W.Nonsingular x y,
        T = WeierstrassCurve.Affine.Point.some x y hns) ∧
      W.Equation x y ∧ y = W.negY x y := by
  rcases T with _ | ⟨x, y, hns⟩
  · exact (hT0 rfl).elim
  · have hneg :
        -WeierstrassCurve.Affine.Point.some x y hns =
          WeierstrassCurve.Affine.Point.some x y hns :=
      neg_eq_of_add_eq_zero_left hT2
    rw [WeierstrassCurve.Affine.Point.neg_some] at hneg
    have hy : W.negY x y = y :=
      (WeierstrassCurve.Affine.Point.some.inj hneg).2
    exact ⟨x, y, ⟨hns, rfl⟩, hns.1, hy.symm⟩

/-- Full rational two-torsion forces the Weierstrass discriminant to be
a rational square. -/
theorem exists_discriminant_square_of_full_two_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ d : ℚ, E.Δ = d ^ 2 := by
  have htwo₁ : f (1, 0) + f (1, 0) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (0 : ZMod 2)) + (1, 0) = 0 by decide,
      map_zero]
  have htwo₂ : f (0, 1) + f (0, 1) = 0 := by
    rw [← map_add, show ((0 : ZMod 2), (1 : ZMod 2)) + (0, 1) = 0 by decide,
      map_zero]
  have htwo₃ : f (1, 1) + f (1, 1) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (1 : ZMod 2)) + (1, 1) = 0 by decide,
      map_zero]
  have hne₁ : f (1, 0) ≠ 0 := fun h =>
    (by
      apply (show ((1 : ZMod 2), (0 : ZMod 2)) ≠ 0 by decide)
      exact hf (h.trans (map_zero f).symm))
  have hne₂ : f (0, 1) ≠ 0 := fun h =>
    (by
      apply (show ((0 : ZMod 2), (1 : ZMod 2)) ≠ 0 by decide)
      exact hf (h.trans (map_zero f).symm))
  have hne₃ : f (1, 1) ≠ 0 := fun h =>
    (by
      apply (show ((1 : ZMod 2), (1 : ZMod 2)) ≠ 0 by decide)
      exact hf (h.trans (map_zero f).symm))
  have hne₁₂ : f (1, 0) ≠ f (0, 1) := fun h =>
    (show ((1 : ZMod 2), (0 : ZMod 2)) ≠ (0, 1) by decide) (hf h)
  have hne₁₃ : f (1, 0) ≠ f (1, 1) := fun h =>
    (show ((1 : ZMod 2), (0 : ZMod 2)) ≠ (1, 1) by decide) (hf h)
  have hne₂₃ : f (0, 1) ≠ f (1, 1) := fun h =>
    (show ((0 : ZMod 2), (1 : ZMod 2)) ≠ (1, 1) by decide) (hf h)
  obtain ⟨x₁, y₁, ⟨hns₁, hpoint₁⟩, heq₁, hneg₁⟩ :=
    exists_two_torsion_coordinates (f (1, 0)) htwo₁ hne₁
  obtain ⟨x₂, y₂, ⟨hns₂, hpoint₂⟩, heq₂, hneg₂⟩ :=
    exists_two_torsion_coordinates (f (0, 1)) htwo₂ hne₂
  obtain ⟨x₃, y₃, ⟨hns₃, hpoint₃⟩, heq₃, hneg₃⟩ :=
    exists_two_torsion_coordinates (f (1, 1)) htwo₃ hne₃
  rw [WeierstrassCurve.Affine.negY] at hneg₁ hneg₂ hneg₃
  rw [WeierstrassCurve.Affine.equation_iff] at heq₁ heq₂ heq₃
  have hx₁₂ : x₁ ≠ x₂ := by
    intro hx
    subst x₂
    have hy : y₁ = y₂ := by linarith
    subst y₂
    rw [hpoint₁, hpoint₂] at hne₁₂
    exact hne₁₂ rfl
  have hx₁₃ : x₁ ≠ x₃ := by
    intro hx
    subst x₃
    have hy : y₁ = y₃ := by linarith
    subst y₃
    rw [hpoint₁, hpoint₃] at hne₁₃
    exact hne₁₃ rfl
  have hx₂₃ : x₂ ≠ x₃ := by
    intro hx
    subst x₃
    have hy : y₂ = y₃ := by linarith
    subst y₃
    rw [hpoint₂, hpoint₃] at hne₂₃
    exact hne₂₃ rfl
  have hroot₁ :
      4 * x₁ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * x₁ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * x₁ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * y₁ + (E⁄ℚ).a₁ * x₁ + (E⁄ℚ).a₃) * hneg₁ - 4 * heq₁
  have hroot₂ :
      4 * x₂ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * x₂ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * x₂ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * y₂ + (E⁄ℚ).a₁ * x₂ + (E⁄ℚ).a₃) * hneg₂ - 4 * heq₂
  have hroot₃ :
      4 * x₃ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * x₃ ^ 2 +
        (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * x₃ +
        ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination
      (2 * y₃ + (E⁄ℚ).a₁ * x₃ + (E⁄ℚ).a₃) * hneg₃ - 4 * heq₃
  obtain ⟨hb₂, hb₄, hb₆⟩ :=
    FullFour.cubic_coefficients_of_three_roots
      hx₁₂ hx₁₃ hx₂₃ hroot₁ hroot₂ hroot₃
  have ha₁ : (E⁄ℚ).a₁ = E.a₁ := by simp [WeierstrassCurve.baseChange]
  have ha₂ : (E⁄ℚ).a₂ = E.a₂ := by simp [WeierstrassCurve.baseChange]
  have ha₃ : (E⁄ℚ).a₃ = E.a₃ := by simp [WeierstrassCurve.baseChange]
  have ha₄ : (E⁄ℚ).a₄ = E.a₄ := by simp [WeierstrassCurve.baseChange]
  have ha₆ : (E⁄ℚ).a₆ = E.a₆ := by simp [WeierstrassCurve.baseChange]
  simp only [ha₁, ha₂, ha₃, ha₄, ha₆] at hb₂ hb₄ hb₆
  have hB₂ : E.b₂ = -4 * (x₁ + x₂ + x₃) := by
    simp only [WeierstrassCurve.b₂]
    linarith
  have hB₄ : E.b₄ = 2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) := by
    simp only [WeierstrassCurve.b₄]
    linarith
  have hB₆ : E.b₆ = -4 * (x₁ * x₂ * x₃) := by
    simp only [WeierstrassCurve.b₆]
    linarith
  have hB₈ : E.b₈ = (E.b₂ * E.b₆ - E.b₄ ^ 2) / 4 := by
    have h := E.b_relation
    linarith
  refine ⟨4 * (x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃), ?_⟩
  simp only [WeierstrassCurve.Δ, hB₈, hB₂, hB₄, hB₆]
  ring

/-- The complete geometric-to-Diophantine reduction: the exceptional
quartic leaf rules out full rational two-torsion together with a point of
order five. -/
theorem false_of_full_two_torsion_and_order_five
    (hquartic : NoExceptionalQuartic)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f)
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 5) :
    False := by
  obtain ⟨t, ht⟩ := exists_discriminant_square_of_full_two_torsion E f hf
  obtain ⟨c, u, hu, hc, hdisc⟩ :=
    exists_tateFive_discriminant_of_order_five E Q hQ
  apply no_rational_solution hquartic hc
  exact conductorTwenty_solution_of_discriminants hc hdisc ht

/-- Conditional only on the explicit quartic leaf, rational elliptic-curve
points forbid an embedding of `ZMod 2 × ZMod 10`. -/
theorem forbidsEmbedding_zmod_two_prod_ten_of_quartic
    (hquartic : NoExceptionalQuartic)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ForbidsEmbedding (ZMod 2 × ZMod 10) (E⁄ℚ).Point := by
  intro f hf
  let crt : ZMod 10 ≃+ ZMod 2 × ZMod 5 :=
    (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 5)).toAddEquiv
  let g : ZMod 2 →+ ZMod 10 :=
    crt.symm.toAddMonoidHom.comp (AddMonoidHom.inl (ZMod 2) (ZMod 5))
  have hg : Function.Injective g :=
    crt.symm.injective.comp (fun _ _ h => congrArg Prod.fst h)
  let f₂ : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point :=
    f.comp ((AddMonoidHom.id (ZMod 2)).prodMap g)
  have hf₂ : Function.Injective f₂ := by
    apply hf.comp
    rw [AddMonoidHom.coe_prodMap]
    exact Function.Injective.prodMap (fun _ _ h => h) hg
  let Q : (E⁄ℚ).Point := f ((0 : ZMod 2), (2 : ZMod 10))
  have hQ : addOrderOf Q = 5 := by
    dsimp [Q]
    rw [addOrderOf_injective f hf]
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact addOrderOf_eq_prime (by decide) (by decide)
  exact false_of_full_two_torsion_and_order_five hquartic E f₂ hf₂ Q hQ

end ExceptionalTwoTen
end MazurTorsion
