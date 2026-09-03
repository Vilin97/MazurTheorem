/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveKummerCoverIntegral

/-!
# The Lehmer root transformation on the order-twenty-five cover

In the sign convention used by `orderTwentyFiveLehmerPolynomial`, the
standard cyclic-cover root transformation is the rational map

`x ↦ (x² - n*x + n - 2) / (1 + (n - 2)*x)`.

This file proves internally that its denominator cannot vanish at a rational
Lehmer root, that it sends roots to roots, and hence that every finite iterate
of a rational root remains rational.  The Kummer-cover consumer applies this
to the pulled-back parameter
`n = -orderTwentyFiveFifthPowerHauptmodul k`.  No distinctness assertion about
the first five iterates is needed here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The standard cyclic-cover transformation on Lehmer roots, in the
parameter and root signs used by this development. -/
def orderTwentyFiveLehmerDeckTransform (n x : ℚ) : ℚ :=
  (x ^ 2 - n * x + n - 2) / (1 + (n - 2) * x)

private noncomputable def orderTwentyFiveLehmerDeckExceptionalPolynomial :
    Polynomial ℤ :=
  Polynomial.X ^ 3 - 5 * Polynomial.X ^ 2 + 10 * Polynomial.X - 7

private theorem orderTwentyFiveLehmerDeckExceptionalPolynomial_monic :
    orderTwentyFiveLehmerDeckExceptionalPolynomial.Monic := by
  unfold orderTwentyFiveLehmerDeckExceptionalPolynomial
  monicity!

private theorem orderTwentyFiveLehmerDeckExceptionalPolynomial_ne_zero
    (n : ℚ) :
    n ^ 3 - 5 * n ^ 2 + 10 * n - 7 ≠ 0 := by
  intro hn
  have hroot :
      Polynomial.aeval n orderTwentyFiveLehmerDeckExceptionalPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderTwentyFiveLehmerDeckExceptionalPolynomial]
    linear_combination hn
  obtain ⟨z, hnz, hdiv⟩ :=
    exists_integer_of_is_root_of_monic
      orderTwentyFiveLehmerDeckExceptionalPolynomial_monic hroot
  have hcases : z ∣ (7 : ℤ) := by
    simpa [orderTwentyFiveLehmerDeckExceptionalPolynomial] using hdiv
  have habs : z.natAbs ∣ (7 : ℕ) := Int.dvd_natCast.mp hcases
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp habs with habs | habs
  · rcases Int.natAbs_eq_iff.mp habs with rfl | rfl
    · norm_num [hnz] at hn
    · norm_num [hnz] at hn
  · rcases Int.natAbs_eq_iff.mp habs with rfl | rfl
    · norm_num [hnz] at hn
    · norm_num [hnz] at hn

/-- The cyclic deck transformation has no rational pole at a Lehmer root.
Eliminating the root at a putative pole produces a monic cubic whose only
possible rational roots are the four signed divisors of seven, none of which
is a root. -/
theorem orderTwentyFiveLehmerDeckTransform_denominator_ne_zero
    (n x : ℚ) (hx : orderTwentyFiveLehmerPolynomial n x = 0) :
    1 + (n - 2) * x ≠ 0 := by
  intro hden
  have hcubicSq : (n ^ 3 - 5 * n ^ 2 + 10 * n - 7) ^ 2 = 0 := by
    simp only [orderTwentyFiveLehmerPolynomial] at hx
    grobner
  have hcubic : n ^ 3 - 5 * n ^ 2 + 10 * n - 7 = 0 :=
    sq_eq_zero_iff.mp hcubicSq
  exact orderTwentyFiveLehmerDeckExceptionalPolynomial_ne_zero n hcubic

/-- The pole-free deck transformation sends every rational Lehmer root to
another rational root of the same quintic. -/
theorem orderTwentyFiveLehmerDeckTransform_isRoot
    (n x : ℚ) (hx : orderTwentyFiveLehmerPolynomial n x = 0) :
    orderTwentyFiveLehmerPolynomial n
      (orderTwentyFiveLehmerDeckTransform n x) = 0 := by
  have hden :=
    orderTwentyFiveLehmerDeckTransform_denominator_ne_zero n x hx
  have hden' : 1 + x * (n - 2) ≠ 0 := by
    simpa only [mul_comm] using hden
  simp only [orderTwentyFiveLehmerDeckTransform,
    orderTwentyFiveLehmerPolynomial] at hx ⊢
  field_simp [hden, hden']
  grobner

/-- Every iterate of the cyclic transformation remains a rational root of
the same Lehmer quintic. -/
theorem orderTwentyFiveLehmerDeckTransform_iterate_isRoot
    (j : ℕ) (n x : ℚ)
    (hx : orderTwentyFiveLehmerPolynomial n x = 0) :
    orderTwentyFiveLehmerPolynomial n
      ((orderTwentyFiveLehmerDeckTransform n)^[j] x) = 0 := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact orderTwentyFiveLehmerDeckTransform_isRoot n _ ih

/-- On a complete Lécacheux orbit, the checked root transformation sends the
first coordinate to the second.  This identifies the algebraic transform
with the already formalized cyclic orbit rather than merely showing that it
preserves the quintic. -/
theorem orderTwentyFiveLehmerDeckTransform_eq_second_of_orbit
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveLehmerDeckTransform
      (orderTwentyFiveOrbitParameter a b c d e) a = b := by
  let n := orderTwentyFiveOrbitParameter a b c d e
  have hroot : orderTwentyFiveLehmerPolynomial n a = 0 :=
    (orderTwentyFiveLehmer_selectedRoots_of_orbit
      a b c d e ha h0 h1 h2 h3 h4 h5).1
  have hdeckDen :=
    orderTwentyFiveLehmerDeckTransform_denominator_ne_zero n a hroot
  have hpairDen := orderTwentyFiveOrbitPairDenominator_ne_zero
    a b c d e h0 h1 h2 h3 h4 h5
  have hn : n = orderTwentyFiveOrbitPairParameter a b :=
    orderTwentyFiveOrbitParameter_eq_pairParameter
      a b c d e h0 h1 h2 h3 h4 h5
  rw [orderTwentyFiveLehmerDeckTransform, div_eq_iff hdeckDen]
  simp only [n, orderTwentyFiveOrbitPairParameter,
    orderTwentyFiveOrbitPairDenominator] at hn
  change 1 - a - a * b ≠ 0 at hpairDen
  field_simp [hpairDen] at hn
  ring_nf at hn ⊢
  linear_combination hn

private noncomputable def orderTwentyFiveLehmerOneExceptionalPolynomial :
    Polynomial ℤ :=
  Polynomial.X ^ 4 - 6 * Polynomial.X ^ 3 + 14 * Polynomial.X ^ 2 -
    15 * Polynomial.X + 5

private theorem orderTwentyFiveLehmerOneExceptionalPolynomial_monic :
    orderTwentyFiveLehmerOneExceptionalPolynomial.Monic := by
  unfold orderTwentyFiveLehmerOneExceptionalPolynomial
  monicity!

private theorem orderTwentyFiveLehmerOneExceptionalPolynomial_ne_zero
    (n : ℚ) :
    n ^ 4 - 6 * n ^ 3 + 14 * n ^ 2 - 15 * n + 5 ≠ 0 := by
  intro hn
  have hroot :
      Polynomial.aeval n orderTwentyFiveLehmerOneExceptionalPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderTwentyFiveLehmerOneExceptionalPolynomial]
    linear_combination hn
  obtain ⟨z, hnz, hdiv⟩ :=
    exists_integer_of_is_root_of_monic
      orderTwentyFiveLehmerOneExceptionalPolynomial_monic hroot
  have hcases : z ∣ (5 : ℤ) := by
    simpa [orderTwentyFiveLehmerOneExceptionalPolynomial] using hdiv
  have habs : z.natAbs ∣ (5 : ℕ) := Int.dvd_natCast.mp hcases
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp habs with habs | habs
  · rcases Int.natAbs_eq_iff.mp habs with rfl | rfl
    · norm_num [hnz] at hn
    · norm_num [hnz] at hn
  · rcases Int.natAbs_eq_iff.mp habs with rfl | rfl
    · norm_num [hnz] at hn
    · norm_num [hnz] at hn

/-- The value one is never a rational root of Lehmer's quintic.  Substitution
would make its rational parameter a root of a monic quartic with constant
coefficient five, and the four signed rational-root candidates all fail. -/
theorem orderTwentyFiveLehmerPolynomial_one_ne_zero (n : ℚ) :
    orderTwentyFiveLehmerPolynomial n 1 ≠ 0 := by
  intro hroot
  apply orderTwentyFiveLehmerOneExceptionalPolynomial_ne_zero n
  norm_num [orderTwentyFiveLehmerPolynomial] at hroot ⊢
  linear_combination -hroot

/-- The symmetric orbit parameter is invariant under cyclic rotation of its
five coordinates. -/
theorem orderTwentyFiveOrbitParameter_rotate
    (a b c d e : ℚ) :
    orderTwentyFiveOrbitParameter b c d e a =
      orderTwentyFiveOrbitParameter a b c d e := by
  simp only [orderTwentyFiveOrbitParameter]
  ring

private theorem orderTwentyFiveOrbitRelations_rotate
    (a b c d e : ℚ)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveOrbitRelationZero b c d e a = 0 ∧
      orderTwentyFiveOrbitRelationOne b c d e a = 0 ∧
      orderTwentyFiveOrbitRelationTwo b c d e a = 0 ∧
      orderTwentyFiveOrbitRelationThree b c d e a = 0 ∧
      orderTwentyFiveOrbitRelationFour b c d e a = 0 ∧
      orderTwentyFiveOrbitRelationFive b c d e a = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [orderTwentyFiveOrbitRelationZero,
      orderTwentyFiveOrbitRelationOne] using h1
  · simpa only [orderTwentyFiveOrbitRelationOne,
      orderTwentyFiveOrbitRelationTwo] using h2
  · simpa only [orderTwentyFiveOrbitRelationTwo,
      orderTwentyFiveOrbitRelationThree] using h3
  · simpa only [orderTwentyFiveOrbitRelationThree,
      orderTwentyFiveOrbitRelationFour] using h4
  · simpa only [orderTwentyFiveOrbitRelationFour,
      orderTwentyFiveOrbitRelationZero] using h0
  · simp only [orderTwentyFiveOrbitRelationFive] at h5 ⊢
    linear_combination h5

/-- On a complete nonexceptional Lécacheux orbit, the root transformation
cycles through all five coordinates and returns to the first. -/
theorem orderTwentyFiveLehmerDeckTransform_cycle_of_orbit
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    let n := orderTwentyFiveOrbitParameter a b c d e
    orderTwentyFiveLehmerDeckTransform n a = b ∧
      orderTwentyFiveLehmerDeckTransform n b = c ∧
      orderTwentyFiveLehmerDeckTransform n c = d ∧
      orderTwentyFiveLehmerDeckTransform n d = e ∧
      orderTwentyFiveLehmerDeckTransform n e = a := by
  dsimp only
  let n := orderTwentyFiveOrbitParameter a b c d e
  have hrootA : orderTwentyFiveLehmerPolynomial n a = 0 :=
    (orderTwentyFiveLehmer_selectedRoots_of_orbit
      a b c d e ha h0 h1 h2 h3 h4 h5).1
  have hab := orderTwentyFiveLehmerDeckTransform_eq_second_of_orbit
    a b c d e ha h0 h1 h2 h3 h4 h5
  have hrootB : orderTwentyFiveLehmerPolynomial n b = 0 := by
    rw [← hab]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n a hrootA
  have hb : b ≠ 1 := by
    intro hb
    apply orderTwentyFiveLehmerPolynomial_one_ne_zero n
    simpa only [hb] using hrootB
  obtain ⟨h0', h1', h2', h3', h4', h5'⟩ :=
    orderTwentyFiveOrbitRelations_rotate a b c d e h0 h1 h2 h3 h4 h5
  have hbc := orderTwentyFiveLehmerDeckTransform_eq_second_of_orbit
    b c d e a hb h0' h1' h2' h3' h4' h5'
  rw [orderTwentyFiveOrbitParameter_rotate a b c d e] at hbc
  have hrootC : orderTwentyFiveLehmerPolynomial n c = 0 := by
    rw [← hbc]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n b hrootB
  have hc : c ≠ 1 := by
    intro hc
    apply orderTwentyFiveLehmerPolynomial_one_ne_zero n
    simpa only [hc] using hrootC
  obtain ⟨h0'', h1'', h2'', h3'', h4'', h5''⟩ :=
    orderTwentyFiveOrbitRelations_rotate b c d e a
      h0' h1' h2' h3' h4' h5'
  have hcd := orderTwentyFiveLehmerDeckTransform_eq_second_of_orbit
    c d e a b hc h0'' h1'' h2'' h3'' h4'' h5''
  rw [orderTwentyFiveOrbitParameter_rotate b c d e a,
    orderTwentyFiveOrbitParameter_rotate a b c d e] at hcd
  have hrootD : orderTwentyFiveLehmerPolynomial n d = 0 := by
    rw [← hcd]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n c hrootC
  have hd : d ≠ 1 := by
    intro hd
    apply orderTwentyFiveLehmerPolynomial_one_ne_zero n
    simpa only [hd] using hrootD
  obtain ⟨h0''', h1''', h2''', h3''', h4''', h5'''⟩ :=
    orderTwentyFiveOrbitRelations_rotate c d e a b
      h0'' h1'' h2'' h3'' h4'' h5''
  have hde := orderTwentyFiveLehmerDeckTransform_eq_second_of_orbit
    d e a b c hd h0''' h1''' h2''' h3''' h4''' h5'''
  rw [orderTwentyFiveOrbitParameter_rotate c d e a b,
    orderTwentyFiveOrbitParameter_rotate b c d e a,
    orderTwentyFiveOrbitParameter_rotate a b c d e] at hde
  have hrootE : orderTwentyFiveLehmerPolynomial n e = 0 := by
    rw [← hde]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n d hrootD
  have he : e ≠ 1 := by
    intro he
    apply orderTwentyFiveLehmerPolynomial_one_ne_zero n
    simpa only [he] using hrootE
  obtain ⟨h0'''', h1'''', h2'''', h3'''', h4'''', h5''''⟩ :=
    orderTwentyFiveOrbitRelations_rotate d e a b c
      h0''' h1''' h2''' h3''' h4''' h5'''
  have hea := orderTwentyFiveLehmerDeckTransform_eq_second_of_orbit
    e a b c d he h0'''' h1'''' h2'''' h3'''' h4'''' h5''''
  rw [orderTwentyFiveOrbitParameter_rotate d e a b c,
    orderTwentyFiveOrbitParameter_rotate c d e a b,
    orderTwentyFiveOrbitParameter_rotate b c d e a,
    orderTwentyFiveOrbitParameter_rotate a b c d e] at hea
  exact ⟨hab, hbc, hcd, hde, hea⟩

/-- A rational point of the pulled-back Kummer cover supplies a rational
Lehmer root in every deck iterate. -/
theorem orderTwentyFiveKummerCoverPolynomial_deckIterate
    (j : ℕ) (k x : ℚ) (hk : k ≠ 0)
    (hx : orderTwentyFiveKummerCoverPolynomial k x = 0) :
    orderTwentyFiveKummerCoverPolynomial k
      ((orderTwentyFiveLehmerDeckTransform
        (-orderTwentyFiveFifthPowerHauptmodul k))^[j] x) = 0 := by
  have hidentity :=
    orderTwentyFiveKummerCoverPolynomial_eq_clearedLehmer k x hk
  rw [hidentity] at hx
  have hroot :
      orderTwentyFiveLehmerPolynomial
        (-orderTwentyFiveFifthPowerHauptmodul k) x = 0 :=
    (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 4 hk)
  rw [orderTwentyFiveKummerCoverPolynomial_eq_clearedLehmer k _ hk,
    orderTwentyFiveLehmerDeckTransform_iterate_isRoot j _ _ hroot,
    mul_zero]

/-- The first five iterates of the cover point furnished by a hypothetical
marked point are rational Lehmer roots.  All residual parameter conditions
from the Kummer bridge are retained. -/
theorem orderTwentyFive_iteratedKummerCover_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ k : ℚ, k ≠ 0 ∧
      orderTwentyFiveFiveTateParameter b c = k ^ 5 ∧
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
        orderTwentyFiveFifthPowerHauptmodul k ∧
      ¬orderTwentyFiveRatIsThreeUnit k ∧
      orderTwentyFiveRatIsThreeIntegral
        (-5 / orderTwentyFiveFifthPowerHauptmodul k) ∧
      orderTwentyFiveBrunaultXZero b c ≠ 0 ∧
      orderTwentyFiveBrunaultXZero b c ≠ 1 ∧
      orderTwentyFiveLehmerDeckTransform
          (-orderTwentyFiveFifthPowerHauptmodul k)
          (orderTwentyFiveBrunaultXZero b c) =
        orderTwentyFiveBrunaultXOne b c ∧
      orderTwentyFiveLehmerDeckTransform
          (-orderTwentyFiveFifthPowerHauptmodul k)
          (orderTwentyFiveBrunaultXOne b c) =
        orderTwentyFiveBrunaultXTwo b c ∧
      orderTwentyFiveLehmerDeckTransform
          (-orderTwentyFiveFifthPowerHauptmodul k)
          (orderTwentyFiveBrunaultXTwo b c) =
        orderTwentyFiveBrunaultXThree b c ∧
      orderTwentyFiveLehmerDeckTransform
          (-orderTwentyFiveFifthPowerHauptmodul k)
          (orderTwentyFiveBrunaultXThree b c) =
        orderTwentyFiveBrunaultXFour b c ∧
      orderTwentyFiveLehmerDeckTransform
          (-orderTwentyFiveFifthPowerHauptmodul k)
          (orderTwentyFiveBrunaultXFour b c) =
        orderTwentyFiveBrunaultXZero b c ∧
      ∀ j : Fin 5,
        orderTwentyFiveKummerCoverPolynomial k
          ((orderTwentyFiveLehmerDeckTransform
            (-orderTwentyFiveFifthPowerHauptmodul k))^[j.val]
              (orderTwentyFiveBrunaultXZero b c)) = 0 := by
  obtain ⟨k, hk, hkPower, hkParameter, hkNotUnit, hreciprocal,
      hxZero, hxOne, hcover⟩ :=
    orderTwentyFive_kummerCover_of_marked_order
      b c hb h00 horder
  have hparameter :
      -orderTwentyFiveFifthPowerHauptmodul k =
        orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c) := by
    linarith
  have hcycle := orderTwentyFiveLehmerDeckTransform_cycle_of_orbit
    (orderTwentyFiveBrunaultXZero b c)
    (orderTwentyFiveBrunaultXOne b c)
    (orderTwentyFiveBrunaultXTwo b c)
    (orderTwentyFiveBrunaultXThree b c)
    (orderTwentyFiveBrunaultXFour b c) hxOne
    (orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationOne_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
      b c hb h00 horder)
  dsimp only at hcycle
  rw [← hparameter] at hcycle
  obtain ⟨hzeroOne, honeTwo, htwoThree, hthreeFour, hfourZero⟩ := hcycle
  refine ⟨k, hk, hkPower, hkParameter, hkNotUnit, hreciprocal,
    hxZero, hxOne, hzeroOne, honeTwo, htwoThree, hthreeFour,
    hfourZero, ?_⟩
  intro j
  exact orderTwentyFiveKummerCoverPolynomial_deckIterate
    j.val k (orderTwentyFiveBrunaultXZero b c) hk hcover

end MazurTorsion.Kubert
