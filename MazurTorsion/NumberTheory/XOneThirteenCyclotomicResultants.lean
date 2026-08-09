/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellInfinityOrder
import MazurTorsion.Foundations.Polynomial.BoundedResultant
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Explicit cyclotomic-thirteen resultant certificates

This file checks six small resultants against `Φ₁₃`.  They are the exact
norm computations needed by a later principal-ideal calculation in
`ℚ(ζ₁₃)`.  No class-number or ideal-generation conclusion is made here.

The certificates use finite monic Euclidean chains over `ℚ`.  Every
remainder identity is checked as a polynomial identity by `ring`; the generic
bounded-resultant step accounts for the scalar content and degree padding.
-/

namespace MazurTorsion.XOneThirteenCyclotomic

open Polynomial

noncomputable section

/-- The thirteenth cyclotomic polynomial over `ℤ`. -/
def phiThirteen : ℤ[X] :=
  X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 +
    X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

/-- The displayed polynomial is Mathlib's thirteenth cyclotomic polynomial. -/
theorem phiThirteen_eq_cyclotomic :
    phiThirteen = Polynomial.cyclotomic 13 ℤ := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  rw [Polynomial.cyclotomic_prime]
  simp [phiThirteen, Finset.sum_range_succ]
  ring

/-- The polynomial representing `1 - ζ`. -/
def alphaThirteen : ℤ[X] := 1 - X

/-- The polynomial representing `ζ³ - ζ - 1`. -/
def alphaTwentySeven : ℤ[X] := X ^ 3 - X - 1

/-- The polynomial representing `1 - ζ² + ζ³`. -/
def alphaFiftyThree : ℤ[X] := 1 - X ^ 2 + X ^ 3

/-- The polynomial representing `1 - ζ + ζ² + ζ⁶`. -/
def alphaSeventyNine : ℤ[X] := 1 - X + X ^ 2 + X ^ 6

/-- The polynomial representing `-1 + ζ² + ζ⁶`. -/
def alphaOneThirtyOne : ℤ[X] := X ^ 6 + X ^ 2 - 1

/-- The polynomial representing `ζ + ζ⁴ + ζ⁵ + ζ⁷`. -/
def alphaOneFiftySeven : ℤ[X] := X + X ^ 4 + X ^ 5 + X ^ 7

private theorem bounded_resultant_monic_remainder
    (f g q r : ℚ[X]) (c : ℚ) (m n k : ℕ)
    (hg : g.natDegree ≤ n) (hr : r.natDegree ≤ k)
    (hq : q.natDegree + n ≤ m) (hkm : k ≤ m)
    (hcoeff : g.coeff n = 1)
    (hid : f = g * q + C c * r) :
    resultant f g m n =
      (-1 : ℚ) ^ (m * n) * c ^ n * resultant g r n k := by
  have h :=
    MazurTorsion.PolynomialResultant.bounded_resultant_pseudoRemainder
      f g q r 1 c m n k 0 hg hr hq hkm hcoeff (by
        calc
          C ((1 : ℚ) ^ 0) * f = f := by simp
          _ = g * q + C c * r := hid
          _ = C c * r + g * q := by ring)
  norm_num at h
  rw [resultant_comm r g k n] at h
  have hexponent : n * (m - k) + k * n = m * n := by
    rw [mul_comm k n, ← Nat.mul_add, Nat.sub_add_cancel hkm, mul_comm]
  calc
    resultant f g m n =
        (-1 : ℚ) ^ (n * (m - k)) * c ^ n *
          ((-1 : ℚ) ^ (k * n) * resultant g r n k) := h
    _ = ((-1 : ℚ) ^ (n * (m - k)) * (-1 : ℚ) ^ (k * n)) *
        c ^ n * resultant g r n k := by ring
    _ = (-1 : ℚ) ^ (m * n) * c ^ n * resultant g r n k := by
      rw [← pow_add, hexponent]

private def mapRat (p : ℤ[X]) : ℚ[X] :=
  p.map (Int.castRingHom ℚ)

private theorem bounded_resultant_eq_of_mapRat
    (f g : ℤ[X]) (m n : ℕ) (a : ℤ)
    (h : resultant (mapRat f) (mapRat g) m n = (a : ℚ)) :
    resultant f g m n = a := by
  apply Int.cast_injective (α := ℚ)
  change (Int.castRingHom ℚ) (resultant f g m n) = (a : ℚ)
  simpa only [mapRat, resultant_map_map] using h

private theorem phiThirteen_natDegree : phiThirteen.natDegree = 12 := by
  unfold phiThirteen
  compute_degree!

private theorem alphaTwentySeven_natDegree :
    alphaTwentySeven.natDegree = 3 := by
  unfold alphaTwentySeven
  compute_degree!

private theorem alphaTwentySeven_coeff_three :
    alphaTwentySeven.coeff 3 = 1 := by
  unfold alphaTwentySeven
  compute_degree!

/-! ## Resultant `27` -/

private def chainTwentySevenRemainder : ℚ[X] :=
  X ^ 2 + C (4 / 3) * X + C (7 / 9)

private def chainTwentySevenQuotientZero : ℚ[X] :=
  X ^ 9 + X ^ 8 + 2 * X ^ 7 + 3 * X ^ 6 + 4 * X ^ 5 +
    6 * X ^ 4 + 8 * X ^ 3 + 11 * X ^ 2 + 15 * X + 20

private def chainTwentySevenQuotientOne : ℚ[X] :=
  X - C (4 / 3)

private theorem alphaTwentySeven_bounded_resultant :
    resultant phiThirteen alphaTwentySeven 12 3 = 27 := by
  apply bounded_resultant_eq_of_mapRat
  have hzero := bounded_resultant_monic_remainder
    (mapRat phiThirteen) (mapRat alphaTwentySeven)
    chainTwentySevenQuotientZero chainTwentySevenRemainder
    27 12 3 2
    (by
      unfold mapRat
      rw [Polynomial.natDegree_map_eq_of_injective
        Int.cast_injective, alphaTwentySeven_natDegree])
    (by
      unfold chainTwentySevenRemainder
      compute_degree!)
    (by
      have hdegree : chainTwentySevenQuotientZero.natDegree ≤ 9 := by
        unfold chainTwentySevenQuotientZero
        compute_degree!
      omega)
    (by norm_num)
    (by simp [mapRat, alphaTwentySeven_coeff_three])
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, phiThirteen, alphaTwentySeven,
        chainTwentySevenQuotientZero, chainTwentySevenRemainder]
      ring)
  have hone := bounded_resultant_monic_remainder
    (mapRat alphaTwentySeven) chainTwentySevenRemainder
    chainTwentySevenQuotientOne 1
    (1 / 27) 3 2 0
    (by
      unfold chainTwentySevenRemainder
      compute_degree!)
    (by simp)
    (by
      have hdegree : chainTwentySevenQuotientOne.natDegree ≤ 1 := by
        unfold chainTwentySevenQuotientOne
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainTwentySevenRemainder
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, alphaTwentySeven, chainTwentySevenRemainder,
        chainTwentySevenQuotientOne]
      ring)
  rw [hzero, hone]
  norm_num

/-- `Res(Φ₁₃, X³-X-1) = 27`. -/
theorem phiThirteen_resultant_alphaTwentySeven :
    phiThirteen.resultant alphaTwentySeven = 27 := by
  change resultant phiThirteen alphaTwentySeven
      phiThirteen.natDegree alphaTwentySeven.natDegree = 27
  rw [phiThirteen_natDegree, alphaTwentySeven_natDegree]
  exact alphaTwentySeven_bounded_resultant

/-! ## Resultant `13` -/

private theorem alphaThirteen_natDegree : alphaThirteen.natDegree = 1 := by
  unfold alphaThirteen
  compute_degree!

private theorem alphaThirteen_bounded_resultant :
    resultant phiThirteen alphaThirteen 12 1 = 13 := by
  rw [show alphaThirteen = C (-1) * (X - C 1) by
    simp [alphaThirteen]]
  rw [resultant_C_mul_right,
    resultant_X_sub_C_right (f := phiThirteen) (r := (1 : ℤ))
      (m := 12) (by rw [phiThirteen_natDegree])]
  norm_num [phiThirteen]

/-- `Res(Φ₁₃, 1-X) = 13`. -/
theorem phiThirteen_resultant_alphaThirteen :
    phiThirteen.resultant alphaThirteen = 13 := by
  change resultant phiThirteen alphaThirteen
      phiThirteen.natDegree alphaThirteen.natDegree = 13
  rw [phiThirteen_natDegree, alphaThirteen_natDegree]
  exact alphaThirteen_bounded_resultant

/-! ## Resultant `53` -/

private theorem alphaFiftyThree_natDegree :
    alphaFiftyThree.natDegree = 3 := by
  unfold alphaFiftyThree
  compute_degree!

private theorem alphaFiftyThree_coeff_three :
    alphaFiftyThree.coeff 3 = 1 := by
  unfold alphaFiftyThree
  compute_degree!

private def chainFiftyThreeRemainderOne : ℚ[X] :=
  X ^ 2 + C (3 / 5) * X

private def chainFiftyThreeRemainderTwo : ℚ[X] :=
  X + C (25 / 24)

private def chainFiftyThreeQuotientZero : ℚ[X] :=
  X ^ 9 + 2 * X ^ 8 + 3 * X ^ 7 + 3 * X ^ 6 + 2 * X ^ 5 -
    2 * X ^ 3 - 3 * X ^ 2 - 2 * X + 1

private def chainFiftyThreeQuotientOne : ℚ[X] :=
  X - C (8 / 5)

private def chainFiftyThreeQuotientTwo : ℚ[X] :=
  X - C (53 / 120)

private theorem alphaFiftyThree_bounded_resultant :
    resultant phiThirteen alphaFiftyThree 12 3 = 53 := by
  apply bounded_resultant_eq_of_mapRat
  have hzero := bounded_resultant_monic_remainder
    (mapRat phiThirteen) (mapRat alphaFiftyThree)
    chainFiftyThreeQuotientZero chainFiftyThreeRemainderOne
    5 12 3 2
    (by
      unfold mapRat
      rw [Polynomial.natDegree_map_eq_of_injective
        Int.cast_injective, alphaFiftyThree_natDegree])
    (by
      unfold chainFiftyThreeRemainderOne
      compute_degree!)
    (by
      have hdegree : chainFiftyThreeQuotientZero.natDegree ≤ 9 := by
        unfold chainFiftyThreeQuotientZero
        compute_degree!
      omega)
    (by norm_num)
    (by simp [mapRat, alphaFiftyThree_coeff_three])
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, phiThirteen, alphaFiftyThree,
        chainFiftyThreeQuotientZero, chainFiftyThreeRemainderOne]
      ring)
  have hone := bounded_resultant_monic_remainder
    (mapRat alphaFiftyThree) chainFiftyThreeRemainderOne
    chainFiftyThreeQuotientOne chainFiftyThreeRemainderTwo
    (24 / 25) 3 2 1
    (by
      unfold chainFiftyThreeRemainderOne
      compute_degree!)
    (by
      unfold chainFiftyThreeRemainderTwo
      compute_degree!)
    (by
      have hdegree : chainFiftyThreeQuotientOne.natDegree ≤ 1 := by
        unfold chainFiftyThreeQuotientOne
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainFiftyThreeRemainderOne
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, alphaFiftyThree, chainFiftyThreeRemainderOne,
        chainFiftyThreeRemainderTwo, chainFiftyThreeQuotientOne]
      ring)
  have htwo := bounded_resultant_monic_remainder
    chainFiftyThreeRemainderOne chainFiftyThreeRemainderTwo
    chainFiftyThreeQuotientTwo 1
    (265 / 576) 2 1 0
    (by
      unfold chainFiftyThreeRemainderTwo
      compute_degree!)
    (by simp)
    (by
      have hdegree : chainFiftyThreeQuotientTwo.natDegree ≤ 1 := by
        unfold chainFiftyThreeQuotientTwo
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainFiftyThreeRemainderTwo
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainFiftyThreeRemainderOne, chainFiftyThreeRemainderTwo,
        chainFiftyThreeQuotientTwo]
      ring)
  rw [hzero, hone, htwo]
  norm_num

/-- `Res(Φ₁₃, 1-X²+X³) = 53`. -/
theorem phiThirteen_resultant_alphaFiftyThree :
    phiThirteen.resultant alphaFiftyThree = 53 := by
  change resultant phiThirteen alphaFiftyThree
      phiThirteen.natDegree alphaFiftyThree.natDegree = 53
  rw [phiThirteen_natDegree, alphaFiftyThree_natDegree]
  exact alphaFiftyThree_bounded_resultant

/-! ## Resultant `79` -/

private theorem alphaSeventyNine_natDegree :
    alphaSeventyNine.natDegree = 6 := by
  unfold alphaSeventyNine
  compute_degree!

private theorem alphaSeventyNine_coeff_six :
    alphaSeventyNine.coeff 6 = 1 := by
  unfold alphaSeventyNine
  compute_degree!

private def chainSeventyNineRemainderOne : ℚ[X] :=
  X ^ 4 - X ^ 3 + 2 * X ^ 2 + 1

private def chainSeventyNineRemainderTwo : ℚ[X] :=
  X ^ 3 - C (2 / 3) * X ^ 2 + C (2 / 3) * X - C (2 / 3)

private def chainSeventyNineRemainderThree : ℚ[X] :=
  X ^ 2 + C (4 / 5) * X + C (7 / 10)

private def chainSeventyNineRemainderFour : ℚ[X] :=
  X + C (6 / 19)

private def chainSeventyNineQuotientZero : ℚ[X] :=
  X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X

private def chainSeventyNineQuotientOne : ℚ[X] :=
  X ^ 2 + X - 1

private def chainSeventyNineQuotientTwo : ℚ[X] :=
  X - C (1 / 3)

private def chainSeventyNineQuotientThree : ℚ[X] :=
  X - C (22 / 15)

private def chainSeventyNineQuotientFour : ℚ[X] :=
  X + C (46 / 95)

private theorem alphaSeventyNine_bounded_resultant :
    resultant phiThirteen alphaSeventyNine 12 6 = 79 := by
  apply bounded_resultant_eq_of_mapRat
  have hzero := bounded_resultant_monic_remainder
    (mapRat phiThirteen) (mapRat alphaSeventyNine)
    chainSeventyNineQuotientZero chainSeventyNineRemainderOne
    1 12 6 4
    (by
      unfold mapRat
      rw [Polynomial.natDegree_map_eq_of_injective
        Int.cast_injective, alphaSeventyNine_natDegree])
    (by
      unfold chainSeventyNineRemainderOne
      compute_degree!)
    (by
      have hdegree : chainSeventyNineQuotientZero.natDegree ≤ 6 := by
        unfold chainSeventyNineQuotientZero
        compute_degree!
      omega)
    (by norm_num)
    (by simp [mapRat, alphaSeventyNine_coeff_six])
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, phiThirteen, alphaSeventyNine,
        chainSeventyNineQuotientZero, chainSeventyNineRemainderOne]
      ring)
  have hone := bounded_resultant_monic_remainder
    (mapRat alphaSeventyNine) chainSeventyNineRemainderOne
    chainSeventyNineQuotientOne chainSeventyNineRemainderTwo
    (-3) 6 4 3
    (by
      unfold chainSeventyNineRemainderOne
      compute_degree!)
    (by
      unfold chainSeventyNineRemainderTwo
      compute_degree!)
    (by
      have hdegree : chainSeventyNineQuotientOne.natDegree ≤ 2 := by
        unfold chainSeventyNineQuotientOne
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainSeventyNineRemainderOne
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, alphaSeventyNine, chainSeventyNineRemainderOne,
        chainSeventyNineRemainderTwo, chainSeventyNineQuotientOne]
      ring)
  have htwo := bounded_resultant_monic_remainder
    chainSeventyNineRemainderOne chainSeventyNineRemainderTwo
    chainSeventyNineQuotientTwo chainSeventyNineRemainderThree
    (10 / 9) 4 3 2
    (by
      unfold chainSeventyNineRemainderTwo
      compute_degree!)
    (by
      unfold chainSeventyNineRemainderThree
      compute_degree!)
    (by
      have hdegree : chainSeventyNineQuotientTwo.natDegree ≤ 1 := by
        unfold chainSeventyNineQuotientTwo
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainSeventyNineRemainderTwo
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainSeventyNineRemainderOne, chainSeventyNineRemainderTwo,
        chainSeventyNineRemainderThree, chainSeventyNineQuotientTwo]
      ring)
  have hthree := bounded_resultant_monic_remainder
    chainSeventyNineRemainderTwo chainSeventyNineRemainderThree
    chainSeventyNineQuotientThree chainSeventyNineRemainderFour
    (57 / 50) 3 2 1
    (by
      unfold chainSeventyNineRemainderThree
      compute_degree!)
    (by
      unfold chainSeventyNineRemainderFour
      compute_degree!)
    (by
      have hdegree : chainSeventyNineQuotientThree.natDegree ≤ 1 := by
        unfold chainSeventyNineQuotientThree
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainSeventyNineRemainderThree
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainSeventyNineRemainderTwo, chainSeventyNineRemainderThree,
        chainSeventyNineRemainderFour, chainSeventyNineQuotientThree]
      ring)
  have hfour := bounded_resultant_monic_remainder
    chainSeventyNineRemainderThree chainSeventyNineRemainderFour
    chainSeventyNineQuotientFour 1
    (395 / 722) 2 1 0
    (by
      unfold chainSeventyNineRemainderFour
      compute_degree!)
    (by simp)
    (by
      have hdegree : chainSeventyNineQuotientFour.natDegree ≤ 1 := by
        unfold chainSeventyNineQuotientFour
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainSeventyNineRemainderFour
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainSeventyNineRemainderThree, chainSeventyNineRemainderFour,
        chainSeventyNineQuotientFour]
      ring)
  rw [hzero, hone, htwo, hthree, hfour]
  norm_num

/-- `Res(Φ₁₃, 1-X+X²+X⁶) = 79`. -/
theorem phiThirteen_resultant_alphaSeventyNine :
    phiThirteen.resultant alphaSeventyNine = 79 := by
  change resultant phiThirteen alphaSeventyNine
      phiThirteen.natDegree alphaSeventyNine.natDegree = 79
  rw [phiThirteen_natDegree, alphaSeventyNine_natDegree]
  exact alphaSeventyNine_bounded_resultant

/-! ## Resultant `131` -/

private theorem alphaOneThirtyOne_natDegree :
    alphaOneThirtyOne.natDegree = 6 := by
  unfold alphaOneThirtyOne
  compute_degree!

private theorem alphaOneThirtyOne_coeff_six :
    alphaOneThirtyOne.coeff 6 = 1 := by
  unfold alphaOneThirtyOne
  compute_degree!

private def chainOneThirtyOneRemainderOne : ℚ[X] :=
  X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + X + 2

private def chainOneThirtyOneRemainderTwo : ℚ[X] :=
  X ^ 4 + 2 * X ^ 3 + C (3 / 2)

private def chainOneThirtyOneRemainderThree : ℚ[X] :=
  X ^ 3 - C (1 / 4) * X + 1

private def chainOneThirtyOneRemainderFour : ℚ[X] :=
  X ^ 2 - 2 * X - 2

private def chainOneThirtyOneRemainderFive : ℚ[X] :=
  X + C (20 / 23)

private def chainOneThirtyOneQuotientZero : ℚ[X] :=
  X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + 1

private def chainOneThirtyOneQuotientOne : ℚ[X] :=
  X - 2

private def chainOneThirtyOneQuotientTwo : ℚ[X] :=
  X

private def chainOneThirtyOneQuotientThree : ℚ[X] :=
  X + 2

private def chainOneThirtyOneQuotientFour : ℚ[X] :=
  X + 2

private def chainOneThirtyOneQuotientFive : ℚ[X] :=
  X - C (66 / 23)

private theorem alphaOneThirtyOne_bounded_resultant :
    resultant phiThirteen alphaOneThirtyOne 12 6 = 131 := by
  apply bounded_resultant_eq_of_mapRat
  have hzero := bounded_resultant_monic_remainder
    (mapRat phiThirteen) (mapRat alphaOneThirtyOne)
    chainOneThirtyOneQuotientZero chainOneThirtyOneRemainderOne
    1 12 6 5
    (by
      unfold mapRat
      rw [Polynomial.natDegree_map_eq_of_injective
        Int.cast_injective, alphaOneThirtyOne_natDegree])
    (by
      unfold chainOneThirtyOneRemainderOne
      compute_degree!)
    (by
      have hdegree : chainOneThirtyOneQuotientZero.natDegree ≤ 6 := by
        unfold chainOneThirtyOneQuotientZero
        compute_degree!
      omega)
    (by norm_num)
    (by simp [mapRat, alphaOneThirtyOne_coeff_six])
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, phiThirteen, alphaOneThirtyOne,
        chainOneThirtyOneQuotientZero, chainOneThirtyOneRemainderOne]
      ring)
  have hone := bounded_resultant_monic_remainder
    (mapRat alphaOneThirtyOne) chainOneThirtyOneRemainderOne
    chainOneThirtyOneQuotientOne chainOneThirtyOneRemainderTwo
    2 6 5 4
    (by
      unfold chainOneThirtyOneRemainderOne
      compute_degree!)
    (by
      unfold chainOneThirtyOneRemainderTwo
      compute_degree!)
    (by
      have hdegree : chainOneThirtyOneQuotientOne.natDegree ≤ 1 := by
        unfold chainOneThirtyOneQuotientOne
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneThirtyOneRemainderOne
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, alphaOneThirtyOne, chainOneThirtyOneRemainderOne,
        chainOneThirtyOneRemainderTwo, chainOneThirtyOneQuotientOne]
      ring)
  have htwo := bounded_resultant_monic_remainder
    chainOneThirtyOneRemainderOne chainOneThirtyOneRemainderTwo
    chainOneThirtyOneQuotientTwo chainOneThirtyOneRemainderThree
    2 5 4 3
    (by
      unfold chainOneThirtyOneRemainderTwo
      compute_degree!)
    (by
      unfold chainOneThirtyOneRemainderThree
      compute_degree!)
    (by
      have hdegree : chainOneThirtyOneQuotientTwo.natDegree ≤ 1 := by
        unfold chainOneThirtyOneQuotientTwo
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneThirtyOneRemainderTwo
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneThirtyOneRemainderOne, chainOneThirtyOneRemainderTwo,
        chainOneThirtyOneRemainderThree, chainOneThirtyOneQuotientTwo]
      ring)
  have hthree := bounded_resultant_monic_remainder
    chainOneThirtyOneRemainderTwo chainOneThirtyOneRemainderThree
    chainOneThirtyOneQuotientThree chainOneThirtyOneRemainderFour
    (1 / 4) 4 3 2
    (by
      unfold chainOneThirtyOneRemainderThree
      compute_degree!)
    (by
      unfold chainOneThirtyOneRemainderFour
      compute_degree!)
    (by
      have hdegree : chainOneThirtyOneQuotientThree.natDegree ≤ 1 := by
        unfold chainOneThirtyOneQuotientThree
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneThirtyOneRemainderThree
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneThirtyOneRemainderTwo, chainOneThirtyOneRemainderThree,
        chainOneThirtyOneRemainderFour, chainOneThirtyOneQuotientThree]
      ring)
  have hfour := bounded_resultant_monic_remainder
    chainOneThirtyOneRemainderThree chainOneThirtyOneRemainderFour
    chainOneThirtyOneQuotientFour chainOneThirtyOneRemainderFive
    (23 / 4) 3 2 1
    (by
      unfold chainOneThirtyOneRemainderFour
      compute_degree!)
    (by
      unfold chainOneThirtyOneRemainderFive
      compute_degree!)
    (by
      have hdegree : chainOneThirtyOneQuotientFour.natDegree ≤ 1 := by
        unfold chainOneThirtyOneQuotientFour
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneThirtyOneRemainderFour
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneThirtyOneRemainderThree, chainOneThirtyOneRemainderFour,
        chainOneThirtyOneRemainderFive, chainOneThirtyOneQuotientFour]
      ring)
  have hfive := bounded_resultant_monic_remainder
    chainOneThirtyOneRemainderFour chainOneThirtyOneRemainderFive
    chainOneThirtyOneQuotientFive 1
    (262 / 529) 2 1 0
    (by
      unfold chainOneThirtyOneRemainderFive
      compute_degree!)
    (by simp)
    (by
      have hdegree : chainOneThirtyOneQuotientFive.natDegree ≤ 1 := by
        unfold chainOneThirtyOneQuotientFive
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneThirtyOneRemainderFive
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneThirtyOneRemainderFour, chainOneThirtyOneRemainderFive,
        chainOneThirtyOneQuotientFive]
      ring)
  rw [hzero, hone, htwo, hthree, hfour, hfive]
  norm_num

/-- `Res(Φ₁₃, -1+X²+X⁶) = 131`. -/
theorem phiThirteen_resultant_alphaOneThirtyOne :
    phiThirteen.resultant alphaOneThirtyOne = 131 := by
  change resultant phiThirteen alphaOneThirtyOne
      phiThirteen.natDegree alphaOneThirtyOne.natDegree = 131
  rw [phiThirteen_natDegree, alphaOneThirtyOne_natDegree]
  exact alphaOneThirtyOne_bounded_resultant

/-! ## Resultant `157` -/

private theorem alphaOneFiftySeven_natDegree :
    alphaOneFiftySeven.natDegree = 7 := by
  unfold alphaOneFiftySeven
  compute_degree!

private theorem alphaOneFiftySeven_coeff_seven :
    alphaOneFiftySeven.coeff 7 = 1 := by
  unfold alphaOneFiftySeven
  compute_degree!

private def chainOneFiftySevenRemainderOne : ℚ[X] :=
  X ^ 6 - 2 * X ^ 5 - X ^ 4 + 2 * X ^ 3 + X ^ 2 - X + 1

private def chainOneFiftySevenRemainderTwo : ℚ[X] :=
  X ^ 5 + C (1 / 6) * X ^ 4 - C (5 / 6) * X ^ 3 -
    C (1 / 6) * X ^ 2 + C (1 / 3) * X - C (1 / 3)

private def chainOneFiftySevenRemainderThree : ℚ[X] :=
  X ^ 4 + C (13 / 7) * X ^ 3 + C (11 / 7) * X ^ 2 +
    C (2 / 7) * X + C (10 / 7)

private def chainOneFiftySevenRemainderFour : ℚ[X] :=
  X ^ 3 + 3 * X ^ 2 - C (5 / 6) * X + C (17 / 6)

private def chainOneFiftySevenRemainderFive : ℚ[X] :=
  X ^ 2 - C (3 / 5) * X + C (4 / 5)

private def chainOneFiftySevenRemainderSix : ℚ[X] :=
  X - C (7 / 79)

private def chainOneFiftySevenQuotientZero : ℚ[X] :=
  X ^ 5 + X ^ 4 - X ^ 2 + 2

private def chainOneFiftySevenQuotientOne : ℚ[X] :=
  X + 2

private def chainOneFiftySevenQuotientTwo : ℚ[X] :=
  X - C (13 / 6)

private def chainOneFiftySevenQuotientThree : ℚ[X] :=
  X - C (71 / 42)

private def chainOneFiftySevenQuotientFour : ℚ[X] :=
  X - C (8 / 7)

private def chainOneFiftySevenQuotientFive : ℚ[X] :=
  X + C (18 / 5)

private def chainOneFiftySevenQuotientSix : ℚ[X] :=
  X - C (202 / 395)

private theorem alphaOneFiftySeven_bounded_resultant :
    resultant phiThirteen alphaOneFiftySeven 12 7 = 157 := by
  apply bounded_resultant_eq_of_mapRat
  have hzero := bounded_resultant_monic_remainder
    (mapRat phiThirteen) (mapRat alphaOneFiftySeven)
    chainOneFiftySevenQuotientZero chainOneFiftySevenRemainderOne
    1 12 7 6
    (by
      unfold mapRat
      rw [Polynomial.natDegree_map_eq_of_injective
        Int.cast_injective, alphaOneFiftySeven_natDegree])
    (by
      unfold chainOneFiftySevenRemainderOne
      compute_degree!)
    (by
      have hdegree : chainOneFiftySevenQuotientZero.natDegree ≤ 5 := by
        unfold chainOneFiftySevenQuotientZero
        compute_degree!
      omega)
    (by norm_num)
    (by simp [mapRat, alphaOneFiftySeven_coeff_seven])
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, phiThirteen, alphaOneFiftySeven,
        chainOneFiftySevenQuotientZero, chainOneFiftySevenRemainderOne]
      ring)
  have hone := bounded_resultant_monic_remainder
    (mapRat alphaOneFiftySeven) chainOneFiftySevenRemainderOne
    chainOneFiftySevenQuotientOne chainOneFiftySevenRemainderTwo
    6 7 6 5
    (by
      unfold chainOneFiftySevenRemainderOne
      compute_degree!)
    (by
      unfold chainOneFiftySevenRemainderTwo
      compute_degree!)
    (by
      have hdegree : chainOneFiftySevenQuotientOne.natDegree ≤ 1 := by
        unfold chainOneFiftySevenQuotientOne
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneFiftySevenRemainderOne
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [mapRat, alphaOneFiftySeven, chainOneFiftySevenRemainderOne,
        chainOneFiftySevenRemainderTwo, chainOneFiftySevenQuotientOne]
      ring)
  have htwo := bounded_resultant_monic_remainder
    chainOneFiftySevenRemainderOne chainOneFiftySevenRemainderTwo
    chainOneFiftySevenQuotientTwo chainOneFiftySevenRemainderThree
    (7 / 36) 6 5 4
    (by
      unfold chainOneFiftySevenRemainderTwo
      compute_degree!)
    (by
      unfold chainOneFiftySevenRemainderThree
      compute_degree!)
    (by
      have hdegree : chainOneFiftySevenQuotientTwo.natDegree ≤ 1 := by
        unfold chainOneFiftySevenQuotientTwo
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneFiftySevenRemainderTwo
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneFiftySevenRemainderOne, chainOneFiftySevenRemainderTwo,
        chainOneFiftySevenRemainderThree, chainOneFiftySevenQuotientTwo]
      ring)
  have hthree := bounded_resultant_monic_remainder
    chainOneFiftySevenRemainderTwo chainOneFiftySevenRemainderThree
    chainOneFiftySevenQuotientThree chainOneFiftySevenRemainderFour
    (36 / 49) 5 4 3
    (by
      unfold chainOneFiftySevenRemainderThree
      compute_degree!)
    (by
      unfold chainOneFiftySevenRemainderFour
      compute_degree!)
    (by
      have hdegree : chainOneFiftySevenQuotientThree.natDegree ≤ 1 := by
        unfold chainOneFiftySevenQuotientThree
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneFiftySevenRemainderThree
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneFiftySevenRemainderTwo, chainOneFiftySevenRemainderThree,
        chainOneFiftySevenRemainderFour, chainOneFiftySevenQuotientThree]
      ring)
  have hfour := bounded_resultant_monic_remainder
    chainOneFiftySevenRemainderThree chainOneFiftySevenRemainderFour
    chainOneFiftySevenQuotientFour chainOneFiftySevenRemainderFive
    (35 / 6) 4 3 2
    (by
      unfold chainOneFiftySevenRemainderFour
      compute_degree!)
    (by
      unfold chainOneFiftySevenRemainderFive
      compute_degree!)
    (by
      have hdegree : chainOneFiftySevenQuotientFour.natDegree ≤ 1 := by
        unfold chainOneFiftySevenQuotientFour
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneFiftySevenRemainderFour
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneFiftySevenRemainderThree, chainOneFiftySevenRemainderFour,
        chainOneFiftySevenRemainderFive, chainOneFiftySevenQuotientFour]
      ring)
  have hfive := bounded_resultant_monic_remainder
    chainOneFiftySevenRemainderFour chainOneFiftySevenRemainderFive
    chainOneFiftySevenQuotientFive chainOneFiftySevenRemainderSix
    (79 / 150) 3 2 1
    (by
      unfold chainOneFiftySevenRemainderFive
      compute_degree!)
    (by
      unfold chainOneFiftySevenRemainderSix
      compute_degree!)
    (by
      have hdegree : chainOneFiftySevenQuotientFive.natDegree ≤ 1 := by
        unfold chainOneFiftySevenQuotientFive
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneFiftySevenRemainderFive
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneFiftySevenRemainderFour, chainOneFiftySevenRemainderFive,
        chainOneFiftySevenRemainderSix, chainOneFiftySevenQuotientFive]
      ring)
  have hsix := bounded_resultant_monic_remainder
    chainOneFiftySevenRemainderFive chainOneFiftySevenRemainderSix
    chainOneFiftySevenQuotientSix 1
    (4710 / 6241) 2 1 0
    (by
      unfold chainOneFiftySevenRemainderSix
      compute_degree!)
    (by simp)
    (by
      have hdegree : chainOneFiftySevenQuotientSix.natDegree ≤ 1 := by
        unfold chainOneFiftySevenQuotientSix
        compute_degree!
      omega)
    (by norm_num)
    (by
      unfold chainOneFiftySevenRemainderSix
      compute_degree!)
    (by
      apply Polynomial.funext
      intro x
      simp [chainOneFiftySevenRemainderFive, chainOneFiftySevenRemainderSix,
        chainOneFiftySevenQuotientSix]
      ring)
  rw [hzero, hone, htwo, hthree, hfour, hfive, hsix]
  norm_num

/-- `Res(Φ₁₃, X+X⁴+X⁵+X⁷) = 157`. -/
theorem phiThirteen_resultant_alphaOneFiftySeven :
    phiThirteen.resultant alphaOneFiftySeven = 157 := by
  change resultant phiThirteen alphaOneFiftySeven
      phiThirteen.natDegree alphaOneFiftySeven.natDegree = 157
  rw [phiThirteen_natDegree, alphaOneFiftySeven_natDegree]
  exact alphaOneFiftySeven_bounded_resultant

/-- The six exact resultant certificates, bundled for the downstream ideal
calculation. -/
theorem phiThirteen_resultant_certificates :
    phiThirteen.resultant alphaThirteen = 13 ∧
      phiThirteen.resultant alphaTwentySeven = 27 ∧
      phiThirteen.resultant alphaFiftyThree = 53 ∧
      phiThirteen.resultant alphaSeventyNine = 79 ∧
      phiThirteen.resultant alphaOneThirtyOne = 131 ∧
      phiThirteen.resultant alphaOneFiftySeven = 157 :=
  ⟨phiThirteen_resultant_alphaThirteen,
    phiThirteen_resultant_alphaTwentySeven,
    phiThirteen_resultant_alphaFiftyThree,
    phiThirteen_resultant_alphaSeventyNine,
    phiThirteen_resultant_alphaOneThirtyOne,
    phiThirteen_resultant_alphaOneFiftySeven⟩

/-- The same bundle stated directly with Mathlib's `cyclotomic 13 ℤ`. -/
theorem cyclotomicThirteen_resultant_certificates :
    (Polynomial.cyclotomic 13 ℤ).resultant alphaThirteen = 13 ∧
      (Polynomial.cyclotomic 13 ℤ).resultant alphaTwentySeven = 27 ∧
      (Polynomial.cyclotomic 13 ℤ).resultant alphaFiftyThree = 53 ∧
      (Polynomial.cyclotomic 13 ℤ).resultant alphaSeventyNine = 79 ∧
      (Polynomial.cyclotomic 13 ℤ).resultant alphaOneThirtyOne = 131 ∧
      (Polynomial.cyclotomic 13 ℤ).resultant alphaOneFiftySeven = 157 := by
  rw [← phiThirteen_eq_cyclotomic]
  exact phiThirteen_resultant_certificates


end

end MazurTorsion.XOneThirteenCyclotomic
