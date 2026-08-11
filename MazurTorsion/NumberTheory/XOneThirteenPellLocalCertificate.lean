/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# A local certificate for the `X₁(13)` Pell-power cover at `191`

This file checks a small local consequence of the two thirty-eighth-power
Pell-factor equations.  After normalizing at a prime which does not divide
`b = r * s`, put `x = a / b` and `t = r / s`.  Subtracting the two factor
equations gives

`pellH x = t¹⁹ - t⁻¹⁹`.

Over `𝔽₁₉₁`, the right side takes only the five values
`0, ±10, ±75`.  Rather than trusting a large enumeration, the proof checks
the degree-ten resultant identity and Fermat's theorem inside Lean.

The final theorem consumes the actual homogeneous factor equations and
restricts their normalized Pell numerator to those five residues whenever
`191 ∤ b`.  A separate preimage/resultant certificate is still needed to
deduce cuspidal reduction, so this file is not the global rational-point
classification.
-/

namespace MazurTorsion.XOneThirteenPellLocalCertificate

open MazurTorsion.XOneThirteenDescent

/-- The residue field used for the local certificate. -/
abbrev F191 := ZMod 191

local instance : NeZero 191 := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 191) := ⟨by norm_num⟩

/-- Direct evaluation formula for the affine Pell numerator modulo `191`. -/
def pellHValueF191 (x : F191) : F191 :=
  x ^ 19 + 3 * x ^ 18 + 2 * x ^ 17 + 5 * x ^ 16 +
    22 * x ^ 15 + 22 * x ^ 14 + 10 * x ^ 13 +
    54 * x ^ 12 + 78 * x ^ 11 + 20 * x ^ 10 +
    51 * x ^ 9 + 113 * x ^ 8 + 36 * x ^ 7 +
    13 * x ^ 6 + 66 * x ^ 5 + 26 * x ^ 4 -
    2 * x ^ 3 + 12 * x ^ 2 + 4 * x

/-- The possible nineteenth-power differences in `𝔽₁₉₁`.  This is a
bounded check over the 191 possible values of `t`. -/
theorem nineteenth_power_difference_values :
    ∀ t : F191,
      t ≠ 0 →
        t ^ 19 - (t ^ 19)⁻¹ = 0 ∨
        t ^ 19 - (t ^ 19)⁻¹ = 10 ∨
        t ^ 19 - (t ^ 19)⁻¹ = -10 ∨
        t ^ 19 - (t ^ 19)⁻¹ = 75 ∨
        t ^ 19 - (t ^ 19)⁻¹ = -75 := by
  intro t ht
  let u : F191 := t ^ 19
  let d : F191 := u - u⁻¹
  have hu : u ≠ 0 := pow_ne_zero 19 ht
  have huTen : u ^ 10 = 1 := by
    dsimp only [u]
    rw [← pow_mul]
    norm_num
    exact ZMod.pow_card_sub_one_eq_one ht
  have hresultant :
      d ^ 2 * (d ^ 4 + 5 * d ^ 2 + 5) ^ 2 = 0 := by
    have hid :
        u ^ 10 * (d ^ 2 * (d ^ 4 + 5 * d ^ 2 + 5) ^ 2) =
          (u ^ 10 - 1) ^ 2 := by
      dsimp only [d]
      field_simp [hu]
      ring
    simpa only [huTen, one_mul, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using hid
  have hfactor :
      (d - 10) * (d + 10) * (d - 75) * (d + 75) =
        d ^ 4 + 5 * d ^ 2 + 5 := by
    have hc : (562500 : F191) = 5 := by decide
    have hc' : (5725 : F191) = -5 := by decide
    calc
      _ = d ^ 4 - 5725 * d ^ 2 + 562500 := by ring
      _ = d ^ 4 + 5 * d ^ 2 + 5 := by rw [hc, hc']; ring
  have hdValues :
      d = 0 ∨ d = 10 ∨ d = -10 ∨ d = 75 ∨ d = -75 := by
    rcases mul_eq_zero.mp hresultant with hd | hq
    · left
      exact sq_eq_zero_iff.mp hd
    · right
      have hq' : d ^ 4 + 5 * d ^ 2 + 5 = 0 := sq_eq_zero_iff.mp hq
      rw [← hfactor] at hq'
      simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hq'
      rcases hq' with ((h | h) | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  simpa only [u, d] using hdValues

private theorem pellHHomogeneous_normalize_mod_191
    (a b : ℤ) (hb : (b : F191) ≠ 0) :
    (pellHHomogeneous a b : F191) =
      (b : F191) ^ 19 * pellHValueF191 ((a : F191) / (b : F191)) := by
  simp only [pellHHomogeneous, pellHValueF191]
  push_cast
  field_simp [hb]

/-- The actual two homogeneous thirty-eighth-power factor equations place
the normalized Pell numerator in the five-element local image certificate
modulo `191`. -/
theorem pell_power_split_mod_191_rhs_values
    (a b c r s : ℤ)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s)
    (hb : (b : F191) ≠ 0) :
    pellHValueF191 ((a : F191) / (b : F191)) = 0 ∨
      pellHValueF191 ((a : F191) / (b : F191)) = 10 ∨
      pellHValueF191 ((a : F191) / (b : F191)) = -10 ∨
      pellHValueF191 ((a : F191) / (b : F191)) = 75 ∨
      pellHValueF191 ((a : F191) / (b : F191)) = -75 := by
  have hr : (r : F191) ≠ 0 := by
    intro hr
    apply hb
    rw [hbSplit]
    push_cast
    simp [hr]
  have hs : (s : F191) ≠ 0 := by
    intro hs
    apply hb
    rw [hbSplit]
    push_cast
    simp [hs]
  have hH : pellHHomogeneous a b = r ^ 38 - s ^ 38 := by
    have hsub := congrArg₂ (· - ·) hplus hminus
    simp only [positivePellFactor, negativePellFactorMagnitude] at hsub
    linarith
  have hH191 :
      (pellHHomogeneous a b : F191) =
        (r : F191) ^ 38 - (s : F191) ^ 38 := by
    simpa using
      congrArg (Int.castRingHom F191) hH
  have hpell :
      pellHValueF191 ((a : F191) / (b : F191)) =
        ((r : F191) / (s : F191)) ^ 19 -
          (((r : F191) / (s : F191)) ^ 19)⁻¹ := by
    apply mul_left_cancel₀ (pow_ne_zero 19 hb)
    rw [← pellHHomogeneous_normalize_mod_191 a b hb, hH191, hbSplit]
    push_cast
    field_simp [hr, hs]
  rw [hpell]
  exact nineteenth_power_difference_values
    ((r : F191) / (s : F191)) (div_ne_zero hr hs)

end MazurTorsion.XOneThirteenPellLocalCertificate
