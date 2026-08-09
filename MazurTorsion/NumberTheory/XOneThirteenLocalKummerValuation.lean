/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit

/-!
# The local valuation obstruction at thirteen

This file isolates the elementary valuation step needed by a local Kummer
calculation for the `X₁(13)` descent.  If a `p`-adic number of the form

`pᵉ · u`

with `u` a unit of `ℤ_[p]` is an `n`-th power in `ℚ_[p]`, then `n ∣ e`.
The proof uses Mathlib's normalized valuations `Padic.valuation_pow`,
`Padic.valuation_p`, and `PadicInt.valuation_coe` directly.

The specialization below says that an element represented by a power of
thirteen can be a nineteenth power in `ℚ_[13]` only when its exponent is
divisible by nineteen.  This is a local valuation certificate, not a
computation of a local Kummer image or a Selmer group.
-/

namespace MazurTorsion.XOneThirteenLocalKummerValuation

/-- A unit of the `p`-adic integers has normalized valuation zero. -/
theorem padicIntUnit_valuation_eq_zero
    {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) :
    (u : ℤ_[p]).valuation = 0 := by
  have hu : (u : ℤ_[p]) ≠ 0 := Units.ne_zero u
  have huInv : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ≠ 0 := Units.ne_zero u⁻¹
  have hmul :
      (u : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    simp
  have hval := congrArg PadicInt.valuation hmul
  rw [PadicInt.valuation_mul hu huInv, PadicInt.valuation_one] at hval
  omega

/-- Generic valuation obstruction for a prime power times a `p`-adic
integer unit to be an `n`-th power in `ℚ_[p]`. -/
theorem exponent_dvd_of_padicPrimePow_mul_unit_eq_power
    {p n e : ℕ} [Fact p.Prime]
    (u : ℤ_[p]ˣ) (z : ℚ_[p])
    (hpow : (p : ℚ_[p]) ^ e * ((u : ℤ_[p]) : ℚ_[p]) = z ^ n) :
    n ∣ e := by
  have hp : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : (((u : ℤ_[p]) : ℚ_[p])) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr (Units.ne_zero u)
  have hval := congrArg Padic.valuation hpow
  rw [Padic.valuation_mul (pow_ne_zero e hp) hu,
    Padic.valuation_pow, Padic.valuation_p,
    PadicInt.valuation_coe, padicIntUnit_valuation_eq_zero,
    mul_one, Nat.cast_zero, add_zero, Padic.valuation_pow] at hval
  have hdiv : (n : ℤ) ∣ (e : ℤ) := ⟨z.valuation, hval⟩
  exact_mod_cast hdiv

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- At thirteen, a power times an integral unit can be a nineteenth power
only when the exponent is divisible by nineteen. -/
theorem nineteen_dvd_exponent_of_thirteen_pow_mul_unit_eq_nineteenthPower
    (e : ℕ) (u : ℤ_[13]ˣ) (z : ℚ_[13])
    (hpow : (13 : ℚ_[13]) ^ e * ((u : ℤ_[13]) : ℚ_[13]) = z ^ 19) :
    19 ∣ e := by
  exact exponent_dvd_of_padicPrimePow_mul_unit_eq_power u z hpow

/-- In particular, a bare power of thirteen that is a nineteenth power has
exponent divisible by nineteen. -/
theorem nineteen_dvd_exponent_of_thirteen_pow_eq_nineteenthPower
    (e : ℕ) (z : ℚ_[13])
    (hpow : (13 : ℚ_[13]) ^ e = z ^ 19) :
    19 ∣ e := by
  apply nineteen_dvd_exponent_of_thirteen_pow_mul_unit_eq_nineteenthPower
    e (1 : ℤ_[13]ˣ) z
  simpa using hpow

/-- Concrete local Kummer exclusion: a nontrivial exponent below nineteen
cannot represent a nineteenth power in `ℚ_[13]`. -/
theorem thirteen_pow_not_nineteenthPower_of_exponent_lt
    (e : ℕ) (hePos : 0 < e) (heLt : e < 19) :
    ¬∃ z : ℚ_[13], (13 : ℚ_[13]) ^ e = z ^ 19 := by
  rintro ⟨z, hz⟩
  have hdvd := nineteen_dvd_exponent_of_thirteen_pow_eq_nineteenthPower e z hz
  exact (Nat.not_dvd_of_pos_of_lt hePos heLt) hdvd

end MazurTorsion.XOneThirteenLocalKummerValuation
