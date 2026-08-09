/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicStickelbergerTwoResidue

/-!
# Faithfulness of a nontrivial cyclotomic residue orbit

Assume that the total residue symbol of `eta` has the inverse-character
Galois weight supplied by `HasDirectCharacterSquareResidueWeightAt`.  A
collision in the Galois orbit of the denominator prime then gives two
distinct powers of the base residue symbol which are equal.  Since that
symbol is a `p`-th root of unity and `p` is prime, the symbol must be one.

Consequently, after the algebraic weight interface has been established, a
nontrivial residue symbol can occur only when the finite prime has a faithful,
full Galois orbit.  No reciprocity law or Jacobi-sum factorization is used in
this reduction.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

variable {p : ℕ} [Fact p.Prime]

local notation "OK" =>
  NumberField.RingOfIntegers (PrimeCyclotomicField p)

private theorem rootsOfUnity_eq_one_of_distinct_powers
    (x : rootsOfUnity p (PrimeCyclotomicField p))
    {m n : ℕ} (hm : m < p) (hn : n < p) (hmn : m ≠ n)
    (hpow : x ^ m = x ^ n) :
    x = 1 := by
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    exact x.property
  rcases lt_or_gt_of_ne hmn with hmn_lt | hnm_lt
  · have hd_pos : 0 < n - m := Nat.sub_pos_iff_lt.mpr hmn_lt
    have hd_lt : n - m < p := (Nat.sub_le n m).trans_lt hn
    have hd_pow : x ^ (n - m) = 1 := by
      have hsplit : x ^ m = x ^ m * x ^ (n - m) := by
        calc
          x ^ m = x ^ n := hpow
          _ = x ^ (m + (n - m)) := by rw [Nat.add_sub_of_le hmn_lt.le]
          _ = x ^ m * x ^ (n - m) := pow_add x m (n - m)
      have hcancel : x ^ m * 1 = x ^ m * x ^ (n - m) := by
        simpa only [mul_one] using hsplit
      exact (mul_left_cancel hcancel).symm
    have hd_coprime : (n - m).Coprime p :=
      (Nat.coprime_of_lt_prime hd_pos.ne' hd_lt (Fact.out : p.Prime)).symm
    exact (pow_eq_one_iff_of_coprime hd_coprime).mp ⟨hd_pow, hxp⟩
  · have hd_pos : 0 < m - n := Nat.sub_pos_iff_lt.mpr hnm_lt
    have hd_lt : m - n < p := (Nat.sub_le m n).trans_lt hm
    have hd_pow : x ^ (m - n) = 1 := by
      have hsplit : x ^ n = x ^ n * x ^ (m - n) := by
        calc
          x ^ n = x ^ m := hpow.symm
          _ = x ^ (n + (m - n)) := by rw [Nat.add_sub_of_le hnm_lt.le]
          _ = x ^ n * x ^ (m - n) := pow_add x n (m - n)
      have hcancel : x ^ n * 1 = x ^ n * x ^ (m - n) := by
        simpa only [mul_one] using hsplit
      exact (mul_left_cancel hcancel).symm
    have hd_coprime : (m - n).Coprime p :=
      (Nat.coprime_of_lt_prime hd_pos.ne' hd_lt (Fact.out : p.Prime)).symm
    exact (pow_eq_one_iff_of_coprime hd_coprime).mp ⟨hd_pow, hxp⟩

/-- A collision between two distinct direct-character representatives in the
orbit of `v` forces the base total residue symbol to be trivial. -/
theorem totalPthPowerResidueSymbolAtPrime_eq_one_of_orbit_collision
    {eta : OK} {v : FinitePrime (PrimeCyclotomicField p)}
    (hweight : HasDirectCharacterSquareResidueWeightAt eta v)
    {a b : (ZMod p)ˣ} (hab : a ≠ b)
    (horbit : mapFinitePrime (galoisOfDirectCharacter a) v =
      mapFinitePrime (galoisOfDirectCharacter b) v) :
    totalPthPowerResidueSymbolAtPrime eta v = 1 := by
  let x := totalPthPowerResidueSymbolAtPrime eta v
  let m := ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val
  let n := ((b⁻¹ : (ZMod p)ˣ) : ZMod p).val
  have hm : m < p := ZMod.val_lt _
  have hn : n < p := ZMod.val_lt _
  have hmn : m ≠ n := by
    intro hval
    apply hab
    apply inv_injective
    apply Units.ext
    exact ZMod.val_injective p hval
  have hpow : x ^ m = x ^ n := by
    calc
      x ^ m = totalPthPowerResidueSymbolAtPrime eta
          (mapFinitePrime (galoisOfDirectCharacter a) v) := by
        simpa only [x, m, directCharacter_galoisOfDirectCharacter] using
          (hweight (galoisOfDirectCharacter a)).symm
      _ = totalPthPowerResidueSymbolAtPrime eta
          (mapFinitePrime (galoisOfDirectCharacter b) v) := by rw [horbit]
      _ = x ^ n := by
        simpa only [x, n, directCharacter_galoisOfDirectCharacter] using
          hweight (galoisOfDirectCharacter b)
  exact rootsOfUnity_eq_one_of_distinct_powers x hm hn hmn hpow

/-- Under inverse-character residue weight, failure of injectivity of the
direct-character orbit map forces the base total residue symbol to be one.
Thus only the faithful/full-orbit case can retain a nontrivial symbol. -/
theorem totalPthPowerResidueSymbolAtPrime_eq_one_of_not_injective_orbit
    {eta : OK} {v : FinitePrime (PrimeCyclotomicField p)}
    (hweight : HasDirectCharacterSquareResidueWeightAt eta v)
    (horbit : ¬ Function.Injective (fun a : (ZMod p)ˣ =>
      mapFinitePrime (galoisOfDirectCharacter a) v)) :
    totalPthPowerResidueSymbolAtPrime eta v = 1 := by
  obtain ⟨a, b, hab_orbit, hab⟩ := Function.not_injective_iff.mp horbit
  exact totalPthPowerResidueSymbolAtPrime_eq_one_of_orbit_collision
    hweight hab hab_orbit

end NumberTheory.CyclotomicCharacter.InverseExtension
