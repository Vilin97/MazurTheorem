/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

open scoped NumberField

/-- A class represented by an ideal is trivial when a coprime power of that ideal is principal. -/
theorem isPrincipal_of_isPrincipal_pow_of_coprime
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Fintype (ClassGroup A)]
    {p : ℕ}
    (H : p.Coprime <| Fintype.card <| ClassGroup A) {I : Ideal A}
    (hI : (I ^ p).IsPrincipal) : I.IsPrincipal := by
  by_cases Izero : I = 0
  · rw [Izero]
    exact bot_isPrincipal
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero _)] at hI ⊢
  swap
  · exact Izero
  swap
  · exact pow_ne_zero p Izero
  · rw [← orderOf_eq_one_iff, ← Nat.dvd_one, ← H, Nat.dvd_gcd_iff]
    refine ⟨?_, orderOf_dvd_card⟩
    rwa [orderOf_dvd_iff_pow_eq_one, ← map_pow, SubmonoidClass.mk_pow]
