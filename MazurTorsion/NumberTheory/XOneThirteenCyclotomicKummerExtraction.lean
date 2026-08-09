/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCyclotomicClassNumber

/-!
# Principal-ideal extraction in the thirteenth cyclotomic field

Class number one makes every integral ideal of `ℚ(ζ₁₃)` principal.  Thus an
equality between a principal ideal and a nineteenth power of an ideal can be
lifted to an equality of elements, up to multiplication by an actual ring
unit.  No nonvanishing hypothesis is needed: the same argument includes the
zero ideal.
-/

namespace MazurTorsion.XOneThirteenCyclotomic

open Ideal NumberField

noncomputable section

local instance : IsPrincipalIdealRing (𝓞 ThirteenCyclotomicField) :=
  thirteenCyclotomic_isPrincipalIdealRing

/-- An element generates a nineteenth power of an integral ideal exactly
when it is a unit times a nineteenth power of an element generating that
ideal. -/
theorem span_eq_nineteenth_ideal_pow_iff
    (x : 𝓞 ThirteenCyclotomicField)
    (I : Ideal (𝓞 ThirteenCyclotomicField)) :
    Ideal.span {x} = I ^ 19 ↔
      ∃ (u : (𝓞 ThirteenCyclotomicField)ˣ)
        (y : 𝓞 ThirteenCyclotomicField),
        Ideal.span {y} = I ∧ x = (u : 𝓞 ThirteenCyclotomicField) * y ^ 19 := by
  let y := Submodule.IsPrincipal.generator I
  have hy : Ideal.span {y} = I := Ideal.span_singleton_generator I
  constructor
  · intro h
    have hxy : Ideal.span {x} = Ideal.span {y ^ 19} := by
      calc
        Ideal.span {x} = I ^ 19 := h
        _ = Ideal.span {y} ^ 19 := by rw [hy]
        _ = Ideal.span {y ^ 19} := Ideal.span_singleton_pow y 19
    have hassociated : Associated x (y ^ 19) :=
      Ideal.span_singleton_eq_span_singleton.mp hxy
    obtain ⟨u, hu⟩ := hassociated.symm
    refine ⟨u, y, hy, ?_⟩
    simpa [mul_comm] using hu.symm
  · rintro ⟨u, y, hy, hx⟩
    rw [hx, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, hy]

/-- Extraction-only form of `span_eq_nineteenth_ideal_pow_iff`, convenient
for downstream Kummer arguments. -/
theorem exists_unit_mul_nineteenth_power_of_span_eq_ideal_pow
    (x : 𝓞 ThirteenCyclotomicField)
    (I : Ideal (𝓞 ThirteenCyclotomicField))
    (h : Ideal.span {x} = I ^ 19) :
    ∃ (u : (𝓞 ThirteenCyclotomicField)ˣ)
      (y : 𝓞 ThirteenCyclotomicField),
      x = (u : 𝓞 ThirteenCyclotomicField) * y ^ 19 := by
  obtain ⟨u, y, _, hxy⟩ :=
    (span_eq_nineteenth_ideal_pow_iff x I).mp h
  exact ⟨u, y, hxy⟩

/-- Concrete ideal-power consumer for the checked prime above `3`: its
nineteenth power is generated precisely by unit multiples of the nineteenth
power of the norm-`27` generator. -/
theorem span_eq_twentySevenIdeal_pow_nineteen_iff
    (x : 𝓞 ThirteenCyclotomicField) :
    Ideal.span {x} = twentySevenIdeal ^ 19 ↔
      ∃ u : (𝓞 ThirteenCyclotomicField)ˣ,
        x = (u : 𝓞 ThirteenCyclotomicField) *
          alphaTwentySevenInteger ^ 19 := by
  constructor
  · intro h
    have hxy : Ideal.span {x} =
        Ideal.span {alphaTwentySevenInteger ^ 19} := by
      simpa [twentySevenIdeal, Ideal.span_singleton_pow] using h
    have hassociated : Associated x (alphaTwentySevenInteger ^ 19) :=
      Ideal.span_singleton_eq_span_singleton.mp hxy
    obtain ⟨u, hu⟩ := hassociated.symm
    refine ⟨u, ?_⟩
    simpa [mul_comm] using hu.symm
  · rintro ⟨u, hx⟩
    rw [hx, Ideal.span_singleton_mul_left_unit u.isUnit,
      twentySevenIdeal, Ideal.span_singleton_pow]

end

end MazurTorsion.XOneThirteenCyclotomic
