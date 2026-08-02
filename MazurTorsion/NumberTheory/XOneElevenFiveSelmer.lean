/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneElevenFiveIsogeny
import MazurTorsion.NumberTheory.SelmerClassGroup
import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup

/-!
# The empty-support fifth-power Selmer calculation over `ℚ`

The `μ₅` side of the five-isogeny descent for `X₁(11)` reduces, after the
local image calculation, to the empty-support fifth-power Selmer group of
`ℚ`.  This file proves that group is trivial.

The proof uses the checked unit-to-Selmer-to-class-group exact sequence.
The class group of `ℤ` is trivial, and both units `1` and `-1` are fifth
powers.  The final theorem unfolds the quotient statement to the concrete
assertion that a rational unit whose finite valuations vanish modulo five is
an actual fifth power.

This is one arithmetic factor of the isogeny descent, not the full descent:
the local Kummer-map comparison and the ramified cyclic-character factor at
`11` remain separate obligations.
-/

open scoped nonZeroDivisors

namespace MazurTorsion.XOneEleven

open IsDedekindDomain
open IsDedekindDomain.selmerGroup

private theorem intUnits_fifthPower_range_eq_top :
    (powMonoidHom 5 : ℤˣ →* ℤˣ).range = ⊤ := by
  apply top_unique
  intro u _
  rcases Int.units_eq_one_or u with hu | hu
  · subst u
    exact ⟨1, by norm_num⟩
  · subst u
    refine ⟨-1, ?_⟩
    ext
    norm_num

private theorem intUnits_mod_fifthPowers_subsingleton :
    Subsingleton (ℤˣ ⧸ (powMonoidHom 5 : ℤˣ →* ℤˣ).range) := by
  rw [intUnits_fifthPower_range_eq_top]
  exact QuotientGroup.subsingleton_quotient_top

/-- Every class in the empty-support fifth-power Selmer group of `ℚ` is
trivial. -/
theorem ratEmptyFiveSelmer_eq_one
    (q : selmerGroup (R := ℤ) (K := ℚ)
      (S := (∅ : Set (HeightOneSpectrum ℤ))) (n := 5)) :
    q = 1 := by
  letI : Fact (0 < (5 : ℕ)) := ⟨by norm_num⟩
  letI : Subsingleton
      (ℤˣ ⧸ (powMonoidHom 5 : ℤˣ →* ℤˣ).range) :=
    intUnits_mod_fifthPowers_subsingleton
  have hclass :
      toClassGroup (R := ℤ) (K := ℚ) 5 q = 1 :=
    Subsingleton.elim _ _
  have hker : q ∈
      (toClassGroup (R := ℤ) (K := ℚ) 5).ker :=
    MonoidHom.mem_ker.mpr hclass
  obtain ⟨u, hu⟩ :=
    ker_le_fromUnitLift_range (R := ℤ) (K := ℚ) 5 hker
  have hu_one : u = 1 := Subsingleton.elim _ _
  subst u
  simpa using hu.symm

/-- The empty-support fifth-power Selmer group of `ℚ` is a singleton. -/
theorem ratEmptyFiveSelmer_subsingleton :
    Subsingleton
      (selmerGroup (R := ℤ) (K := ℚ)
        (S := (∅ : Set (HeightOneSpectrum ℤ))) (n := 5)) :=
  ⟨fun a b => (ratEmptyFiveSelmer_eq_one a).trans
    (ratEmptyFiveSelmer_eq_one b).symm⟩

/-- Concrete consumer of the Selmer computation: a nonzero rational number
whose valuation at every finite prime is divisible by five is an actual
fifth power in `ℚˣ`. -/
theorem exists_fifthPower_of_emptyFiveSelmer
    (a : ℚˣ)
    (ha : ∀ v : HeightOneSpectrum ℤ,
      v.valuationOfNeZeroMod 5 (QuotientGroup.mk a) = 1) :
    ∃ b : ℚˣ, b ^ 5 = a := by
  let q : selmerGroup (R := ℤ) (K := ℚ)
      (S := (∅ : Set (HeightOneSpectrum ℤ))) (n := 5) :=
    ⟨QuotientGroup.mk a, fun v _ => ha v⟩
  have hq : q = 1 := ratEmptyFiveSelmer_eq_one q
  have hmk : QuotientGroup.mk
      (s := (powMonoidHom 5 : ℚˣ →* ℚˣ).range) a = 1 :=
    congrArg Subtype.val hq
  exact (QuotientGroup.eq_one_iff a).mp hmk

end MazurTorsion.XOneEleven
