/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentLocalScalarGenerators

/-!
# Scalar normal form in the dyadic sextic algebra

Combining the checked `ℚ₂` squareclass normal form with
`-1 = i²` and `2 = lambda * pi²` shows that every scalar unit, after mapping
to the dyadic sextic algebra, is a square times optional factors `lambda`
and `5`.  This is the exact bridge from arbitrary scalar ambiguity in the
fake Kummer quotient to the finite local-intersection certificate.
-/

namespace MazurTorsion.XOneThirteenTwoDescentLocalScalarNormalForm

open XOneThirteenPadicSquareclass
open XOneThirteenTwoDescentLocalKummerPoints
open XOneThirteenTwoDescentLocalKummerQuotient
open XOneThirteenTwoDescentLocalScalarGenerators

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem square_root_ne_zero_of_normalForm
    (q : ℚ_[2]ˣ) (s : ℚ_[2]) (e f g : Bool)
    (hform : (q : ℚ_[2]) =
      s ^ 2 * bitPow (-1 : ℚ_[2]) e *
        bitPow ((2 : ℕ) : ℚ_[2]) f *
        bitPow ((5 : ℕ) : ℚ_[2]) g) :
    s ≠ 0 := by
  intro hs
  rw [hs, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
    zero_mul, zero_mul] at hform
  exact q.ne_zero hform

/-- Every dyadic scalar unit maps to a square times optional `lambda` and
`5` factors in the explicit sextic algebra. -/
theorem scalarUnit_normalForm (q : ℚ_[2]ˣ) :
    ∃ (w : MagmaPadicAlgebraˣ) (f g : Bool),
      scalarUnitMap q = w ^ 2 * bitPow padicLambdaUnit f *
        bitPow (scalarUnitMap padicFiveUnit) g := by
  obtain ⟨s, e, f, g, hform⟩ :=
    nonzero_squareclass_normalForm (q : ℚ_[2]) q.ne_zero
  have hs : s ≠ 0 :=
    square_root_ne_zero_of_normalForm q s e f g hform
  let sUnit : ℚ_[2]ˣ := Units.mk0 s hs
  have hunit : q = sUnit ^ 2 * bitPow padicMinusOneUnit e *
      bitPow padicTwoUnit f * bitPow padicFiveUnit g := by
    apply Units.ext
    simpa [sUnit, bitPow, padicMinusOneUnit,
      padicTwoUnit, padicFiveUnit] using hform
  have hmapped : scalarUnitMap q =
      (scalarUnitMap sUnit) ^ 2 *
        bitPow (scalarUnitMap padicMinusOneUnit) e *
        bitPow (scalarUnitMap padicTwoUnit) f *
        bitPow (scalarUnitMap padicFiveUnit) g := by
    simpa only [map_mul, map_pow, bitPow] using congrArg scalarUnitMap hunit
  refine ⟨scalarUnitMap sUnit * bitPow padicIUnit e *
      bitPow padicPiUnit f, f, g, ?_⟩
  rw [hmapped, scalarMinusOne_eq_padicI_sq,
    scalarTwo_eq_padicLambda_mul_padicPi_sq]
  cases e <;> cases f <;> cases g <;>
    simp only [bitPow_false, bitPow_true, mul_one, mul_pow] <;>
    ac_rfl

/-- In element-valued form, every scalar ambiguity has the same two finite
residual factors. -/
theorem scalarUnit_normalForm_values (q : ℚ_[2]ˣ) :
    ∃ (w : MagmaPadicAlgebraˣ) (f g : Bool),
      (scalarUnitMap q : MagmaPadicAlgebra) =
        (w : MagmaPadicAlgebra) ^ 2 *
          (bitPow padicLambdaUnit f : MagmaPadicAlgebraˣ) *
          (bitPow (scalarUnitMap padicFiveUnit) g :
            MagmaPadicAlgebraˣ) := by
  obtain ⟨w, f, g, h⟩ := scalarUnit_normalForm q
  exact ⟨w, f, g, congrArg Units.val h⟩

/-- Equality in the local fake Kummer quotient is exactly equality after
multiplying by a square and a scalar unit. -/
theorem localKummerClass_eq_iff_square_scalar
    (u v : MagmaPadicAlgebraˣ) :
    localKummerClass u = localKummerClass v ↔
      ∃ (w : MagmaPadicAlgebraˣ) (q : ℚ_[2]ˣ),
        u = v * w ^ 2 * scalarUnitMap q := by
  constructor
  · intro h
    have hmem : u / v ∈ localKummerRelations :=
      QuotientGroup.eq_iff_div_mem.mp h
    rcases Subgroup.mem_sup.mp hmem with
      ⟨y, hy, z, hz, hyz⟩
    rcases hy with ⟨w, rfl⟩
    rcases hz with ⟨q, rfl⟩
    refine ⟨w, q, ?_⟩
    calc
      u = (u / v) * v := by simp
      _ = (w * w * scalarUnitMap q) * v := by rw [← hyz]
      _ = v * w ^ 2 * scalarUnitMap q := by
        simp only [pow_two]
        ac_rfl
  · rintro ⟨w, q, rfl⟩
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hw : w ^ 2 ∈ Subgroup.square MagmaPadicAlgebraˣ :=
      (show IsSquare (w ^ 2) from ⟨w, by simp [pow_two]⟩)
    have hq : scalarUnitMap q ∈ scalarUnitMap.range := ⟨q, rfl⟩
    have hproduct :
        w ^ 2 * scalarUnitMap q ∈ localKummerRelations :=
      Subgroup.mul_mem_sup hw hq
    have hcancel :
        (v * w ^ 2 * scalarUnitMap q) / v =
          w ^ 2 * scalarUnitMap q := by
      rw [div_eq_mul_inv]
      calc
        v * w ^ 2 * scalarUnitMap q * v⁻¹ =
            (v * v⁻¹) * (w ^ 2 * scalarUnitMap q) := by ac_rfl
        _ = w ^ 2 * scalarUnitMap q := by simp
    rw [hcancel]
    exact hproduct

/-- Consequently, equality in the fake quotient has the exact finite normal
form used by the local certificate: only optional `lambda` and `5` factors
remain after absorbing all other terms into a square. -/
theorem localKummerClass_eq_implies_finite_normalForm
    (u v : MagmaPadicAlgebraˣ)
    (h : localKummerClass u = localKummerClass v) :
    ∃ (w : MagmaPadicAlgebraˣ) (f g : Bool),
      u = v * w ^ 2 * bitPow padicLambdaUnit f *
        bitPow (scalarUnitMap padicFiveUnit) g := by
  obtain ⟨w, q, huv⟩ :=
    (localKummerClass_eq_iff_square_scalar u v).mp h
  obtain ⟨s, f, g, hq⟩ := scalarUnit_normalForm q
  refine ⟨w * s, f, g, ?_⟩
  rw [huv, hq]
  simp only [mul_pow]
  ac_rfl

end

end MazurTorsion.XOneThirteenTwoDescentLocalScalarNormalForm
