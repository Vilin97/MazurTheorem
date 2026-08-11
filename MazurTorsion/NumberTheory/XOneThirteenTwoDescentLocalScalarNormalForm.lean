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

end

end MazurTorsion.XOneThirteenTwoDescentLocalScalarNormalForm
