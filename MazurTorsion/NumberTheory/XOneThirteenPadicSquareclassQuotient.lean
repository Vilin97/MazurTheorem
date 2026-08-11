/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPadicSquareclass
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The dyadic squareclass quotient

This file packages the explicit normal form over `Q_2` as a statement about
the quotient of the unit group by its subgroup of squares.  It proves that
the classes of `-1`, `2`, and `5` generate and that the quotient has at most
eight elements.  It does not assert that the eight displayed classes are
distinct.
-/

namespace MazurTorsion.XOneThirteenPadicSquareclassQuotient

open XOneThirteenPadicSquareclass

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The multiplicative squareclass group of `Q_2`. -/
abbrev Q2Squareclasses :=
  ℚ_[2]ˣ ⧸ Subgroup.square ℚ_[2]ˣ

/-- The canonical projection to dyadic squareclasses. -/
def classMap : ℚ_[2]ˣ →* Q2Squareclasses :=
  QuotientGroup.mk' (Subgroup.square ℚ_[2]ˣ)

/-- The unit represented by `-1`. -/
def negOneUnit : ℚ_[2]ˣ := Units.mk0 (-1) (by norm_num)

/-- The unit represented by `2`. -/
def twoUnit : ℚ_[2]ˣ := Units.mk0 2 (by norm_num)

/-- The unit represented by `5`. -/
def fiveUnit : ℚ_[2]ˣ := Units.mk0 5 (by norm_num)

/-- The squareclass represented by `-1`. -/
def negOneClass : Q2Squareclasses := classMap negOneUnit

/-- The squareclass represented by `2`. -/
def twoClass : Q2Squareclasses := classMap twoUnit

/-- The squareclass represented by `5`. -/
def fiveClass : Q2Squareclasses := classMap fiveUnit

/-- The eight Boolean triples used to enumerate the quotient. -/
abbrev BitTriple := Bool × Bool × Bool

/-- The class attached to a Boolean exponent triple. -/
def classOfBits : BitTriple → Q2Squareclasses
  | (e, f, g) =>
      bitPow negOneClass e * bitPow twoClass f * bitPow fiveClass g

/-- The eight displayed Boolean triples cover every dyadic squareclass. -/
theorem classOfBits_surjective : Function.Surjective classOfBits := by
  intro c
  obtain ⟨u, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.square ℚ_[2]ˣ) c
  obtain ⟨s, e, f, g, hform⟩ :=
    nonzero_squareclass_normalForm (u : ℚ_[2]) u.ne_zero
  have hs : s ≠ 0 := by
    intro hs
    apply u.ne_zero
    rw [hform, hs]
    simp
  let sUnit : ℚ_[2]ˣ := Units.mk0 s hs
  have hUnits :
      u = sUnit ^ 2 * bitPow negOneUnit e *
        bitPow twoUnit f * bitPow fiveUnit g := by
    apply Units.ext
    simpa [sUnit, negOneUnit, twoUnit, fiveUnit, bitPow] using hform
  have hsClass : classMap (sUnit ^ 2) = 1 := by
    apply (QuotientGroup.eq_one_iff (sUnit ^ 2)).2
    exact ⟨sUnit, pow_two sUnit⟩
  refine ⟨(e, f, g), ?_⟩
  symm
  calc
    classMap u = classMap
        (sUnit ^ 2 * bitPow negOneUnit e *
          bitPow twoUnit f * bitPow fiveUnit g) :=
      congrArg (fun v : ℚ_[2]ˣ ↦ classMap v) hUnits
    _ = classOfBits (e, f, g) := by
      simp [classOfBits, bitPow, hsClass, negOneClass, twoClass,
        fiveClass]

/-- The three standard dyadic classes generate the squareclass quotient. -/
theorem standardClasses_generate :
    Subgroup.closure
      ({negOneClass, twoClass, fiveClass} : Set Q2Squareclasses) = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  obtain ⟨⟨e, f, g⟩, h⟩ := classOfBits_surjective x
  rw [← h]
  simp only [classOfBits, bitPow]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact (Subgroup.closure
        ({negOneClass, twoClass, fiveClass} : Set Q2Squareclasses)).pow_mem
          (Subgroup.subset_closure (by simp)) _
    · exact (Subgroup.closure
        ({negOneClass, twoClass, fiveClass} : Set Q2Squareclasses)).pow_mem
          (Subgroup.subset_closure (by simp)) _
  · exact (Subgroup.closure
      ({negOneClass, twoClass, fiveClass} : Set Q2Squareclasses)).pow_mem
        (Subgroup.subset_closure (by simp)) _

/-- The dyadic squareclass quotient is finite. -/
instance q2Squareclasses_finite : Finite Q2Squareclasses :=
  Finite.of_surjective classOfBits classOfBits_surjective

/-- There are at most eight dyadic squareclasses. -/
theorem natCard_q2Squareclasses_le_eight :
    Nat.card Q2Squareclasses ≤ 8 :=
  (Nat.card_le_card_of_surjective classOfBits
    classOfBits_surjective).trans_eq (by simp [BitTriple])

end

end MazurTorsion.XOneThirteenPadicSquareclassQuotient
