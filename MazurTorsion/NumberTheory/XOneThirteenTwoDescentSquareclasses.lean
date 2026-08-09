/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod

/-!
# A finite squareclass-coordinate verifier for `X₁(13)`

This file checks the linear-algebra part of a possible `2`-descent on the
sextic field attached to

`x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

The coordinate convention has six generators: three generators supported at
the primes above `2` and `13`, two fundamental units, and one generator of
the fourth roots of unity.  Exact number-field arithmetic gives the two norm
conditions

`e₀ = 0`, `e₁ + e₂ = 0`,

while the rational scalars `2` and `13` give the relations

`(0,0,0,0,0,1)` and `(0,1,1,1,0,1)`.

The declarations below independently verify that these equations and
relations leave exactly four classes, canonically described by two bits.  No
claim is made here that the displayed coordinates exhaust a Selmer group:
the number-field generator theorem and the local Kummer-image calculation
remain separate arithmetic obligations.

The descent schema is from Michael Stoll, *Implementing 2-descent for
Jacobians of hyperelliptic curves*, Acta Arith. 98 (2001), Section 5,
DOI `10.4064/aa98-3-4`.  The publisher supplies the source PDF at
`https://www.impan.pl/shop/en/publication/transaction/download/product/83397`
under its displayed CC-BY licence.  This file contains no third-party code;
all finite identities are checked by Lean.
-/

namespace MazurTorsion.XOneThirteenTwoDescentSquareclasses

abbrev F2 := ZMod 2

private instance : NeZero (2 : ℕ) := ⟨by decide⟩
private instance : Fintype F2 := ZMod.fintype 2

/-- Six parity coordinates before imposing norms and rational scalars. -/
@[ext]
structure RawCoordinates where
  e0 : F2
  e1 : F2
  e2 : F2
  e3 : F2
  e4 : F2
  e5 : F2
deriving DecidableEq

/-- The two norm-parity equations for the audited generator convention. -/
def NormCompatible (v : RawCoordinates) : Prop :=
  v.e0 = 0 ∧ v.e1 + v.e2 = 0

/-- The squareclass relation supplied by the rational scalar `2`. -/
def rationalTwoRelation : RawCoordinates :=
  ⟨0, 0, 0, 0, 0, 1⟩

/-- The squareclass relation supplied by the rational scalar `13`. -/
def rationalThirteenRelation : RawCoordinates :=
  ⟨0, 1, 1, 1, 0, 1⟩

/-- Equivalence modulo the two audited rational-scalar relations. -/
def RationallyEquivalent (v w : RawCoordinates) : Prop :=
  ∃ a b : F2,
    w.e0 = v.e0 ∧
    w.e1 = v.e1 + b ∧
    w.e2 = v.e2 + b ∧
    w.e3 = v.e3 + b ∧
    w.e4 = v.e4 ∧
    w.e5 = v.e5 + a + b

/-- The two invariant bits left by the norm equations and scalar relations. -/
def canonicalBits (v : RawCoordinates) : F2 × F2 :=
  (v.e1 + v.e3, v.e4)

/-- Canonical norm-compatible representative of a pair of invariant bits. -/
def representative (z : F2 × F2) : RawCoordinates :=
  ⟨0, z.1, z.1, 0, z.2, 0⟩

theorem representative_normCompatible (z : F2 × F2) :
    NormCompatible (representative z) := by
  simp [NormCompatible, representative, CharTwo.add_self_eq_zero]

@[simp]
theorem canonicalBits_representative (z : F2 × F2) :
    canonicalBits (representative z) = z := by
  ext <;> simp [canonicalBits, representative]

/-- The two displayed bits are a complete invariant of norm-compatible
coordinates modulo rational scalars. -/
theorem rationallyEquivalent_iff_canonicalBits_eq
    (v w : RawCoordinates) (hv : NormCompatible v)
    (hw : NormCompatible w) :
    RationallyEquivalent v w ↔ canonicalBits v = canonicalBits w := by
  rcases hv with ⟨hv₀, hv₁₂⟩
  rcases hw with ⟨hw₀, hw₁₂⟩
  constructor
  · rintro ⟨a, b, h₀, h₁, h₂, h₃, h₄, h₅⟩
    apply Prod.ext
    · change v.e1 + v.e3 = w.e1 + w.e3
      symm
      rw [h₁, h₃]
      calc
        (v.e1 + b) + (v.e3 + b) =
            (v.e1 + v.e3) + (b + b) := by abel
        _ = v.e1 + v.e3 := by rw [CharTwo.add_self_eq_zero, add_zero]
    · exact h₄.symm
  · intro hbits
    have hbit₀ : w.e1 + w.e3 = v.e1 + v.e3 := by
      simpa [canonicalBits] using (congrArg Prod.fst hbits).symm
    have hbit₁ : w.e4 = v.e4 := by
      simpa [canonicalBits] using (congrArg Prod.snd hbits).symm
    let b : F2 := w.e1 - v.e1
    let a : F2 := w.e5 - v.e5 - b
    refine ⟨a, b, hw₀.trans hv₀.symm, ?_, ?_, ?_, hbit₁, ?_⟩
    · dsimp [b]
      abel
    · have hv₂ : v.e2 = v.e1 := (CharTwo.add_eq_zero.mp hv₁₂).symm
      have hw₂ : w.e2 = w.e1 := (CharTwo.add_eq_zero.mp hw₁₂).symm
      rw [hv₂, hw₂]
      dsimp [b]
      rw [CharTwo.sub_eq_add]
      symm
      calc
        v.e1 + (w.e1 + v.e1) = w.e1 + (v.e1 + v.e1) := by abel
        _ = w.e1 := by rw [CharTwo.add_self_eq_zero, add_zero]
    · dsimp [b]
      rw [CharTwo.sub_eq_add]
      calc
        w.e3 = w.e1 + (w.e1 + w.e3) := by
          rw [CharTwo.add_cancel_left]
        _ = w.e1 + (v.e1 + v.e3) := by rw [hbit₀]
        _ = v.e3 + (w.e1 + v.e1) := by abel
    · dsimp [a]
      abel

/-- Every norm-compatible vector is equivalent to its canonical
representative. -/
theorem rationallyEquivalent_representative_canonicalBits
    (v : RawCoordinates) (hv : NormCompatible v) :
    RationallyEquivalent v (representative (canonicalBits v)) := by
  apply (rationallyEquivalent_iff_canonicalBits_eq v
    (representative (canonicalBits v)) hv
    (representative_normCompatible (canonicalBits v))).2
  simp

/-- The finite checked target for the surviving global squareclasses. -/
abbrev GlobalSquareclassCertificate := F2 × F2

/-- Exactly four coordinate classes survive the audited global equations. -/
theorem card_globalSquareclassCertificate :
    Fintype.card GlobalSquareclassCertificate = 4 := by
  decide

/-- The two fundamental-unit coordinates give the canonical four
representatives. -/
theorem representative_eq_fundamental_unit_coordinates
    (z : GlobalSquareclassCertificate) :
    representative z = ⟨0, z.1, z.1, 0, z.2, 0⟩ := rfl

end MazurTorsion.XOneThirteenTwoDescentSquareclasses
