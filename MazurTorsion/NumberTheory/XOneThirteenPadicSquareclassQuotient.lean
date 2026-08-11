/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPadicSquareclass
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Ring

/-!
# The dyadic squareclass quotient

This file packages the explicit normal form over `Q_2` as a statement about
the quotient of the unit group by its subgroup of squares.  It proves that
the classes of `-1`, `2`, and `5` give exactly the eight elements of the
quotient.
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

/-- The unit represented by a Boolean exponent triple. -/
def unitOfBits : BitTriple → ℚ_[2]ˣ
  | (e, f, g) =>
      bitPow negOneUnit e * bitPow twoUnit f * bitPow fiveUnit g

/-- The class attached to a Boolean exponent triple. -/
def classOfBits : BitTriple → Q2Squareclasses
  | b => classMap (unitOfBits b)

@[simp]
theorem classOfBits_apply (e f g : Bool) :
    classOfBits (e, f, g) =
      bitPow negOneClass e * bitPow twoClass f * bitPow fiveClass g := by
  simp [classOfBits, unitOfBits, negOneClass, twoClass, fiveClass,
    bitPow]

private def oddUnit (e g : Bool) : ℚ_[2]ˣ :=
  bitPow negOneUnit e * bitPow fiveUnit g

private def negOnePadicUnit : ℤ_[2]ˣ :=
  -1

private theorem norm_five_q2 : ‖(5 : ℚ_[2])‖ = 1 := by
  have hfive : ((5 : ℚ_[2])).valuation = 0 := by
    change Padic.valuation (((5 : ℕ) : ℚ_[2])) = 0
    rw [Padic.valuation_natCast,
      padicValNat.eq_zero_of_not_dvd (by decide)]
    norm_num
  rw [Padic.norm_eq_zpow_neg_valuation (by norm_num), hfive]
  simp

private def fivePadicUnit : ℤ_[2]ˣ :=
  PadicInt.mkUnits norm_five_q2

private theorem fivePadicUnit_val :
    ((fivePadicUnit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  apply Subtype.coe_injective
  change
    ((((fivePadicUnit : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2])) =
      (((5 : ℤ_[2]) : ℚ_[2]))
  calc
    ((((fivePadicUnit : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2])) = (5 : ℚ_[2]) := by
      exact PadicInt.mkUnits_eq norm_five_q2
    _ = (((5 : ℤ_[2]) : ℚ_[2])) :=
      (PadicInt.coe_natCast 5).symm

private theorem fivePadicUnit_coe :
    (((fivePadicUnit : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) = (5 : ℚ_[2]) :=
  PadicInt.mkUnits_eq norm_five_q2

private theorem fivePadicUnit_mod_eight :
    PadicInt.toZModPow 3 ((fivePadicUnit : ℤ_[2]ˣ) : ℤ_[2]) =
      ((5 : ℕ) : ZMod 8) := by
  rw [fivePadicUnit_val]
  exact map_natCast (PadicInt.toZModPow 3) 5

private def oddPadicUnit (e g : Bool) : ℤ_[2]ˣ :=
  bitPow negOnePadicUnit e * bitPow fivePadicUnit g

private theorem unitOfBits_valuation (e f g : Bool) :
    ((unitOfBits (e, f, g) : ℚ_[2]ˣ) : ℚ_[2]).valuation =
      f.toNat := by
  have hneg : ((-1 : ℚ_[2])).valuation = 0 := by
    change Padic.valuation (((-1 : ℤ) : ℚ_[2])) = 0
    rw [Padic.valuation_intCast,
      padicValInt.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  change
    ((bitPow (-1 : ℚ_[2]) e * bitPow (2 : ℚ_[2]) f) *
      bitPow (5 : ℚ_[2]) g).valuation = f.toNat
  rw [Padic.valuation_mul (mul_ne_zero (by simp [bitPow]) (by simp [bitPow]))
      (by simp [bitPow]),
    Padic.valuation_mul (by simp [bitPow]) (by simp [bitPow])]
  simp [bitPow, hneg]

private theorem unitOfBits_div_same_twoBit
    (e₁ e₂ f g₁ g₂ : Bool) :
    unitOfBits (e₁, f, g₁) / unitOfBits (e₂, f, g₂) =
      oddUnit e₁ g₁ / oddUnit e₂ g₂ := by
  cases f
  · simp [unitOfBits, oddUnit, bitPow]
  · simp only [unitOfBits, bitPow_true]
    rw [show bitPow negOneUnit e₁ * twoUnit * bitPow fiveUnit g₁ =
        oddUnit e₁ g₁ * twoUnit by
          simp only [oddUnit]
          ac_rfl,
      show bitPow negOneUnit e₂ * twoUnit * bitPow fiveUnit g₂ =
        oddUnit e₂ g₂ * twoUnit by
          simp only [oddUnit]
          ac_rfl,
      mul_div_mul_right_eq_div]

private theorem unitOfBits_div_valuation
    (e₁ e₂ f₁ f₂ g₁ g₂ : Bool) :
    ((((unitOfBits (e₁, f₁, g₁) /
        unitOfBits (e₂, f₂, g₂) : ℚ_[2]ˣ)) : ℚ_[2])).valuation =
      (f₁.toNat : ℤ) - f₂.toNat := by
  rw [Units.val_div_eq_div_val]
  change
    (((unitOfBits (e₁, f₁, g₁) : ℚ_[2]ˣ) : ℚ_[2]) /
      ((unitOfBits (e₂, f₂, g₂) : ℚ_[2]ˣ) : ℚ_[2])).valuation =
        (f₁.toNat : ℤ) - f₂.toNat
  rw [div_eq_mul_inv,
    Padic.valuation_mul (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)),
    Padic.valuation_inv, unitOfBits_valuation, unitOfBits_valuation]
  ring

private theorem oddPadicUnit_coe (e g : Bool) :
    (((oddPadicUnit e g : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) =
      ((oddUnit e g : ℚ_[2]ˣ) : ℚ_[2]) := by
  cases e <;> cases g
  · simp [oddPadicUnit, oddUnit, bitPow]
  · simpa only [oddPadicUnit, oddUnit, bitPow_false, bitPow_true,
      one_mul, fiveUnit, Units.val_mk0] using fivePadicUnit_coe
  · simp [oddPadicUnit, oddUnit, negOnePadicUnit, negOneUnit, bitPow,
      PadicInt.coe_neg, PadicInt.coe_one]
  · have h := congrArg Neg.neg fivePadicUnit_coe
    simpa only [oddPadicUnit, oddUnit, bitPow_true, negOnePadicUnit,
      negOneUnit, fiveUnit, Units.val_mul, PadicInt.coe_mul,
      Units.val_neg, Units.val_mk0, PadicInt.coe_neg,
      PadicInt.coe_one, neg_one_mul] using h

private theorem oddPadicUnit_mod_eight (e g : Bool) :
    PadicInt.toZModPow 3 ((oddPadicUnit e g : ℤ_[2]ˣ) : ℤ_[2]) =
      bitPow (-1 : ZMod 8) e *
        bitPow ((5 : ℕ) : ZMod 8) g := by
  cases e <;> cases g
  · simp [oddPadicUnit, bitPow]
  · simpa only [oddPadicUnit, bitPow_false, bitPow_true, one_mul] using
      fivePadicUnit_mod_eight
  · simp [oddPadicUnit, negOnePadicUnit, bitPow]
  · have h := congrArg Neg.neg fivePadicUnit_mod_eight
    simpa only [oddPadicUnit, bitPow_true, negOnePadicUnit,
      Units.val_mul, Units.val_neg, neg_mul, one_mul, map_neg,
      map_one] using h

private theorem zmodEight_bitGenerators_injective :
    Function.Injective
      (fun b : Bool × Bool ↦
        bitPow (-1 : ZMod 8) b.1 *
          bitPow ((5 : ℕ) : ZMod 8) b.2) := by
  decide

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
      rw [classOfBits_apply]
      simp [bitPow, hsClass, negOneClass, twoClass, fiveClass]

/-- The eight displayed Boolean triples represent distinct dyadic
squareclasses. -/
theorem classOfBits_injective : Function.Injective classOfBits := by
  rintro ⟨e₁, f₁, g₁⟩ ⟨e₂, f₂, g₂⟩ hclass
  have hclass' :
      (unitOfBits (e₁, f₁, g₁) : Q2Squareclasses) =
        (unitOfBits (e₂, f₂, g₂) : Q2Squareclasses) := by
    exact hclass
  have hmem :
      unitOfBits (e₁, f₁, g₁) /
          unitOfBits (e₂, f₂, g₂) ∈
        Subgroup.square ℚ_[2]ˣ :=
    (QuotientGroup.eq_iff_div_mem).mp hclass'
  obtain ⟨t, ht⟩ := (Subgroup.mem_square.mp hmem)
  have hval :
      (f₁.toNat : ℤ) - f₂.toNat =
        2 * (((t : ℚ_[2]ˣ) : ℚ_[2])).valuation := by
    have hval' := congrArg
      (fun u : ℚ_[2]ˣ ↦ ((u : ℚ_[2])).valuation) ht
    rw [unitOfBits_div_valuation] at hval'
    change
      (f₁.toNat : ℤ) - f₂.toNat =
        (((t : ℚ_[2]ˣ) : ℚ_[2]) * ((t : ℚ_[2]ˣ) : ℚ_[2])).valuation at hval'
    rw [Padic.valuation_mul (Units.ne_zero t) (Units.ne_zero t)] at hval'
    linarith
  have hf : f₁ = f₂ := by
    cases f₁ <;> cases f₂ <;> simp_all <;> omega
  have htVal : (((t : ℚ_[2]ˣ) : ℚ_[2])).valuation = 0 := by
    rw [hf] at hval
    simp at hval
    omega
  have htNorm : ‖((t : ℚ_[2]ˣ) : ℚ_[2])‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (Units.ne_zero t), htVal]
    simp
  let T : ℤ_[2]ˣ := PadicInt.mkUnits htNorm
  have hTCoe : (((T : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) =
      ((t : ℚ_[2]ˣ) : ℚ_[2]) := by
    exact PadicInt.mkUnits_eq htNorm
  subst f₂
  have hoddUnits :
      oddUnit e₁ g₁ / oddUnit e₂ g₂ = t * t := by
    rw [← unitOfBits_div_same_twoBit e₁ e₂ f₁ g₁ g₂]
    exact ht
  have hoddField :
      ((oddUnit e₁ g₁ : ℚ_[2]ˣ) : ℚ_[2]) =
        (((t : ℚ_[2]ˣ) : ℚ_[2]) * ((t : ℚ_[2]ˣ) : ℚ_[2])) *
          ((oddUnit e₂ g₂ : ℚ_[2]ˣ) : ℚ_[2]) := by
    have hoddField' := congrArg Units.val hoddUnits
    rw [Units.val_div_eq_div_val, Units.val_mul] at hoddField'
    calc
      ((oddUnit e₁ g₁ : ℚ_[2]ˣ) : ℚ_[2]) =
          (((oddUnit e₁ g₁ : ℚ_[2]ˣ) : ℚ_[2]) /
            ((oddUnit e₂ g₂ : ℚ_[2]ˣ) : ℚ_[2])) *
              ((oddUnit e₂ g₂ : ℚ_[2]ˣ) : ℚ_[2]) := by
        rw [div_mul_cancel₀ _ (Units.ne_zero _)]
      _ = (((t : ℚ_[2]ˣ) : ℚ_[2]) * ((t : ℚ_[2]ˣ) : ℚ_[2])) *
          ((oddUnit e₂ g₂ : ℚ_[2]ˣ) : ℚ_[2]) := by
        rw [hoddField']
  have hPadicInt :
      ((oddPadicUnit e₁ g₁ : ℤ_[2]ˣ) : ℤ_[2]) =
        ((T : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 *
          ((oddPadicUnit e₂ g₂ : ℤ_[2]ˣ) : ℤ_[2]) := by
    apply Subtype.coe_injective
    change
      (((oddPadicUnit e₁ g₁ : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) =
        ((((T : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 *
          ((oddPadicUnit e₂ g₂ : ℤ_[2]ˣ) : ℤ_[2]) : ℤ_[2]) : ℚ_[2])
    rw [PadicInt.coe_mul, PadicInt.coe_pow, hTCoe,
      oddPadicUnit_coe, oddPadicUnit_coe]
    simpa only [pow_two] using hoddField
  have hmod := congrArg (PadicInt.toZModPow 3) hPadicInt
  have heg : (e₁, g₁) = (e₂, g₂) := by
    apply zmodEight_bitGenerators_injective
    rw [oddPadicUnit_mod_eight, map_mul,
      padicIntUnit_square_mod_eight T, one_mul,
      oddPadicUnit_mod_eight] at hmod
    exact hmod
  have he : e₁ = e₂ := congrArg Prod.fst heg
  have hg : g₁ = g₂ := congrArg Prod.snd heg
  cases he
  cases hg
  rfl

/-- The standard Boolean exponent triples classify dyadic squareclasses. -/
def classOfBitsEquiv : BitTriple ≃ Q2Squareclasses :=
  Equiv.ofBijective classOfBits
    ⟨classOfBits_injective, classOfBits_surjective⟩

/-- The three standard dyadic classes generate the squareclass quotient. -/
theorem standardClasses_generate :
    Subgroup.closure
      ({negOneClass, twoClass, fiveClass} : Set Q2Squareclasses) = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  obtain ⟨⟨e, f, g⟩, h⟩ := classOfBits_surjective x
  rw [← h]
  rw [classOfBits_apply]
  simp only [bitPow]
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

/-- There are exactly eight dyadic squareclasses. -/
theorem natCard_q2Squareclasses_eq_eight :
    Nat.card Q2Squareclasses = 8 := by
  calc
    Nat.card Q2Squareclasses = Nat.card BitTriple :=
      Nat.card_congr classOfBitsEquiv.symm
    _ = 8 := by simp [BitTriple]

end

end MazurTorsion.XOneThirteenPadicSquareclassQuotient
