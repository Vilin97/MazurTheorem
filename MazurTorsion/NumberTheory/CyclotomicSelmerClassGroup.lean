/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicKummer
import MazurTorsion.NumberTheory.SelmerClassGroup

/-!
# The ideal class attached to an unramified cyclotomic Kummer radicand

This file identifies the explicit divisor root constructed from the canonical
Kummer radicand with the canonical empty-support Selmer-to-class-group map.
It is the ideal-theoretic part of the obstruction and uses no reciprocity
theorem.  In particular, it does not assert that the resulting class is
nontrivial: the kernel is exactly the contribution of global units modulo
`p`-th powers.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- The canonical Kummer radicand, before quotienting by actual `p`-th
powers, as an empty-support pre-Selmer representative. -/
noncomputable def unramifiedRadicandPreSelmer
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    IsDedekindDomain.selmerGroup.preSelmer
      (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (K := PrimeCyclotomicField p) p :=
  ⟨Units.mk0 E.kummerPresentation.radicand
      (E.kummerPresentation.radicand_ne_zero E),
    E.radicand_mem_selmerGroup E.kummerPresentation hunramified⟩

/-- Passing the canonical pre-Selmer representative to the Selmer quotient
recovers the previously defined radicand class. -/
@[simp]
theorem preSelmerToSelmer_unramifiedRadicandPreSelmer
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    IsDedekindDomain.selmerGroup.preSelmerToSelmer
        (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (K := PrimeCyclotomicField p) p
        (E.unramifiedRadicandPreSelmer hunramified) =
      E.unramifiedRadicandSelmerClass hunramified := by
  rfl

/-- The generic divisor-root construction on the canonical pre-Selmer
representative agrees with the explicit Kummer divisor root. -/
theorem rootIdealHom_unramifiedRadicandPreSelmer
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    IsDedekindDomain.selmerGroup.rootIdealHom
        (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (K := PrimeCyclotomicField p) p
        (E.unramifiedRadicandPreSelmer hunramified) =
      E.unramifiedRadicandRootIdeal := by
  let e := NumberTheory.UnramifiedArtin.fractionalIdealDivisorMulEquiv
    (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (K := PrimeCyclotomicField p)
  have hpow :
      (IsDedekindDomain.selmerGroup.rootIdealHom
        (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (K := PrimeCyclotomicField p) p
        (E.unramifiedRadicandPreSelmer hunramified)) ^ p =
        E.unramifiedRadicandRootIdeal ^ p := by
    rw [IsDedekindDomain.selmerGroup.rootIdealHom_pow,
      E.unramifiedRadicandRootIdeal_pow_eq hunramified]
    rfl
  apply e.injective
  exact pow_left_injective (M := Multiplicative
    (FinitePrime (PrimeCyclotomicField p) →₀ ℤ))
    (Fact.out : p.Prime).ne_zero (by simpa only [map_pow] using congrArg e hpow)

/-- The canonical Selmer-to-class-group map sends the unramified radicand
class to the class of its explicit divisor root. -/
theorem toClassGroup_unramifiedRadicandSelmerClass
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    IsDedekindDomain.selmerGroup.toClassGroup
        (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (K := PrimeCyclotomicField p) p
        (E.unramifiedRadicandSelmerClass hunramified) =
      ClassGroup.mk (PrimeCyclotomicField p)
        E.unramifiedRadicandRootIdeal := by
  rw [← E.preSelmerToSelmer_unramifiedRadicandPreSelmer hunramified,
    IsDedekindDomain.selmerGroup.toClassGroup_preSelmerToSelmer]
  change ClassGroup.mk (PrimeCyclotomicField p)
      (IsDedekindDomain.selmerGroup.rootIdealHom
        (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (K := PrimeCyclotomicField p) p
        (E.unramifiedRadicandPreSelmer hunramified)) = _
  rw [E.rootIdealHom_unramifiedRadicandPreSelmer hunramified]

/-- The canonical class, bundled in the `p`-torsion subgroup of the ideal
class group. -/
noncomputable def unramifiedRadicandClassTorsion
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    IsDedekindDomain.selmerGroup.classGroupTorsion
      (R := NumberField.RingOfIntegers (PrimeCyclotomicField p)) p :=
  IsDedekindDomain.selmerGroup.toClassGroupTorsion
    (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (K := PrimeCyclotomicField p) p
    (E.unramifiedRadicandSelmerClass hunramified)

/-- The underlying ideal class of the bundled torsion element is the
explicit Kummer divisor-root class. -/
@[simp]
theorem unramifiedRadicandClassTorsion_val
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces) :
    (E.unramifiedRadicandClassTorsion hunramified :
        ClassGroup (NumberField.RingOfIntegers
          (PrimeCyclotomicField p))) =
      ClassGroup.mk (PrimeCyclotomicField p)
        E.unramifiedRadicandRootIdeal := by
  exact E.toClassGroup_unramifiedRadicandSelmerClass hunramified

/-- The canonical unramified radicand Selmer class transforms through the
square of the direct cyclotomic character. -/
theorem selmerEquiv_baseIntegerEquiv_unramifiedRadicandSelmerClass
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    IsDedekindDomain.selmerGroup.selmerEquivOfRingEquiv
        (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (K := PrimeCyclotomicField p) p (baseIntegerEquiv sigma)
        (E.unramifiedRadicandSelmerClass hunramified) =
      (E.unramifiedRadicandSelmerClass hunramified) ^
        (((((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p)).val) := by
  apply Subtype.ext
  rw [IsDedekindDomain.selmerGroup.selmerEquivOfRingEquiv_coe]
  change IsDedekindDomain.selmerGroup.fieldUnitQuotientEquivOfRingEquiv
      (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (K := PrimeCyclotomicField p) p (baseIntegerEquiv sigma)
      (QuotientGroup.mk
        (Units.mk0 E.kummerPresentation.radicand
          (E.kummerPresentation.radicand_ne_zero E))) =
    (QuotientGroup.mk
      (Units.mk0 E.kummerPresentation.radicand
        (E.kummerPresentation.radicand_ne_zero E)) :
      (PrimeCyclotomicField p)ˣ ⧸
        (powMonoidHom p : (PrimeCyclotomicField p)ˣ →*
          (PrimeCyclotomicField p)ˣ).range) ^
      (((((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p)).val)
  rw [IsDedekindDomain.selmerGroup.fieldUnitQuotientEquivOfRingEquiv_mk]
  change QuotientGroup.mk
      (Units.map
        (IsFractionRing.ringEquivOfRingEquiv
          (baseIntegerEquiv sigma)).toMonoidHom
        (Units.mk0 E.kummerPresentation.radicand
          (E.kummerPresentation.radicand_ne_zero E))) = _
  rw [inducedBaseIntegerEquiv_eq]
  exact E.map_canonicalRadicandClass_eq_directCharacter_sq sigma

/-- The explicit ideal class of the unramified radicand root transforms
through the same square character. -/
theorem classGroupAutomorphism_unramifiedRadicandRootClass
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    classGroupAutomorphism p sigma
        (ClassGroup.mk (PrimeCyclotomicField p)
          E.unramifiedRadicandRootIdeal) =
      (ClassGroup.mk (PrimeCyclotomicField p)
        E.unramifiedRadicandRootIdeal) ^
        (((((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p)).val) := by
  rw [← E.toClassGroup_unramifiedRadicandSelmerClass hunramified]
  change NumberTheory.UnramifiedArtin.classGroupEquiv
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) (baseIntegerEquiv sigma)
      (IsDedekindDomain.selmerGroup.toClassGroup
        (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (K := PrimeCyclotomicField p) p
        (E.unramifiedRadicandSelmerClass hunramified)) =
    (IsDedekindDomain.selmerGroup.toClassGroup
      (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (K := PrimeCyclotomicField p) p
      (E.unramifiedRadicandSelmerClass hunramified)) ^
      (((((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p)).val)
  rw [IsDedekindDomain.selmerGroup.classGroupEquiv_toClassGroup,
    E.selmerEquiv_baseIntegerEquiv_unramifiedRadicandSelmerClass,
    map_pow]

end NumberTheory.CyclotomicCharacter.InverseExtension
