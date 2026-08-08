/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import MazurTorsion.NumberTheory.CyclotomicCapitulation
import MazurTorsion.NumberTheory.CyclotomicSelmerClassGroup
import MazurTorsion.NumberTheory.UnramifiedNormArtin

/-!
# Prime division fields and the cyclotomic obstruction

This module is the checked downstream consumer of the cyclotomic
unramifiedness API.  It deliberately does not construct the division field or
prove its local ramification indices: those inputs belong to the blocked
Eisenstein-specialization branch. `DivisionFieldData` makes the curve, rational
prime-order point, x-coordinate splitting field, inverse extension, and exact
local input explicit. From that datum, this module derives everywhere
finite-place unramifiedness and feeds the result into the class-group
obstruction.
-/

namespace MazurTorsion.PrimeOrder

open NumberTheory.CyclotomicCharacter

universe u

/-- A checked interface for the prime-division field attached to a rational
prime-order point.  It identifies `L` as the splitting field of the
`x`-coordinate `p`-division polynomial, records the rational point that
selects the upper-triangular Galois situation, packages the resulting
inverse-cyclotomic degree-`p` extension over `ℚ(ζ_p)`, and retains the exact
local ramification input still owed by the Eisenstein-specialization
argument.  No comparison with a separately constructed full torsion field
is asserted. -/
structure DivisionFieldData
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) where
  /-- The prime lies in the odd-prime range used by the division-field
  argument. -/
  prime_ge_five : 5 ≤ p
  /-- The rational prime-order point that produces the reducible mod-`p`
  representation. -/
  point : W.toAffine.Point
  /-- The selected rational point has exact additive order `p`. -/
  point_addOrderOf : addOrderOf point = p
  /-- The extension field is the `x`-coordinate `p`-division field. -/
  xDivisionSplittingField : Polynomial.IsSplittingField ℚ L (W.preΨ' p)
  /-- The local arithmetic conclusion supplied by the future
  Eisenstein-specialization argument. -/
  ramificationIndexOneAtFinitePlaces :
    E.RamificationIndexOneAtFinitePlaces

/-- MT-PRIME-DIVISION-FIELD's checked finite-place bridge.  The conclusion is
substantive, while the ramification field in `hdivision` remains the precise
arithmetic input to be obtained from the future Eisenstein-specialization
argument. -/
theorem divisionField_everywhereUnramified
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    E.IsUnramifiedAtFinitePlaces :=
  unramifiedAtFinitePlaces E hdivision.ramificationIndexOneAtFinitePlaces

/-- Hilbert 94 gives a second genuine consequence of the division-field local
datum: the prime degree divides the full class number of the cyclotomic base.
This is non-equivariant and therefore does not by itself select or exclude the
inverse-character component. -/
theorem divisionField_prime_dvd_card_classGroup
    {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    p ∣ Fintype.card
      (ClassGroup (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :=
  E.prime_dvd_card_classGroup_of_isUnramifiedAtFinitePlaces hp
    (divisionField_everywhereUnramified W E hdivision)

/-- The division-field local datum consequently yields an abstract cyclic
order-`p` quotient of the cyclotomic class group.  The statement deliberately
uses `UnramifiedClassGroupQuotient`: Hilbert 94 alone does not supply the
inverse-character action required by `InverseClassGroupQuotient`. -/
theorem divisionField_unramifiedClassGroupQuotient
    {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    Nonempty (UnramifiedClassGroupQuotient p) :=
  E.nonempty_unramifiedClassGroupQuotient_of_isUnramifiedAtFinitePlaces hp
    (divisionField_everywhereUnramified W E hdivision)

/-- Equivariant Hilbert 94 gives a concrete further consumer of the
division-field local datum: there is a nontrivial exponent-`p` ideal class
whose entire cyclotomic Galois orbit capitulates in the division field.  This
records genuine equivariance of the capitulation kernel without claiming
that the kernel carries the inverse cyclotomic character. -/
theorem divisionField_exists_nontrivial_p_torsion_capitulating_orbit
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    ∃ c : ClassGroup
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)),
      c ≠ 1 ∧ c ^ p = 1 ∧
        ∀ σ : Gal(PrimeCyclotomicField p/ℚ),
          E.capitulationHom (classGroupAutomorphism p σ c) = 1 :=
  E.exists_nontrivial_p_torsion_capitulating_orbit (by
    have := hdivision.prime_ge_five
    omega)
    (divisionField_everywhereUnramified W E hdivision)

/-- The division-field local datum also rules out surjectivity of the
relative norm on nonzero fractional ideals.  Thus annihilation of relative
ideal norms cannot be promoted to principal reciprocity by a surjectivity
shortcut. -/
theorem divisionField_fractionalIdealRelNorm_not_surjective
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    ¬ Function.Surjective
      (NumberTheory.UnramifiedArtin.fractionalIdealRelNorm
        (K := PrimeCyclotomicField p) (L := L)) :=
  E.not_surjective_fractionalIdealRelNorm
    (divisionField_everywhereUnramified W E hdivision)

/-- The division-field local datum also controls the unique prime above `p`:
the canonical Kummer radicand becomes a `p`-th power in the corresponding
finite completion.  This is the local input used by one-sided cyclotomic
reciprocity. -/
theorem divisionField_radicand_isPow_at_cyclotomicPrime
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hp : 2 < p) (E : InverseExtension p L)
    (hdivision : DivisionFieldData W E) :
    ∃ x : (cyclotomicPrime p).adicCompletion
        (PrimeCyclotomicField p),
      x ^ p = algebraMap (PrimeCyclotomicField p)
        ((cyclotomicPrime p).adicCompletion
          (PrimeCyclotomicField p)) E.kummerPresentation.radicand :=
  NumberTheory.CyclotomicCharacter.InverseExtension.cyclotomicPrime_radicand_isPow hp E
    (divisionField_everywhereUnramified W E hdivision)

/-- The division-field local datum has a concrete Kummer-theoretic
consequence: it supplies a nontrivial empty-support `p`-Selmer class of the
cyclotomic field.  This is a genuine downstream consumer of the finite-place
bridge and does not assert the still-deeper class-group reflection step. -/
noncomputable def divisionField_radicandSelmerClass
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    IsDedekindDomain.selmerGroup
      (K := PrimeCyclotomicField p)
      (S := (∅ : Set (FinitePrime (PrimeCyclotomicField p))))
      (n := p) :=
  E.unramifiedRadicandSelmerClass
    (divisionField_everywhereUnramified W E hdivision)

/-- The Selmer class produced from the division-field local datum is
nontrivial. -/
theorem divisionField_radicandSelmerClass_ne_one
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    divisionField_radicandSelmerClass W E hdivision ≠ 1 :=
  E.unramifiedRadicandSelmerClass_ne_one
    (divisionField_everywhereUnramified W E hdivision)

/-- The same division-field local datum canonically produces a class-group
`p`-torsion element.  This is the image of the nontrivial Selmer class; it
may still be trivial precisely when that Selmer class comes from a global
unit modulo `p`-th powers. -/
noncomputable def divisionField_radicandClassTorsion
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    IsDedekindDomain.selmerGroup.classGroupTorsion
      (R := NumberField.RingOfIntegers (PrimeCyclotomicField p)) p :=
  E.unramifiedRadicandClassTorsion
    (divisionField_everywhereUnramified W E hdivision)

/-- The underlying ideal class of the division-field torsion element is the
class of the explicit root of the Kummer radicand's principal divisor. -/
@[simp]
theorem divisionField_radicandClassTorsion_val
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) :
    (divisionField_radicandClassTorsion W E hdivision :
        ClassGroup (NumberField.RingOfIntegers
          (PrimeCyclotomicField p))) =
      ClassGroup.mk (PrimeCyclotomicField p)
        E.unramifiedRadicandRootIdeal :=
  E.unramifiedRadicandClassTorsion_val
    (divisionField_everywhereUnramified W E hdivision)

/-- A genuine consumer of `divisionField_everywhereUnramified`: global
reciprocity turns its conclusion into an inverse-cyclotomic quotient of the
class group, while the class-group eigenspace obstruction rules that quotient
out. -/
theorem inverseCyclotomic_extension_impossible
    {p : ℕ} [Fact p.Prime]
    (hp : 2 < p)
    (hclassField : ClassFieldTheoryPrinciple.{u} p)
    (hclassGroup : ¬ Nonempty (InverseClassGroupQuotient p))
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (E : InverseExtension p L) (hdivision : DivisionFieldData W E) : False :=
  noEverywhereUnramified hp hclassField hclassGroup E
    (divisionField_everywhereUnramified W E hdivision)

end MazurTorsion.PrimeOrder
