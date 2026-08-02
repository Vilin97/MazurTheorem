/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicKummer

/-!
# Prime division fields and the cyclotomic obstruction

This module is the checked downstream consumer of the cyclotomic
unramifiedness API.  It deliberately does not construct the division field or
prove its local ramification indices: those inputs belong to the blocked
Eisenstein-specialization branch.  Given that exact local input, it derives
everywhere finite-place unramifiedness and feeds the result into the
class-group obstruction.
-/

namespace MazurTorsion.PrimeOrder

open NumberTheory.CyclotomicCharacter

universe u

/-- The local arithmetic datum that the prime-division-field argument must
supply: every prime above every finite cyclotomic prime has ramification index
one. -/
def DivisionFieldLocalData
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L) : Prop :=
  E.RamificationIndexOneAtFinitePlaces

/-- MT-PRIME-DIVISION-FIELD's checked finite-place bridge.  The conclusion is
substantive, while `hlocal` remains the precise arithmetic input to be
obtained from the future division-field construction. -/
theorem divisionField_everywhereUnramified
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L) (hlocal : DivisionFieldLocalData E) :
    E.IsUnramifiedAtFinitePlaces :=
  unramifiedAtFinitePlaces E hlocal

/-- The division-field local datum has a concrete Kummer-theoretic
consequence: it supplies a nontrivial empty-support `p`-Selmer class of the
cyclotomic field.  This is a genuine downstream consumer of the finite-place
bridge and does not assert the still-deeper class-group reflection step. -/
noncomputable def divisionField_radicandSelmerClass
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L) (hlocal : DivisionFieldLocalData E) :
    IsDedekindDomain.selmerGroup
      (K := PrimeCyclotomicField p)
      (S := (∅ : Set (FinitePrime (PrimeCyclotomicField p))))
      (n := p) :=
  E.unramifiedRadicandSelmerClass
    (divisionField_everywhereUnramified E hlocal)

/-- The Selmer class produced from the division-field local datum is
nontrivial. -/
theorem divisionField_radicandSelmerClass_ne_one
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L) (hlocal : DivisionFieldLocalData E) :
    divisionField_radicandSelmerClass E hlocal ≠ 1 :=
  E.unramifiedRadicandSelmerClass_ne_one
    (divisionField_everywhereUnramified E hlocal)

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
    (E : InverseExtension p L) (hlocal : DivisionFieldLocalData E) : False :=
  noEverywhereUnramified hp hclassField hclassGroup E
    (divisionField_everywhereUnramified E hlocal)

end MazurTorsion.PrimeOrder
