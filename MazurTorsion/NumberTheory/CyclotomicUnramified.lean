/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Inverse-cyclotomic unramified extensions

This file isolates the number-theoretic interface used in Mazur's prime-order
argument.  It packages a cyclic degree-`p` extension of the `p`-th cyclotomic
field together with the inverse-cyclotomic conjugation law, expresses local
unramifiedness at actual finite places, and records the class-group quotient
that global class field theory must produce.

The pinned Mathlib supplies cyclotomic Galois theory, finite places,
ramification indices, and ideal class groups.  It does not yet supply Artin
reciprocity or Hilbert class fields.  Accordingly, the finite-place criterion
below is proved, while the global reciprocity step is exposed as the precise
proposition `ClassFieldTheoryPrinciple`.
-/

open scoped NumberField

namespace NumberTheory.CyclotomicCharacter

universe u

/-- The `p`-th cyclotomic field over the rationals. -/
abbrev PrimeCyclotomicField (p : ℕ) := CyclotomicField p ℚ

/-- A finite place in the ideal-theoretic ramification API: a nonzero prime
ideal in the ring of integers. -/
abbrev FinitePrime (K : Type*) [Field K] :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- The inverse of the mod-`p` cyclotomic character on the Galois group of
the `p`-th cyclotomic field. -/
noncomputable def inverseCharacter (p : ℕ) [Fact p.Prime] :
    Gal(PrimeCyclotomicField p/ℚ) →* (ZMod p)ˣ :=
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  invMonoidHom.comp
    (IsCyclotomicExtension.autEquivPow (PrimeCyclotomicField p)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p))).toMonoidHom

/-- For `p > 2`, the cyclotomic base is totally complex.  Thus the intended
prime-order range has no real places requiring a narrow-class-group
correction. -/
theorem primeCyclotomicField_isTotallyComplex
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    NumberField.IsTotallyComplex (PrimeCyclotomicField p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact IsCyclotomicExtension.Rat.isTotallyComplex (PrimeCyclotomicField p) hp

/-- A cyclic degree-`p` extension of `ℚ(ζ_p)` on which conjugation by
`Gal(ℚ(ζ_p)/ℚ)` acts through the inverse cyclotomic character.

The lifts and the conjugates are included as data, but both are tied to the
field operations by `lift_algebraMap` and `conjugate_apply`; in particular,
`inverse_action` is an assertion about actual conjugation in the field tower,
not an unrelated abstract action. -/
structure InverseExtension (p : ℕ) [Fact p.Prime]
    (L : Type u) [Field L] [NumberField L] [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L] where
  /-- Galoisness over the cyclotomic base. -/
  isGalois : IsGalois (PrimeCyclotomicField p) L
  /-- Galoisness over the rationals, needed to lift cyclotomic automorphisms. -/
  isGaloisOverRat : IsGalois ℚ L
  /-- Identification of the relative Galois group with the cyclic group of order `p`. -/
  galEquiv : Gal(L/PrimeCyclotomicField p) ≃* Multiplicative (ZMod p)
  /-- A lift to `L` of each automorphism of the cyclotomic base. -/
  lift : Gal(PrimeCyclotomicField p/ℚ) → Gal(L/ℚ)
  /-- Each chosen lift restricts to the original cyclotomic automorphism. -/
  lift_algebraMap : ∀ σ x,
    lift σ (algebraMap (PrimeCyclotomicField p) L x) =
      algebraMap (PrimeCyclotomicField p) L (σ x)
  /-- Conjugation of the relative Galois group by a chosen lift. -/
  conjugate : Gal(PrimeCyclotomicField p/ℚ) →
    Gal(L/PrimeCyclotomicField p) → Gal(L/PrimeCyclotomicField p)
  /-- The packaged conjugation is the actual conjugation on field elements. -/
  conjugate_apply : ∀ σ τ x,
    conjugate σ τ x = lift σ (τ ((lift σ).symm x))
  /-- Conjugation acts on the cyclic relative group through the inverse character. -/
  inverse_action : ∀ σ τ,
    Multiplicative.toAdd (galEquiv (conjugate σ τ)) =
      (inverseCharacter p σ : ZMod p) *
        Multiplicative.toAdd (galEquiv τ)

/-- The roadmap-facing name for an inverse-cyclotomic extension. -/
abbrev inverseExtension := InverseExtension

namespace InverseExtension

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L] [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- Unramifiedness of an inverse-cyclotomic extension at a finite place of
the cyclotomic base field. -/
def IsUnramifiedAtFinitePlace (_E : InverseExtension p L)
    (v : FinitePrime (PrimeCyclotomicField p)) : Prop :=
  Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) v.asIdeal

/-- Unramifiedness at every finite place of the cyclotomic base field. -/
def IsUnramifiedAtFinitePlaces (E : InverseExtension p L) : Prop :=
  ∀ v : FinitePrime (PrimeCyclotomicField p), E.IsUnramifiedAtFinitePlace v

/-- For rings of integers in a number-field extension, global algebraic
unramifiedness is equivalent to unramifiedness at every nonzero prime of the
base.  The generic prime contributes no extra hypothesis in characteristic
zero. -/
theorem algebraUnramified_iff_isUnramifiedAtFinitePlaces
    (E : InverseExtension p L) :
    Algebra.Unramified
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (NumberField.RingOfIntegers L) ↔
      E.IsUnramifiedAtFinitePlaces := by
  rw [Algebra.unramified_iff_forall]
  constructor
  · intro h v P hP _
    exact h ⟨P, hP⟩
  · intro h q
    by_cases hq : q.asIdeal = ⊥
    · simpa only [hq] using
        (Algebra.isUnramifiedAt_bot
          (R := NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (S := NumberField.RingOfIntegers L))
    · let basePrime : Ideal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)) :=
        q.asIdeal.under (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      have hqmax : q.asIdeal.IsMaximal := q.isPrime.isMaximal hq
      letI : q.asIdeal.IsMaximal := hqmax
      have hp : basePrime.IsMaximal :=
        Ideal.IsMaximal.under
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)) q.asIdeal
      let v : FinitePrime (PrimeCyclotomicField p) :=
        ⟨basePrime, hp.isPrime,
          Ideal.IsMaximal.ne_bot_of_isIntegral_int basePrime⟩
      have hu : Algebra.IsUnramifiedIn
          (NumberField.RingOfIntegers L) basePrime := by
        simpa only [IsUnramifiedAtFinitePlace] using h v
      have hover : q.asIdeal.LiesOver basePrime := inferInstance
      exact hu q.asIdeal q.isPrime hover

/-- Mathlib's ramification-index criterion, specialized to an actual finite
place of the cyclotomic field. -/
theorem isUnramifiedAtFinitePlace_iff_ramificationIdx_eq_one
    (E : InverseExtension p L) (v : FinitePrime (PrimeCyclotomicField p)) :
    E.IsUnramifiedAtFinitePlace v ↔
      ∀ (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime],
        P.LiesOver v.asIdeal →
          Ideal.ramificationIdx P
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)) = 1 :=
  Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one

/-- The simultaneous ramification-index-one condition at all finite places. -/
def RamificationIndexOneAtFinitePlaces (_E : InverseExtension p L) : Prop :=
  ∀ (v : FinitePrime (PrimeCyclotomicField p))
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime],
    P.LiesOver v.asIdeal →
      Ideal.ramificationIdx P
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)) = 1

/-- Everywhere finite-place unramifiedness is equivalent to ramification
index one above every finite place. -/
theorem isUnramifiedAtFinitePlaces_iff_ramificationIndexOne
    (E : InverseExtension p L) :
    E.IsUnramifiedAtFinitePlaces ↔ E.RamificationIndexOneAtFinitePlaces := by
  constructor
  · intro h v P hP hPover
    exact (E.isUnramifiedAtFinitePlace_iff_ramificationIdx_eq_one v).mp (h v) P hPover
  · intro h v
    exact (E.isUnramifiedAtFinitePlace_iff_ramificationIdx_eq_one v).mpr (h v)

/-- The full number-ring extension is unramified exactly when every
ramification index above every finite cyclotomic prime is one. -/
theorem algebraUnramified_iff_ramificationIndexOne
    (E : InverseExtension p L) :
    Algebra.Unramified
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (NumberField.RingOfIntegers L) ↔
      E.RamificationIndexOneAtFinitePlaces :=
  E.algebraUnramified_iff_isUnramifiedAtFinitePlaces.trans
    E.isUnramifiedAtFinitePlaces_iff_ramificationIndexOne

end InverseExtension

/-- The strongest unconditional finite-place bridge currently supported by
the pinned library: local ramification indices equal to one imply
unramifiedness at every finite place. -/
theorem unramifiedAtFinitePlaces
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L] [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L) (h : E.RamificationIndexOneAtFinitePlaces) :
    E.IsUnramifiedAtFinitePlaces :=
  E.isUnramifiedAtFinitePlaces_iff_ramificationIndexOne.mpr h

/-- The action of a cyclotomic Galois automorphism on the class group of the
ring of integers. -/
noncomputable def classGroupAutomorphism (p : ℕ)
    (σ : Gal(PrimeCyclotomicField p/ℚ)) :
    ClassGroup (NumberField.RingOfIntegers (PrimeCyclotomicField p)) ≃*
      ClassGroup (NumberField.RingOfIntegers (PrimeCyclotomicField p)) :=
  ClassGroup.mulEquiv
    (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv)

/-- The quotient supplied by the unramified abelian correspondence, before
recording its Galois eigenspace. -/
structure UnramifiedClassGroupQuotient (p : ℕ) [Fact p.Prime] where
  /-- The cyclic order-`p` quotient map from the ideal class group. -/
  quotient : ClassGroup (NumberField.RingOfIntegers (PrimeCyclotomicField p)) →*
    Multiplicative (ZMod p)
  /-- The quotient map is onto. -/
  surjective : Function.Surjective quotient

/-- The assertion that a class-group quotient transforms through the inverse
cyclotomic character. -/
def UnramifiedClassGroupQuotient.IsInverseCyclotomic
    {p : ℕ} [Fact p.Prime] (Q : UnramifiedClassGroupQuotient p) : Prop :=
  ∀ (σ : Gal(PrimeCyclotomicField p/ℚ))
    (c : ClassGroup (NumberField.RingOfIntegers (PrimeCyclotomicField p))),
    Multiplicative.toAdd (Q.quotient (classGroupAutomorphism p σ c)) =
      (inverseCharacter p σ : ZMod p) *
        Multiplicative.toAdd (Q.quotient c)

/-- A nonzero inverse-cyclotomic quotient of the ideal class group.  Its
existence is the precise class-group obstruction forced by a cyclic
everywhere-unramified inverse-cyclotomic extension. -/
structure InverseClassGroupQuotient (p : ℕ) [Fact p.Prime]
    extends UnramifiedClassGroupQuotient p where
  /-- The quotient transforms through the inverse cyclotomic character. -/
  inverseCyclotomic : toUnramifiedClassGroupQuotient.IsInverseCyclotomic

/-- The missing class-field-theory statement: over a totally complex base,
every everywhere-unramified inverse-cyclotomic extension produces the
corresponding ordinary ideal-class-group quotient. -/
def ClassFieldTheoryPrinciple (p : ℕ) [Fact p.Prime] : Prop :=
  NumberField.IsTotallyComplex (PrimeCyclotomicField p) →
    ∀ {L : Type u} [Field L] [NumberField L] [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L] (E : InverseExtension p L),
    E.IsUnramifiedAtFinitePlaces → Nonempty (InverseClassGroupQuotient p)

/-- If global reciprocity produces the class-group quotient and the relevant
inverse-cyclotomic quotient is known not to exist, then no such extension can
be everywhere unramified. -/
theorem noEverywhereUnramified
    {p : ℕ} [Fact p.Prime]
    (hp : 2 < p)
    (hclassField : ClassFieldTheoryPrinciple.{u} p)
    (hclassGroup : ¬ Nonempty (InverseClassGroupQuotient p))
    {L : Type u} [Field L] [NumberField L] [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L] (E : InverseExtension p L) :
    ¬ E.IsUnramifiedAtFinitePlaces := by
  intro hunramified
  exact hclassGroup
    (hclassField (primeCyclotomicField_isTotallyComplex hp) E hunramified)

end NumberTheory.CyclotomicCharacter
