/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientConnecting

/-!
# Upper cardinal bounds for fppf cohomology groups

An exact cardinal calculation is stronger than the rank-zero consumer needs.  This file packages
the weaker, carrier-preserving assertion that a specified finite commutative group has cardinality
at most a specified power of `p`.  Such bounds propagate across two consecutive maps in an exact
sequence: the middle group has cardinality at most the product of the two endpoint bounds.

This distinction is useful for bad-fibre localization.  A localization sequence can bound a
global `H¹` by a supported degree-zero term and an ambient `H¹` without manufacturing an exact
cardinality, while the existing `CertifiedData` remains available whenever the exact power is
known.
-/

noncomputable section

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.FinitePGroup

universe w v u

/-- Finiteness and a certified upper bound for an already specified commutative group. -/
structure BoundedData (p : ℕ) (A : Type u) [CommGroup A] where
  /-- The specified carrier is finite. -/
  finite : Finite A
  /-- Exponent in the supplied upper bound. -/
  length : ℕ
  /-- The carrier has at most `p ^ length` elements. -/
  card_le : Nat.card A ≤ p ^ length

namespace CertifiedData

/-- Every exact `p`-power cardinal certificate supplies the corresponding upper bound. -/
def toBoundedData {p : ℕ} {A : Type u} [CommGroup A]
    (D : CertifiedData p A) : BoundedData p A where
  finite := D.finite
  length := D.length
  card_le := D.card_eq.le

@[simp]
theorem toBoundedData_length {p : ℕ} {A : Type u} [CommGroup A]
    (D : CertifiedData p A) : D.toBoundedData.length = D.length :=
  rfl

end CertifiedData

namespace BoundedData

/-- Pull a finite cardinal upper bound back along an injective homomorphism.  The source carrier
is not assumed finite separately. -/
def ofInjective {p : ℕ} {A : Type u} {B : Type v} [CommGroup A] [CommGroup B]
    (target : BoundedData p B) (f : A →* B) (hf : Function.Injective f) :
    BoundedData p A := by
  letI : Finite B := target.finite
  letI : Finite A := Finite.of_injective f hf
  exact
    { finite := inferInstance
      length := target.length
      card_le := (Nat.card_le_card_of_injective f hf).trans target.card_le }

@[simp]
theorem ofInjective_length {p : ℕ} {A : Type u} {B : Type v}
    [CommGroup A] [CommGroup B] (target : BoundedData p B)
    (f : A →* B) (hf : Function.Injective f) :
    (target.ofInjective f hf).length = target.length :=
  rfl

/-- Transport a finite cardinal upper bound across a multiplicative equivalence. -/
def congr {p : ℕ} {A : Type u} {B : Type v} [CommGroup A] [CommGroup B]
    (D : BoundedData p A) (e : A ≃* B) : BoundedData p B := by
  letI : Finite A := D.finite
  exact
    { finite := Finite.of_equiv A e.toEquiv
      length := D.length
      card_le := by
        rw [Nat.card_congr e.symm.toEquiv]
        exact D.card_le }

@[simp]
theorem congr_length {p : ℕ} {A : Type u} {B : Type v}
    [CommGroup A] [CommGroup B] (D : BoundedData p A) (e : A ≃* B) :
    (D.congr e).length = D.length :=
  rfl

/-- Two finite endpoint bounds propagate to the middle of an exact pair. -/
def middleOfMulExact {p : ℕ} {A : Type u} {B : Type v} {C : Type w}
    [CommGroup A] [CommGroup B] [CommGroup C]
    (left : BoundedData p A) (right : BoundedData p C)
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    BoundedData p B := by
  letI : Finite A := left.finite
  letI : Finite C := right.finite
  letI : Finite B := FppfLowDegreeExactSequence.finite_middle_of_mulExact f g h
  exact
    { finite := inferInstance
      length := left.length + right.length
      card_le := by
        have hcard : Nat.card B = Nat.card f.range * Nat.card g.range := by
          calc
            Nat.card B = Nat.card g.ker * g.ker.index := g.ker.card_mul_index.symm
            _ = Nat.card f.range * Nat.card g.range := by
              rw [Subgroup.index_ker g, h.monoidHom_ker_eq]
        calc
          Nat.card B = Nat.card f.range * Nat.card g.range := hcard
          _ ≤ Nat.card A * Nat.card C := by
            exact Nat.mul_le_mul
              (Nat.card_le_card_of_surjective f.rangeRestrict
                f.rangeRestrict_surjective)
              g.range.card_le_card_group
          _ ≤ p ^ left.length * p ^ right.length :=
            Nat.mul_le_mul left.card_le right.card_le
          _ = p ^ (left.length + right.length) := (pow_add _ _ _).symm }

@[simp]
theorem middleOfMulExact_length {p : ℕ} {A : Type u} {B : Type v} {C : Type w}
    [CommGroup A] [CommGroup B] [CommGroup C]
    (left : BoundedData p A) (right : BoundedData p C)
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    (middleOfMulExact left right f g h).length = left.length + right.length :=
  rfl

end BoundedData

end AlgebraicGeometry.FiniteFlatCommGroupScheme.FinitePGroup
