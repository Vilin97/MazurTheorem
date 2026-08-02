/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle

/-!
# The absolute degree-zero Picard subgroup

This is a downstream consumer of the divisor-class/Picard interface for
`MT-TC-D1-PICARD-FUNCTOR`. Given a product formula and a divisor-class/Picard equivalence, it
transports Tau Ceti's weighted degree-zero divisor classes to an absolute `Pic⁰` subgroup of the
scheme Picard group.

No relative Picard functor or representability claim is made here. In particular, the product
formula remains an explicit input.
-/

namespace MazurTorsion.AlgebraicGeometry

universe u v

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace PicardGroup

variable {X : Scheme.{u}}
variable {Y : Type*} {G : Type v} [AddCommGroup G]

/-- The degree-zero subgroup of the scheme Picard group transported from divisor classes. -/
noncomputable def degreeZero
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X) :
    AddSubgroup (PicardGroup X) :=
  (S.picZero w h).map e.toAddMonoidHom

/-- The divisor-class/Picard equivalence restricts to the degree-zero subgroups. -/
noncomputable def picZeroEquiv
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X) :
    S.picZero w h ≃+ degreeZero S w h e :=
  e.addSubgroupMap (S.picZero w h)

/-- Membership in transported `Pic⁰` can be tested after applying the inverse equivalence. -/
@[simp]
lemma mem_degreeZero_iff
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    (p : PicardGroup X) :
    p ∈ degreeZero S w h e ↔ e.symm p ∈ S.picZero w h := by
  rw [degreeZero, AddSubgroup.mem_map_equiv]

/-- A divisor class lands in absolute `Pic⁰` exactly when its weighted degree is zero. -/
lemma divisorClass_mem_degreeZero_iff
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    (D : WeilDivisor Y) :
    e (S.divisorClass D) ∈ degreeZero S w h e ↔
      WeilDivisor.weightedDegree w D = 0 := by
  rw [mem_degreeZero_iff, e.symm_apply_apply, S.divisorClass_mem_picZero]

end PicardGroup

namespace DivisorPicard.Dictionary

variable {X : Scheme.{u}}
variable {Y : Type*} {G : Type v} [AddCommGroup G]
variable {S : WeilDivisor.OrderSystem Y G}

/-- The absolute degree-zero Picard subgroup attached to an exact divisor-line-bundle
dictionary. This is the named `MT-TC-D1` consumer of the A3 dictionary interface. -/
noncomputable def degreeZero
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w) :
    AddSubgroup (PicardGroup X) :=
  PicardGroup.degreeZero S w h d.classEquivalence

/-- An exact dictionary identifies divisor `Pic⁰` with its absolute scheme-Picard image. -/
noncomputable def picZeroEquiv
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w) :
    S.picZero w h ≃+ d.degreeZero w h :=
  PicardGroup.picZeroEquiv S w h d.classEquivalence

/-- A chosen Tau Ceti invertible-sheaf representative of an absolute degree-zero Picard class.
This consumes the full Picard comparison forced by the exact divisor dictionary. -/
noncomputable def degreeZeroRepresentative
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (p : d.degreeZero w h) : InvertibleSheaf X :=
  d.picardComparison.representative (Additive.toMul p.1)

/-- The chosen degree-zero line bundle represents the underlying Picard class. -/
@[simp]
lemma degreeZeroRepresentative_toPic
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (p : d.degreeZero w h) :
    Additive.ofMul
      (d.picardComparison.toPic (d.degreeZeroRepresentative w h p)) = p.1 := by
  change Additive.ofMul
    (d.picardComparison.toPic
      (d.picardComparison.representative (Additive.toMul p.1))) = p.1
  rw [PicardComparison.toPic_representative]
  rfl

/-- The Picard class of the chosen representative remains in the transported degree-zero
subgroup. -/
lemma degreeZeroRepresentative_mem
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (p : d.degreeZero w h) :
    Additive.ofMul
        (d.picardComparison.toPic (d.degreeZeroRepresentative w h p)) ∈
      d.degreeZero w h := by
  rw [d.degreeZeroRepresentative_toPic w h p]
  exact p.property

/-- Under an exact dictionary, a divisor represents an absolute degree-zero Picard class
exactly when its weighted degree vanishes. -/
lemma divisorToPic_mem_degreeZero_iff
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (D : WeilDivisor Y) :
    d.divisorToPic D ∈ d.degreeZero w h ↔ WeilDivisor.weightedDegree w D = 0 := by
  rw [← d.classEquivalence_divisorClass D]
  exact PicardGroup.divisorClass_mem_degreeZero_iff S w h d.classEquivalence D

end DivisorPicard.Dictionary

end MazurTorsion.AlgebraicGeometry
