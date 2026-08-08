/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfCardinalityBound
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFppfHOneField
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeKummer

/-!
# Kummer cohomology on the bad fibre

This file combines the checked geometric Kummer sequence with fppf Hilbert 90.  Over
`Spec (ZMod p)`, Frobenius makes every unit an actual `p`th power.  Consequently the unit
Kummer quotient, the kernel of extension from the scheme-theoretic power kernel, and the full
degree-one fppf cohomology of that power kernel are all trivial.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.CommGroupScheme.MultiplicativeKummer

universe u

open AffineCommGroupScheme
open FiniteFlatCommGroupScheme

/-- Over a field, Hilbert 90 upgrades the checked Kummer kernel equivalence to an equivalence
with the full fppf `H¹` of the scheme-theoretic power kernel. -/
noncomputable def powerKernelFppfHOneMulEquivUnitKummerClasses
    (K : Type u) [Field K] (n : ℕ) (hn : n ≠ 0) :
    (powerKernel K n).FppfHOne.{u} ≃* UnitKummerClasses K n := by
  let f : (powerKernel K n).FppfHOne.{u} →*
      (fppfHOneMap (powerKernelPresentation K n).inclusion).ker :=
    (MonoidHom.id (powerKernel K n).FppfHOne.{u}).codRestrict
      (fppfHOneMap (powerKernelPresentation K n).inclusion).ker
      (fun z ↦ MonoidHom.mem_ker.mpr (Subsingleton.elim _ _))
  let e : (powerKernel K n).FppfHOne.{u} ≃*
      (fppfHOneMap (powerKernelPresentation K n).inclusion).ker :=
    MulEquiv.ofBijective f ⟨
      (fun _ _ h ↦ congrArg Subtype.val h),
      (fun z ↦ ⟨z.1, Subtype.ext rfl⟩)⟩
  exact e.trans (unitKummerBoundaryMulEquivKernel (R := K) n hn).symm

/-- For prime exponent `p`, the unit Kummer quotient of a prime field has at most `p`
elements. -/
noncomputable def unitKummerClasses_zmod_primes_boundedData
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    FinitePGroup.BoundedData p (UnitKummerClasses (ZMod q) p) := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq
  letI : Finite (UnitKummerClasses (ZMod q) p) := inferInstance
  exact
    { finite := inferInstance
      length := 1
      card_le := by
        rw [pow_one, ← Subgroup.index_eq_card,
          IsCyclic.index_powMonoidHom_range]
        exact Nat.le_of_dvd hp.pos (Nat.gcd_dvd_right _ _) }

@[simp]
theorem unitKummerClasses_zmod_primes_boundedData_length
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (unitKummerClasses_zmod_primes_boundedData p q hp hq).length = 1 :=
  rfl

/-- Over any prime field, the full fppf `H¹` of a prime-power kernel of `G_m` has
`p`-length at most one. -/
noncomputable def powerKernelFppfHOne_zmod_primes_boundedData
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    FinitePGroup.BoundedData p (powerKernel (ZMod q) p).FppfHOne.{0} := by
  letI : Fact q.Prime := ⟨hq⟩
  exact (unitKummerClasses_zmod_primes_boundedData p q hp hq).congr
    (powerKernelFppfHOneMulEquivUnitKummerClasses
      (ZMod q) p hp.ne_zero).symm

@[simp]
theorem powerKernelFppfHOne_zmod_primes_boundedData_length
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (powerKernelFppfHOne_zmod_primes_boundedData p q hp hq).length = 1 :=
  rfl

/-- Frobenius makes the unit Kummer quotient over the prime field trivial. -/
theorem unitKummerClasses_zmod_prime_eq_one
    (p : ℕ) (hp : p.Prime)
    (z : UnitKummerClasses (ZMod p) p) : z = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : (ZMod p)ˣ →* (ZMod p)ˣ).range z
  apply (QuotientGroup.eq_one_iff u).mpr
  apply MonoidHom.mem_range.mpr
  refine ⟨u, ?_⟩
  apply Units.ext
  exact ZMod.pow_card (u : ZMod p)

/-- Units modulo `p`th powers over the prime field form a subsingleton. -/
theorem unitKummerClasses_zmod_prime_subsingleton
    (p : ℕ) (hp : p.Prime) :
    Subsingleton (UnitKummerClasses (ZMod p) p) :=
  ⟨fun x y ↦ (unitKummerClasses_zmod_prime_eq_one p hp x).trans
    (unitKummerClasses_zmod_prime_eq_one p hp y).symm⟩

/-- Every fppf torsor under the scheme-theoretic kernel of Frobenius on `G_m` over the prime
field is trivial. -/
theorem powerKernelFppfHOne_zmod_prime_eq_one
    (p : ℕ) (hp : p.Prime)
    (z : (powerKernel (ZMod p) p).FppfHOne.{0}) : z = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Subsingleton (multiplicativeScheme (ZMod p)).FppfHOne.{0} :=
    MultiplicativeCocycleDescent.multiplicativeFppfHOne_subsingleton (ZMod p)
  let e := unitKummerBoundaryMulEquivKernel (R := ZMod p) p hp.ne_zero
  letI : Subsingleton (UnitKummerClasses (ZMod p) p) :=
    unitKummerClasses_zmod_prime_subsingleton p hp
  letI : Subsingleton
      (fppfHOneMap (powerKernelPresentation (ZMod p) p).inclusion).ker :=
    e.toEquiv.symm.subsingleton
  have hz : fppfHOneMap (powerKernelPresentation (ZMod p) p).inclusion z = 1 :=
    Subsingleton.elim _ _
  let z' : (fppfHOneMap (powerKernelPresentation (ZMod p) p).inclusion).ker :=
    ⟨z, MonoidHom.mem_ker.mpr hz⟩
  exact congrArg Subtype.val (Subsingleton.elim z' 1)

/-- The fppf `H¹` of the scheme-theoretic Frobenius kernel over the prime field is a
subsingleton. -/
theorem powerKernelFppfHOne_zmod_prime_subsingleton
    (p : ℕ) (hp : p.Prime) :
    Subsingleton (powerKernel (ZMod p) p).FppfHOne.{0} :=
  ⟨fun x y ↦ (powerKernelFppfHOne_zmod_prime_eq_one p hp x).trans
    (powerKernelFppfHOne_zmod_prime_eq_one p hp y).symm⟩

/-- The actual degree-one fppf cohomology of the scheme-theoretic Frobenius kernel has
`p`-length zero. -/
noncomputable def powerKernelFppfHOne_zmod_prime_boundedData
    (p : ℕ) (hp : p.Prime) :
    FinitePGroup.BoundedData p (powerKernel (ZMod p) p).FppfHOne.{0} := by
  letI : Subsingleton (powerKernel (ZMod p) p).FppfHOne.{0} :=
    powerKernelFppfHOne_zmod_prime_subsingleton p hp
  letI : Finite (powerKernel (ZMod p) p).FppfHOne.{0} := Finite.of_subsingleton
  exact
    { finite := inferInstance
      length := 0
      card_le := by
        rw [pow_zero]
        exact (Finite.card_le_one_iff_subsingleton).mpr inferInstance }

@[simp]
theorem powerKernelFppfHOne_zmod_prime_boundedData_length
    (p : ℕ) (hp : p.Prime) :
    (powerKernelFppfHOne_zmod_prime_boundedData p hp).length = 0 :=
  rfl

end AlgebraicGeometry.CommGroupScheme.MultiplicativeKummer
