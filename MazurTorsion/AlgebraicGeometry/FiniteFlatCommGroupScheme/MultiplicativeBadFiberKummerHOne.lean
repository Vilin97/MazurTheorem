/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.FieldTheory.Finite.Basic
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

open AffineCommGroupScheme
open FiniteFlatCommGroupScheme

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
