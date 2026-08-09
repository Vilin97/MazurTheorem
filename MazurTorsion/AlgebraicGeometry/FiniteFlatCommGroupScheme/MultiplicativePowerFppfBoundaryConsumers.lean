/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemePowerKummerRankZero
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativePowerMapFppf

/-!
# Fppf boundary consumers for the multiplicative power map

The positive power map on `G_m` is an actual fppf quotient projection.  This file feeds its
proved flatness, surjectivity, and local finite presentation directly into the generic power
Kummer injection, and consumes the resulting canonical quotient presentation through the
low-degree fppf boundary equivalence.

Over a field, fppf Hilbert 90 identifies the boundary quotient with the full represented
`H¹` of the scheme-theoretic power kernel.  The final consumers transport the existing
power-kernel cardinal data to this actual quotient over `ZMod 5` and `ZMod 11`.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme.MultiplicativeKummer

universe u

open AffineCommGroupScheme
open FiniteFlatCommGroupScheme

variable (R : Type u) [CommRing R]

/-- Base points of `G_m` modulo the image of its actual positive power projection. -/
abbrev MultiplicativePowerBoundaryQuotient [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :=
  (multiplicativePowerFppfQuotientPresentation R n hn).BoundarySourceQuotient

/-- The actual power Kummer homomorphism for `G_m`, with all three fppf laws discharged by
Laurent-coordinate geometry. -/
noncomputable def multiplicativePowerKummerHom [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    BasePoint (multiplicativeScheme R) ⧸
        (powMonoidHom (α := BasePoint (multiplicativeScheme R)) n).range →*
      (powerKernel R n).FppfHOne.{u} :=
  FppfQuotientPresentation.powerKummerHom
    (multiplicativeScheme R) n
    (powerMap_flat_and_surjective R n hn).1
    (powerMap_flat_and_surjective R n hn).2
    (powerMap_locallyOfFinitePresentation R n hn)

/-- The no-law multiplicative power Kummer homomorphism is injective. -/
theorem multiplicativePowerKummerHom_injective [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (multiplicativePowerKummerHom R n hn) :=
  FppfQuotientPresentation.powerKummerHom_injective
    (multiplicativeScheme R) n
    (powerMap_flat_and_surjective R n hn).1
    (powerMap_flat_and_surjective R n hn).2
    (powerMap_locallyOfFinitePresentation R n hn)

/-- Low-degree exactness for the actual multiplicative power presentation identifies its
base-point quotient with the kernel of extension from the power-kernel `H¹` to `G_m`-valued
`H¹`. -/
noncomputable def multiplicativePowerBoundaryQuotientKernelMulEquiv [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    MultiplicativePowerBoundaryQuotient R n hn ≃*
      (fppfHOneMap (powerKernelPresentation R n).inclusion).ker :=
  (multiplicativePowerFppfQuotientPresentation R n hn)
    |>.boundaryQuotientKernelMulEquiv

/-- Over a field, Hilbert 90 upgrades the actual boundary quotient to the full represented
fppf `H¹` of the power kernel. -/
noncomputable def multiplicativePowerBoundaryQuotientMulEquivFppfHOne
    (K : Type u) [Field K] (n : ℕ) (hn : n ≠ 0) :
    MultiplicativePowerBoundaryQuotient K n hn ≃*
      (powerKernel K n).FppfHOne.{u} := by
  letI : Subsingleton (multiplicativeScheme K).FppfHOne.{u} :=
    MultiplicativeCocycleDescent.multiplicativeFppfHOne_subsingleton K
  let f : (powerKernel K n).FppfHOne.{u} →*
      (fppfHOneMap (powerKernelPresentation K n).inclusion).ker :=
    (MonoidHom.id (powerKernel K n).FppfHOne.{u}).codRestrict
      (fppfHOneMap (powerKernelPresentation K n).inclusion).ker
      (fun z ↦ MonoidHom.mem_ker.mpr (Subsingleton.elim _ _))
  let e : (powerKernel K n).FppfHOne.{u} ≃*
      (fppfHOneMap (powerKernelPresentation K n).inclusion).ker :=
    MulEquiv.ofBijective f
      ⟨(fun _ _ h ↦ congrArg Subtype.val h),
        (fun z ↦ ⟨z.1, Subtype.ext rfl⟩)⟩
  exact (multiplicativePowerBoundaryQuotientKernelMulEquiv K n hn).trans e.symm

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- At residue characteristic five, the actual positive-power boundary quotient has
`p`-length at most one for every prime exponent `p`. -/
noncomputable def multiplicativePowerBoundaryQuotientBoundedDataAtFive
    (p : ℕ) (hp : p.Prime) :
    FinitePGroup.BoundedData p
      (MultiplicativePowerBoundaryQuotient (ZMod 5) p hp.ne_zero) := by
  exact (powerKernelFppfHOne_zmod_primes_boundedData p 5 hp (by decide)).congr
    (multiplicativePowerBoundaryQuotientMulEquivFppfHOne
      (ZMod 5) p hp.ne_zero).symm

/-- At residue characteristic eleven, the actual positive-power boundary quotient has
`p`-length at most one for every prime exponent `p`. -/
noncomputable def multiplicativePowerBoundaryQuotientBoundedDataAtEleven
    (p : ℕ) (hp : p.Prime) :
    FinitePGroup.BoundedData p
      (MultiplicativePowerBoundaryQuotient (ZMod 11) p hp.ne_zero) := by
  exact (powerKernelFppfHOne_zmod_primes_boundedData p 11 hp (by decide)).congr
    (multiplicativePowerBoundaryQuotientMulEquivFppfHOne
      (ZMod 11) p hp.ne_zero).symm

@[simp]
theorem multiplicativePowerBoundaryQuotientBoundedDataAtFive_length
    (p : ℕ) (hp : p.Prime) :
    (multiplicativePowerBoundaryQuotientBoundedDataAtFive p hp).length = 1 := by
  rfl

@[simp]
theorem multiplicativePowerBoundaryQuotientBoundedDataAtEleven_length
    (p : ℕ) (hp : p.Prime) :
    (multiplicativePowerBoundaryQuotientBoundedDataAtEleven p hp).length = 1 := by
  rfl

/-- The actual fifth-power boundary quotient over `ZMod 5` has exact cardinality `5 ^ 0`. -/
noncomputable def multiplicativePowerBoundaryQuotientCertifiedDataAtFive :
    FinitePGroup.CertifiedData 5
      (MultiplicativePowerBoundaryQuotient (ZMod 5) 5 (by decide)) := by
  have hp : Nat.Prime 5 := by decide
  exact (powerKernelFppfHOne_zmod_prime_certifiedData 5 hp).congr
    (multiplicativePowerBoundaryQuotientMulEquivFppfHOne
      (ZMod 5) 5 hp.ne_zero).symm

/-- The actual eleventh-power boundary quotient over `ZMod 11` has exact cardinality
`11 ^ 0`. -/
noncomputable def multiplicativePowerBoundaryQuotientCertifiedDataAtEleven :
    FinitePGroup.CertifiedData 11
      (MultiplicativePowerBoundaryQuotient (ZMod 11) 11 (by decide)) := by
  have hp : Nat.Prime 11 := by decide
  exact (powerKernelFppfHOne_zmod_prime_certifiedData 11 hp).congr
    (multiplicativePowerBoundaryQuotientMulEquivFppfHOne
      (ZMod 11) 11 hp.ne_zero).symm

@[simp]
theorem multiplicativePowerBoundaryQuotientCertifiedDataAtFive_length :
    multiplicativePowerBoundaryQuotientCertifiedDataAtFive.length = 0 := by
  rfl

@[simp]
theorem multiplicativePowerBoundaryQuotientCertifiedDataAtEleven_length :
    multiplicativePowerBoundaryQuotientCertifiedDataAtEleven.length = 0 := by
  rfl

end AlgebraicGeometry.CommGroupScheme.MultiplicativeKummer
