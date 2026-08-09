/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenEndomorphismArithmetic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Module

/-!
# The characteristic-nineteen eigenspace splitting at level thirteen

Let `gamma` be a linear endomorphism over `ZMod 19` satisfying
`gamma^2 - gamma + 1 = 0`.  This file identifies the kernels of the two
linear factors `3 + 2 * gamma` and `5 - 2 * gamma` with the eigenspaces for
the two roots `8` and `12`, respectively.  Explicit complementary
projections then give an equivalence between the ambient space and the
product of these kernels.

This is a general linear-algebra calculation.  In particular, it does not
assert the existence of a geometric endomorphism or any dimension or Galois
property of a Jacobian.
-/

namespace MazurTorsion.XOneThirteenEndomorphismEigenspaces

local notation "F" => ZMod 19

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- Pointwise form of the relation `gamma^2 - gamma + 1 = 0`. -/
def SatisfiesQuadraticRelation (gamma : Module.End F V) : Prop :=
  forall x, gamma (gamma x) = gamma x - x

/-- The linear and additive formulations of the quadratic relation agree. -/
theorem satisfiesQuadraticRelation_iff_toAddMonoidHom
    (gamma : Module.End F V) :
    SatisfiesQuadraticRelation gamma ↔
      XOneThirteenEndomorphismArithmetic.SatisfiesQuadraticRelation
        gamma.toAddMonoidHom :=
  Iff.rfl

/-- The linear endomorphism `3 + 2 * gamma`. -/
def primeLinearEndomorphism (gamma : Module.End F V) : Module.End F V :=
  (3 : F) • LinearMap.id + (2 : F) • gamma

/-- The conjugate linear endomorphism `5 - 2 * gamma`. -/
def conjugatePrimeLinearEndomorphism (gamma : Module.End F V) : Module.End F V :=
  (5 : F) • LinearMap.id - (2 : F) • gamma

@[simp]
theorem primeLinearEndomorphism_apply (gamma : Module.End F V) (x : V) :
    primeLinearEndomorphism gamma x = (3 : F) • x + (2 : F) • gamma x := by
  simp [primeLinearEndomorphism]

@[simp]
theorem conjugatePrimeLinearEndomorphism_apply (gamma : Module.End F V) (x : V) :
    conjugatePrimeLinearEndomorphism gamma x = (5 : F) • x - (2 : F) • gamma x := by
  simp [conjugatePrimeLinearEndomorphism]

/-- Forgetting scalar linearity recovers the additive prime factor from
`XOneThirteenEndomorphismArithmetic`. -/
theorem primeLinearEndomorphism_toAddMonoidHom (gamma : Module.End F V) :
    (primeLinearEndomorphism gamma).toAddMonoidHom =
      XOneThirteenEndomorphismArithmetic.primeEndomorphism
        gamma.toAddMonoidHom := by
  ext x
  change (3 : F) • x + (2 : F) • gamma x =
    (3 : ℕ) • x + (2 : ℕ) • gamma x
  simp only [ofNat_smul_eq_nsmul]

/-- Forgetting scalar linearity recovers the additive conjugate factor. -/
theorem conjugatePrimeLinearEndomorphism_toAddMonoidHom
    (gamma : Module.End F V) :
    (conjugatePrimeLinearEndomorphism gamma).toAddMonoidHom =
      XOneThirteenEndomorphismArithmetic.conjugatePrimeEndomorphism
        gamma.toAddMonoidHom := by
  ext x
  change (5 : F) • x - (2 : F) • gamma x =
    (5 : ℕ) • x - (2 : ℕ) • gamma x
  simp only [ofNat_smul_eq_nsmul]

/-- The first factor is a nonzero scalar multiple of `gamma - 8`. -/
theorem primeLinearEndomorphism_eq_two_smul_sub (gamma : Module.End F V) :
    primeLinearEndomorphism gamma =
      (2 : F) • (gamma - (8 : F) • LinearMap.id) := by
  ext x
  simp only [primeLinearEndomorphism_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_coe, id_eq]
  match_scalars
  all_goals decide

/-- The conjugate factor is a nonzero scalar multiple of `gamma - 12`. -/
theorem conjugatePrimeLinearEndomorphism_eq_neg_two_smul_sub
    (gamma : Module.End F V) :
    conjugatePrimeLinearEndomorphism gamma =
      (-2 : F) • (gamma - (12 : F) • LinearMap.id) := by
  ext x
  simp only [conjugatePrimeLinearEndomorphism_apply, neg_smul,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_coe, id_eq]
  match_scalars
  all_goals decide

/-- The kernel of `3 + 2 * gamma` is exactly the `8`-eigenspace. -/
theorem ker_primeLinearEndomorphism_eq_eigenspace_eight
    (gamma : Module.End F V) :
    LinearMap.ker (primeLinearEndomorphism gamma) = gamma.eigenspace (8 : F) := by
  rw [Module.End.eigenspace_def, primeLinearEndomorphism_eq_two_smul_sub]
  exact LinearMap.ker_smul
    (gamma - (8 : F) • LinearMap.id) (2 : F) (by decide)

/-- The kernel of `5 - 2 * gamma` is exactly the `12`-eigenspace. -/
theorem ker_conjugatePrimeLinearEndomorphism_eq_eigenspace_twelve
    (gamma : Module.End F V) :
    LinearMap.ker (conjugatePrimeLinearEndomorphism gamma) =
      gamma.eigenspace (12 : F) := by
  rw [Module.End.eigenspace_def,
    conjugatePrimeLinearEndomorphism_eq_neg_two_smul_sub]
  exact LinearMap.ker_smul
    (gamma - (12 : F) • LinearMap.id) (-2 : F) (by decide)

/-- Projection onto the `8`-eigenspace. -/
def eightProjection (gamma : Module.End F V) : Module.End F V :=
  (3 : F) • LinearMap.id - (5 : F) • gamma

/-- Projection onto the `12`-eigenspace. -/
def twelveProjection (gamma : Module.End F V) : Module.End F V :=
  (5 : F) • gamma - (2 : F) • LinearMap.id

@[simp]
theorem eightProjection_apply (gamma : Module.End F V) (x : V) :
    eightProjection gamma x = (3 : F) • x - (5 : F) • gamma x := by
  simp [eightProjection]

@[simp]
theorem twelveProjection_apply (gamma : Module.End F V) (x : V) :
    twelveProjection gamma x = (5 : F) • gamma x - (2 : F) • x := by
  simp [twelveProjection]

/-- The two explicit projections sum to the identity. -/
theorem eightProjection_add_twelveProjection (gamma : Module.End F V) :
    eightProjection gamma + twelveProjection gamma = LinearMap.id := by
  ext x
  simp only [LinearMap.add_apply, eightProjection_apply, twelveProjection_apply,
    sub_add_sub_cancel, LinearMap.id_coe, id_eq]
  match_scalars
  decide

theorem eightProjection_add_twelveProjection_apply
    (gamma : Module.End F V) (x : V) :
    eightProjection gamma x + twelveProjection gamma x = x := by
  have h := LinearMap.congr_fun (eightProjection_add_twelveProjection gamma) x
  simpa using h

/-- The first explicit projection lands in the `8`-eigenspace. -/
theorem eightProjection_mem_eigenspace_eight
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) (x : V) :
    eightProjection gamma x ∈ gamma.eigenspace (8 : F) := by
  rw [Module.End.mem_eigenspace_iff]
  simp only [eightProjection_apply, map_sub, map_smul]
  rw [hgamma x]
  match_scalars
  all_goals decide

/-- The second explicit projection lands in the `12`-eigenspace. -/
theorem twelveProjection_mem_eigenspace_twelve
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) (x : V) :
    twelveProjection gamma x ∈ gamma.eigenspace (12 : F) := by
  rw [Module.End.mem_eigenspace_iff]
  simp only [twelveProjection_apply, map_sub, map_smul]
  rw [hgamma x]
  match_scalars
  all_goals decide

theorem eightProjection_mem_primeKernel
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) (x : V) :
    eightProjection gamma x ∈ LinearMap.ker (primeLinearEndomorphism gamma) := by
  rw [ker_primeLinearEndomorphism_eq_eigenspace_eight]
  exact eightProjection_mem_eigenspace_eight gamma hgamma x

theorem twelveProjection_mem_conjugatePrimeKernel
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) (x : V) :
    twelveProjection gamma x ∈
      LinearMap.ker (conjugatePrimeLinearEndomorphism gamma) := by
  rw [ker_conjugatePrimeLinearEndomorphism_eq_eigenspace_twelve]
  exact twelveProjection_mem_eigenspace_twelve gamma hgamma x

/-- The `8`-projection restricted to the kernel of `3 + 2 * gamma` is the
identity. -/
theorem eightProjection_eq_self_of_mem_primeKernel
    (gamma : Module.End F V) {x : V}
    (hx : x ∈ LinearMap.ker (primeLinearEndomorphism gamma)) :
    eightProjection gamma x = x := by
  have hx' : x ∈ gamma.eigenspace (8 : F) := by
    rwa [← ker_primeLinearEndomorphism_eq_eigenspace_eight]
  have hgamma_x := Module.End.mem_eigenspace_iff.mp hx'
  rw [eightProjection_apply, hgamma_x]
  match_scalars
  all_goals decide

/-- The `8`-projection vanishes on the kernel of `5 - 2 * gamma`. -/
theorem eightProjection_eq_zero_of_mem_conjugatePrimeKernel
    (gamma : Module.End F V) {x : V}
    (hx : x ∈ LinearMap.ker (conjugatePrimeLinearEndomorphism gamma)) :
    eightProjection gamma x = 0 := by
  have hx' : x ∈ gamma.eigenspace (12 : F) := by
    rwa [← ker_conjugatePrimeLinearEndomorphism_eq_eigenspace_twelve]
  have hgamma_x := Module.End.mem_eigenspace_iff.mp hx'
  rw [eightProjection_apply, hgamma_x]
  match_scalars
  all_goals decide

/-- The `12`-projection vanishes on the kernel of `3 + 2 * gamma`. -/
theorem twelveProjection_eq_zero_of_mem_primeKernel
    (gamma : Module.End F V) {x : V}
    (hx : x ∈ LinearMap.ker (primeLinearEndomorphism gamma)) :
    twelveProjection gamma x = 0 := by
  have hx' : x ∈ gamma.eigenspace (8 : F) := by
    rwa [← ker_primeLinearEndomorphism_eq_eigenspace_eight]
  have hgamma_x := Module.End.mem_eigenspace_iff.mp hx'
  rw [twelveProjection_apply, hgamma_x]
  match_scalars
  all_goals decide

/-- The `12`-projection restricted to the kernel of `5 - 2 * gamma` is the
identity. -/
theorem twelveProjection_eq_self_of_mem_conjugatePrimeKernel
    (gamma : Module.End F V) {x : V}
    (hx : x ∈ LinearMap.ker (conjugatePrimeLinearEndomorphism gamma)) :
    twelveProjection gamma x = x := by
  have hx' : x ∈ gamma.eigenspace (12 : F) := by
    rwa [← ker_conjugatePrimeLinearEndomorphism_eq_eigenspace_twelve]
  have hgamma_x := Module.End.mem_eigenspace_iff.mp hx'
  rw [twelveProjection_apply, hgamma_x]
  match_scalars
  all_goals decide

/-- The two kernels are complementary. -/
theorem primeKernel_isCompl_conjugatePrimeKernel
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    IsCompl (LinearMap.ker (primeLinearEndomorphism gamma))
      (LinearMap.ker (conjugatePrimeLinearEndomorphism gamma)) where
  disjoint := by
    rw [Submodule.disjoint_def]
    intro x hxPrime hxConjugate
    have hxEight : x ∈ gamma.eigenspace (8 : F) := by
      rwa [← ker_primeLinearEndomorphism_eq_eigenspace_eight]
    have hxTwelve : x ∈ gamma.eigenspace (12 : F) := by
      rwa [← ker_conjugatePrimeLinearEndomorphism_eq_eigenspace_twelve]
    have hEight := Module.End.mem_eigenspace_iff.mp hxEight
    have hTwelve := Module.End.mem_eigenspace_iff.mp hxTwelve
    have hzero : ((8 : F) - (12 : F)) • x = 0 := by
      rw [sub_smul, ← hEight, ← hTwelve, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (by decide)
  codisjoint := Submodule.codisjoint_iff_exists_add_eq.mpr fun x =>
    ⟨eightProjection gamma x, twelveProjection gamma x,
      eightProjection_mem_primeKernel gamma hgamma x,
      twelveProjection_mem_conjugatePrimeKernel gamma hgamma x,
      eightProjection_add_twelveProjection_apply gamma x⟩

/-- The explicit map from `V` to the product of the two kernels. -/
def splitToPrimeKernels
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    V →ₗ[F] LinearMap.ker (primeLinearEndomorphism gamma) ×
      LinearMap.ker (conjugatePrimeLinearEndomorphism gamma) :=
  ((eightProjection gamma).codRestrict _
      (eightProjection_mem_primeKernel gamma hgamma)).prod
    ((twelveProjection gamma).codRestrict _
      (twelveProjection_mem_conjugatePrimeKernel gamma hgamma))

/-- Addition maps the product of the two kernels back to `V`. -/
def addFromPrimeKernels (gamma : Module.End F V) :
    LinearMap.ker (primeLinearEndomorphism gamma) ×
        LinearMap.ker (conjugatePrimeLinearEndomorphism gamma) →ₗ[F] V :=
  (LinearMap.ker (primeLinearEndomorphism gamma)).subtype.coprod
    (LinearMap.ker (conjugatePrimeLinearEndomorphism gamma)).subtype

theorem addFromPrimeKernels_comp_splitToPrimeKernels
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    (addFromPrimeKernels gamma).comp (splitToPrimeKernels gamma hgamma) =
      LinearMap.id := by
  ext x
  exact eightProjection_add_twelveProjection_apply gamma x

theorem splitToPrimeKernels_comp_addFromPrimeKernels
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    (splitToPrimeKernels gamma hgamma).comp (addFromPrimeKernels gamma) =
      LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · apply Subtype.ext
    change eightProjection gamma ((x : V) + (y : V)) = (x : V)
    rw [map_add, eightProjection_eq_self_of_mem_primeKernel gamma x.property,
      eightProjection_eq_zero_of_mem_conjugatePrimeKernel gamma y.property, add_zero]
  · apply Subtype.ext
    change twelveProjection gamma ((x : V) + (y : V)) = (y : V)
    rw [map_add, twelveProjection_eq_zero_of_mem_primeKernel gamma x.property,
      twelveProjection_eq_self_of_mem_conjugatePrimeKernel gamma y.property, zero_add]

/-- Explicit eigenspace decomposition over `ZMod 19`. -/
def kernelProductEquiv
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    V ≃ₗ[F] LinearMap.ker (primeLinearEndomorphism gamma) ×
      LinearMap.ker (conjugatePrimeLinearEndomorphism gamma) :=
  LinearEquiv.ofLinear (splitToPrimeKernels gamma hgamma)
    (addFromPrimeKernels gamma)
    (splitToPrimeKernels_comp_addFromPrimeKernels gamma hgamma)
    (addFromPrimeKernels_comp_splitToPrimeKernels gamma hgamma)

@[simp]
theorem kernelProductEquiv_apply_fst
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) (x : V) :
    ((kernelProductEquiv gamma hgamma x).1 : V) =
      (3 : F) • x - (5 : F) • gamma x := by
  rfl

@[simp]
theorem kernelProductEquiv_apply_snd
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) (x : V) :
    ((kernelProductEquiv gamma hgamma x).2 : V) =
      (5 : F) • gamma x - (2 : F) • x := by
  rfl

@[simp]
theorem kernelProductEquiv_symm_apply
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma)
    (x : LinearMap.ker (primeLinearEndomorphism gamma) ×
      LinearMap.ker (conjugatePrimeLinearEndomorphism gamma)) :
    (kernelProductEquiv gamma hgamma).symm x = (x.1 : V) + (x.2 : V) := by
  rfl

/-- In characteristic `19`, multiplication by `19` is the zero linear
endomorphism. -/
theorem nineteen_smul_linearMap_id :
    19 • (LinearMap.id : Module.End F V) = 0 := by
  ext x
  change 19 • x = 0
  rw [← Nat.cast_smul_eq_nsmul F, ZMod.natCast_self, zero_smul]

/-- The product of the two linear factors is zero over `ZMod 19`. -/
theorem prime_comp_conjugate_eq_zero
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    (primeLinearEndomorphism gamma).comp
        (conjugatePrimeLinearEndomorphism gamma) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, primeLinearEndomorphism_apply,
    conjugatePrimeLinearEndomorphism_apply, map_sub, map_smul,
    LinearMap.zero_apply]
  rw [hgamma x]
  match_scalars
  all_goals decide

/-- The product is also the additive multiplication-by-`19` map. -/
theorem prime_comp_conjugate_eq_nineteen
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    (primeLinearEndomorphism gamma).comp
        (conjugatePrimeLinearEndomorphism gamma) =
      19 • (LinearMap.id : Module.End F V) := by
  rw [prime_comp_conjugate_eq_zero gamma hgamma,
    nineteen_smul_linearMap_id]

/-- The same characteristic-`19` identity holds in the other order. -/
theorem conjugate_comp_prime_eq_zero
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    (conjugatePrimeLinearEndomorphism gamma).comp
        (primeLinearEndomorphism gamma) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, primeLinearEndomorphism_apply,
    conjugatePrimeLinearEndomorphism_apply, map_add, map_smul,
    LinearMap.zero_apply]
  rw [hgamma x]
  match_scalars
  all_goals decide

theorem conjugate_comp_prime_eq_nineteen
    (gamma : Module.End F V) (hgamma : SatisfiesQuadraticRelation gamma) :
    (conjugatePrimeLinearEndomorphism gamma).comp
        (primeLinearEndomorphism gamma) =
      19 • (LinearMap.id : Module.End F V) := by
  rw [conjugate_comp_prime_eq_zero gamma hgamma,
    nineteen_smul_linearMap_id]

end MazurTorsion.XOneThirteenEndomorphismEigenspaces
