/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

This file selectively adapts `AlgebraicGeometry.exists_smul_algHom_eq` from
AINTLIB's `Moduli/GammaHRepresentability.lean`, exact source blob
`dcd6e523ba797116398a1566ffa596f0e412e8e8`. The source blob is present at
AINTLIB's Apache-2.0 licensed default commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import Mathlib.RingTheory.Invariant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Geometric points of an affine invariant quotient

Two algebra homomorphisms from an affine coordinate ring to an algebraically
closed base field which agree on every invariant differ by the finite group
action. This is the algebraic geometric-point orbit statement needed to
identify fibres of an affine invariant quotient.
-/

universe u v

namespace AlgebraicGeometry

open Pointwise in
/-- Over an algebraically closed field, two affine points agreeing on every invariant
differ by the finite group action. -/
theorem exists_smul_algHom_eq
    {k B : Type u} [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    {G : Type v} [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G k B] (a₁ a₂ : B →ₐ[k] k)
    (hagree : ∀ b : B, (∀ g : G, g • b = b) → a₁ b = a₂ b) :
    ∃ g : G, ∀ b : B, a₂ b = a₁ (g • b) := by
  classical
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra k B G) B G :=
    ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI h₁ : (RingHom.ker a₁.toRingHom).IsPrime := RingHom.ker_isPrime _
  haveI h₂ : (RingHom.ker a₂.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨g₀, hg₀⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (FixedPoints.subalgebra k B G) B G
    (RingHom.ker a₁.toRingHom) (RingHom.ker a₂.toRingHom)
    (by
      ext b'
      change algebraMap _ B b' ∈ RingHom.ker a₁.toRingHom ↔
        algebraMap _ B b' ∈ RingHom.ker a₂.toRingHom
      rw [RingHom.mem_ker, RingHom.mem_ker]
      have hfix : ∀ g : G, g • (b' : B) = (b' : B) := b'.2
      rw [show a₁.toRingHom (algebraMap _ B b') = a₁ (b' : B) from rfl,
        show a₂.toRingHom (algebraMap _ B b') = a₂ (b' : B) from rfl,
        hagree (b' : B) hfix])
  refine ⟨g₀⁻¹, fun b => ?_⟩
  have hker : ∀ x : B, a₂ x = 0 ↔ a₁ (g₀⁻¹ • x) = 0 := by
    intro x
    constructor
    · intro hx
      have : x ∈ g₀ • RingHom.ker a₁.toRingHom := hg₀ ▸ (RingHom.mem_ker.mpr hx)
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at this
      exact RingHom.mem_ker.mp this
    · intro hx
      have : x ∈ g₀ • RingHom.ker a₁.toRingHom := by
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        exact RingHom.mem_ker.mpr hx
      rw [← hg₀] at this
      exact RingHom.mem_ker.mp this
  have hsmul_alg : ∀ c : k, g₀⁻¹ • (algebraMap k B c) = algebraMap k B c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, smul_comm g₀⁻¹ c (1 : B), smul_one]
  have hz : a₂ (b - algebraMap k B (a₁ (g₀⁻¹ • b))) = 0 := by
    rw [(hker _)]
    rw [smul_sub, hsmul_alg, map_sub, AlgHom.commutes, sub_eq_zero]
    rfl
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at hz
  exact hz

end AlgebraicGeometry
