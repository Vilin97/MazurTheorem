/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q1.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.Invariant.Basic

/-!
# Finite group actions on affine schemes and the invariants morphism

For a group `G` acting on a commutative ring `B` (by `R`-algebra automorphisms, for a
base ring `R`), this file provides the induced action on `Spec B` and the projection to
the spectrum of the fixed subalgebra `A := FixedPoints.subalgebra R B G`:

* `AlgebraicGeometry.specSMul g : Spec B ⟶ Spec B` — the automorphism induced by
  `g • ·`, with the covariant composition law `specSMul (g * h) = specSMul g ≫
  specSMul h` (on points it acts by `PrimeSpectrum.comap (g • ·)`, i.e. the classical
  `g⁻¹`-action on primes; invariance statements are convention-independent).
* `AlgebraicGeometry.invariantsπ R B G : Spec B ⟶ Spec A` — the orbit map, invariant
  under `specSMul` (`specSMul_invariantsπ`).
* For finite `G`: `invariantsπ` is integral (`invariantsπ_isIntegralHom`), surjective
  (`invariantsπ_surjective`), and its fibres are exactly the `G`-orbits
  (`invariantsπ_apply_eq_iff`).

These are the affine bones of the quotient of a scheme by a finite group
([Loeffler, *Modular curves*, Prop 3.6.1]; SGA I V.1.1; Stacks 07S3–07S7): the
universal property of `Spec A` as the categorical quotient is
`ModularCurves/ForMathlib/AffineQuotient.lean` (ticket T-Q3).

Upstream note: mathlib's `RingTheory/Invariant/Basic.lean` has the prime-level
statements (`Algebra.IsInvariant.isIntegral`, `exists_smul_of_under_eq`); nothing in
`Mathlib/AlgebraicGeometry/` currently touches `MulSemiringAction`.
-/

universe u v

open AlgebraicGeometry CategoryTheory

open scoped Pointwise

namespace AlgebraicGeometry

variable (G : Type*) [Group G]
variable {B : Type u} [CommRing B] [MulSemiringAction G B]

section SpecSMul

variable {G}

/-- The automorphism of `Spec B` induced by the action of `g : G` on `B`. On points it
is `PrimeSpectrum.comap (MulSemiringAction.toRingHom G B g)` (the classical action of
`g⁻¹` on primes); the assignment `g ↦ specSMul g` is covariant for `≫`
(`specSMul_mul`). -/
noncomputable def specSMul (g : G) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g))

@[simp]
theorem specSMul_one : specSMul (1 : G) (B := B) = 𝟙 _ := by
  rw [specSMul, show CommRingCat.ofHom (MulSemiringAction.toRingHom G B 1) =
    𝟙 (CommRingCat.of B) from by ext b; exact one_smul G b, Spec.map_id]

theorem specSMul_mul (g h : G) :
    specSMul (g * h) (B := B) = specSMul g ≫ specSMul h := by
  rw [specSMul, show CommRingCat.ofHom (MulSemiringAction.toRingHom G B (g * h)) =
    CommRingCat.ofHom (MulSemiringAction.toRingHom G B h) ≫
      CommRingCat.ofHom (MulSemiringAction.toRingHom G B g) from by
    ext b; exact mul_smul g h b, Spec.map_comp]
  rfl

instance (g : G) : IsIso (specSMul (B := B) g) :=
  ⟨specSMul g⁻¹, by rw [← specSMul_mul, mul_inv_cancel, specSMul_one],
    by rw [← specSMul_mul, inv_mul_cancel, specSMul_one]⟩

theorem specSMul_apply (g : G) (p : Spec (CommRingCat.of B)) :
    specSMul g p = PrimeSpectrum.comap (MulSemiringAction.toRingHom G B g) p :=
  rfl

/-- The scheme-theoretic action and the pointwise action on prime ideals: `specSMul g`
sends a prime `p` to `g⁻¹ • p`. -/
theorem specSMul_apply_asIdeal (g : G) (p : Spec (CommRingCat.of B)) :
    (specSMul g p).asIdeal = g⁻¹ • p.asIdeal := by
  ext b
  rw [specSMul_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.mem_inv_pointwise_smul_iff]
  rfl

end SpecSMul

variable (R : Type v) [CommRing R] [Algebra R B] [SMulCommClass G R B]
variable (B)

/-- Every fixed point of `B` lies in the fixed subalgebra — the tautological
`Algebra.IsInvariant` instance for the honest invariants. -/
instance : Algebra.IsInvariant (FixedPoints.subalgebra R B G) B G :=
  ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

/-- The invariants morphism `Spec B ⟶ Spec (Bᴳ)`: the affine orbit map of the
`G`-action, induced by the inclusion of the fixed subalgebra. -/
noncomputable def invariantsπ :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B G) B))

/-- The invariants morphism coequalizes the `G`-action. -/
@[reassoc (attr := simp)]
theorem specSMul_invariantsπ (g : G) :
    specSMul g ≫ invariantsπ G B R = invariantsπ G B R := by
  rw [specSMul, invariantsπ, ← Spec.map_comp]
  congr 1
  ext a
  exact a.2 g

/-- For a finite group, the invariants morphism is integral (in particular affine and
universally closed). -/
instance invariantsπ_isIntegralHom [Finite G] : IsIntegralHom (invariantsπ G B R) := by
  rw [invariantsπ, IsIntegralHom.SpecMap_iff]
  exact Algebra.isIntegral_def.mp
    (Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R B G) B G)

/-- For a finite group, the invariants morphism is surjective: every prime of the fixed
subalgebra lies under a prime of `B`. -/
theorem invariantsπ_surjective [Finite G] :
    Function.Surjective (invariantsπ G B R).base := by
  have hint : (algebraMap (FixedPoints.subalgebra R B G) B).IsIntegral :=
    Algebra.isIntegral_def.mp
      (Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R B G) B G)
  exact hint.comap_surjective Subtype.val_injective

/-- The fibres of the invariants morphism are exactly the `G`-orbits: two primes of `B`
lie over the same prime of `Bᴳ` iff they differ by the action of some `g : G`. -/
theorem invariantsπ_apply_eq_iff [Finite G] (x y : Spec (CommRingCat.of B)) :
    invariantsπ G B R x = invariantsπ G B R y ↔ ∃ g : G, specSMul g x = y := by
  constructor
  · intro hxy
    have h : x.asIdeal.under (FixedPoints.subalgebra R B G) =
        y.asIdeal.under (FixedPoints.subalgebra R B G) :=
      congrArg PrimeSpectrum.asIdeal hxy
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      (FixedPoints.subalgebra R B G) B G x.asIdeal y.asIdeal h
    refine ⟨g⁻¹, PrimeSpectrum.ext ?_⟩
    rw [specSMul_apply_asIdeal, inv_inv, hg]
  · rintro ⟨g, rfl⟩
    rw [← Scheme.Hom.comp_apply, specSMul_invariantsπ]

end AlgebraicGeometry
