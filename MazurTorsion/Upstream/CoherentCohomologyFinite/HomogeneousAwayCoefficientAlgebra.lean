/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Coefficient algebra structure on homogeneous localizations

For a graded `k`-algebra, a degree-zero homogeneous localization inherits
its coefficient algebra structure through the injective map to the
ordinary localization.  Mathlib's homogeneous-localization API does not
package this structure at the benchmark pin.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open HomogeneousLocalization

section MapTo

variable {ι A σ B τ : Type*}
variable [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A]
variable [AddCommMonoid ι] [DecidableEq ι]
variable {𝒜 : ι → σ} [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B]
variable [AddSubgroupClass τ B]
variable {ℬ : ι → τ} [GradedRing ℬ]

/-- Map a homogeneous localization to an explicitly equal target
denominator.  This is a type-stable wrapper around `Away.map`; it is
useful when the equality of denominators is propositional rather than
definitional. -/
def homogeneousAwayMapTo
    (g : 𝒜 →+*ᵍ ℬ) (f : A) (t : B)
    (h : g f = t) :
    Away 𝒜 f →+* Away ℬ t :=
  HomogeneousLocalization.map g (by
    rintro _ ⟨q, rfl⟩
    exact ⟨q, by simp [h]⟩)

@[simp]
lemma homogeneousAwayMapTo_mk
    (g : 𝒜 →+*ᵍ ℬ)
    {d : ι} (f : A) (t : B) (h : g f = t)
    (hf : f ∈ 𝒜 d) (ht : t ∈ ℬ d)
    (q : ℕ) (x : A) (hx : x ∈ 𝒜 (q • d)) :
    homogeneousAwayMapTo g f t h
        (Away.mk 𝒜 hf q x hx) =
      Away.mk ℬ ht q (g x) (GradedRingHom.map_mem g hx) := by
  apply HomogeneousLocalization.val_injective
  simp [homogeneousAwayMapTo, Away.mk,
    HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, h]

end MapTo

/-- The coefficient-module structure inherited through the ordinary
localization. -/
@[reducible]
def homogeneousAwayCoefficientModule
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedRing 𝒜]
    (f : A) :
    Module k (Away 𝒜 f) := by
  apply Function.Injective.module k
    (algebraMap
      (Away 𝒜 f)
      (Localization.Away f)).toAddMonoidHom
    (HomogeneousLocalization.val_injective
      (Submonoid.powers f))
  intro r x
  exact
    HomogeneousLocalization.val_smul
      (Submonoid.powers f) r x

/-- The compatible coefficient-algebra structure on a homogeneous
localization. -/
@[reducible]
def homogeneousAwayCoefficientAlgebra
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedRing 𝒜]
    (f : A) :
    Algebra k (Away 𝒜 f) := by
  letI : Module k (Away 𝒜 f) :=
    homogeneousAwayCoefficientModule k A 𝒜 f
  exact
    Algebra.ofModule
      (fun r x y => by
        apply HomogeneousLocalization.val_injective
        simp only [HomogeneousLocalization.val_mul,
          HomogeneousLocalization.val_smul]
        exact Algebra.smul_mul_assoc r x.val y.val)
      (fun r x y => by
        apply HomogeneousLocalization.val_injective
        simp only [HomogeneousLocalization.val_mul,
          HomogeneousLocalization.val_smul]
        exact Algebra.mul_smul_comm r x.val y.val)

section MapToAlgHom

variable {k A B : Type u}
variable [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]
variable {𝒜 : ℕ → Submodule k A} [GradedRing 𝒜]
variable {ℬ : ℕ → Submodule k B} [GradedRing ℬ]

local instance sourceAwayCoefficientAlgebra (f : A) :
    Algebra k (Away 𝒜 f) :=
  homogeneousAwayCoefficientAlgebra k A 𝒜 f

local instance targetAwayCoefficientAlgebra (t : B) :
    Algebra k (Away ℬ t) :=
  homogeneousAwayCoefficientAlgebra k B ℬ t

/-- A coefficient is the degree-zero homogeneous fraction with
denominator exponent zero. -/
lemma homogeneousAway_algebraMap_eq_mk
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) (r : k) :
    algebraMap k (Away 𝒜 f) r =
      Away.mk 𝒜 hf 0 (algebraMap k A r)
        (by
          simpa using
            SetLike.algebraMap_mem_graded 𝒜 r) := by
  apply HomogeneousLocalization.val_injective
  rw [Algebra.algebraMap_eq_smul_one,
    HomogeneousLocalization.val_smul,
    HomogeneousLocalization.val_one,
    Algebra.smul_def, mul_one,
    HomogeneousLocalization.Away.val_mk]
  rw [← Localization.mk_algebraMap]
  congr 1
  apply Subtype.ext
  simp

/-- A graded algebra map induces an algebra map between homogeneous
localizations when its denominator is identified with the chosen target
denominator. -/
def homogeneousAwayMapToAlgHom
    (g : 𝒜 →ₐᵍ[k] ℬ)
    {d : ℕ} (f : A) (t : B)
    (h : g f = t) (hf : f ∈ 𝒜 d) (ht : t ∈ ℬ d) :
    Away 𝒜 f →ₐ[k] Away ℬ t where
  __ :=
    homogeneousAwayMapTo
      g.toGradedRingHom f t h
  commutes' r := by
    change
      homogeneousAwayMapTo
          g.toGradedRingHom f t h
          (algebraMap k (Away 𝒜 f) r) =
        algebraMap k (Away ℬ t) r
    rw [homogeneousAway_algebraMap_eq_mk f hf r,
      homogeneousAwayMapTo_mk
        g.toGradedRingHom f t h hf ht]
    rw [homogeneousAway_algebraMap_eq_mk
      (𝒜 := ℬ) t ht r]
    congr 1
    exact g.toAlgHom.commutes r

@[simp]
lemma homogeneousAwayMapToAlgHom_mk
    (g : 𝒜 →ₐᵍ[k] ℬ)
    {d : ℕ} (f : A) (t : B)
    (h : g f = t) (hf : f ∈ 𝒜 d) (ht : t ∈ ℬ d)
    (q : ℕ) (x : A) (hx : x ∈ 𝒜 (q • d)) :
    homogeneousAwayMapToAlgHom g f t h hf ht
        (Away.mk 𝒜 hf q x hx) =
      Away.mk ℬ ht q (g x)
        (GradedRingHom.map_mem g.toGradedRingHom hx) :=
  homogeneousAwayMapTo_mk
    g.toGradedRingHom f t h hf ht q x hx

lemma homogeneousAwayMapToAlgHom_mk_of_eq
    (g : 𝒜 →ₐᵍ[k] ℬ)
    {d : ℕ} (f : A) (t : B)
    (h : g f = t) (hf : f ∈ 𝒜 d) (ht : t ∈ ℬ d)
    (q : ℕ) (x : A) (hx : x ∈ 𝒜 (q • d))
    (y : B) (hy : y ∈ ℬ (q • d))
    (hxy : g x = y) :
    homogeneousAwayMapToAlgHom g f t h hf ht
        (Away.mk 𝒜 hf q x hx) =
      Away.mk ℬ ht q y hy := by
  rw [homogeneousAwayMapToAlgHom_mk]
  subst y
  rfl

end MapToAlgHom

section DegreeOneGeneration

variable {A σ : Type*}
variable [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The bounded monomial fractions used to generate a localization away
from a degree-one element.  Naming this set keeps later specializations
of the general Mathlib generation theorem type-stable. -/
def degreeOneAwayMonomialGenerators
    (f : A) (hf : f ∈ 𝒜 1)
    (ι : Type*) [Fintype ι]
    (v : ι → A) (hv : ∀ i, v i ∈ 𝒜 1) :
    Set (Away 𝒜 f) :=
  { Away.mk 𝒜 hf a (∏ i, v i ^ e i)
      (he ▸
        SetLike.prod_pow_mem_graded
          𝒜 (fun _ => 1) v e
          (fun i _ => hv i)) |
    (a : ℕ) (e : ι → ℕ)
    (he : ∑ i, e i • 1 = a • 1)
    (_ : ∀ i, e i ≤ 1) }

/-- If degree-one elements generate a graded ring over degree zero, the
associated bounded monomial fractions generate its degree-zero
localization. -/
lemma degreeOneAwayMonomialGenerators_adjoin_eq_top
    (f : A) (hf : f ∈ 𝒜 1)
    (ι : Type*) [Fintype ι]
    (v : ι → A)
    (hv : ∀ i, v i ∈ 𝒜 1)
    (hgenerate :
      Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) :
    Algebra.adjoin (𝒜 0)
        (degreeOneAwayMonomialGenerators
          f hf ι v hv) =
      (⊤ : Subalgebra (𝒜 0) (Away 𝒜 f)) :=
  Away.adjoin_mk_prod_pow_eq_top
    hf ι v hgenerate (fun _ => 1) hv

end DegreeOneGeneration

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
