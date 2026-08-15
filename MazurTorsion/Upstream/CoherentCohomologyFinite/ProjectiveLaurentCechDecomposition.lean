/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechModuleFiniteness
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Exponentwise decomposition of the Laurent Čech differential

The Laurent Čech differential preserves the signed exponent vector.  This
file records that fact as a commuting square between the total cochain
module and its direct sum of fixed-exponent subcomplexes.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- The direct sum of all fixed-exponent cochain differentials. -/
noncomputable def exponentDirectSumDifferential
    [CommRing R] (d : ℤ) (q : ℕ) :
    (Π₀ a : HomogeneousExponent (ι := ι) d,
        ExponentCochain (ι := ι) R a q) →ₗ[R]
      Π₀ a : HomogeneousExponent (ι := ι) d,
        ExponentCochain (ι := ι) R a (q + 1) :=
  DFinsupp.mapRange.linearMap
    (fun a => exponentDifferential (R := R) a q)

@[simp]
lemma exponentDirectSumDifferential_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : Π₀ a : HomogeneousExponent (ι := ι) d,
      ExponentCochain (ι := ι) R a q)
    (a : HomogeneousExponent (ι := ι) d) :
    exponentDirectSumDifferential (R := R) d q c a =
      exponentDifferential (R := R) a q (c a) :=
  rfl

@[simp]
lemma basisIndexEquivExponent_insert
    {d : ℤ} {q : ℕ}
    (p : BasisIndex (ι := ι) d q)
    (j : MissingVertex p.1.1) :
    basisIndexEquivExponent (ι := ι) d (q + 1)
        (p.insert j) =
      ⟨(basisIndexEquivExponent (ι := ι) d q p).1,
        (basisIndexEquivExponent (ι := ι) d q p).2.insert j⟩ :=
  rfl

/--
Reindexing Laurent cochains by exponent intertwines the total differential
with the direct sum of the fixed-exponent differentials.
-/
theorem cochainEquivExponentDirectSum_naturality
    [CommRing R] (d : ℤ) (q : ℕ) :
    (cochainEquivExponentDirectSum
        (ι := ι) (R := R) d (q + 1)).toLinearMap.comp
        (differential (ι := ι) (R := R) d q) =
      (exponentDirectSumDifferential
        (ι := ι) (R := R) d q).comp
        (cochainEquivExponentDirectSum
          (ι := ι) (R := R) d q).toLinearMap := by
  apply Finsupp.lhom_ext
  intro p r
  rcases p with ⟨pI, pa⟩
  simp [cochainEquivExponentDirectSum,
    exponentDirectSumDifferential, differential_single,
    basisCoboundary, exponentDifferential_single,
    exponentBasisCoboundary]
  congr 1
  ext a I
  by_cases h :
      (basisIndexEquivExponent
        (ι := ι) d q ⟨pI, pa⟩).1 = a
  · subst a
    simp
    apply Finset.sum_congr rfl
    intro c hc
    rfl
  · simp [h]

/--
The part of the exponentwise direct sum supported on the finite set of
cohomologically exceptional exponents.
-/
abbrev ExponentEndpointCochain
    (R : Type*) [Semiring R] (d : ℤ) (q : ℕ) :=
  Π₀ a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d},
    ExponentCochain (ι := ι) R a.1 q

/-- The exponentwise differential restricted to the endpoint exponents. -/
noncomputable def exponentEndpointDifferential
    [CommRing R] (d : ℤ) (q : ℕ) :
    ExponentEndpointCochain (ι := ι) R d q →ₗ[R]
      ExponentEndpointCochain (ι := ι) R d (q + 1) :=
  DFinsupp.mapRange.linearMap
    (fun a => exponentDifferential (R := R) a.1 q)

@[simp]
lemma exponentEndpointDifferential_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : ExponentEndpointCochain (ι := ι) R d q)
    (a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d}) :
    exponentEndpointDifferential (ι := ι) (R := R) d q c a =
      exponentDifferential (R := R) a.1 q (c a) :=
  rfl

/-- Restrict an exponentwise cochain to the endpoint exponents. -/
noncomputable def exponentEndpointProjection
    [CommRing R] (d : ℤ) (q : ℕ) :
    (Π₀ a : HomogeneousExponent (ι := ι) d,
        ExponentCochain (ι := ι) R a q) →ₗ[R]
      ExponentEndpointCochain (ι := ι) R d q := by
  classical
  exact DFinsupp.subtypeDomainLinearMap R _
    (fun a => a ∈ CohomologyExponentSet (ι := ι) d)

@[simp]
lemma exponentEndpointProjection_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : Π₀ a : HomogeneousExponent (ι := ι) d,
      ExponentCochain (ι := ι) R a q)
    (a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d}) :
    exponentEndpointProjection (ι := ι) (R := R) d q c a =
      c a.1 :=
  rfl

/-- Extend an endpoint-supported cochain by zero. -/
noncomputable def exponentEndpointInclusion
    [CommRing R] (d : ℤ) (q : ℕ) :
    ExponentEndpointCochain (ι := ι) R d q →ₗ[R]
      Π₀ a : HomogeneousExponent (ι := ι) d,
        ExponentCochain (ι := ι) R a q := by
  classical
  exact DFinsupp.coprodMap
    (fun a =>
      DFinsupp.lsingle
        (R := R)
        (M := fun b : HomogeneousExponent (ι := ι) d =>
          ExponentCochain (ι := ι) R b q)
        a.1)

@[simp]
lemma exponentEndpointInclusion_single
    [CommRing R] (d : ℤ) (q : ℕ)
    (a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d})
    (c : ExponentCochain (ι := ι) R a.1 q) :
    exponentEndpointInclusion (ι := ι) (R := R) d q
        (DFinsupp.single a c) =
      DFinsupp.single a.1 c := by
  classical
  unfold exponentEndpointInclusion
  rw [DFinsupp.coprodMap_apply_single]
  rfl

/-- Restriction is a left inverse to extension by zero. -/
theorem exponentEndpointProjection_comp_inclusion
    [CommRing R] (d : ℤ) (q : ℕ) :
    (exponentEndpointProjection (ι := ι) (R := R) d q).comp
        (exponentEndpointInclusion (ι := ι) (R := R) d q) =
      LinearMap.id := by
  classical
  apply DFinsupp.lhom_ext
  intro a c
  rw [LinearMap.comp_apply,
    exponentEndpointInclusion_single]
  ext b
  by_cases h : a = b
  · subst b
    simp
  · have hval : a.1 ≠ b.1 := by
      intro hab
      exact h (Subtype.ext hab)
    simp [h, hval]

/--
Extension by zero intertwines the endpoint differential and the full
exponentwise differential.
-/
theorem exponentEndpointInclusion_naturality
    [CommRing R] (d : ℤ) (q : ℕ) :
    (exponentEndpointInclusion (ι := ι) (R := R) d (q + 1)).comp
        (exponentEndpointDifferential (ι := ι) (R := R) d q) =
      (exponentDirectSumDifferential (ι := ι) (R := R) d q).comp
        (exponentEndpointInclusion (ι := ι) (R := R) d q) := by
  classical
  apply DFinsupp.lhom_ext
  intro a c
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    exponentEndpointInclusion_single]
  change
    exponentEndpointInclusion (ι := ι) (R := R) d (q + 1)
        (DFinsupp.mapRange
          (fun b x => exponentDifferential (R := R) b.1 q x)
          (fun _ => map_zero _)
          (DFinsupp.single a c)) =
      DFinsupp.mapRange
        (fun b x => exponentDifferential (R := R) b q x)
        (fun _ => map_zero _)
        (DFinsupp.single a.1 c)
  rw [DFinsupp.mapRange_single, DFinsupp.mapRange_single,
    exponentEndpointInclusion_single]

/--
Restriction to the endpoints also intertwines the full and endpoint
differentials.
-/
theorem exponentEndpointProjection_naturality
    [CommRing R] (d : ℤ) (q : ℕ) :
    (exponentEndpointProjection (ι := ι) (R := R) d (q + 1)).comp
        (exponentDirectSumDifferential (ι := ι) (R := R) d q) =
      (exponentEndpointDifferential (ι := ι) (R := R) d q).comp
        (exponentEndpointProjection (ι := ι) (R := R) d q) := by
  apply LinearMap.ext
  intro c
  ext a
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
