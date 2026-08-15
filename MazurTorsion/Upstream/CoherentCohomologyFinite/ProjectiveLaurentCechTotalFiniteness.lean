/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechDecomposition

/-!
# Finiteness of the total projective Laurent Čech cohomology

The Laurent Čech complex is a direct sum of its fixed-exponent
subcomplexes.  All but finitely many exponent summands are contractible.
This file turns that calculation into a finiteness theorem for the
cohomology of the full direct-sum complex over a Noetherian coefficient
ring.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- Cycles in the direct sum of all fixed-exponent subcomplexes. -/
noncomputable abbrev ExponentDirectSumCycles
    (R : Type*) [CommRing R] (d : ℤ) (q : ℕ) :=
  (exponentDirectSumDifferential
    (ι := ι) (R := R) d q).ker

/-- Boundaries, regarded as a submodule of the cycle module. -/
noncomputable def exponentDirectSumBoundaries
    (R : Type*) [CommRing R] (d : ℤ) (q : ℕ) :
    Submodule R
      (ExponentDirectSumCycles (ι := ι) R d (q + 1)) :=
  Submodule.comap
    (exponentDirectSumDifferential
      (ι := ι) (R := R) d (q + 1)).ker.subtype
    (exponentDirectSumDifferential
      (ι := ι) (R := R) d q).range

noncomputable local instance exponentDirectSumCyclesAddCommGroup
    [CommRing R] (d : ℤ) (q : ℕ) :
    AddCommGroup
      (ExponentDirectSumCycles (ι := ι) R d q) :=
  Module.addCommMonoidToAddCommGroup R

/-- Positive-degree cycles modulo boundaries. -/
noncomputable abbrev ExponentDirectSumPositiveCohomology
    (R : Type*) [CommRing R] (d : ℤ) (q : ℕ) :=
  ExponentDirectSumCycles (ι := ι) R d (q + 1) ⧸
    exponentDirectSumBoundaries (ι := ι) R d q

/-- Cohomology of the direct sum of all fixed-exponent subcomplexes. -/
noncomputable abbrev ExponentDirectSumModuleCohomology
    (R : Type*) [CommRing R] (d : ℤ) :
    ℕ → Type _
  | 0 =>
      ExponentDirectSumCycles (ι := ι) R d 0
  | q + 1 =>
      ExponentDirectSumPositiveCohomology (ι := ι) R d q

/-- Endpoint cochains form a finite module over a Noetherian ring. -/
theorem exponentEndpointCochain_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      (ExponentEndpointCochain (ι := ι) R d q) := by
  letI :
      Fintype {a : HomogeneousExponent (ι := ι) d //
        a ∈ CohomologyExponentSet (ι := ι) d} :=
    (cohomologyExponentSet_finite (ι := ι) d).fintype
  infer_instance

/-- Endpoint cycles, extended by zero, are cycles in the full direct sum. -/
noncomputable def exponentEndpointCyclesToDirectSumCycles
    [CommRing R] (d : ℤ) (q : ℕ) :
    (exponentEndpointDifferential
        (ι := ι) (R := R) d q).ker →ₗ[R]
      (exponentDirectSumDifferential
        (ι := ι) (R := R) d q).ker :=
  LinearMap.codRestrict
    (exponentDirectSumDifferential
      (ι := ι) (R := R) d q).ker
    ((exponentEndpointInclusion
      (ι := ι) (R := R) d q).comp
        (exponentEndpointDifferential
          (ι := ι) (R := R) d q).ker.subtype)
    (fun c => by
      change exponentDirectSumDifferential
        (ι := ι) (R := R) d q
          (exponentEndpointInclusion
            (ι := ι) (R := R) d q c.1) = 0
      rw [← LinearMap.comp_apply,
        ← exponentEndpointInclusion_naturality]
      simp)

/--
In positive degree, endpoint cycles map to the cohomology of the full
direct-sum complex.
-/
noncomputable def exponentDirectSumCohomologyMkQ
    [CommRing R] (d : ℤ) (q : ℕ) :
    ExponentDirectSumCycles (ι := ι) R d (q + 1) →ₗ[R]
      ExponentDirectSumPositiveCohomology (ι := ι) R d q := by
  letI : AddCommGroup
      (ExponentDirectSumCycles (ι := ι) R d (q + 1)) :=
    Module.addCommMonoidToAddCommGroup R
  exact Submodule.mkQ
    (exponentDirectSumBoundaries (ι := ι) R d q)

/--
Endpoint cycles descend along the quotient map to positive-degree
cohomology.
-/
noncomputable def exponentEndpointCyclesToDirectSumCohomology
    [CommRing R] (d : ℤ) (q : ℕ) :
    (exponentEndpointDifferential
        (ι := ι) (R := R) d (q + 1)).ker →ₗ[R]
      ExponentDirectSumModuleCohomology (ι := ι) R d (q + 1) :=
  (exponentDirectSumCohomologyMkQ
    (ι := ι) (R := R) d q).comp
    (exponentEndpointCyclesToDirectSumCycles
      (ι := ι) (R := R) d (q + 1))

/-- Restrict a full cycle to its endpoint-exponent components. -/
noncomputable def exponentDirectSumCyclesToEndpointCochain
    [CommRing R] (d : ℤ) (q : ℕ) :
    ExponentDirectSumCycles (ι := ι) R d q →ₗ[R]
      ExponentEndpointCochain (ι := ι) R d q :=
  (exponentEndpointProjection
    (ι := ι) (R := R) d q).comp
      (ExponentDirectSumCycles
        (ι := ι) R d q).subtype

/--
A degree-zero cycle is determined by its endpoint-exponent components.
The non-endpoint components vanish by injectivity of their first
differential.
-/
theorem exponentDirectSumCyclesToEndpointCochain_degreeZero_injective
    [CommRing R] (d : ℤ) :
    Function.Injective
      (exponentDirectSumCyclesToEndpointCochain
        (ι := ι) (R := R) d 0) := by
  intro x y hxy
  apply Subtype.ext
  apply DFinsupp.ext
  intro a
  by_cases ha :
      a ∈ CohomologyExponentSet (ι := ι) d
  · have hcomponent :=
      congrArg
        (fun c : ExponentEndpointCochain (ι := ι) R d 0 =>
          c ⟨a, ha⟩)
        hxy
    exact hcomponent
  · apply
      (exponentCohomology_vanishes_outside_set
        (κ := R) a ha).1
    calc
      exponentDifferential (R := R) a 0 (x.1 a) =
          (exponentDirectSumDifferential
            (ι := ι) (R := R) d 0 x.1) a :=
        rfl
      _ = 0 := congrArg
        (fun c : Π₀ b : HomogeneousExponent (ι := ι) d,
          ExponentCochain (ι := ι) R b 1 => c a)
        x.2
      _ = (exponentDirectSumDifferential
            (ι := ι) (R := R) d 0 y.1) a :=
        (congrArg
          (fun c : Π₀ b : HomogeneousExponent (ι := ι) d,
            ExponentCochain (ι := ι) R b 1 => c a)
          y.2).symm
      _ = exponentDifferential (R := R) a 0 (y.1 a) :=
        rfl

/-- Extension by zero has the prescribed value at every endpoint. -/
lemma exponentEndpointInclusion_apply_of_mem
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : ExponentEndpointCochain (ι := ι) R d q)
    (a : HomogeneousExponent (ι := ι) d)
    (ha : a ∈ CohomologyExponentSet (ι := ι) d) :
    exponentEndpointInclusion (ι := ι) (R := R) d q c a =
      c ⟨a, ha⟩ := by
  have hleft :=
    LinearMap.congr_fun
      (exponentEndpointProjection_comp_inclusion
        (ι := ι) (R := R) d q) c
  exact congrArg
    (fun x : ExponentEndpointCochain (ι := ι) R d q =>
      x ⟨a, ha⟩)
    hleft

/-- Restrict a full cycle to an endpoint-supported cycle. -/
noncomputable def exponentEndpointCycleOfDirectSumCycle
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : ExponentDirectSumCycles (ι := ι) R d q) :
    (exponentEndpointDifferential
      (ι := ι) (R := R) d q).ker :=
  ⟨exponentEndpointProjection
      (ι := ι) (R := R) d q c.1,
    by
      change
        exponentEndpointDifferential
          (ι := ι) (R := R) d q
            (exponentEndpointProjection
              (ι := ι) (R := R) d q c.1) = 0
      rw [← LinearMap.comp_apply,
        ← exponentEndpointProjection_naturality,
        LinearMap.comp_apply, c.2, map_zero]⟩

/--
A positive-degree cycle which vanishes on every endpoint exponent is a
boundary.
-/
theorem exponentDirectSumCycle_mem_range_of_endpoint_eq_zero
    [CommRing R] (d : ℤ) (q : ℕ)
    (w : ExponentDirectSumCycles (ι := ι) R d (q + 1))
    (hw : ∀ (a : HomogeneousExponent (ι := ι) d),
      a ∈ CohomologyExponentSet (ι := ι) d → w.1 a = 0) :
    w.1 ∈
      (exponentDirectSumDifferential
        (ι := ι) (R := R) d q).range := by
  classical
  have hpreimage
      (a : HomogeneousExponent (ι := ι) d) :
      ∃ b : ExponentCochain (ι := ι) R a q,
        exponentDifferential (R := R) a q b = w.1 a := by
    by_cases ha :
        a ∈ CohomologyExponentSet (ι := ι) d
    · exact ⟨0, by simp [hw a ha]⟩
    · apply
        ((exponentCohomology_vanishes_outside_set
          (κ := R) a ha).2 q _).mp
      exact congrArg
        (fun x : Π₀ b : HomogeneousExponent (ι := ι) d,
          ExponentCochain (ι := ι) R b (q + 1 + 1) => x a)
        w.2
  let preimage :
      ∀ a : HomogeneousExponent (ι := ι) d,
        ExponentCochain (ι := ι) R a q :=
    fun a => Classical.choose (hpreimage a)
  let b :
      Π₀ a : HomogeneousExponent (ι := ι) d,
        ExponentCochain (ι := ι) R a q :=
    DFinsupp.mk w.1.support (fun a => preimage a.1)
  refine ⟨b, ?_⟩
  apply DFinsupp.ext
  intro a
  by_cases ha : a ∈ w.1.support
  · change
      exponentDifferential (R := R) a q (b a) = w.1 a
    simpa [b, preimage, ha] using
      Classical.choose_spec (hpreimage a)
  · have hwzero : w.1 a = 0 := by
      simpa using ha
    change
      exponentDifferential (R := R) a q (b a) = w.1 a
    simp [b, ha, hwzero]

/--
Subtracting the endpoint restriction of a positive-degree cycle leaves a
boundary.
-/
theorem exponentEndpointCycle_difference_mem_boundaries
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : ExponentDirectSumCycles (ι := ι) R d (q + 1)) :
    exponentEndpointCyclesToDirectSumCycles
          (ι := ι) (R := R) d (q + 1)
          (exponentEndpointCycleOfDirectSumCycle
            (ι := ι) (R := R) d (q + 1) c) +
        (-1 : R) • c ∈
      exponentDirectSumBoundaries (ι := ι) R d q := by
  unfold exponentDirectSumBoundaries
  rw [Submodule.mem_comap]
  apply exponentDirectSumCycle_mem_range_of_endpoint_eq_zero
    (ι := ι) (R := R) d q
    (w :=
      exponentEndpointCyclesToDirectSumCycles
          (ι := ι) (R := R) d (q + 1)
          (exponentEndpointCycleOfDirectSumCycle
            (ι := ι) (R := R) d (q + 1) c) +
        (-1 : R) • c)
  intro a ha
  change
    exponentEndpointInclusion
        (ι := ι) (R := R) d (q + 1)
        (exponentEndpointProjection
          (ι := ι) (R := R) d (q + 1) c.1) a +
      (-1 : R) • c.1 a = 0
  rw [exponentEndpointInclusion_apply_of_mem
    (ι := ι) (R := R) d (q + 1)
    (exponentEndpointProjection
      (ι := ι) (R := R) d (q + 1) c.1) a ha]
  simp

/--
Every positive-degree direct-sum cohomology class has an
endpoint-supported representative.
-/
theorem exponentEndpointCyclesToDirectSumCohomology_surjective
    [CommRing R] (d : ℤ) (q : ℕ) :
    Function.Surjective
      (exponentEndpointCyclesToDirectSumCohomology
        (ι := ι) (R := R) d q) := by
  intro z
  obtain ⟨c, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (exponentDirectSumBoundaries
        (ι := ι) R d q) z
  let e :
      (exponentEndpointDifferential
        (ι := ι) (R := R) d (q + 1)).ker :=
    exponentEndpointCycleOfDirectSumCycle
      (ι := ι) (R := R) d (q + 1) c
  refine ⟨e, ?_⟩
  have hboundary :=
    exponentEndpointCycle_difference_mem_boundaries
      (ι := ι) (R := R) d q c
  have hzero :
      exponentDirectSumCohomologyMkQ
        (ι := ι) (R := R) d q
          (exponentEndpointCyclesToDirectSumCycles
              (ι := ι) (R := R) d (q + 1) e +
            (-1 : R) • c) = 0 := by
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := exponentDirectSumBoundaries
          (ι := ι) R d q)).mpr hboundary
  have hadd :
      exponentDirectSumCohomologyMkQ
          (ι := ι) (R := R) d q
          (exponentEndpointCyclesToDirectSumCycles
            (ι := ι) (R := R) d (q + 1) e) +
        (-1 : R) •
          exponentDirectSumCohomologyMkQ
            (ι := ι) (R := R) d q c = 0 := by
    rw [← map_smul, ← map_add]
    exact hzero
  change
    exponentDirectSumCohomologyMkQ
        (ι := ι) (R := R) d q
        (exponentEndpointCyclesToDirectSumCycles
          (ι := ι) (R := R) d (q + 1) e) =
      exponentDirectSumCohomologyMkQ
        (ι := ι) (R := R) d q c
  calc
    exponentDirectSumCohomologyMkQ
        (ι := ι) (R := R) d q
        (exponentEndpointCyclesToDirectSumCycles
          (ι := ι) (R := R) d (q + 1) e) =
        (exponentDirectSumCohomologyMkQ
            (ι := ι) (R := R) d q
            (exponentEndpointCyclesToDirectSumCycles
              (ι := ι) (R := R) d (q + 1) e) +
          (-1 : R) •
            exponentDirectSumCohomologyMkQ
              (ι := ι) (R := R) d q c) +
            exponentDirectSumCohomologyMkQ
              (ι := ι) (R := R) d q c := by
      simp
    _ = 0 +
        exponentDirectSumCohomologyMkQ
          (ι := ι) (R := R) d q c := by
      rw [hadd]
    _ = exponentDirectSumCohomologyMkQ
          (ι := ι) (R := R) d q c := zero_add _

/-- Degree-zero cohomology of the full direct-sum complex is finite. -/
theorem exponentDirectSumDegreeZeroCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) :
    Module.Finite R
      (ExponentDirectSumCycles (ι := ι) R d 0) := by
  letI :
      Module.Finite R
        (ExponentEndpointCochain (ι := ι) R d 0) :=
    exponentEndpointCochain_finite
      (ι := ι) (R := R) d 0
  letI :
      AddCommGroup
        (ExponentEndpointCochain (ι := ι) R d 0) :=
    Module.addCommMonoidToAddCommGroup R
  letI :
      IsNoetherian R
        (ExponentEndpointCochain (ι := ι) R d 0) :=
    isNoetherian_of_isNoetherianRing_of_finite R _
  exact Module.Finite.of_injective
    (exponentDirectSumCyclesToEndpointCochain
      (ι := ι) (R := R) d 0)
    (exponentDirectSumCyclesToEndpointCochain_degreeZero_injective
      (ι := ι) (R := R) d)

/-- Every positive-degree cohomology module of the full direct-sum
complex is finite. -/
theorem exponentDirectSumPositiveCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      (ExponentDirectSumPositiveCohomology
        (ι := ι) R d q) := by
  letI :
      Module.Finite R
        (ExponentEndpointCochain (ι := ι) R d (q + 1)) :=
    exponentEndpointCochain_finite
      (ι := ι) (R := R) d (q + 1)
  letI :
      AddCommGroup
        (ExponentEndpointCochain (ι := ι) R d (q + 1)) :=
    Module.addCommMonoidToAddCommGroup R
  letI :
      IsNoetherian R
        (ExponentEndpointCochain (ι := ι) R d (q + 1)) :=
    isNoetherian_of_isNoetherianRing_of_finite R _
  letI :
      Module.Finite R
        (exponentEndpointDifferential
          (ι := ι) (R := R) d (q + 1)).ker := by
    exact Module.Finite.of_injective
      (exponentEndpointDifferential
        (ι := ι) (R := R) d (q + 1)).ker.subtype
      (exponentEndpointDifferential
        (ι := ι) (R := R) d (q + 1)).ker.subtype_injective
  exact Module.Finite.of_surjective
    (exponentEndpointCyclesToDirectSumCohomology
      (ι := ι) (R := R) d q)
    (exponentEndpointCyclesToDirectSumCohomology_surjective
      (ι := ι) (R := R) d q)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
