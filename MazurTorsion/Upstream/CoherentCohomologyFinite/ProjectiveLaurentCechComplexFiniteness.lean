/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechTotalFiniteness

/-!
# Finiteness of the Laurent Čech complex

The exponentwise reindexing is a chain isomorphism.  This file transports
the direct-sum finiteness calculation back to the original Laurent Čech
complex.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- Cycles in the original Laurent Čech complex. -/
noncomputable abbrev LaurentCechCycles
    (R : Type*) [CommRing R] (d : ℤ) (q : ℕ) :=
  (differential (ι := ι) (R := R) d q).ker

/-- Boundaries in the original Laurent Čech complex, as a submodule of
cycles. -/
noncomputable def laurentCechBoundaries
    (R : Type*) [CommRing R] (d : ℤ) (q : ℕ) :
    Submodule R
      (differential (ι := ι) (R := R) d (q + 1)).ker :=
  Submodule.comap
    (differential
      (ι := ι) (R := R) d (q + 1)).ker.subtype
    (differential (ι := ι) (R := R) d q).range

noncomputable local instance laurentCechCyclesAddCommGroup
    [CommRing R] (d : ℤ) (q : ℕ) :
    AddCommGroup (LaurentCechCycles (ι := ι) R d q) :=
  inferInstance

noncomputable local instance exponentDirectSumCyclesAddCommGroup'
    [CommRing R] (d : ℤ) (q : ℕ) :
    AddCommGroup
      (ExponentDirectSumCycles (ι := ι) R d q) :=
  Module.addCommMonoidToAddCommGroup R

/-- Positive-degree Laurent Čech cohomology. -/
noncomputable abbrev LaurentCechPositiveCohomology
    (R : Type*) [CommRing R] (d : ℤ) (q : ℕ) :=
  (differential (ι := ι) (R := R) d (q + 1)).ker ⧸
    laurentCechBoundaries (ι := ι) R d q

/--
The cochain reindexing sends cycles in the Laurent Čech complex to
cycles in the exponentwise direct sum.
-/
noncomputable def laurentCechCyclesToExponentDirectSumCycles
    [CommRing R] (d : ℤ) (q : ℕ) :
    LaurentCechCycles (ι := ι) R d q →ₗ[R]
      ExponentDirectSumCycles (ι := ι) R d q :=
  LinearMap.codRestrict
    (ExponentDirectSumCycles (ι := ι) R d q)
    ((cochainEquivExponentDirectSum
      (ι := ι) (R := R) d q).toLinearMap.comp
        (LaurentCechCycles (ι := ι) R d q).subtype)
    (fun c => by
      change
        exponentDirectSumDifferential
          (ι := ι) (R := R) d q
            (cochainEquivExponentDirectSum
              (ι := ι) (R := R) d q c.1) = 0
      calc
        exponentDirectSumDifferential
            (ι := ι) (R := R) d q
              (cochainEquivExponentDirectSum
                (ι := ι) (R := R) d q c.1) =
            cochainEquivExponentDirectSum
              (ι := ι) (R := R) d (q + 1)
              (differential (ι := ι) (R := R) d q c.1) :=
          (LinearMap.congr_fun
            (cochainEquivExponentDirectSum_naturality
              (ι := ι) (R := R) d q) c.1).symm
        _ = 0 := by rw [c.2, map_zero])

/-- The cycle reindexing is injective. -/
theorem laurentCechCyclesToExponentDirectSumCycles_injective
    [CommRing R] (d : ℤ) (q : ℕ) :
    Function.Injective
      (laurentCechCyclesToExponentDirectSumCycles
        (ι := ι) (R := R) d q) := by
  intro x y hxy
  apply Subtype.ext
  apply
    (cochainEquivExponentDirectSum
      (ι := ι) (R := R) d q).injective
  exact congrArg Subtype.val hxy

/-- The cycle reindexing is surjective. -/
theorem laurentCechCyclesToExponentDirectSumCycles_surjective
    [CommRing R] (d : ℤ) (q : ℕ) :
    Function.Surjective
      (laurentCechCyclesToExponentDirectSumCycles
        (ι := ι) (R := R) d q) := by
  intro y
  let x₀ : Cochain (ι := ι) R d q :=
    (cochainEquivExponentDirectSum
      (ι := ι) (R := R) d q).symm y.1
  have hx₀ :
      differential (ι := ι) (R := R) d q x₀ = 0 := by
    apply
      (cochainEquivExponentDirectSum
        (ι := ι) (R := R) d (q + 1)).injective
    calc
      cochainEquivExponentDirectSum
          (ι := ι) (R := R) d (q + 1)
          (differential (ι := ι) (R := R) d q x₀) =
          exponentDirectSumDifferential
            (ι := ι) (R := R) d q
            (cochainEquivExponentDirectSum
              (ι := ι) (R := R) d q x₀) := by
        exact LinearMap.congr_fun
          (cochainEquivExponentDirectSum_naturality
            (ι := ι) (R := R) d q) x₀
      _ = exponentDirectSumDifferential
            (ι := ι) (R := R) d q y.1 := by
        simp [x₀]
      _ = 0 := y.2
      _ = cochainEquivExponentDirectSum
            (ι := ι) (R := R) d (q + 1) 0 := by
        rw [map_zero]
  let x : LaurentCechCycles (ι := ι) R d q :=
    ⟨x₀, hx₀⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simp [laurentCechCyclesToExponentDirectSumCycles, x, x₀]

/-- Cycle modules of the two presentations are linearly equivalent. -/
noncomputable def laurentCechCyclesEquivExponentDirectSumCycles
    [CommRing R] (d : ℤ) (q : ℕ) :
    LaurentCechCycles (ι := ι) R d q ≃ₗ[R]
      ExponentDirectSumCycles (ι := ι) R d q :=
  LinearEquiv.ofBijective
    (laurentCechCyclesToExponentDirectSumCycles
      (ι := ι) (R := R) d q)
    ⟨laurentCechCyclesToExponentDirectSumCycles_injective
        (ι := ι) (R := R) d q,
      laurentCechCyclesToExponentDirectSumCycles_surjective
        (ι := ι) (R := R) d q⟩

/--
The cycle reindexing identifies boundaries in the two presentations of
the Laurent Čech complex.
-/
theorem laurentCechCyclesEquiv_map_boundaries
    [CommRing R] (d : ℤ) (q : ℕ) :
    Submodule.map
        (laurentCechCyclesEquivExponentDirectSumCycles
          (ι := ι) (R := R) d (q + 1)).toLinearMap
        (laurentCechBoundaries (ι := ι) R d q) =
      exponentDirectSumBoundaries (ι := ι) R d q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x.1 ∈
      (differential (ι := ι) (R := R) d q).range at hx
    change
      (laurentCechCyclesEquivExponentDirectSumCycles
        (ι := ι) (R := R) d (q + 1) x).1 ∈
        (exponentDirectSumDifferential
          (ι := ι) (R := R) d q).range
    obtain ⟨b, hb⟩ := hx
    refine
      ⟨cochainEquivExponentDirectSum
          (ι := ι) (R := R) d q b, ?_⟩
    change
      exponentDirectSumDifferential
          (ι := ι) (R := R) d q
          (cochainEquivExponentDirectSum
            (ι := ι) (R := R) d q b) =
        cochainEquivExponentDirectSum
          (ι := ι) (R := R) d (q + 1) x.1
    calc
      exponentDirectSumDifferential
          (ι := ι) (R := R) d q
          (cochainEquivExponentDirectSum
            (ι := ι) (R := R) d q b) =
          cochainEquivExponentDirectSum
            (ι := ι) (R := R) d (q + 1)
            (differential (ι := ι) (R := R) d q b) :=
        (LinearMap.congr_fun
          (cochainEquivExponentDirectSum_naturality
            (ι := ι) (R := R) d q) b).symm
      _ = cochainEquivExponentDirectSum
            (ι := ι) (R := R) d (q + 1) x.1 := by
        rw [hb]
  · intro hy
    change y.1 ∈
      (exponentDirectSumDifferential
        (ι := ι) (R := R) d q).range at hy
    obtain ⟨b, hb⟩ := hy
    let x :
        LaurentCechCycles (ι := ι) R d (q + 1) :=
      (laurentCechCyclesEquivExponentDirectSumCycles
        (ι := ι) (R := R) d (q + 1)).symm y
    refine ⟨x, ?_, ?_⟩
    · change x.1 ∈
        (differential (ι := ι) (R := R) d q).range
      refine
        ⟨(cochainEquivExponentDirectSum
            (ι := ι) (R := R) d q).symm b, ?_⟩
      apply
        (cochainEquivExponentDirectSum
          (ι := ι) (R := R) d (q + 1)).injective
      calc
        cochainEquivExponentDirectSum
            (ι := ι) (R := R) d (q + 1)
            (differential (ι := ι) (R := R) d q
              ((cochainEquivExponentDirectSum
                (ι := ι) (R := R) d q).symm b)) =
            exponentDirectSumDifferential
              (ι := ι) (R := R) d q
              (cochainEquivExponentDirectSum
                (ι := ι) (R := R) d q
                ((cochainEquivExponentDirectSum
                  (ι := ι) (R := R) d q).symm b)) :=
          LinearMap.congr_fun
            (cochainEquivExponentDirectSum_naturality
              (ι := ι) (R := R) d q)
            ((cochainEquivExponentDirectSum
              (ι := ι) (R := R) d q).symm b)
        _ = exponentDirectSumDifferential
              (ι := ι) (R := R) d q b := by
          simp
        _ = y.1 := hb
        _ = cochainEquivExponentDirectSum
              (ι := ι) (R := R) d (q + 1) x.1 := by
          change y.1 =
            (laurentCechCyclesEquivExponentDirectSumCycles
              (ι := ι) (R := R) d (q + 1) x).1
          rw [show
            (laurentCechCyclesEquivExponentDirectSumCycles
              (ι := ι) (R := R) d (q + 1)) x = y by
              exact (laurentCechCyclesEquivExponentDirectSumCycles
                (ι := ι) (R := R) d (q + 1)).apply_symm_apply y]
    · exact
        (laurentCechCyclesEquivExponentDirectSumCycles
          (ι := ι) (R := R) d (q + 1)).apply_symm_apply y

/--
The exponentwise reindexing induces a linear equivalence on
positive-degree Laurent Čech cohomology.
-/
noncomputable def
    laurentCechPositiveCohomologyEquivExponentDirectSum
    [CommRing R] (d : ℤ) (q : ℕ) :
    ((differential (ι := ι) (R := R) d (q + 1)).ker ⧸
        laurentCechBoundaries (ι := ι) R d q) ≃ₗ[R]
      ExponentDirectSumPositiveCohomology (ι := ι) R d q :=
  Submodule.Quotient.equiv
    (laurentCechBoundaries (ι := ι) R d q)
    (exponentDirectSumBoundaries (ι := ι) R d q)
    (laurentCechCyclesEquivExponentDirectSumCycles
      (ι := ι) (R := R) d (q + 1))
    (laurentCechCyclesEquiv_map_boundaries
      (ι := ι) (R := R) d q)

/-- Degree-zero Laurent Čech cohomology is finite over a Noetherian
coefficient ring. -/
theorem laurentCechDegreeZeroCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) :
    Module.Finite R
      (LaurentCechCycles (ι := ι) R d 0) := by
  letI :
      Module.Finite R
        (ExponentDirectSumCycles (ι := ι) R d 0) :=
    exponentDirectSumDegreeZeroCohomology_finite
      (ι := ι) (R := R) d
  exact Module.Finite.equiv
    (laurentCechCyclesEquivExponentDirectSumCycles
      (ι := ι) (R := R) d 0).symm

/-- Every positive-degree Laurent Čech cohomology module is finite over
a Noetherian coefficient ring. -/
theorem laurentCechPositiveCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((differential (ι := ι) (R := R) d (q + 1)).ker ⧸
        laurentCechBoundaries (ι := ι) R d q) := by
  letI :
      Module.Finite R
        (ExponentDirectSumPositiveCohomology
          (ι := ι) R d q) :=
    exponentDirectSumPositiveCohomology_finite
      (ι := ι) (R := R) d q
  exact Module.Finite.equiv
    (laurentCechPositiveCohomologyEquivExponentDirectSum
      (ι := ι) (R := R) d q).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
