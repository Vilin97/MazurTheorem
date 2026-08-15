/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechComplexFiniteness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Laurent Čech differential as a `CochainComplex`

The combinatorial development uses explicit linear maps because that
presentation is convenient for exponentwise calculations.  This file
packages the same data in Mathlib's categorical homological-complex API,
which is the interface used by acyclic-resolution comparison.
-/

open CategoryTheory


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- The explicit Laurent Čech cochains and differential, bundled as a
cochain complex of modules. -/
noncomputable def laurentCechComplex
    [CommRing R] (d : ℤ) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R (Cochain (ι := ι) R d q))
    (fun q => ModuleCat.ofHom (differential (ι := ι) (R := R) d q))
    (fun q => by
      apply ModuleCat.hom_ext
      exact differential_comp (ι := ι) (R := R) d q)

@[simp]
lemma laurentCechComplex_X
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechComplex (ι := ι) (R := R) d).X q =
      ModuleCat.of R (Cochain (ι := ι) R d q) :=
  rfl

@[simp]
lemma laurentCechComplex_d
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechComplex (ι := ι) (R := R) d).d q (q + 1) =
      ModuleCat.ofHom (differential (ι := ι) (R := R) d q) := by
  simp [laurentCechComplex, CochainComplex.of_d]

@[simp]
lemma laurentCechComplex_d_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (c : Cochain (ι := ι) R d q) :
    (laurentCechComplex (ι := ι) (R := R) d).d q (q + 1) c =
      differential (ι := ι) (R := R) d q c := by
  rw [laurentCechComplex_d]
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
