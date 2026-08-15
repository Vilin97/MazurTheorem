/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechCategoricalFiniteTransport

/-!
# Total finiteness of categorical Laurent Čech homology

The positive-degree categorical comparison was established separately
from the degree-zero kernel comparison.  This file combines them into
one degree-uniform theorem over a Noetherian coefficient ring.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- Degree-zero categorical Laurent Čech homology is finite over a
Noetherian coefficient ring. -/
theorem laurentCechDegreeZeroCategoricalHomologyFinite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) :
    Module.Finite R
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology 0) :=
  moduleFiniteOfLinearEquiv
    (laurentCechDegreeZeroCohomology_finite
      (ι := ι) (R := R) d)
    (laurentCechDegreeZeroHomologyLinearEquiv
      (ι := ι) (R := R) d).symm

/-- Every categorical Laurent Čech homology module is finite over a
Noetherian coefficient ring. -/
theorem laurentCechCategoricalHomologyFinite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (n : ℕ) :
    Module.Finite R
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology n) := by
  cases n with
  | zero =>
      exact
        laurentCechDegreeZeroCategoricalHomologyFinite
          (ι := ι) (R := R) d
  | succ q =>
      exact
        laurentCechPositiveCategoricalHomologyFinite
          (ι := ι) (R := R) d q

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
