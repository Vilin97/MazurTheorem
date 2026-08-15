/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechShortComplexFiniteness

/-!
# Transporting Laurent Čech finiteness to categorical homology

The explicit quotient, its lifted finiteness witness, and its
categorical comparison have each been checked in preceding modules.
This final layer only transports finite generation across that compiled
linear equivalence.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- Positive categorical Laurent Čech homology is finite over a
Noetherian coefficient ring. -/
theorem laurentCechPositiveCategoricalHomologyFinite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology (q + 1)) :=
  moduleFiniteOfLinearEquiv
    (laurentCechShortComplexPositiveHomology_finite
      (ι := ι) (R := R) d q)
    (laurentCechHomologyShortComplexLinearEquiv
      (ι := ι) (R := R) d q).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
