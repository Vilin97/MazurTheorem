/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechRawShortComplexFiniteness

/-!
# Finiteness for the extracted Laurent Čech short complex

The raw short-complex finiteness result is transported across the
compiled isomorphism of explicit left-homology objects.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- The explicit left homology of the short complex extracted from the
categorical Laurent complex is finite. -/
theorem laurentCechShortComplexPositiveHomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((laurentCechShortComplex
        (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H) :=
  moduleFiniteOfLinearEquiv
    (laurentCechRawShortComplexHomology_finite
      (ι := ι) (R := R) d q)
    (laurentCechShortComplexRawHomologyLinearEquiv
      (ι := ι) (R := R) d q).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
