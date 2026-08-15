/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechRawShortComplex

/-!
# Finiteness of the raw Laurent Čech short-complex homology

The raw three-term complex exposes the same cochain types used by the
explicit exponent calculation.  Thus its left homology can receive the
kernel-modulo-boundary finiteness theorem without a large dependent
carrier conversion.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

attribute [local instance 2000] laurentCechCyclesAddCommGroup

/--
The explicit positive quotient stated using the exact `ModuleCat.ofHom`
carrier expressions used by the raw short complex.
-/
theorem laurentCechPositiveModuleCarrierCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((ModuleCat.ofHom
          (differential
            (ι := ι) (R := R) d (q + 1))).hom.ker ⧸
        Submodule.comap
          (ModuleCat.ofHom
            (differential
              (ι := ι) (R := R) d (q + 1))).hom.ker.subtype
          (ModuleCat.ofHom
            (differential
              (ι := ι) (R := R) d q)).hom.range) :=
  laurentCechPositiveCohomology_finite
    (ι := ι) (R := R) d q

/-- Positive left homology of the raw Laurent Čech short complex is
finite over a Noetherian coefficient ring. -/
theorem laurentCechRawShortComplexHomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((laurentCechRawShortComplex
        (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H) :=
  shortComplexHomologyFiniteOfEqSubmodule
    (laurentCechRawShortComplex (ι := ι) (R := R) d q)
    (ModuleCat.ofHom
      (differential (ι := ι) (R := R) d q)).hom
    (ModuleCat.ofHom
      (differential (ι := ι) (R := R) d (q + 1))).hom
    rfl
    rfl
    (Submodule.comap
      (ModuleCat.ofHom
        (differential
          (ι := ι) (R := R) d (q + 1))).hom.ker.subtype
      (ModuleCat.ofHom
        (differential
          (ι := ι) (R := R) d q)).hom.range)
    rfl
    (laurentCechPositiveModuleCarrierCohomology_finite
      (ι := ι) (R := R) d q)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
