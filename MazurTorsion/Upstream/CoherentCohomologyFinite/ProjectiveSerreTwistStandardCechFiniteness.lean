/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechCategoricalFiniteTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistStandardCechComplex

/-!
# Finiteness of the standard-cover Serre-twist Čech homology

The explicit Laurent calculation is transported first to categorical
homology of the Laurent complex and then across the geometric
standard-cover complex isomorphism.
-/


open CategoryTheory

noncomputable section

/-- Explicit transport of module finiteness across a linear equivalence.
Keeping the source finiteness proof explicit avoids fragile typeclass
search through large definitional homology quotients. -/
theorem moduleFinite_of_linearEquiv
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (hM : Module.Finite R M) (e : M ≃ₗ[R] N) :
    Module.Finite R N := by
  letI : Module.Finite R M := hM
  exact Module.Finite.equiv e

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Categorical degree-zero Laurent Čech homology is finite-dimensional. -/
theorem laurentCechDegreeZeroCategoricalHomology_finite
    (m : ℤ) :
    Module.Finite ℚ
      ((laurentCechComplex
        (ι := ι) (R := ℚ) m).homology 0) :=
  moduleFinite_of_linearEquiv
    (laurentCechDegreeZeroCohomology_finite
      (ι := ι) (R := ℚ) m)
    (laurentCechDegreeZeroHomologyLinearEquiv
      (ι := ι) (R := ℚ) m).symm

/-- Every positive categorical Laurent Čech homology object is
finite-dimensional. -/
theorem laurentCechPositiveCategoricalHomology_finite
    (m : ℤ) (q : ℕ) :
    Module.Finite ℚ
      ((laurentCechComplex
        (ι := ι) (R := ℚ) m).homology (q + 1)) :=
  laurentCechPositiveCategoricalHomologyFinite
    (ι := ι) (R := ℚ) m q

/-- Every categorical homology object of the Laurent Čech complex over
`ℚ` is finite-dimensional. -/
theorem laurentCechHomology_finite
    (m : ℤ) (n : ℕ) :
    Module.Finite ℚ
      ((laurentCechComplex
        (ι := ι) (R := ℚ) m).homology n) := by
  cases n with
  | zero =>
      exact laurentCechDegreeZeroCategoricalHomology_finite m
  | succ q =>
      exact laurentCechPositiveCategoricalHomology_finite m q

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

/-- The normalized standard-cover Čech complex of every integer twist
has finite-dimensional categorical homology. -/
theorem standardCoverOIntCechHomology_finite
    (d : ℕ) (m : ℤ) (n : ℕ) :
    Module.Finite ℚ
      ((standardCoverOIntCechComplex d m).homology n) := by
  let e :=
    (HomologicalComplex.homologyFunctor
      (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
        (standardCoverOIntCechComplexIsoLaurent d m)
  let e' :
      (laurentCechComplex
        (ι := Fin (d + 1)) (R := ℚ) m).homology n ≃ₗ[ℚ]
        (standardCoverOIntCechComplex d m).homology n :=
    e.toLinearEquiv.symm
  exact moduleFinite_of_linearEquiv
    (laurentCechHomology_finite
      (ι := Fin (d + 1)) m n) e'

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
