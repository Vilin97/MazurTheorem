/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechCategoricalHomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechVanishing

/-!
# Categorical positive-twist vanishing for the Laurent Čech complex

The exponentwise contraction proves that the explicit positive-degree
Laurent Čech quotient vanishes in every nonnegative homogeneous degree.
This file transports that result to the categorical homology object of
the Laurent Čech complex.

The result is uniform over an arbitrary commutative coefficient ring.  It
is the algebraic vanishing input for relative projective acyclicity over
Noetherian affine base charts.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/--
Positive categorical Laurent Čech homology vanishes in nonnegative
homogeneous degree.
-/
theorem laurentCechPositiveCategoricalHomology_subsingleton
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton
      ((laurentCechComplex
        (ι := ι) (R := R) d).homology (q + 1)) := by
  have hvanish :
      Subsingleton
        (LaurentCechPositiveCohomology
          (ι := ι) R d q) :=
    laurentCechPositiveCohomology_subsingleton
      (ι := ι) (R := R) hd q
  let e :=
    laurentCechPositiveNamedHomologyLinearEquiv
      (ι := ι) (R := R) d q
  constructor
  intro x y
  apply e.injective
  exact hvanish.elim (e x) (e y)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
