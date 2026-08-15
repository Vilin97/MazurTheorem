/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechFiniteness
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Laurent Čech cohomology over a Noetherian coefficient ring

The exponentwise Laurent calculation is not inherently restricted to a
field.  Over a Noetherian coefficient ring, every fixed-exponent cochain
module is finite, its cycle submodule is finite, and its homology quotient
is finite.  Since only finitely many endpoint exponents can contribute,
their direct sum is finite as well.

This is the commutative-algebra finiteness input needed by the relative
projective direct-image argument.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- Cycles modulo those boundaries which lie in the cycle submodule, over
an arbitrary commutative coefficient ring. -/
abbrev ModuleHomology
    (R : Type*) [CommRing R]
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :=
  g.ker ⧸ Submodule.comap g.ker.subtype f.range

/-- The algebraic cohomology of one exponent summand over a commutative
ring. -/
abbrev ExponentModuleCohomology
    (R : Type*) [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d) :
    ℕ → Type _
  | 0 =>
      (exponentDifferential (R := R) a 0).ker
  | q + 1 =>
      ModuleHomology R
        (exponentDifferential (R := R) a q)
        (exponentDifferential (R := R) a (q + 1))

noncomputable instance exponentModuleCohomologyAddCommGroup
    [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    AddCommGroup (ExponentModuleCohomology (ι := ι) R a q) := by
  cases q <;> infer_instance

noncomputable instance exponentModuleCohomologyModule
    [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    Module R (ExponentModuleCohomology (ι := ι) R a q) := by
  cases q <;> infer_instance

/--
Over a Noetherian ring, each fixed-exponent cohomology module is finite.
-/
theorem exponentModuleCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    Module.Finite R
      (ExponentModuleCohomology (ι := ι) R a q) := by
  cases q <;> infer_instance

/-- The direct sum of the fixed-exponent cohomology modules at the two
possible endpoint supports. -/
abbrev EndpointExponentModuleCohomology
    (R : Type*) [CommRing R]
    (d : ℤ) (q : ℕ) :=
  Π₀ a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d},
    ExponentModuleCohomology (ι := ι) R a.1 q

/--
The full endpoint carrier is a finite module over a Noetherian coefficient
ring.
-/
theorem endpointExponentModuleCohomology_finite
    [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R
      (EndpointExponentModuleCohomology (ι := ι) R d q) := by
  letI :
      Fintype {a : HomogeneousExponent (ι := ι) d //
        a ∈ CohomologyExponentSet (ι := ι) d} :=
    (cohomologyExponentSet_finite (ι := ι) d).fintype
  letI (a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d}) :
      Module.Finite R
        (ExponentModuleCohomology (ι := ι) R a.1 q) :=
    exponentModuleCohomology_finite
      (ι := ι) a.1 q
  infer_instance

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
