/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechComplexFiniteness

/-!
# Positive-twist vanishing in the projective Laurent Čech complex

For a nonnegative homogeneous degree, an exponent vector cannot be
strictly negative in every variable.  The fixed-exponent contraction
therefore applies to every summand of the Laurent Čech complex in positive
cochain degree.  This proves the algebraic vanishing theorem

`H^q(Čech(𝒪(d))) = 0` for `d ≥ 0` and `q > 0`

over an arbitrary commutative coefficient ring.

This is the twist-level local algebra needed by relative Serre
acyclicity.  It is deliberately independent of a sheaf/Čech comparison.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/--
A homogeneous exponent of nonnegative total degree cannot have full
negative support when there is at least one variable.
-/
lemma negativeSupport_ne_univ_of_nonnegative_degree
    [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d)
    (a : HomogeneousExponent (ι := ι) d) :
    ProjectiveExponent.negativeSupport a.1 ≠
      (Finset.univ : Finset ι) := by
  intro hsupport
  have hnegative :
      ProjectiveExponent.IsStrictlyNegative a.1 :=
    (ProjectiveExponent.isStrictlyNegative_iff_negativeSupport_eq_univ
      a.1).mpr hsupport
  have huniv : (Finset.univ : Finset ι).Nonempty :=
    Finset.univ_nonempty
  have hdegreeNegative :
      ProjectiveExponent.totalDegree a.1 < 0 := by
    rw [ProjectiveExponent.totalDegree]
    simpa using
      (Finset.sum_lt_sum_of_nonempty huniv
        (fun i _ => hnegative i))
  rw [a.2] at hdegreeNegative
  exact (not_lt_of_ge hd) hdegreeNegative

/--
In nonnegative homogeneous degree, every positive spot of every fixed
exponent summand is exact.
-/
theorem exponentDifferential_exact_of_nonnegative_degree
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d)
    (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    Function.Exact
      (exponentDifferential (R := R) a q)
      (exponentDifferential (R := R) a (q + 1)) :=
  exponentDifferential_exact_of_negativeSupport_ne_univ
    (R := R) a q
    (negativeSupport_ne_univ_of_nonnegative_degree hd a)

/--
Every positive-degree cycle in the exponentwise direct sum is a
boundary when the homogeneous degree is nonnegative.
-/
theorem exponentDirectSumCycle_mem_range_of_nonnegative_degree
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ)
    (w : ExponentDirectSumCycles (ι := ι) R d (q + 1)) :
    w.1 ∈
      (exponentDirectSumDifferential
        (ι := ι) (R := R) d q).range := by
  classical
  have hpreimage
      (a : HomogeneousExponent (ι := ι) d) :
      ∃ b : ExponentCochain (ι := ι) R a q,
        exponentDifferential (R := R) a q b = w.1 a := by
    apply
      (exponentDifferential_exact_of_nonnegative_degree
        (R := R) hd a q _).mp
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
Positive-degree cohomology of the exponentwise direct-sum complex
vanishes in nonnegative homogeneous degree.
-/
theorem exponentDirectSumPositiveCohomology_subsingleton
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton
      (ExponentDirectSumPositiveCohomology
        (ι := ι) R d q) := by
  letI :
      AddCommGroup
        (ExponentDirectSumCycles (ι := ι) R d (q + 1)) :=
    Module.addCommMonoidToAddCommGroup R
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply Submodule.eq_top_iff'.mpr
  intro z
  change z.1 ∈
    (exponentDirectSumDifferential
      (ι := ι) (R := R) d q).range
  exact
    exponentDirectSumCycle_mem_range_of_nonnegative_degree
      (ι := ι) (R := R) hd q z

/--
Positive-degree cohomology of the original Laurent Čech complex
vanishes in nonnegative homogeneous degree.
-/
theorem laurentCechPositiveCohomology_subsingleton
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton
      (LaurentCechPositiveCohomology
        (ι := ι) R d q) := by
  letI :
      Subsingleton
        (ExponentDirectSumPositiveCohomology
          (ι := ι) R d q) :=
    exponentDirectSumPositiveCohomology_subsingleton
      (ι := ι) (R := R) hd q
  constructor
  intro x y
  apply
    (laurentCechPositiveCohomologyEquivExponentDirectSum
      (ι := ι) (R := R) d q).injective
  exact Subsingleton.elim _ _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
