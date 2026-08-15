/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechHomology

/-!
# Finite exceptional exponents in the projective Laurent Čech complex

The contracting homotopy kills every fixed-exponent summand except at the
two endpoints:

* empty negative support, equivalently an everywhere nonnegative exponent;
* full negative support, equivalently an everywhere strictly negative
  exponent.

At fixed homogeneous degree both sets are finite.  This file packages that
classification and records a finite-dimensional carrier containing every
possible exponentwise cohomology contribution.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open scoped BigOperators

namespace ProjectiveLaurentCech

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι]

/--
The fixed-degree exponents which can contribute to Laurent Čech
cohomology: their negative support is empty or full.
-/
def CohomologyExponentSet (d : ℤ) :
    Set (HomogeneousExponent (ι := ι) d) :=
  {a |
    ProjectiveExponent.negativeSupport a.1 = ∅ ∨
      ProjectiveExponent.negativeSupport a.1 =
        (Finset.univ : Finset ι)}

omit [LinearOrder ι] in
/-- There are only finitely many potentially contributing exponents. -/
theorem cohomologyExponentSet_finite (d : ℤ) :
    (CohomologyExponentSet (ι := ι) d).Finite := by
  let f : HomogeneousExponent (ι := ι) d →
      ProjectiveExponent ι :=
    fun a => a.1
  have hraw :
      (ProjectiveExponent.nonnegativeOfDegree (ι := ι) d ∪
        ProjectiveExponent.strictlyNegativeOfDegree (ι := ι) d).Finite :=
    (ProjectiveExponent.nonnegativeOfDegree_finite
      (ι := ι) d).union
      (ProjectiveExponent.strictlyNegativeOfDegree_finite
        (ι := ι) d)
  have hpreimage :
      (f ⁻¹'
        (ProjectiveExponent.nonnegativeOfDegree (ι := ι) d ∪
          ProjectiveExponent.strictlyNegativeOfDegree
            (ι := ι) d)).Finite :=
    hraw.preimage
      (Set.injOn_of_injective Subtype.val_injective)
  refine hpreimage.subset ?_
  intro a ha
  rcases ha with hempty | hfull
  · exact Or.inl
      ⟨(ProjectiveExponent.isNonnegative_iff_negativeSupport_eq_empty
          a.1).mpr hempty,
        a.2⟩
  · exact Or.inr
      ⟨(ProjectiveExponent.isStrictlyNegative_iff_negativeSupport_eq_univ
          a.1).mpr hfull,
        a.2⟩

/--
Outside the finite endpoint set, degree-zero cohomology vanishes and every
positive-degree spot is exact.
-/
theorem exponentCohomology_vanishes_outside_set [CommRing κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (ha : a ∉ CohomologyExponentSet (ι := ι) d) :
    Function.Injective
        (exponentDifferential (R := κ) a 0) ∧
      ∀ q : ℕ,
        Function.Exact
          (exponentDifferential (R := κ) a q)
          (exponentDifferential (R := κ) a (q + 1)) := by
  have hnonempty :
      (ProjectiveExponent.negativeSupport a.1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact ha (Or.inl hempty)
  have hneuniv :
      ProjectiveExponent.negativeSupport a.1 ≠
        (Finset.univ : Finset ι) := by
    intro hfull
    exact ha (Or.inr hfull)
  exact
    ⟨exponentDifferential_degreeZero_injective_of_support_nonempty_ne_univ
        (R := κ) a hnonempty hneuniv,
      fun q =>
        exponentDifferential_exact_of_negativeSupport_ne_univ
          (R := κ) a q hneuniv⟩

omit [LinearOrder ι] in
/-- Every individual fixed-exponent cochain space is finite-dimensional. -/
theorem exponentCochain_finiteDimensional [Field κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    FiniteDimensional κ
      (ExponentCochain (ι := ι) κ a q) := by
  infer_instance

/--
The direct sum of all fixed-exponent cochains which can possibly
contribute to cohomology.
-/
abbrev CohomologyEndpointCochain (κ : Type*) [Semiring κ]
    (d : ℤ) (q : ℕ) :=
  Π₀ a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d},
    ExponentCochain (ι := ι) κ a.1 q

omit [LinearOrder ι] in
/--
At every Čech degree, the carrier of all possible exponentwise
cohomology contributions is finite-dimensional.
-/
theorem cohomologyEndpointCochain_finiteDimensional [Field κ]
    (d : ℤ) (q : ℕ) :
    FiniteDimensional κ
      (CohomologyEndpointCochain (ι := ι) κ d q) := by
  letI :
      Fintype {a : HomogeneousExponent (ι := ι) d //
        a ∈ CohomologyExponentSet (ι := ι) d} :=
    (cohomologyExponentSet_finite (ι := ι) d).fintype
  infer_instance

/-- Cycles modulo those boundaries which lie in the cycle subspace. -/
abbrev LinearHomology
    (κ : Type*) [Field κ]
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module κ A] [Module κ B] [Module κ C]
    (f : A →ₗ[κ] B) (g : B →ₗ[κ] C) :=
  g.ker ⧸ Submodule.comap g.ker.subtype f.range

/--
The algebraic cohomology of one exponent summand.  In degree zero this is
the kernel of the first differential.  In positive degree it is cycles
modulo boundaries.
-/
abbrev ExponentCohomology (κ : Type*) [Field κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d) :
    ℕ → Type _
  | 0 =>
      (exponentDifferential (R := κ) a 0).ker
  | q + 1 =>
      LinearHomology κ
        (exponentDifferential (R := κ) a q)
        (exponentDifferential (R := κ) a (q + 1))

noncomputable instance exponentCohomologyAddCommGroup
    [Field κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    AddCommGroup (ExponentCohomology (ι := ι) κ a q) := by
  cases q <;> infer_instance

noncomputable instance exponentCohomologyModule
    [Field κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    Module κ (ExponentCohomology (ι := ι) κ a q) := by
  cases q <;> infer_instance

/--
Each individual exponentwise cohomology group is finite-dimensional.
-/
theorem exponentCohomology_finiteDimensional [Field κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    FiniteDimensional κ
      (ExponentCohomology (ι := ι) κ a q) := by
  cases q <;> infer_instance

/--
The direct sum of every exponentwise cohomology group which can be
nonzero.  The contraction theorem proves that all omitted summands vanish.
-/
abbrev EndpointExponentCohomology (κ : Type*) [Field κ]
    (d : ℤ) (q : ℕ) :=
  Π₀ a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d},
    ExponentCohomology (ι := ι) κ a.1 q

/--
The exponentwise Laurent Čech cohomology carrier is finite-dimensional in
every degree.
-/
theorem endpointExponentCohomology_finiteDimensional [Field κ]
    (d : ℤ) (q : ℕ) :
    FiniteDimensional κ
      (EndpointExponentCohomology (ι := ι) κ d q) := by
  letI :
      Fintype {a : HomogeneousExponent (ι := ι) d //
        a ∈ CohomologyExponentSet (ι := ι) d} :=
    (cohomologyExponentSet_finite (ι := ι) d).fintype
  letI (a : {a : HomogeneousExponent (ι := ι) d //
      a ∈ CohomologyExponentSet (ι := ι) d}) :
      FiniteDimensional κ
        (ExponentCohomology (ι := ι) κ a.1 q) :=
    exponentCohomology_finiteDimensional
      (ι := ι) a.1 q
  infer_instance

/--
Every exponentwise cohomology group outside the finite endpoint set is
zero.
-/
theorem exponentCohomology_subsingleton_outside_set [Field κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (ha : a ∉ CohomologyExponentSet (ι := ι) d)
    (q : ℕ) :
    Subsingleton (ExponentCohomology (ι := ι) κ a q) := by
  have hvanish :=
    exponentCohomology_vanishes_outside_set
      (κ := κ) a ha
  cases q with
  | zero =>
      constructor
      intro x y
      apply Subtype.ext
      apply hvanish.1
      exact x.2.trans y.2.symm
  | succ q =>
      apply Submodule.Quotient.subsingleton_iff.mpr
      apply Submodule.eq_top_iff'.mpr
      intro z
      change z.1 ∈
        (exponentDifferential (R := κ) a q).range
      exact (hvanish.2 q z.1).mp z.2

omit [LinearOrder ι] in
/--
For a strictly negative exponent, any admissible simplex is the full
simplex.  In particular the fixed-exponent basis has at most one element.
-/
lemma simplexForExponent_subsingleton_of_strictlyNegative
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    (ha : ProjectiveExponent.IsStrictlyNegative a.1)
    (q : ℕ) :
    Subsingleton (SimplexForExponent (ι := ι) a q) := by
  constructor
  intro I J
  apply Subtype.ext
  apply Subtype.ext
  calc
    I.1.1 = Finset.univ :=
      ProjectiveExponent.eq_univ_of_isStrictlyNegative_of_admissibleOn
        ha I.2
    _ = J.1.1 :=
      (ProjectiveExponent.eq_univ_of_isStrictlyNegative_of_admissibleOn
        ha J.2).symm

/-- The unique full simplex in its Čech degree. -/
def fullSimplexForExponent
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ}
    (hcard : Fintype.card ι = q + 1) :
    SimplexForExponent (ι := ι) a q :=
  ⟨⟨Finset.univ, by simpa using hcard⟩,
    ProjectiveExponent.admissibleOn_univ a.1⟩

omit [LinearOrder ι] in
/--
A strictly negative exponent has no cochains outside the degree of the
full simplex.
-/
lemma exponentCochain_eq_zero_of_strictlyNegative_of_card_ne
    [Semiring κ]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    (ha : ProjectiveExponent.IsStrictlyNegative a.1)
    {q : ℕ} (hcard : Fintype.card ι ≠ q + 1)
    (c : ExponentCochain (ι := ι) κ a q) :
    c = 0 := by
  ext I
  have hIuniv : I.1.1 = Finset.univ :=
    ProjectiveExponent.eq_univ_of_isStrictlyNegative_of_admissibleOn
      ha I.2
  have hcard' : Fintype.card ι = q + 1 := by
    simpa [hIuniv] using I.1.2
  exact (hcard hcard').elim

/--
In the full-simplex degree, a strictly negative fixed-exponent cochain
space is one-dimensional.
-/
noncomputable def strictlyNegativeCochainEquiv
    [Field κ]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    (ha : ProjectiveExponent.IsStrictlyNegative a.1)
    {q : ℕ} (hcard : Fintype.card ι = q + 1) :
    ExponentCochain (ι := ι) κ a q ≃ₗ[κ] κ := by
  let I := fullSimplexForExponent (a := a) hcard
  letI : Subsingleton (SimplexForExponent (ι := ι) a q) :=
    simplexForExponent_subsingleton_of_strictlyNegative ha q
  exact Finsupp.uniqueLinearEquiv κ κ I

/--
Every fixed-exponent differential for a strictly negative exponent is
zero: the only nonzero cochain space is the full-simplex degree.
-/
theorem exponentDifferential_eq_zero_of_strictlyNegative
    [CommRing κ]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (ha : ProjectiveExponent.IsStrictlyNegative a.1)
    (q : ℕ) :
    exponentDifferential (R := κ) a q = 0 := by
  by_cases hcard : Fintype.card ι = q + 1
  · have hnext : Fintype.card ι ≠ q + 1 + 1 := by
      omega
    apply LinearMap.ext
    intro c
    exact exponentCochain_eq_zero_of_strictlyNegative_of_card_ne
      ha hnext _
  · apply LinearMap.ext
    intro c
    rw [exponentCochain_eq_zero_of_strictlyNegative_of_card_ne
      ha hcard c, map_zero]
    rfl

end ProjectiveLaurentCech

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
