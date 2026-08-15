/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechVanishing
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat


/-!
# Additive positive-twist vanishing for the Laurent Čech complex

For relative applications, the geometric Laurent-coordinate comparison is
available additively over an arbitrary commutative base ring even before it
is packaged as a linear comparison over that base.  We therefore regard all
cochain groups as canonical `ℤ`-modules.

The underlying functions of the Laurent differentials are unchanged.  The
explicit monomial contraction consequently proves exactness, and hence
vanishing of categorical homology, for this additive Laurent complex.
-/

open CategoryTheory Limits


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/--
The two consecutive Laurent differentials are exact in every positive
cochain degree when the homogeneous degree is nonnegative.
-/
theorem laurentCechDifferential_exact_of_nonnegative_degree
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    Function.Exact
      (differential (ι := ι) (R := R) d q)
      (differential (ι := ι) (R := R) d (q + 1)) := by
  intro x
  constructor
  · intro hx
    let z : LaurentCechCycles (ι := ι) R d (q + 1) :=
      ⟨x, hx⟩
    have hvanish :
        Subsingleton
          (LaurentCechPositiveCohomology
            (ι := ι) R d q) :=
      laurentCechPositiveCohomology_subsingleton
        (ι := ι) (R := R) hd q
    have hz :
        (Submodule.Quotient.mk z :
          LaurentCechPositiveCohomology
            (ι := ι) R d q) = 0 :=
      hvanish.elim _ _
    rw [Submodule.Quotient.mk_eq_zero
      (laurentCechBoundaries (ι := ι) R d q)] at hz
    exact hz
  · rintro ⟨y, rfl⟩
    exact differential_differential
      (ι := ι) (R := R) d q y

/-- A Laurent differential regarded only as a `ℤ`-linear map. -/
noncomputable def additiveDifferential
    [CommRing R] (d : ℤ) (q : ℕ) :
    Cochain (ι := ι) R d q →ₗ[ℤ]
      Cochain (ι := ι) R d (q + 1) :=
  (differential
    (ι := ι) (R := R) d q).toAddMonoidHom.toIntLinearMap

@[simp]
lemma additiveDifferential_apply
    [CommRing R] (d : ℤ) (q : ℕ)
    (x : Cochain (ι := ι) R d q) :
    additiveDifferential (ι := ι) (R := R) d q x =
      differential (ι := ι) (R := R) d q x :=
  rfl

/-- The Laurent Čech complex in the additive (`ℤ`-linear) category. -/
noncomputable def additiveLaurentCechComplex
    [CommRing R] (d : ℤ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of ℤ (Cochain (ι := ι) R d q))
    (fun q => ModuleCat.ofHom
      (additiveDifferential (ι := ι) (R := R) d q))
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact differential_differential
        (ι := ι) (R := R) d q x)

@[simp]
lemma additiveLaurentCechComplex_d
    [CommRing R] (d : ℤ) (q : ℕ) :
    (additiveLaurentCechComplex
      (ι := ι) (R := R) d).d q (q + 1) =
      ModuleCat.ofHom
        (additiveDifferential
          (ι := ι) (R := R) d q) := by
  simp only [additiveLaurentCechComplex,
    CochainComplex.of_d]

/--
The additive Laurent Čech complex is exact in every positive cochain
degree for a nonnegative twist.
-/
theorem additiveLaurentCechComplex_exactAt_succ
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    (additiveLaurentCechComplex
      (ι := ι) (R := R) d).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (additiveLaurentCechComplex
      (ι := ι) (R := R) d)
    q (q + 1) ((q + 1) + 1) (by simp) (by simp)]
  apply ModuleCat.shortComplex_exact
  dsimp only [HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g]
  change
    Function.Exact
      ((additiveLaurentCechComplex
        (ι := ι) (R := R) d).d q (q + 1))
      ((additiveLaurentCechComplex
        (ι := ι) (R := R) d).d
          (q + 1) ((q + 1) + 1))
  rw [additiveLaurentCechComplex_d,
    additiveLaurentCechComplex_d]
  exact
    laurentCechDifferential_exact_of_nonnegative_degree
      (ι := ι) (R := R) hd q

/--
Every positive homology object of the additive Laurent Čech complex
vanishes for a nonnegative twist.
-/
theorem additiveLaurentCechPositiveHomology_isZero
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    IsZero
      ((additiveLaurentCechComplex
        (ι := ι) (R := R) d).homology (q + 1)) :=
  (additiveLaurentCechComplex_exactAt_succ
    (ι := ι) (R := R) hd q).isZero_homology

/--
Carrier form of additive Laurent positive-degree vanishing.
-/
theorem additiveLaurentCechPositiveHomology_subsingleton
    [CommRing R] [Nonempty ι]
    {d : ℤ} (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton
      ((additiveLaurentCechComplex
        (ι := ι) (R := R) d).homology (q + 1)) :=
  ModuleCat.subsingleton_of_isZero
    (additiveLaurentCechPositiveHomology_isZero
      (ι := ι) (R := R) hd q)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
