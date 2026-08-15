/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteCoproductCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveEmbeddingReduction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorization
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistFiniteSumCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProperCohomologyDevissage

/-!
# Coherent cohomology on projective space from Serre twists

This file packages the formal dévissage step in the projective-space
argument.  Once finite-dimensionality is known for every integer Serre
twist, and every coherent module is a quotient of a finite sum of such
twists, bounded descending induction gives the result for every coherent
module.
-/


open CategoryTheory Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

noncomputable local instance projectiveDevissageCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- A module on projective space which is isomorphic to a finite sum of
integer Serre twists. -/
def IsFiniteIntegerTwistSum (d : ℕ)
    (E : (scheme ℚ d).Modules) : Prop :=
  ∃ (ι : Type) (hι : Fintype ι) (degree : ι → ℤ),
    Nonempty
      (E ≅
        @finiteIntegerSum ℚ inferInstance d ι hι degree)

/--
Finite-dimensionality of the cohomology of every integer twist implies
finite-dimensionality for every finite sum of integer twists.
-/
theorem rationalizedSheafH_finite_of_isFiniteIntegerTwistSum
    (d : ℕ)
    (htwist :
      ∀ (m : ℤ) (n : ℕ),
        Module.Finite ℚ
          (ℚ ⊗[ℤ] (OInt ℚ d m).sheaf.H n))
    (E : (scheme ℚ d).Modules)
    (hE : IsFiniteIntegerTwistSum d E)
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] E.sheaf.H n) := by
  obtain ⟨ι, hι, degree, ⟨e⟩⟩ := hE
  letI : Fintype ι := hι
  have hsum :
      Module.Finite ℚ
        (ℚ ⊗[ℤ] (finiteIntegerSum ℚ d degree).sheaf.H n) :=
    rationalized_moduleSheafH_finite_coproduct
      (fun i => OInt ℚ d (degree i)) n
      (fun i => htwist (degree i) n)
  exact
    (rationalized_moduleSheafH_finite_congr e n).mpr hsum

/--
The projective-space coherent-cohomology theorem, reduced to its two
geometric inputs: cohomology finiteness for twists and finite twisted-free
generation of coherent modules.
-/
theorem coherentCohomologyFinite_of_twists_and_generation
    (d : ℕ)
    (htwist :
      ∀ (m : ℤ) (n : ℕ),
        Module.Finite ℚ
          (ℚ ⊗[ℤ] (OInt ℚ d m).sheaf.H n))
    (hgeneration :
      ∀ (Y : (scheme ℚ d).Modules)
        [Y.IsFiniteType] [Y.IsQuasicoherent],
        ∃ (E : (scheme ℚ d).Modules) (e : E ⟶ Y),
          Epi e ∧
            CoherentModule E ∧
            IsFiniteIntegerTwistSum d E)
    (M : (scheme ℚ d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  apply
    proper_coherent_cohomology_finite_of_presentations
      (toSpec ℚ d)
      (IsFiniteIntegerTwistSum d)
      hgeneration
  · intro E hE q
    exact
      rationalizedSheafH_finite_of_isFiniteIntegerTwistSum
        d htwist E hE q

/--
Once coherent cohomology is finite on every standard projective space,
the same conclusion holds for a scheme equipped with a concrete closed
projective-space factorization.
-/
theorem coherentCohomologyFinite_of_projectiveFactorization
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (hprojectiveSpace :
      ∀ (d : ℕ) (N : (scheme ℚ d).Modules)
        [N.IsFiniteType] [N.IsQuasicoherent] (q : ℕ),
        Module.Finite ℚ (ℚ ⊗[ℤ] N.sheaf.H q))
    (hproj : IsProjectiveFactorization f)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  obtain ⟨d, N, hNfp, hNqc, hcohomology⟩ :=
    exists_projectiveSpace_coherentModule_of_projectiveFactorization
      (f := f) (M := M) hproj
  letI : N.IsFinitePresentation := hNfp
  letI : N.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation N
  letI : N.IsQuasicoherent := hNqc
  exact
    (hcohomology n).mpr
      (hprojectiveSpace d N n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
