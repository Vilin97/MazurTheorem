/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedGeneratorFiniteSum
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistFiniteSumCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProperCohomologyDevissage

/-!
# Twisted-free generation on projective space over a base ring

Corrected generators from the standard affine charts assemble into an
epimorphism from a finite sum of integer Serre twists.  The construction
is uniform over the coefficient ring; its only remaining geometric input
is the isolated negative-twist coordinate transition.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

/-- A module on projective space over `R` which is isomorphic to a finite
sum of integer Serre twists. -/
def IsBaseFiniteIntegerTwistSum
    (R : Type) [CommRing R] (d : ℕ)
    (E : (scheme R d).Modules) : Prop :=
  ∃ (ι : Type) (hι : Fintype ι) (degree : ι → ℤ),
    Nonempty
      (E ≅
        @finiteIntegerSum R inferInstance d ι hι degree)

/-- Corrected standard-chart generators give a finite twisted-free
presentation over any commutative base ring. -/
theorem exists_baseFiniteIntegerTwistSum_epi
    (R : Type) [CommRing R]
    (d : ℕ)
    (hcoordinate :
      ∀ N : ℕ,
        IntegerOverChartCoordinateTransition R d N)
    (Y : (scheme R d).Modules)
    [Y.IsFiniteType] [Y.IsQuasicoherent] :
    ∃ (E : (scheme R d).Modules) (e : E ⟶ Y),
      Epi e ∧
        CoherentModule E ∧
        IsBaseFiniteIntegerTwistSum R d E := by
  classical
  let G :
      ∀ j : Fin (d + 1), ChartGenerators R d Y j :=
    fun j => Classical.choice (ChartGenerators.exists R d Y j)
  let E₀ :
      ∀ j : Fin (d + 1),
        ChartGeneratorExtensions R d (G j) :=
    fun j =>
      Classical.choice (ChartGeneratorExtensions.exists R d (G j))
  let C :
      ∀ j : Fin (d + 1),
        CorrectedChartGeneratorExtensions R d (E₀ j) :=
    fun j =>
      Classical.choice
        (CorrectedChartGeneratorExtensions.exists_unconditionally
          R d (E₀ j))
  let degree :
      (Σ j : Fin (d + 1), Fin (G j).count) → ℤ :=
    fun p => -((C p.1).totalExponent : ℤ)
  let source : (scheme R d).Modules :=
    finiteIntegerSum R d degree
  let e : source ⟶ Y :=
    finiteIntegerSumDesc R d degree
      (fun p =>
        (C p.1).correctedGlobalHom
          p.2 (hcoordinate (C p.1).totalExponent))
  refine ⟨source, e, ?_, ?_, ?_⟩
  · exact
      CorrectedChartGeneratorExtensions.correctedFiniteIntegerSumDesc_epi
        G E₀ C (fun j => hcoordinate (C j).totalExponent)
  · exact
      ⟨finiteIntegerSum_isFiniteType R d degree,
        finiteIntegerSum_isQuasicoherent R d degree⟩
  · exact
      ⟨Σ j : Fin (d + 1), Fin (G j).count,
        inferInstance, degree, ⟨Iso.refl _⟩⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
