/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedGeneratorFiniteSum
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistFreeSheafExtAcyclic
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceCohomologyDevissage

/-!
# Coherent cohomology on projective space from coordinate seams

This file assembles the two completed halves of the projective-space
argument.  Corrected standard-chart generators produce an epimorphism
from a finite sum of integer twists, while the normalized standard-cover
resolution proves finite cohomology for each such twist.

The capstone is conditional only on the two explicit coordinate
compatibility statements for integer Serre twists.
-/

open CategoryTheory AlgebraicGeometry TensorProduct


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

noncomputable local instance conditionalCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Corrected generators on all standard charts give a finite
integer-twist presentation, assuming the negative-twist coordinate
transition used to glue their local maps. -/
theorem exists_finiteIntegerTwistSum_epi
    (d : ℕ)
    (hcoordinate :
      ∀ N : ℕ,
        IntegerOverChartCoordinateTransition ℚ d N)
    (Y : (scheme ℚ d).Modules)
    [Y.IsFiniteType] [Y.IsQuasicoherent] :
    ∃ (E : (scheme ℚ d).Modules) (e : E ⟶ Y),
      Epi e ∧
        CoherentModule E ∧
        IsFiniteIntegerTwistSum d E := by
  classical
  let G :
      ∀ j : Fin (d + 1), ChartGenerators ℚ d Y j :=
    fun j => Classical.choice (ChartGenerators.exists ℚ d Y j)
  let E₀ :
      ∀ j : Fin (d + 1),
        ChartGeneratorExtensions ℚ d (G j) :=
    fun j =>
      Classical.choice (ChartGeneratorExtensions.exists ℚ d (G j))
  let C :
      ∀ j : Fin (d + 1),
        CorrectedChartGeneratorExtensions ℚ d (E₀ j) :=
    fun j =>
      Classical.choice
        (CorrectedChartGeneratorExtensions.exists_unconditionally
          ℚ d (E₀ j))
  let degree :
      (Σ j : Fin (d + 1), Fin (G j).count) → ℤ :=
    fun p => -((C p.1).totalExponent : ℤ)
  let source : (scheme ℚ d).Modules :=
    finiteIntegerSum ℚ d degree
  let e : source ⟶ Y :=
    finiteIntegerSumDesc ℚ d degree
      (fun p =>
        (C p.1).correctedGlobalHom
          p.2 (hcoordinate (C p.1).totalExponent))
  refine ⟨source, e, ?_, ?_, ?_⟩
  · exact
      CorrectedChartGeneratorExtensions.correctedFiniteIntegerSumDesc_epi
        G E₀ C (fun j => hcoordinate (C j).totalExponent)
  · exact
      ⟨finiteIntegerSum_isFiniteType ℚ d degree,
        finiteIntegerSum_isQuasicoherent ℚ d degree⟩
  · exact
      ⟨Σ j : Fin (d + 1), Fin (G j).count,
        inferInstance, degree, ⟨Iso.refl _⟩⟩

/-- Coherent cohomology on rational projective space is finite once the
integer-twist Laurent chart coordinates and the negative-twist gluing
coordinates satisfy their isolated compatibility statements. -/
theorem coherentCohomologyFinite_of_coordinate_seams
    (d : ℕ)
    (hchart :
      ∀ m : ℤ, IntegerChartCoordinatesIndependent d m)
    (hcoordinate :
      ∀ N : ℕ,
        IntegerOverChartCoordinateTransition ℚ d N)
    (M : (scheme ℚ d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  apply coherentCohomologyFinite_of_twists_and_generation d
  · intro m q
    exact rationalizedOIntSheafH_finite d m (hchart m) q
  · intro Y _ _
    exact exists_finiteIntegerTwistSum_epi d hcoordinate Y

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
