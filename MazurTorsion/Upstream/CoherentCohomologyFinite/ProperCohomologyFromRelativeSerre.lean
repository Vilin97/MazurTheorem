/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowAssembly

/-!
# Proper coherent cohomology from relative Serre inputs

This module isolates the final mathematical assembly from the concrete
construction of the two relative-projective functoriality inputs.
-/


open CategoryTheory AlgebraicGeometry TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

noncomputable local instance properRelativeSerreSheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

variable {X : Scheme.{0}}

/--
Relative Serre affine comparisons and projective-coordinate maps imply
finite-dimensional rationalized coherent cohomology on a proper scheme.
-/
theorem coherentCohomologyFinite_of_relativeSerreInputs
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (hserre : HasRelativeSerreAffineComparisons)
    (hcoordinate : HasRelativeProjectiveCoordinateMaps)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  coherentCohomologyFinite_of_canonicalSupportChowAcyclicExtensions
    f
    (hasCanonicalSupportChowAcyclicExtensions_of_relativeSerreInputs
      f hserre hcoordinate)
    M n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
