/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistRationalOverChartTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceConditionalFiniteness

/-!
# Coherent cohomology on rational projective space

The two coordinate compatibilities isolated by the projective-space
calculation are now unconditional over `ℚ`, so the projective
cohomology theorem no longer carries seam hypotheses.
-/


open CategoryTheory AlgebraicGeometry TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

noncomputable local instance rationalProjectiveCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
Rationalized coherent cohomology on standard projective space over
`ℚ` is finite-dimensional.
-/
theorem coherentCohomologyFinite_rat
    (d : ℕ)
    (M : (scheme ℚ d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  coherentCohomologyFinite_of_coordinate_seams
    d
    (integerChartCoordinatesIndependent d)
    (integerOverChartCoordinateTransition_rat d)
    M n

/--
The same finiteness result holds on any rational scheme equipped with
a closed projective-space factorization.
-/
theorem coherentCohomologyFinite_projectiveFactorization_rat
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}
    (hproj : IsProjectiveFactorization f)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  coherentCohomologyFinite_of_projectiveFactorization
    coherentCohomologyFinite_rat hproj M n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
