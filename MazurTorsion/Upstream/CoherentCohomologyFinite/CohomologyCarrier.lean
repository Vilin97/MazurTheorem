/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtChangeOfScalars

/-!
# The rational and abelian carriers for coherent cohomology

This file specializes the sheaf-Ext change-of-scalars equivalence to the
rational sheaf underlying a scheme module.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.CohomologyCarrier

open CoefficientRationalization

noncomputable local instance carrierCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

variable {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of ℚ))]

/--
Finite-dimensionality of cohomology computed in rational-module sheaves
implies finite-dimensionality of the rationalized abelian-sheaf carrier in
the LeanEval statement.
-/
theorem rationalizedCohomology_moduleFinite_of_moduleSheafExt
    (M : X.Modules) (n : ℕ)
    [Module.Finite ℚ
      (Abelian.Ext
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
          (ModuleCat.of ℚ ℚ))
        (Geometric.moduleSheaf M) n)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  letI := Geometric.cohomologyModule M n
  haveI : Module.Finite ℚ (M.sheaf.H n) := by
    exact ExtChangeOfScalars.constantSheafExtAb_moduleFinite
      (Opens.grothendieckTopology X) (isTerminalTop : IsTerminal (⊤ : X.Opens))
      (Geometric.moduleSheaf M) n
  exact Geometric.rationalizedCohomology_moduleFinite M n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.CohomologyCarrier
