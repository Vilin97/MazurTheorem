/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseGlobalCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreVanishing

/-!
# Cohomological form of projective Serre vanishing

The base-linear constant-source Ext vanishing theorem is transported to
ordinary sheaf cohomology through flat change of coefficients.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseOpenCohomology
open SerreTwist

local instance projectiveSpaceOverBaseForSerreCohomology
    (R : Type) [CommRing R] (d : ℕ) :
    (scheme R d).Over (Spec (CommRingCat.of R)) :=
  ⟨toSpec R d⟩

noncomputable local instance projectiveSerreSheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Every positive ordinary cohomology group of sufficiently positive
projective scalar twists of a finite-type quasicoherent module vanishes. -/
theorem eventually_positiveScalarTwist_sheafH_subsingleton
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    [IsNoetherianRing R]
    (d : ℕ)
    (M : (scheme R d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ q : ℕ, 0 < q →
        Subsingleton
          (((positiveScalarTwistFunctor
            R d n).obj M).sheaf.H q) := by
  obtain ⟨b, hb⟩ :=
    eventually_positiveScalarTwist_moduleSheafExt_subsingleton
      R d M
  refine ⟨b, fun n hn q hq => ?_⟩
  let E :=
    constantBaseModuleSheafExtAddEquivH
      (R := R)
      ((positiveScalarTwistFunctor R d n).obj M) q
  have hExt :=
    hb n hn q hq
  exact
    ⟨fun x y =>
      E.symm.injective
        (hExt.elim (E.symm x) (E.symm y))⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
