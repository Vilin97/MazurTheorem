/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FreeModuleSheafOpenCohomology

/-!
# Ext from an integer free module sheaf

The equivalence between abelian groups and integer modules lifts to
sheaves.  Consequently Ext from the free integer-module sheaf represented
by an open computes ordinary open-indexed cohomology of an abelian sheaf.

This coefficient-free comparison is useful when a geometric
trivialization is only naturally additive.
-/

open CategoryTheory TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeIntegerModuleSheafOpenCohomology

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeModuleSheafOpenCohomology

/-- Lifting an abelian sheaf to integer modules and forgetting again
recovers the original sheaf. -/
noncomputable def sheafLiftForgetIsoAt
    {C : Type} [SmallCategory C]
    (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat) :
    (sheafForgetZToAb J).obj
        ((sheafLiftAbToZ J).obj G) ≅ G :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft G.obj
      forgetZToAb.asEquivalence.counitIso)

/-- Ext from the free integer-module sheaf represented by `V` agrees
additively with open-indexed cohomology of the original abelian sheaf. -/
noncomputable def freeIntegerModuleSheafExtAddEquivHPrime
    {T : TopCat} (V : Opens T)
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (n : ℕ) :
    Abelian.Ext
        (freeModuleSheaf (R := ℤ) V)
        ((sheafLiftAbToZ
          (Opens.grothendieckTopology T)).obj G) n ≃+
      CategoryTheory.Sheaf.H' G n V := by
  let J := Opens.grothendieckTopology T
  exact
    (sheafForgetZToAb_extAddEquiv J
      (freeModuleSheaf (R := ℤ) V)
      ((sheafLiftAbToZ J).obj G) n).trans <|
      (ExtAdjunction.precompIsoAddEquiv
        (freeModuleSheafForgetIso V) n).symm.trans <|
        ExtAdjunction.postcompIsoAddEquiv
          (sheafLiftForgetIsoAt J G) n

/-- Ext from the constant rank-one integer-module sheaf computes ordinary
global cohomology of the original abelian sheaf. -/
noncomputable def constantIntegerModuleSheafExtAddEquivH
    {T : TopCat}
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (n : ℕ) :
    Abelian.Ext
        (constantRankOneSheaf (R := ℤ) T)
        ((sheafLiftAbToZ
          (Opens.grothendieckTopology T)).obj G) n ≃+
      CategoryTheory.Sheaf.H G n := by
  let J := Opens.grothendieckTopology T
  exact
    (sheafForgetZToAb_extAddEquiv J
      (constantRankOneSheaf (R := ℤ) T)
      ((sheafLiftAbToZ J).obj G) n).trans <|
      (ExtAdjunction.precompIsoAddEquiv
        (constantZForgetIso J) n).symm.trans <|
        (ExtAdjunction.postcompIsoAddEquiv
          (sheafLiftForgetIsoAt J G) n).trans <|
          (ExtAdjunction.precompIsoAddEquiv
            (constantAbZULiftIso J) n).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeIntegerModuleSheafOpenCohomology
