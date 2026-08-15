/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseChangeModuleSheaf
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheaf

/-!
# Open cohomology for module sheaves over a flat base

For a scheme over a coefficient ring flat over `ℤ`, the sheaf of
coefficient modules underlying a scheme module has the same abelian
sheaf as the original module.  Combining this observation with flat
change of coefficients identifies Ext from a represented free module
sheaf with ordinary open-indexed sheaf cohomology.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseOpenCohomology

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseChange

variable {R : Type} [CommRing R] [Module.Flat ℤ R]
variable {X : Scheme.{0}}
  [X.Over (Spec (CommRingCat.of R))]

/-- Restricting the coefficient action to `ℤ` and then forgetting it
recovers the ordinary abelian sheaf underlying a scheme module. -/
noncomputable def moduleSheafUnderlyingAbIso
    (M : X.Modules) :
    ((sheafForgetZToAb
      (Opens.grothendieckTopology X)).obj
      ((sheafRestrictToIntegers R
        (Opens.grothendieckTopology X)).obj
        (moduleSheaf (k := R) M))) ≅
      M.sheaf :=
  Iso.refl _

/-- Ext from the free coefficient-module sheaf represented by an open
is ordinary open-indexed cohomology of the underlying module sheaf. -/
noncomputable def freeBaseModuleSheafExtAddEquivHPrime
    (V : X.Opens) (M : X.Modules) (n : ℕ) :
    Abelian.Ext
        (freeModuleSheaf (R := R) V)
        (moduleSheaf (k := R) M) n ≃+
      CategoryTheory.Sheaf.H' M.sheaf n V :=
  (freeModuleSheafExtAddEquivUnderlyingAbHPrime
    R V (moduleSheaf (k := R) M) n).trans
      (postcompIsoAddEquiv
        (moduleSheafUnderlyingAbIso M) n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseOpenCohomology
