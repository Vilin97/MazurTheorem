/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent

/-!
# Quasicoherence of the unit module

The unit sheaf of modules is a rank-one free sheaf.  Mathlib defines free
sheaves as coproducts, so the one-generator case is exposed through the
canonical coproduct isomorphism for a unique indexing type.
-/

open CategoryTheory Limits

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafUnit

variable {C : Type} [Category C]
  {J : GrothendieckTopology C}
  (R : Sheaf J RingCat)
  [HasBinaryProducts C]
  [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, (J.over X).HasSheafCompose
    (forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

/-- A free sheaf on one generator is the unit sheaf. -/
def freePUnitIso :
    SheafOfModules.free PUnit ≅
      SheafOfModules.unit R :=
  coproductUniqueIso
    (fun _ : PUnit => SheafOfModules.unit R)

/-- The unit sheaf is quasicoherent. -/
instance unit_isQuasicoherent :
    (SheafOfModules.unit R).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent R).prop_of_iso
    (freePUnitIso R)
    (inferInstance :
      (SheafOfModules.free (R := R) PUnit).IsQuasicoherent)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafUnit
