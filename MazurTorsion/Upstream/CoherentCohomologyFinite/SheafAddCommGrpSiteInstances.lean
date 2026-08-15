/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverPresentationInverse

/-!
# Explicit abelian-group sheaf instances on small sites

These named witnesses keep downstream local-to-global arguments from
repeating expensive typeclass searches for sheafification and local
bijectivity on iterated slice sites.
-/

open CategoryTheory

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- Composition with the forgetful functor to abelian groups preserves
sheaves on a small site. -/
theorem hasSheafComposeAddCommGrp
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  infer_instance

/-- Abelian-group-valued presheaves on a small site have a weak
sheafification. -/
theorem hasWeakSheafifyAddCommGrp
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{u} := by
  infer_instance

/-- Abelian-group-valued presheaves on a small site have a
sheafification. -/
theorem hasSheafifyAddCommGrp
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u} := by
  infer_instance

/-- On a small site, local bijectivity computes the morphisms inverted
by abelian-group sheafification. -/
theorem wEqualsLocallyBijectiveAddCommGrp
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  infer_instance

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
