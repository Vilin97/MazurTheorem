/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finite presentations under colimit-preserving functors

Mathlib transports a presentation through a colimit-preserving functor.
The index types of generators and relations are unchanged, so finiteness of
the presentation is preserved as well.
-/

open CategoryTheory Limits

universe u v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable {C' : Type u₂} [Category.{v₂} C']
  {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat]
  [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable {M : SheafOfModules.{u} R}
  (P : Presentation M)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  [PreservesColimitsOfSize.{u, u} F]
  (η : unit S ≅ F.obj (unit R))

/-- Mapping a finite presentation through a colimit-preserving functor
preserves finiteness. -/
instance Presentation.map_isFinite [P.IsFinite] :
    (P.map F η).IsFinite where
  isFiniteType_generators := by
    constructor
    simpa only [Presentation.map_generators_I] using
      (inferInstance : Finite P.generators.I)
  isFiniteType_relations := by
    constructor
    simpa only [Presentation.map_relations_I] using
      (inferInstance : Finite P.relations.I)

end SheafOfModules
