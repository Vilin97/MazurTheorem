/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFinitePresentationCover

/-!
# Finite presentation from one global presentation

A finite global presentation yields finite quasicoherent data on the
trivial cover.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]
  [HasBinaryProducts C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, (J.over X).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- The quasicoherent data associated to a finite global presentation
has finite local presentations. -/
instance Presentation.quasicoherentData_isFinitePresentation
    {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite] :
    P.quasicoherentData.IsFinitePresentation where
  isFinite_presentation X := by
    change C at X
    letI :
        (J.over X).HasSheafCompose
          (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
      inferInstance
    letI : HasSheafify (J.over X) AddCommGrpCat.{u} :=
      inferInstance
    letI :
        (J.over X).WEqualsLocallyBijective
          AddCommGrpCat.{u} :=
      inferInstance
    letI :
        (J.over (id X)).HasSheafCompose
          (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
      change
        (J.over X).HasSheafCompose
          (forget₂ RingCat.{u} AddCommGrpCat.{u})
      infer_instance
    letI :
        HasSheafify (J.over (id X))
          AddCommGrpCat.{u} := by
      change HasSheafify (J.over X) AddCommGrpCat.{u}
      infer_instance
    letI :
        HasWeakSheafify (J.over (id X))
          AddCommGrpCat.{u} :=
      HasSheafify.isRightAdjoint
    letI :
        (J.over (id X)).WEqualsLocallyBijective
          AddCommGrpCat.{u} := by
      change
        (J.over X).WEqualsLocallyBijective
          AddCommGrpCat.{u}
      infer_instance
    refine Presentation.isFinite_of_finite_indices
      (P.quasicoherentData.presentation X) ?_ ?_
    · change Finite P.generators.I
      exact GeneratingSections.IsFiniteType.finite
        (σ := P.generators)
    · change Finite P.relations.I
      exact GeneratingSections.IsFiniteType.finite
        (σ := P.relations)

/-- A finite global presentation makes the module sheaf finitely
presented. -/
theorem Presentation.isFinitePresentation
    {M : SheafOfModules.{u} R}
    (P : M.Presentation) (hP : P.IsFinite) :
    M.IsFinitePresentation := by
  letI : P.IsFinite := hP
  exact
    {
      exists_quasicoherentData :=
        ⟨P.quasicoherentData, inferInstance⟩
    }

end SheafOfModules
