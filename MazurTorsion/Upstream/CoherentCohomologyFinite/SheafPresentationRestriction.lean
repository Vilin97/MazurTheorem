/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction

/-!
# Restricting presentations of module sheaves

A presentation by free module sheaves can be transported along an open
immersion.  We also record the cancellation isomorphism obtained by
restricting successively along the two arrows of an isomorphism of
schemes.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Restriction preserves colimits, witnessed by its explicit adjunction. -/
theorem restrictPreservesColimits :
    Limits.PreservesColimitsOfSize.{u, u} (restrictFunctor f) :=
  (restrictAdjunction f).leftAdjoint_preservesColimits

/-- Restrict a global presentation along an open immersion. -/
noncomputable def Presentation.restrict
    {M : Y.Modules} (P : M.Presentation) :
    (M.restrict f).Presentation :=
  @SheafOfModules.Presentation.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (restrictFunctor f) (restrictPreservesColimits f)
    (restrictUnitIso f).symm

@[simp]
theorem Presentation.restrict_generators_I
    {M : Y.Modules} (P : M.Presentation) :
    (Presentation.restrict f P).generators.I = P.generators.I :=
  @SheafOfModules.Presentation.map_generators_I
    _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (restrictFunctor f) (restrictPreservesColimits f)
    (restrictUnitIso f).symm

@[simp]
theorem Presentation.restrict_relations_I
    {M : Y.Modules} (P : M.Presentation) :
    (Presentation.restrict f P).relations.I = P.relations.I :=
  @SheafOfModules.Presentation.map_relations_I
    _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (restrictFunctor f) (restrictPreservesColimits f)
    (restrictUnitIso f).symm

/-- Finiteness of a presentation is preserved by open restriction. -/
instance Presentation.restrict_isFinite
    {M : Y.Modules} (P : M.Presentation) [hP : P.IsFinite] :
    (Presentation.restrict f P).IsFinite where
  isFiniteType_generators := by
    refine
      SheafOfModules.GeneratingSections.IsFiniteType.mk
        (σ := (Presentation.restrict f P).generators) ?_
    rw [Presentation.restrict_generators_I f P]
    exact hP.isFiniteType_generators.finite
  isFiniteType_relations := by
    refine
      SheafOfModules.GeneratingSections.IsFiniteType.mk
        (σ := (Presentation.restrict f P).relations) ?_
    rw [Presentation.restrict_relations_I f P]
    exact hP.isFiniteType_relations.finite

/--
Restricting a module sheaf along the inverse and then the forward map of
an isomorphism recovers the original module sheaf.
-/
noncomputable def restrictIsoOfIso
    (e : X ≅ Y) (M : X.Modules) :
    (M.restrict e.inv).restrict e.hom ≅ M :=
  (restrictFunctorComp e.hom e.inv).symm.app M ≪≫
    (restrictFunctorCongr e.hom_inv_id).app M ≪≫
    (restrictFunctorId).app M

end AlgebraicGeometry.Scheme.Modules
