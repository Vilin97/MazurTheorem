/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoSections

/-!
# Pullback--pushforward along an isomorphism

Pullback along an isomorphism of schemes is an equivalence on sheaves of
modules.  Consequently the unit of the geometric pullback--pushforward
adjunction is an isomorphism.  This small categorical bridge is useful when
a morphism becomes an isomorphism after restricting its target to an open
subscheme.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback functor along an isomorphism of schemes is fully faithful. -/
noncomputable def pullbackFullyFaithfulOfIsIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (pullback f).FullyFaithful := by
  let e : Y.Modules ≌ X.Modules :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections.pushforwardEquivalenceOfIso f
  exact e.fullyFaithfulFunctor.ofIso
    (MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections.pullbackIsoPushforwardInverse f).symm

/--
For an isomorphism of schemes, every component of the unit of the
pullback--pushforward adjunction is an isomorphism.
-/
instance pullbackPushforwardAdjunction_unit_app_isIso_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  let hff := pullbackFullyFaithfulOfIsIso f
  letI : (pullback f).Full := hff.full
  letI : (pullback f).Faithful := hff.faithful
  infer_instance

end AlgebraicGeometry.Scheme.Modules
