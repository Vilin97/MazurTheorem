/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafPresentationRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.PresheafPushforwardExactness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness of restriction to an open subscheme

Restriction along an open immersion is computed by precomposition on
sections.  In Mathlib it is both the explicit restriction left adjoint
and an instance of the general sheaf-module pushforward right adjoint.
Thus it preserves all limits and colimits, hence is exact.
-/


universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsOpenImmersion f]


/-- Restriction along an open immersion preserves finite limits. -/
noncomputable instance restrictFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (restrictFunctor f) := by
  let α :
      X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  let φ :
      X.ringCatSheaf ⟶
        (f.opensFunctor.sheafPushforwardContinuous
          RingCat (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology Y)).obj
          Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α
      (forget₂ CommRingCat RingCat)⟩
  change PreservesFiniteLimits
    (SheafOfModules.pushforward φ)
  letI : (PresheafOfModules.pushforward φ.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : (SheafOfModules.pushforward φ).IsRightAdjoint :=
    (SheafOfModules.PullbackConstruction.adjunction φ).isRightAdjoint
  letI : PreservesFiniteLimits
      (SheafOfModules.pushforward φ) := by
    infer_instance
  letI : PreservesFiniteLimits
      (SheafOfModules.forget X.ringCatSheaf) := by
    infer_instance
  letI : PreservesFiniteLimits
      (SheafOfModules.pushforward φ ⋙
        SheafOfModules.forget X.ringCatSheaf) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves
    (SheafOfModules.pushforward φ)
    (SheafOfModules.forget X.ringCatSheaf)

/-- A named witness for finite-limit preservation by open restriction. -/
theorem restrictPreservesFiniteLimits :
    PreservesFiniteLimits (restrictFunctor f) :=
  inferInstance

end AlgebraicGeometry.Scheme.Modules
