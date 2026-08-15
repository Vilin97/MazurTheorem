/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearPullback
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Fixed-coefficient linear structures on topological sheaves

Mathlib's bundled topological presheaf and sheaf categories are
definitionally equivalent to the corresponding functor and site-sheaf
categories, but their linear structures are not exposed as instances.
This file transfers those structures and records linearity of direct
image.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

variable {R : Type u} [CommRing R]

/-- Presheaves of `R`-modules on a topological space form an
`R`-linear category. -/
noncomputable instance presheafLinear
    (X : TopCat.{u}) :
    Linear R (X.Presheaf (ModuleCat.{u} R)) :=
  inferInstanceAs
    (Linear R
      ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R))

/-- Sheaves of `R`-modules on a topological space form an `R`-linear
category. -/
noncomputable instance sheafLinear
    (X : TopCat.{u}) :
    Linear R (X.Sheaf (ModuleCat.{u} R)) :=
  inferInstanceAs
    (Linear R
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)))

/-- Direct image of fixed-coefficient presheaves is `R`-linear. -/
noncomputable instance presheafPushforwardLinear
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Presheaf.pushforward
      (ModuleCat.{u} R) f).Linear R where
  map_smul α r := by
    ext U
    rfl

/-- Direct image of fixed-coefficient sheaves is `R`-linear. -/
noncomputable instance sheafPushforwardLinear
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward
      (ModuleCat.{u} R) f).Linear R where
  map_smul α r := by
    apply
      (TopCat.Sheaf.forget
        (ModuleCat.{u} R) Y).map_injective
    ext U
    rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat
