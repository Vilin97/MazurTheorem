/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed
`CoherentCohomologyFinite/ModuleSupport.lean` in Vilin97/Clawristotle.
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Topology.Sheaves.Abelian
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf

/-!
# Closed stalk support of a scheme module

This is the support-rank core of AINTLIB's `SchemeModuleSupport`. It retains
only the underlying stalk functor, the nonzero-stalk locus, and its closure,
which are the declarations consumed by low-degree support induction. The
finite-type closedness and comparison lemmas remain outside this narrow
slice until the proper Chow-comodel layer needs them.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The underlying abelian-group stalk functor at a point of a scheme. -/
noncomputable def underlyingStalkFunctor (x : X) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  toSheaf X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor.{u, u + 1} AddCommGrpCat.{u} x

noncomputable instance underlyingStalkFunctor_additive (x : X) :
    (underlyingStalkFunctor x).Additive := by
  dsimp [underlyingStalkFunctor]
  infer_instance

noncomputable instance underlyingStalkFunctor_preservesFiniteLimits
    (x : X) :
    PreservesFiniteLimits (underlyingStalkFunctor x) := by
  dsimp [underlyingStalkFunctor]
  infer_instance

noncomputable instance underlyingStalkFunctor_preservesFiniteColimits
    (x : X) :
    PreservesFiniteColimits (underlyingStalkFunctor x) := by
  dsimp [underlyingStalkFunctor]
  infer_instance

/-- The set of points where the underlying sheaf stalk is nonzero. -/
def stalkSupport (M : X.Modules) : Set X :=
  {x | ¬ IsZero ((underlyingStalkFunctor x).obj M)}

/-- The closure of the nonzero-stalk locus. -/
def closedStalkSupport (M : X.Modules) : Closeds X :=
  ⟨closure (stalkSupport M), isClosed_closure⟩

end AlgebraicGeometry.Scheme.Modules
