/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Linear Ext comparison for an exact right adjoint

The additive Ext comparison attached to an adjunction is linear when
the right adjoint is linear.  This file packages that observation as a
linear equivalence.
-/


open CategoryTheory Limits

noncomputable section

universe w w' v v' u u' t

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction

variable {R : Type t} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]
variable (L : C ⥤ D) (U : D ⥤ C) (adj : L ⊣ U)
  [U.Additive] [U.Linear R]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- The Ext comparison for an exact linear right adjoint, as a linear
equivalence. -/
noncomputable def extLinearEquiv
    [EnoughInjectives D] [U.PreservesInjectiveObjects]
    (X : C) (Y : D) (n : ℕ) :
    Abelian.Ext (L.obj X) Y n ≃ₗ[R]
      Abelian.Ext X (U.obj Y) n where
  toAddEquiv := extAddEquiv L U adj X Y n
  map_smul' r x := by
    simp [extAddEquiv, extAddHom]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction
