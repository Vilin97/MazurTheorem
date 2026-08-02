/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData
import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Effective descent boundary for curve line bundles

Mathlib provides the pseudofunctor of sheaves of modules and the category of coherent descent
data for a family of scheme morphisms. The current dependency graph does not yet prove that
these descent data are effective for a Zariski cover, nor that an effective object assembled
from invertible local objects is globally invertible.

This file isolates exactly the object-specific conclusion needed by the divisor--line-bundle
dictionary. `EffectiveInvertible` says that one specified coherent descent datum is represented
by a global Tau Ceti invertible sheaf. Its checked consumers recover the chosen global line
bundle, the descent isomorphism, and every chart restriction isomorphism. It does not construct
overlap cocycles and does not assert that the module pseudofunctor is a stack.
-/

open CategoryTheory Bicategory

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

universe u

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

/-- The scheme-module pseudofunctor with only its pullback functors retained. -/
noncomputable def modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp (Adj.forget₁ (B := Cat))

/-- A specified coherent module descent datum on an open cover is effectively represented by
a global invertible sheaf. This packages object-specific effectivity and global invertibility;
it does not assert effectivity for all module descent data or a stack theorem. -/
noncomputable def EffectiveInvertible
    {X : Scheme.{u}} (cov : X.OpenCover)
    (D : modulesPseudofunctor.DescentData cov.f) : Prop :=
  ∃ L : InvertibleSheaf X,
    Nonempty ((modulesPseudofunctor.toDescentData cov.f).obj L.obj ≅ D)

namespace EffectiveInvertible

/-- The global invertible sheaf supplied by effective descent. -/
noncomputable def lineBundle
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D) : InvertibleSheaf X :=
  h.choose

/-- The chosen global line bundle induces the specified coherent descent datum. -/
noncomputable def descentIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D) :
    (modulesPseudofunctor.toDescentData cov.f).obj h.lineBundle.obj ≅ D :=
  h.choose_spec.some

/-- On every member of the cover, the chosen global line bundle restricts to the corresponding
local object of the specified descent datum. This is the genuine consumer of
`EffectiveInvertible`. -/
noncomputable def restrictionIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj h.lineBundle.obj ≅ D.obj i where
  hom := h.descentIso.hom.hom i
  inv := h.descentIso.inv.hom i
  hom_inv_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) h.descentIso.hom_inv_id
    change h.descentIso.hom.hom i ≫ h.descentIso.inv.hom i = 𝟙 _
    exact hi
  inv_hom_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) h.descentIso.inv_hom_id
    change h.descentIso.inv.hom i ≫ h.descentIso.hom.hom i = 𝟙 _
    exact hi

end EffectiveInvertible

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
