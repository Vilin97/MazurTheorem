/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.ModuleCat.Products
import MazurTorsion.Upstream.CurveLineBundleDescent

/-!
# The equalizer candidate for effective module descent

This file constructs the canonical compatible-family object attached to module descent data on
one scheme open cover.  The construction is an equalizer of the two overlap-restriction maps.
It is only a candidate until its restriction to every member of the cover is identified with the
specified local module.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

universe u

/-- The product of the direct images of all local modules in a descent datum. -/
noncomputable def compatibleFamilyAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ fun i ↦ (Scheme.Modules.pushforward (cov.f i)).obj (D.obj i)

/-- The product of the direct images of the second local module restricted to every chosen
pairwise overlap. -/
noncomputable def compatibleFamilyOverlapAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ fun ij : cov.I₀ × cov.I₀ ↦
    let P := overlap cov ij.1 ij.2
    (Scheme.Modules.pushforward (P.p₁ ≫ cov.f ij.1)).obj
      ((Scheme.Modules.pullback P.p₂).obj (D.obj ij.2))

/-- Restrict the first member of a local family to an overlap and transport it through the
descent isomorphism. -/
noncomputable def compatibleFamilyFirstComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward
        ((overlap cov i j).p₁ ≫ cov.f i)).obj
        ((Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j)) :=
  let P := overlap cov i j
  Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) i ≫
    (Scheme.Modules.pushforward (cov.f i)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction P.p₁).unit.app (D.obj i)) ≫
    (Scheme.Modules.pushforwardComp P.p₁ (cov.f i)).hom.app
      ((Scheme.Modules.pullback P.p₁).obj (D.obj i)) ≫
    (Scheme.Modules.pushforward (P.p₁ ≫ cov.f i)).map
      (D.hom (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm)

/-- Restrict the second member of a local family to an overlap, then identify the two equal
structural maps to the base. -/
noncomputable def compatibleFamilySecondComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward
        ((overlap cov i j).p₁ ≫ cov.f i)).obj
        ((Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j)) :=
  let P := overlap cov i j
  Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j ≫
    (Scheme.Modules.pushforward (cov.f j)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction P.p₂).unit.app (D.obj j)) ≫
    (Scheme.Modules.pushforwardComp P.p₂ (cov.f j)).hom.app
      ((Scheme.Modules.pullback P.p₂).obj (D.obj j)) ≫
    (Scheme.Modules.pushforwardCongr P.condition.symm).hom.app
      ((Scheme.Modules.pullback P.p₂).obj (D.obj j))

/-- The first overlap-restriction map from all local families. -/
noncomputable def compatibleFamilyFirst
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) :
    compatibleFamilyAmbient D ⟶ compatibleFamilyOverlapAmbient D :=
  Pi.lift fun ij ↦ compatibleFamilyFirstComponent D ij.1 ij.2

/-- The second overlap-restriction map from all local families. -/
noncomputable def compatibleFamilySecond
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) :
    compatibleFamilyAmbient D ⟶ compatibleFamilyOverlapAmbient D :=
  Pi.lift fun ij ↦ compatibleFamilySecondComponent D ij.1 ij.2

/-- The global module candidate consisting of compatible local families. -/
noncomputable def compatibleFamilyModule
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  equalizer (compatibleFamilyFirst D) (compatibleFamilySecond D)

/-- The candidate's universal inclusion satisfies the required compatibility equation. -/
theorem compatibleFamilyModule_condition
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) :
    equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
        compatibleFamilyFirst D =
      equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
        compatibleFamilySecond D :=
  equalizer.condition _ _

/-- The compatible-family module projects to each pushed-forward local module. -/
noncomputable def compatibleFamilyProjection
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyModule D ⟶
      (Scheme.Modules.pushforward (cov.f i)).obj (D.obj i) :=
  equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
    Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i

/-- The adjoint transpose of the chart projection, stated with the genuine module pullback
functor used by `EffectiveModule`.  Proving that this morphism is an isomorphism is the remaining
effective-descent theorem for the equalizer candidate. -/
noncomputable def compatibleFamilyRestrictionHom
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj (compatibleFamilyModule D) ⟶ D.obj i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
    (compatibleFamilyModule D) (D.obj i)).symm (compatibleFamilyProjection D i)

/-- The chart restriction map is definitionally adjoint to the corresponding projection of
compatible families.  This is the comparison equation used when constructing its inverse. -/
theorem compatibleFamilyRestrictionHom_adjunct
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
        (compatibleFamilyModule D) (D.obj i) (compatibleFamilyRestrictionHom D i) =
      compatibleFamilyProjection D i := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
    (compatibleFamilyModule D) (D.obj i)).apply_symm_apply _

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
