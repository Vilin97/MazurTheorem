/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleDescent

/-!
# Naturality of line-bundle overlap transport

The morphism below is the pseudofunctorially canonical transport of an isomorphism on an
explicit fibre-product model.  Mathlib's iterated-`pullHom` theorem proves its naturality under
all further pullbacks. Packaging its inverse without unfolding the module pseudofunctor is kept
separate from this comparison theorem.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

universe u

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-- The canonical transition morphism on the standard pullback, obtained from a comparison on
any explicit fibre-product model. -/
noncomputable def pullbackOverlapHomOfModel
    {S X₁ X₂ W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (e : (Scheme.Modules.pullback p₁).obj M₁ ≅
      (Scheme.Modules.pullback p₂).obj M₂) :
    (Scheme.Modules.pullback (pullback.fst f₁ f₂)).obj M₁ ⟶
      (Scheme.Modules.pullback (pullback.snd f₁ f₂)).obj M₂ :=
  pullHom (F := modulesPseudofunctor) e.hom hpb.isoPullback.inv
    (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)

/-- Further pullback of the canonical transition is pullback of the original model comparison
along the composite map to that model. -/
theorem pullHom_pullbackOverlapHomOfModel
    {S X₁ X₂ W T : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (e : (Scheme.Modules.pullback p₁).obj M₁ ≅
      (Scheme.Modules.pullback p₂).obj M₂)
    (q : T ⟶ pullback f₁ f₂)
    (q₁ : T ⟶ X₁) (q₂ : T ⟶ X₂)
    (hq₁ : q ≫ pullback.fst f₁ f₂ = q₁)
    (hq₂ : q ≫ pullback.snd f₁ f₂ = q₂) :
    pullHom (F := modulesPseudofunctor)
        (pullbackOverlapHomOfModel f₁ f₂ p₁ p₂ hpb M₁ M₂ e)
        q q₁ q₂ hq₁ hq₂ =
      pullHom (F := modulesPseudofunctor) e.hom
        (q ≫ hpb.isoPullback.inv) q₁ q₂
        (by rw [Category.assoc, hpb.isoPullback_inv_fst, hq₁])
        (by rw [Category.assoc, hpb.isoPullback_inv_snd, hq₂]) := by
  change pullHom (F := modulesPseudofunctor)
      (pullHom (F := modulesPseudofunctor) e.hom hpb.isoPullback.inv
        (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)) q q₁ q₂ = _
  apply pullHom_pullHom

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
