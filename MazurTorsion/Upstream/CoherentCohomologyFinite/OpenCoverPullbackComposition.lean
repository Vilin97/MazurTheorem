/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Associativity of pulled-back open covers

Pulling an open cover back successively along `f` and `g` gives a cover
canonically isomorphic to its pullback along `g ≫ f`.  The component
isomorphisms are the standard horizontal-pasting isomorphisms for
pullbacks.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Cover

variable {S T R : Scheme.{0}}
  (𝒰 : S.OpenCover) (f : T ⟶ S) (g : R ⟶ T)

local instance openCoverMapIsOpenImmersion (i : 𝒰.I₀) :
    IsOpenImmersion (𝒰.f i) :=
  𝒰.map_prop i

local instance openCoverMapHasPullback (i : 𝒰.I₀) :
    HasPullback f (𝒰.f i) :=
  IsOpenImmersion.hasPullback_of_right (𝒰.f i) f

local instance pullbackFstIsOpenImmersion (i : 𝒰.I₀) :
    IsOpenImmersion (pullback.fst f (𝒰.f i)) := by
  infer_instance

local instance pullbackFstHasPullback (i : 𝒰.I₀) :
    HasPullback g (pullback.fst f (𝒰.f i)) :=
  IsOpenImmersion.hasPullback_of_right
    (pullback.fst f (𝒰.f i)) g

/-- The canonical cover isomorphism from successive pullback to
pullback along the composite. -/
noncomputable def pullbackPullbackIso :
    (𝒰.pullback₁ f).pullback₁ g ≅
      𝒰.pullback₁ (g ≫ f) :=
  Precoverage.ZeroHypercover.isoMk
    (PreZeroHypercover.isoMk
      (Equiv.refl 𝒰.I₀)
      (fun i =>
        @pullbackRightPullbackFstIso _ _ _ _ _ _
          f (𝒰.f i) g
          (openCoverMapHasPullback 𝒰 f i)
          (pullbackFstHasPullback 𝒰 f g i))
      (fun i => by
        exact
          @pullbackRightPullbackFstIso_hom_fst _ _ _ _ _ _
            f (𝒰.f i) g
            (openCoverMapHasPullback 𝒰 f i)
            (pullbackFstHasPullback 𝒰 f g i)))

@[simp]
theorem pullbackPullbackIso_hom_s₀
    (i : 𝒰.I₀) :
    (pullbackPullbackIso 𝒰 f g).hom.s₀ i = i :=
  rfl

@[reassoc (attr := simp)]
theorem pullbackPullbackIso_hom_h₀_f
    (i : 𝒰.I₀) :
    (pullbackPullbackIso 𝒰 f g).hom.h₀ i ≫
        (𝒰.pullback₁ (g ≫ f)).f i =
      ((𝒰.pullback₁ f).pullback₁ g).f i :=
  (pullbackPullbackIso 𝒰 f g).hom.w₀ i

@[reassoc]
theorem pullbackPullbackIso_hom_h₀_pullbackHom
    (i : 𝒰.I₀) :
    (pullbackPullbackIso 𝒰 f g).hom.h₀ i ≫
        𝒰.pullbackHom (g ≫ f) i =
      Cover.pullbackHom (𝒰.pullback₁ f) g i ≫
        𝒰.pullbackHom f i := by
  exact pullbackRightPullbackFstIso_hom_snd
    f (𝒰.f i) g

end AlgebraicGeometry.Scheme.Cover
