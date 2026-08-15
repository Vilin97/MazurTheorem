/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentSections

/-!
# Sections and transport along scheme isomorphisms

For an isomorphism of schemes, pullback is naturally isomorphic to
pushforward along the inverse.  This file packages that observation together
with the elementary equivalence on global sections induced by an isomorphism
of sheaves of modules.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections

/-- The two pushforwards associated to mutually inverse scheme maps form an
equivalence on sheaves of modules. -/
def pushforwardEquivalenceOfIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] :
    Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk
    (Scheme.Modules.pushforward (inv f))
    (Scheme.Modules.pushforward f)
    ((Scheme.Modules.pushforwardId Y).symm ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id f).symm ≪≫
      (Scheme.Modules.pushforwardComp (inv f) f).symm)
    (Scheme.Modules.pushforwardComp f (inv f) ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id f) ≪≫
      Scheme.Modules.pushforwardId X)

/-- Pullback along a scheme isomorphism agrees with pushforward along its
inverse. -/
def pullbackIsoPushforwardInverse {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] :
    Scheme.Modules.pullback f ≅
      Scheme.Modules.pushforward (inv f) :=
  Adjunction.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (pushforwardEquivalenceOfIso f).toAdjunction

/-- An isomorphism of sheaves of modules induces an additive equivalence on
global sections. -/
def sectionsAddEquivOfIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) :
    Γ(M, ⊤) ≃+ Γ(N, ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv x := by
    change (e.hom ≫ e.inv).app ⊤ x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change (e.inv ≫ e.hom).app ⊤ x = x
    rw [e.inv_hom_id]
    rfl
  map_add' x y := map_add _ x y

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections
