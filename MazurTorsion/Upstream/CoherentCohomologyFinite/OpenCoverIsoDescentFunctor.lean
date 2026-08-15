/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentScalarTwist

/-!
# The descent pullback functor of an open-cover isomorphism

The coherent object construction along a cover isomorphism acts on
morphisms by pulling their chart components back along the component
isomorphisms.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Pull a morphism of target-cover descent data to the source cover. -/
noncomputable def pullbackAlongCoverIsoMap
    (e : 𝒰 ≅ 𝒱)
    {A B : CoverDescentData 𝒱.gluedCover}
    (φ : A ⟶ B) :
    pullbackAlongCoverIso e A ⟶
      pullbackAlongCoverIso e B where
  app i :=
    (pullback (e.hom.h₀ i)).map
      (φ.app (e.hom.s₀ i))
  compatible := by
    intro (i : 𝒰.I₀) (j : 𝒰.I₀)
    rw [pullbackAlongCoverIso_transition,
      pullbackAlongCoverIso_transition]
    exact
      coverIsoPullbackTransition_naturality
        e φ i j

@[simp]
theorem pullbackAlongCoverIsoMap_app
    (e : 𝒰 ≅ 𝒱)
    {A B : CoverDescentData 𝒱.gluedCover}
    (φ : A ⟶ B) (i : 𝒰.I₀) :
    (pullbackAlongCoverIsoMap e φ).app i =
      (pullback (e.hom.h₀ i)).map
        (φ.app (e.hom.s₀ i)) :=
  rfl

/-- Pullback of descent data along an isomorphism of open covers. -/
noncomputable def pullbackAlongCoverIsoFunctor
    (e : 𝒰 ≅ 𝒱) :
    CoverDescentData 𝒱.gluedCover ⥤
      CoverDescentData 𝒰.gluedCover where
  obj := pullbackAlongCoverIso e
  map := pullbackAlongCoverIsoMap e
  map_id A := by
    apply Hom.ext
    intro i
    exact (pullback (e.hom.h₀ i)).map_id
      (A.chart (e.hom.s₀ i))
  map_comp {A B C} φ ψ := by
    apply Hom.ext
    intro i
    exact
      (pullback (e.hom.h₀ i)).map_comp
        (φ.app (e.hom.s₀ i))
        (ψ.app (e.hom.s₀ i))

@[simp]
theorem pullbackAlongCoverIsoFunctor_obj_chart
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover)
    (i : 𝒰.I₀) :
    ((pullbackAlongCoverIsoFunctor e).obj A).chart i =
      (pullback (e.hom.h₀ i)).obj
        (A.chart (e.hom.s₀ i)) :=
  rfl

@[simp]
theorem pullbackAlongCoverIsoFunctor_map_app
    (e : 𝒰 ≅ 𝒱)
    {A B : CoverDescentData 𝒱.gluedCover}
    (φ : A ⟶ B) (i : 𝒰.I₀) :
    ((pullbackAlongCoverIsoFunctor e).map φ).app i =
      (pullback (e.hom.h₀ i)).map
        (φ.app (e.hom.s₀ i)) :=
  rfl

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
