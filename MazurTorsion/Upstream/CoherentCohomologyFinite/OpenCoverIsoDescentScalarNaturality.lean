/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentFunctor
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistInverse

/-!
# Scalar-twist naturality under an isomorphism of open covers

The chartwise identity maps identify twisting before descent pullback
with twisting afterward by the transported overlap-unit family.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- The chartwise identity comparison between scalar twisting before
and after pulling descent data along a cover isomorphism. -/
noncomputable def scalarTwistPullbackAlongCoverIsoHom
    (e : 𝒰 ≅ 𝒱)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (hbself : ∀ i, b i i = 1)
    (hbcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (haself : ∀ i,
      pullbackCoverUnitAlongIso e b i i = 1)
    (hacocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover
        (pullbackCoverUnitAlongIso e b))
    (A : CoverDescentData 𝒱.gluedCover) :
    ((scalarTwistFunctor
        b hbself hbcocycle ⋙
      pullbackAlongCoverIsoFunctor e).obj A) ⟶
    ((pullbackAlongCoverIsoFunctor e ⋙
      scalarTwistFunctor
        (pullbackCoverUnitAlongIso e b)
        haself hacocycle).obj A) where
  app i := 𝟙 _
  compatible := by
      let M : ∀ i : 𝒰.I₀,
          (𝒰.gluedCover.U i).Modules :=
        fun i =>
          (pullback (e.hom.h₀ i)).obj
            (A.chart (e.hom.s₀ i))
      let g : CoverTransition 𝒰.gluedCover M :=
        fun i j =>
          (pullbackAlongCoverIso e
            (scalarTwistObject
              b hbself hbcocycle A)).transition i j
      let h : CoverTransition 𝒰.gluedCover M :=
        fun i j =>
          scalarTwistedTransition
            (pullbackAlongCoverIso e A)
            (pullbackCoverUnitAlongIso e b)
            i j
      change DescentMorphismCompatible
        𝒰.gluedCover M M g h
          (fun i => 𝟙 (M i))
      have htransition : h = g := by
        funext i j
        dsimp only [h, g]
        unfold scalarTwistedTransition
        rw [pullbackAlongCoverIso_transition
              e A i j,
          pullbackAlongCoverIso_transition
            e
            (scalarTwistObject
              b hbself hbcocycle A)
            i j]
        exact
          (coverIsoPullbackTransition_scalarTwist
            e A b hbself hbcocycle i j).symm
      rw [htransition]
      exact
        descentMorphismCompatible_id
          𝒰.gluedCover M g

@[simp]
theorem scalarTwistPullbackAlongCoverIsoHom_app
    (e : 𝒰 ≅ 𝒱)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (hbself : ∀ i, b i i = 1)
    (hbcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (haself : ∀ i,
      pullbackCoverUnitAlongIso e b i i = 1)
    (hacocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover
        (pullbackCoverUnitAlongIso e b))
    (A : CoverDescentData 𝒱.gluedCover)
    (i : 𝒰.I₀) :
    (scalarTwistPullbackAlongCoverIsoHom
      e b hbself hbcocycle haself hacocycle A).app i =
        𝟙 _ :=
  rfl

/-- Objectwise isomorphism between the two orders of scalar twisting
and descent pullback along a cover isomorphism. -/
noncomputable def scalarTwistPullbackAlongCoverIsoIso
    (e : 𝒰 ≅ 𝒱)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (hbself : ∀ i, b i i = 1)
    (hbcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (haself : ∀ i,
      pullbackCoverUnitAlongIso e b i i = 1)
    (hacocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover
        (pullbackCoverUnitAlongIso e b))
    (A : CoverDescentData 𝒱.gluedCover) :
    ((scalarTwistFunctor
        b hbself hbcocycle ⋙
      pullbackAlongCoverIsoFunctor e).obj A) ≅
    ((pullbackAlongCoverIsoFunctor e ⋙
      scalarTwistFunctor
        (pullbackCoverUnitAlongIso e b)
        haself hacocycle).obj A) := by
  let h :=
    scalarTwistPullbackAlongCoverIsoHom
      e b hbself hbcocycle haself hacocycle A
  letI : ∀ i, IsIso (h.app i) := fun i => by
    change IsIso (𝟙 _)
    infer_instance
  exact h.isoOfComponents

@[simp]
theorem scalarTwistPullbackAlongCoverIsoIso_hom_app
    (e : 𝒰 ≅ 𝒱)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (hbself : ∀ i, b i i = 1)
    (hbcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (haself : ∀ i,
      pullbackCoverUnitAlongIso e b i i = 1)
    (hacocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover
        (pullbackCoverUnitAlongIso e b))
    (A : CoverDescentData 𝒱.gluedCover)
    (i : 𝒰.I₀) :
    (scalarTwistPullbackAlongCoverIsoIso
      e b hbself hbcocycle haself hacocycle A).hom.app i =
        𝟙 _ :=
  rfl

/-- Scalar twisting commutes naturally with descent pullback along a
cover isomorphism. -/
noncomputable def scalarTwistPullbackAlongCoverIsoNatIso
    (e : 𝒰 ≅ 𝒱)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (hbself : ∀ i, b i i = 1)
    (hbcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (haself : ∀ i,
      pullbackCoverUnitAlongIso e b i i = 1)
    (hacocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover
        (pullbackCoverUnitAlongIso e b)) :
    scalarTwistFunctor
        b hbself hbcocycle ⋙
      pullbackAlongCoverIsoFunctor e ≅
    pullbackAlongCoverIsoFunctor e ⋙
      scalarTwistFunctor
        (pullbackCoverUnitAlongIso e b)
        haself hacocycle :=
  NatIso.ofComponents
    (scalarTwistPullbackAlongCoverIsoIso
      e b hbself hbcocycle haself hacocycle)
    (fun {A B} φ => by
      apply Hom.ext
      intro i
      simp only [comp_app, Functor.comp_map,
        scalarTwistPullbackAlongCoverIsoIso_hom_app,
        scalarTwistFunctor_map_app,
        pullbackAlongCoverIsoFunctor_map_app]
      exact
        (Category.comp_id
          ((pullback (e.hom.h₀ i)).map
            (φ.app (e.hom.s₀ i)))).trans
          (Category.id_comp
            ((pullback (e.hom.h₀ i)).map
              (φ.app (e.hom.s₀ i)))).symm)

/-- Version of scalar-twist naturality in which the supplied source
unit family is merely equal to the transported target family. -/
noncomputable def scalarTwistPullbackAlongCoverIsoNatIsoOfUnitsEq
    (e : 𝒰 ≅ 𝒱)
    (a : ∀ i j,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (haself : ∀ i, a i i = 1)
    (hacocycle :
      CoverUnitCocycleCondition
        𝒰.gluedCover a)
    (hbself : ∀ i, b i i = 1)
    (hbcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (hab :
      pullbackCoverUnitAlongIso e b = a) :
    scalarTwistFunctor
        b hbself hbcocycle ⋙
      pullbackAlongCoverIsoFunctor e ≅
    pullbackAlongCoverIsoFunctor e ⋙
      scalarTwistFunctor
        a haself hacocycle := by
  subst a
  exact scalarTwistPullbackAlongCoverIsoNatIso
    e b hbself hbcocycle haself hacocycle

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
