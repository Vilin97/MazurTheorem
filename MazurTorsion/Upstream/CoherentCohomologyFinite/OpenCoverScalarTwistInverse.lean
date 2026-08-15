/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistEquivalence

/-!
# Inverses of open-cover scalar twists

The inverse functor of a scalar twist is the scalar twist by the
pointwise inverse cocycle.  We record this at the transported
open-cover level.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable {D : Scheme.GlueData.{0}}

/-- Scalar-twist functors agree when their unit families agree. -/
lemma scalarTwistFunctor_eq_of_units_eq
    (a b : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (ha : ∀ i, a i i = 1)
    (hca : CoverUnitCocycleCondition D a)
    (hb : ∀ i, b i i = 1)
    (hcb : CoverUnitCocycleCondition D b)
    (hab : a = b) :
    scalarTwistFunctor a ha hca =
      scalarTwistFunctor b hb hcb := by
  subst b
  have habSelf : ha = hb := Subsingleton.elim _ _
  subst hb
  have habCocycle : hca = hcb := Subsingleton.elim _ _
  subst hcb
  rfl

end AlgebraicGeometry.Scheme.Modules.CoverDescentData

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData

variable {X : Scheme.{0}} (𝒰 : X.OpenCover)

/-- Equal cover-unit families induce naturally isomorphic transported
scalar-twist functors. -/
noncomputable def openCoverScalarTwistFunctorIsoOfUnitsEq
    (a b : ∀ i j,
      Γ((Scheme.Cover.gluedCover 𝒰).V (i, j), ⊤)ˣ)
    (ha : ∀ i, a i i = 1)
    (hca :
      CoverUnitCocycleCondition
        (Scheme.Cover.gluedCover 𝒰) a)
    (hb : ∀ i, b i i = 1)
    (hcb :
      CoverUnitCocycleCondition
        (Scheme.Cover.gluedCover 𝒰) b)
    (hab : a = b) :
    (openCoverScalarTwistEquivalence
        𝒰 a ha hca).functor ≅
      (openCoverScalarTwistEquivalence
        𝒰 b hb hcb).functor := by
  let E := modulesToGluedEquivalence 𝒰
  have hfun :
      scalarTwistFunctor a ha hca =
        scalarTwistFunctor b hb hcb :=
    scalarTwistFunctor_eq_of_units_eq
      a b ha hca hb hcb hab
  change
    (E.functor ⋙
        (restrictionFunctor ⋙
          scalarTwistFunctor a ha hca ⋙
          glueFunctor) ⋙
        E.inverse) ≅
      (E.functor ⋙
        (restrictionFunctor ⋙
          scalarTwistFunctor b hb hcb ⋙
          glueFunctor) ⋙
        E.inverse)
  rw [hfun]

/-- The inverse of a transported scalar twist is naturally the
transported twist by the pointwise inverse unit cocycle. -/
noncomputable def openCoverScalarTwistInverseFunctorIso
    (a : ∀ i j,
      Γ((Scheme.Cover.gluedCover 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition
        (Scheme.Cover.gluedCover 𝒰) a) :
    (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).inverse ≅
      (openCoverScalarTwistEquivalence
        𝒰
        (inverseCoverUnit a)
        (inverseCoverUnit_self a hself)
        (inverseCoverUnit_cocycle a hcocycle)).functor := by
  let E := modulesToGluedEquivalence 𝒰
  change
    (E.functor ⋙
        (restrictionFunctor ⋙
          scalarTwistFunctor
            (inverseCoverUnit a)
            (inverseCoverUnit_self a hself)
            (inverseCoverUnit_cocycle a hcocycle) ⋙
          glueFunctor) ⋙
        E.inverse) ≅
      (E.functor ⋙
        (restrictionFunctor ⋙
          scalarTwistFunctor
            (inverseCoverUnit a)
            (inverseCoverUnit_self a hself)
            (inverseCoverUnit_cocycle a hcocycle) ⋙
          glueFunctor) ⋙
        E.inverse)
  exact Iso.refl _

/-- If `b` is the pointwise inverse of `a`, the inverse `a`-twist
functor is naturally the `b`-twist functor. -/
noncomputable def openCoverScalarTwistInverseFunctorIsoOfUnitsEq
    (a b : ∀ i j,
      Γ((Scheme.Cover.gluedCover 𝒰).V (i, j), ⊤)ˣ)
    (ha : ∀ i, a i i = 1)
    (hca :
      CoverUnitCocycleCondition
        (Scheme.Cover.gluedCover 𝒰) a)
    (hb : ∀ i, b i i = 1)
    (hcb :
      CoverUnitCocycleCondition
        (Scheme.Cover.gluedCover 𝒰) b)
    (hab : inverseCoverUnit a = b) :
    (openCoverScalarTwistEquivalence
        𝒰 a ha hca).inverse ≅
      (openCoverScalarTwistEquivalence
        𝒰 b hb hcb).functor :=
  openCoverScalarTwistInverseFunctorIso
      𝒰 a ha hca ≪≫
    openCoverScalarTwistFunctorIsoOfUnitsEq
      𝒰
      (inverseCoverUnit a) b
      (inverseCoverUnit_self a ha)
      (inverseCoverUnit_cocycle a hca)
      hb hcb hab

end AlgebraicGeometry.Scheme.Modules
