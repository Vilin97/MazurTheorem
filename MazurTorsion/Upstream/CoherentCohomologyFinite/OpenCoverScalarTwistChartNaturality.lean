/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistChartRestriction

/-!
# Natural chart trivializations for open-cover scalar twists

Scalar twisting is the identity on the chart objects of descent data.
This file packages that observation functorially and transports it
through effective descent and the canonical glued-cover equivalence.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable {D : Scheme.GlueData.{0}}

/-- Evaluate a cover descent datum on one chart. -/
def chartFunctor (i : D.J) :
    CoverDescentData D ⥤ (D.U i).Modules where
  obj A := A.chart i
  map φ := φ.app i
  map_id A := id_app A i
  map_comp φ ψ := comp_app φ ψ i

/-- Restriction of a global module followed by chart evaluation is the
usual pullback to that chart. -/
noncomputable def restrictionChartFunctorIso (i : D.J) :
    restrictionFunctor (D := D) ⋙ chartFunctor i ≅
      pullback (D.ι i) :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun _ => by rfl)

/-- Scalar twisting acts naturally as the identity after evaluating on
one chart. -/
noncomputable def scalarTwistChartFunctorIso
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i : D.J) :
    scalarTwistFunctor a hself hcocycle ⋙
        chartFunctor i ≅
      chartFunctor i :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun _ => by rfl)

/-- A globally glued scalar twist is naturally trivial after restriction
to one chart. -/
noncomputable def scalarTwistGluedChartNatIso
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i : D.J) :
    (scalarTwistGluedEquivalence
        a hself hcocycle).functor ⋙
        pullback (D.ι i) ≅
      pullback (D.ι i) :=
  Functor.isoWhiskerLeft
      (scalarTwistGluedEquivalence
        a hself hcocycle).functor
      (restrictionChartFunctorIso i).symm ≪≫
    (Functor.associator
      (scalarTwistGluedEquivalence
        a hself hcocycle).functor
      (restrictionFunctor (D := D))
      (chartFunctor i)).symm ≪≫
    Functor.isoWhiskerRight
      (scalarTwistGluedRestrictionNatIso
        a hself hcocycle)
      (chartFunctor i) ≪≫
    Functor.associator
      (restrictionFunctor (D := D))
      (scalarTwistFunctor a hself hcocycle)
      (chartFunctor i) ≪≫
    Functor.isoWhiskerLeft
      (restrictionFunctor (D := D))
      (scalarTwistChartFunctorIso
        a hself hcocycle i) ≪≫
    restrictionChartFunctorIso i

end AlgebraicGeometry.Scheme.Modules.CoverDescentData

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData

variable {X : Scheme.{0}} (𝒰 : X.OpenCover)

/-- Restricting the inverse glued-cover equivalence to an original chart
is naturally the same as restricting directly to the corresponding
glued chart. -/
noncomputable def gluedToModulesChartRestrictionNatIso
    (i : 𝒰.I₀) :
    (modulesToGluedEquivalence 𝒰).inverse ⋙
        pullback (𝒰.f i) ≅
      pullback ((Scheme.Cover.gluedCover 𝒰).ι i) :=
  Functor.isoWhiskerRight
      (gluedToModulesEquivalenceFunctorIso 𝒰)
      (pullback (𝒰.f i)) ≪≫
    pullbackComp
      (𝒰.f i) (inv 𝒰.fromGlued) ≪≫
    pullbackCongr
      (by
        have h₁ :
            𝒰.f i ≫ inv 𝒰.fromGlued =
              (((Scheme.Cover.gluedCover 𝒰).ι i ≫
                𝒰.fromGlued) ≫ inv 𝒰.fromGlued) :=
          congrArg (· ≫ inv 𝒰.fromGlued)
            (𝒰.ι_fromGlued i).symm
        have h₂ :
            (((Scheme.Cover.gluedCover 𝒰).ι i ≫
                𝒰.fromGlued) ≫ inv 𝒰.fromGlued) =
              (Scheme.Cover.gluedCover 𝒰).ι i ≫
                (𝒰.fromGlued ≫ inv 𝒰.fromGlued) :=
          Category.assoc _ _ _
        have h₃ :
            (Scheme.Cover.gluedCover 𝒰).ι i ≫
                (𝒰.fromGlued ≫ inv 𝒰.fromGlued) =
              (Scheme.Cover.gluedCover 𝒰).ι i := by
          rw [IsIso.hom_inv_id, Category.comp_id]
        exact h₁.trans (h₂.trans h₃))

/-- Restricting the forward glued-cover equivalence to a glued chart is
naturally the same as restriction to the corresponding original chart. -/
noncomputable def modulesToGluedChartRestrictionNatIso
    (i : 𝒰.I₀) :
    (modulesToGluedEquivalence 𝒰).functor ⋙
        pullback ((Scheme.Cover.gluedCover 𝒰).ι i) ≅
      pullback (𝒰.f i) :=
  Functor.isoWhiskerRight
      (modulesToGluedEquivalenceFunctorIso 𝒰)
      (pullback
        ((Scheme.Cover.gluedCover 𝒰).ι i)) ≪≫
    pullbackComp
      ((Scheme.Cover.gluedCover 𝒰).ι i)
      𝒰.fromGlued ≪≫
    pullbackCongr (𝒰.ι_fromGlued i)

/-- The scalar twist transported from an open cover is naturally
trivial on each member of that cover. -/
noncomputable def openCoverScalarTwistChartRestrictionNatIso
    (a : ∀ i j,
      Γ((Scheme.Cover.gluedCover 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition
        (Scheme.Cover.gluedCover 𝒰) a)
    (i : 𝒰.I₀) :
    (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).functor ⋙
        pullback (𝒰.f i) ≅
      pullback (𝒰.f i) := by
  let E := modulesToGluedEquivalence 𝒰
  let G :=
    scalarTwistGluedEquivalence
      a hself hcocycle
  change
    ((E.functor ⋙ G.functor) ⋙ E.inverse) ⋙
        pullback (𝒰.f i) ≅
      pullback (𝒰.f i)
  exact
    Functor.associator
        (E.functor ⋙ G.functor)
        E.inverse
        (pullback (𝒰.f i)) ≪≫
      Functor.isoWhiskerLeft
        (E.functor ⋙ G.functor)
        (gluedToModulesChartRestrictionNatIso
          𝒰 i) ≪≫
      Functor.associator
        E.functor G.functor
        (pullback
          ((Scheme.Cover.gluedCover 𝒰).ι i)) ≪≫
      Functor.isoWhiskerLeft
        E.functor
        (scalarTwistGluedChartNatIso
          a hself hcocycle i) ≪≫
      modulesToGluedChartRestrictionNatIso
        𝒰 i

end AlgebraicGeometry.Scheme.Modules
