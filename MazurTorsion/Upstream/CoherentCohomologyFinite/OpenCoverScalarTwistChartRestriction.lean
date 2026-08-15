/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistEquivalence

/-!
# Chart restrictions of open-cover scalar twists

Scalar twisting changes only the transition isomorphisms of a cover
descent datum.  Consequently, after transporting the construction back
to the covered scheme, its restriction to every chart is canonically
isomorphic to the original module's restriction.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

namespace CoverDescentData

variable {D : Scheme.GlueData.{0}}

/-- The component of an isomorphism of cover descent data on one chart. -/
noncomputable def chartIso
    {A B : CoverDescentData D} (e : A ≅ B) (i : D.J) :
    A.chart i ≅ B.chart i where
  hom := e.hom.app i
  inv := e.inv.app i
  hom_inv_id := by
    change (e.hom ≫ e.inv).app i = 𝟙 (A.chart i)
    rw [e.hom_inv_id, id_app]
  inv_hom_id := by
    change (e.inv ≫ e.hom).app i = 𝟙 (B.chart i)
    rw [e.inv_hom_id, id_app]

end CoverDescentData

open CoverDescentData

variable {X : Scheme.{0}} (𝒰 : X.OpenCover)

/--
The chart restriction of the module transported to the glued cover agrees
with pullback to the corresponding chart of the original open cover.
-/
noncomputable def modulesToGluedChartRestrictionIso
    (M : X.Modules) (i : 𝒰.I₀) :
    (pullback
      ((Scheme.Cover.gluedCover 𝒰).ι i)).obj
        ((modulesToGluedEquivalence 𝒰).functor.obj M) ≅
      (pullback (𝒰.f i)).obj M :=
  (pullback
      ((Scheme.Cover.gluedCover 𝒰).ι i)).mapIso
        ((modulesToGluedEquivalenceFunctorIso 𝒰).app M) ≪≫
    (pullbackComp
      ((Scheme.Cover.gluedCover 𝒰).ι i)
      (Scheme.Cover.fromGlued 𝒰)).app M ≪≫
    (pullbackCongr
      (Scheme.Cover.ι_fromGlued 𝒰 i)).app M

section

variable
    (a : ∀ i j,
      Γ((Scheme.Cover.gluedCover 𝒰).V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition
        (Scheme.Cover.gluedCover 𝒰) a)

/--
On every chart of an open cover, a transported scalar twist is
canonically isomorphic to the original chart restriction.
-/
noncomputable def openCoverScalarTwistChartRestrictionIso
    (M : X.Modules) (i : 𝒰.I₀) :
    (pullback (𝒰.f i)).obj
        ((openCoverScalarTwistEquivalence
          𝒰 a hself hcocycle).functor.obj M) ≅
      (pullback (𝒰.f i)).obj M := by
  let E := modulesToGluedEquivalence 𝒰
  let W := E.functor.obj M
  let G :=
    scalarTwistGluedEquivalence
      a hself hcocycle
  let N := E.inverse.obj (G.functor.obj W)
  exact
    (modulesToGluedChartRestrictionIso
      𝒰 N i).symm ≪≫
      (pullback
        ((Scheme.Cover.gluedCover 𝒰).ι i)).mapIso
          (E.counitIso.app (G.functor.obj W)) ≪≫
      chartIso
        (scalarTwistGluedRestrictionIso
          a hself hcocycle W) i ≪≫
      modulesToGluedChartRestrictionIso
        𝒰 M i

end

end AlgebraicGeometry.Scheme.Modules
