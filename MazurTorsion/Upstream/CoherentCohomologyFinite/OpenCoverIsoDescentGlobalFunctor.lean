/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentScalarNaturality

/-!
# Global realization of descent pullback along a cover isomorphism

The literal-chart descent pullback functor is naturally the composite
which glues on the target cover, pulls back between the glued schemes,
and restricts to the source cover.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Glue, pull back between the glued schemes, and restrict. -/
noncomputable def coverIsoGlobalFunctor
    (e : 𝒰 ≅ 𝒱) :
    CoverDescentData 𝒱.gluedCover ⥤
      CoverDescentData 𝒰.gluedCover :=
  glueFunctor (D := 𝒱.gluedCover) ⋙
    pullback (coverIsoGluedIso e).hom ⋙
    restrictionFunctor (D := 𝒰.gluedCover)

/-- Naturality of the canonical chart comparison before applying the
effective-descent counit. -/
theorem coverIsoCanonicalChartIso_naturality
    (e : 𝒰 ≅ 𝒱)
    {W Z : 𝒱.gluedCover.glued.Modules}
    (φ : W ⟶ Z) (i : 𝒰.I₀) :
    (pullback (𝒰.gluedCover.ι i)).map
          ((pullback (coverIsoGluedIso e).hom).map φ) ≫
        (coverIsoCanonicalChartIso e Z i).hom =
      (coverIsoCanonicalChartIso e W i).hom ≫
        (pullback (e.hom.h₀ i)).map
          ((pullback
            (𝒱.gluedCover.ι
              (e.hom.s₀ i))).map φ) := by
  exact
    pullbackSquareIso_naturality
      (𝒰.gluedCover.ι i)
      (coverIsoGluedIso e).hom
      (e.hom.h₀ i)
      (𝒱.gluedCover.ι (e.hom.s₀ i))
      (gluedCover_ι_coverIsoGluedIso_hom e i)
      φ

/-- Naturality of the chart comparison for the global cover-isomorphism
construction. -/
theorem coverIsoRestrictionChartIso_naturality
    (e : 𝒰 ≅ 𝒱)
    {A B : CoverDescentData 𝒱.gluedCover}
    (φ : A ⟶ B) (i : 𝒰.I₀) :
    ((coverIsoGlobalFunctor e).map φ).app i ≫
        (coverIsoRestrictionChartIso e B i).hom =
      (coverIsoRestrictionChartIso e A i).hom ≫
        (pullback (e.hom.h₀ i)).map
          (φ.app (e.hom.s₀ i)) := by
  let jV : 𝒱.gluedCover.J := e.hom.s₀ i
  have hd :=
    congrArg
      (fun q => q.app jV)
      (descentGlueRestrictionIso_naturality
        (D := 𝒱.gluedCover) φ)
  let EA :=
    coverIsoCanonicalChartIso e
      ((glueFunctor (D := 𝒱.gluedCover)).obj A) i
  let EB :=
    coverIsoCanonicalChartIso e
      ((glueFunctor (D := 𝒱.gluedCover)).obj B) i
  let dA :=
    isoApp
      (descentGlueRestrictionIso
        (D := 𝒱.gluedCover) A)
      jV
  let dB :=
    isoApp
      (descentGlueRestrictionIso
        (D := 𝒱.gluedCover) B)
      jV
  have hs :
      (pullback (𝒰.gluedCover.ι i)).map
            ((pullback
              (coverIsoGluedIso e).hom).map
              ((glueFunctor
                (D := 𝒱.gluedCover)).map φ)) ≫
          EB.hom =
        EA.hom ≫
          (pullback (e.hom.h₀ i)).map
            ((pullback
              (𝒱.gluedCover.ι
                jV)).map
              ((glueFunctor
                (D := 𝒱.gluedCover)).map φ)) :=
    coverIsoCanonicalChartIso_naturality
      e
      ((glueFunctor
        (D := 𝒱.gluedCover)).map φ)
      i
  have hd' :
      (pullback
          (𝒱.gluedCover.ι
            jV)).map
            ((glueFunctor
              (D := 𝒱.gluedCover)).map φ) ≫
          dB.hom =
        dA.hom ≫ φ.app jV := by
    change
      (pullback
          (𝒱.gluedCover.ι jV)).map
            ((glueFunctor
              (D := 𝒱.gluedCover)).map φ) ≫
          dB.hom =
        dA.hom ≫ φ.app jV at hd
    exact hd
  let p :=
    (pullback (𝒰.gluedCover.ι i)).map
      ((pullback (coverIsoGluedIso e).hom).map
        ((glueFunctor (D := 𝒱.gluedCover)).map φ))
  let q :=
    (pullback (e.hom.h₀ i)).map
      ((pullback (𝒱.gluedCover.ι jV)).map
        ((glueFunctor (D := 𝒱.gluedCover)).map φ))
  let a := (pullback (e.hom.h₀ i)).map dA.hom
  let b := (pullback (e.hom.h₀ i)).map dB.hom
  let t := (pullback (e.hom.h₀ i)).map (φ.app jV)
  change p ≫ (EB.hom ≫ b) = (EA.hom ≫ a) ≫ t
  change p ≫ EB.hom = EA.hom ≫ q at hs
  have hsq :
      (p ≫ EB.hom) ≫ b = (EA.hom ≫ q) ≫ b :=
    congrArg (fun z => z ≫ b) hs
  have h₁ :
      p ≫ (EB.hom ≫ b) = (p ≫ EB.hom) ≫ b :=
    (Category.assoc p EB.hom b).symm
  have h₂ :
      (EA.hom ≫ q) ≫ b = EA.hom ≫ (q ≫ b) :=
    Category.assoc EA.hom q b
  have h₃ :
      EA.hom ≫ (q ≫ b) =
        EA.hom ≫
          (pullback (e.hom.h₀ i)).map
            (((pullback (𝒱.gluedCover.ι jV)).map
                ((glueFunctor (D := 𝒱.gluedCover)).map φ)) ≫
              dB.hom) := by
    apply congrArg (fun z => EA.hom ≫ z)
    exact ((pullback (e.hom.h₀ i)).map_comp
      ((pullback (𝒱.gluedCover.ι jV)).map
        ((glueFunctor (D := 𝒱.gluedCover)).map φ))
      dB.hom).symm
  have h₄ :
      EA.hom ≫
          (pullback (e.hom.h₀ i)).map
            (((pullback (𝒱.gluedCover.ι jV)).map
                ((glueFunctor (D := 𝒱.gluedCover)).map φ)) ≫
              dB.hom) =
        EA.hom ≫
          (pullback (e.hom.h₀ i)).map
            (dA.hom ≫ φ.app jV) :=
    congrArg
      (fun z => EA.hom ≫
        (pullback (e.hom.h₀ i)).map z)
      hd'
  have h₅ :
      EA.hom ≫
          (pullback (e.hom.h₀ i)).map
            (dA.hom ≫ φ.app jV) =
        EA.hom ≫ (a ≫ t) := by
    apply congrArg (fun z => EA.hom ≫ z)
    exact (pullback (e.hom.h₀ i)).map_comp
      dA.hom (φ.app jV)
  have h₆ :
      EA.hom ≫ (a ≫ t) = (EA.hom ≫ a) ≫ t :=
    (Category.assoc EA.hom a t).symm
  exact h₁.trans <| hsq.trans <| h₂.trans <|
    h₃.trans <| h₄.trans <| h₅.trans h₆

/-- The global glue-pullback-restrict construction is naturally
isomorphic to the literal-chart descent pullback functor. -/
noncomputable def coverIsoGlobalNatIso
    (e : 𝒰 ≅ 𝒱) :
    coverIsoGlobalFunctor e ≅
      pullbackAlongCoverIsoFunctor e :=
  NatIso.ofComponents
    (coverIsoRestrictionTransportIso e)
    (fun {A B} φ => by
      apply Hom.ext
      intro i
      exact
        coverIsoRestrictionChartIso_naturality
          e φ i)

/-- Restriction identifies geometric pullback between the glued schemes
with descent pullback along the cover isomorphism. -/
noncomputable def restrictionCoverIsoNatIso
    (e : 𝒰 ≅ 𝒱) :
    pullback (coverIsoGluedIso e).hom ⋙
        restrictionFunctor (D := 𝒰.gluedCover) ≅
      restrictionFunctor (D := 𝒱.gluedCover) ⋙
        pullbackAlongCoverIsoFunctor e :=
  (pullback (coverIsoGluedIso e).hom ⋙
      restrictionFunctor
        (D := 𝒰.gluedCover)).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight
      (restrictionGlueIso
        (D := 𝒱.gluedCover))
      (pullback (coverIsoGluedIso e).hom ⋙
        restrictionFunctor
          (D := 𝒰.gluedCover)) ≪≫
    Functor.associator
      (restrictionFunctor
        (D := 𝒱.gluedCover))
      (glueFunctor (D := 𝒱.gluedCover))
      (pullback (coverIsoGluedIso e).hom ⋙
        restrictionFunctor
          (D := 𝒰.gluedCover)) ≪≫
    Functor.isoWhiskerLeft
      (restrictionFunctor
        (D := 𝒱.gluedCover))
      (Functor.associator
        (glueFunctor (D := 𝒱.gluedCover))
        (pullback (coverIsoGluedIso e).hom)
        (restrictionFunctor
          (D := 𝒰.gluedCover))).symm ≪≫
    Functor.isoWhiskerLeft
      (restrictionFunctor
        (D := 𝒱.gluedCover))
      (coverIsoGlobalNatIso e)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
