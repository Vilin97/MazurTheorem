/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeGluedMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoGluedComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentTransport

/-!
# Pullback functor for module descent data

For an open cover and its pullback, descent data are pulled back by
first gluing globally, pulling back between the glued schemes, and then
restricting to the pulled-back cover.  We conjugate this canonical
construction by its chart comparison isomorphisms, so that its chart
objects are literally the expected pullbacks.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

private abbrev D' := gluedCover (𝒰.pullback₁ f)

/-- The chart morphism of a pulled-back cover, with its common index
exposed in the type. -/
private abbrev pullbackChartMap (i : 𝒰.I₀) :
    (𝒰.pullback₁ f).X i ⟶ 𝒰.X i :=
  𝒰.pullbackHom f i

/-- The canonical global construction underlying pullback of cover
descent data. -/
noncomputable def globalBaseChangeFunctor :
    CoverDescentData (D 𝒰) ⥤ CoverDescentData (D' 𝒰 f) :=
  glueFunctor (D := D 𝒰) ⋙
    pullback (baseChangeGluedMap 𝒰 f) ⋙
    restrictionFunctor (D := D' 𝒰 f)

/-- The canonical global construction has the expected chartwise
pullback, after reassociation and effective descent. -/
noncomputable def globalBaseChangeChartIso
    (A : CoverDescentData (D 𝒰)) (i : 𝒰.I₀) :
    ((globalBaseChangeFunctor 𝒰 f).obj A).chart i ≅
      (pullback (pullbackChartMap 𝒰 f i)).obj (A.chart i) :=
  pullbackSquareIso
      (gluedCoverChartMap (𝒰.pullback₁ f) i)
      (baseChangeGluedMap 𝒰 f)
      (pullbackChartMap 𝒰 f i)
      (gluedCoverChartMap 𝒰 i)
      (gluedCover_ι_baseChangeGluedMap 𝒰 f i)
      ((glueFunctor (D := D 𝒰)).obj A) ≪≫
    (pullback (pullbackChartMap 𝒰 f i)).mapIso
      (isoApp
        (descentGlueRestrictionIso (D := D 𝒰) A) i)

/-- Naturality of the chart comparison for the global base-change
construction. -/
theorem globalBaseChangeChartIso_naturality
    {A B : CoverDescentData (D 𝒰)}
    (φ : A ⟶ B) (i : 𝒰.I₀) :
    ((globalBaseChangeFunctor 𝒰 f).map φ).app i ≫
        (globalBaseChangeChartIso 𝒰 f B i).hom =
      (globalBaseChangeChartIso 𝒰 f A i).hom ≫
        (pullback (pullbackChartMap 𝒰 f i)).map (φ.app i) := by
  have hd :=
    congrArg (fun q => q.app i)
      (descentGlueRestrictionIso_naturality
        (D := D 𝒰) φ)
  change
    (pullback (gluedCoverChartMap (𝒰.pullback₁ f) i)).map
          ((pullback (baseChangeGluedMap 𝒰 f)).map
            ((glueFunctor (D := D 𝒰)).map φ)) ≫
        (globalBaseChangeChartIso 𝒰 f B i).hom =
      (globalBaseChangeChartIso 𝒰 f A i).hom ≫
        (pullback (pullbackChartMap 𝒰 f i)).map (φ.app i)
  let EA :=
    pullbackSquareIso
      (gluedCoverChartMap (𝒰.pullback₁ f) i)
      (baseChangeGluedMap 𝒰 f)
      (pullbackChartMap 𝒰 f i)
      (gluedCoverChartMap 𝒰 i)
      (gluedCover_ι_baseChangeGluedMap 𝒰 f i)
      ((glueFunctor (D := D 𝒰)).obj A)
  let EB :=
    pullbackSquareIso
      (gluedCoverChartMap (𝒰.pullback₁ f) i)
      (baseChangeGluedMap 𝒰 f)
      (pullbackChartMap 𝒰 f i)
      (gluedCoverChartMap 𝒰 i)
      (gluedCover_ι_baseChangeGluedMap 𝒰 f i)
      ((glueFunctor (D := D 𝒰)).obj B)
  let dA :
      (pullback (gluedCoverChartMap 𝒰 i)).obj
          ((glueFunctor (D := D 𝒰)).obj A) ≅ A.chart i :=
    isoApp (descentGlueRestrictionIso (D := D 𝒰) A) i
  let dB :
      (pullback (gluedCoverChartMap 𝒰 i)).obj
          ((glueFunctor (D := D 𝒰)).obj B) ≅ B.chart i :=
    isoApp (descentGlueRestrictionIso (D := D 𝒰) B) i
  have hs :
      (pullback (gluedCoverChartMap (𝒰.pullback₁ f) i)).map
            ((pullback (baseChangeGluedMap 𝒰 f)).map
              ((glueFunctor (D := D 𝒰)).map φ)) ≫
          EB.hom =
        EA.hom ≫
          (pullback (pullbackChartMap 𝒰 f i)).map
            ((pullback (gluedCoverChartMap 𝒰 i)).map
              ((glueFunctor (D := D 𝒰)).map φ)) :=
    pullbackSquareIso_naturality
      (gluedCoverChartMap (𝒰.pullback₁ f) i)
      (baseChangeGluedMap 𝒰 f)
      (pullbackChartMap 𝒰 f i)
      (gluedCoverChartMap 𝒰 i)
      (gluedCover_ι_baseChangeGluedMap 𝒰 f i)
      ((glueFunctor (D := D 𝒰)).map φ)
  have hd' :
      (pullback (gluedCoverChartMap 𝒰 i)).map
            ((glueFunctor (D := D 𝒰)).map φ) ≫
          dB.hom =
        dA.hom ≫ φ.app i := by
    change
      (pullback (gluedCoverChartMap 𝒰 i)).map
            ((glueFunctor (D := D 𝒰)).map φ) ≫
          (descentGlueRestrictionIso (D := D 𝒰) B).hom.app i =
        (descentGlueRestrictionIso (D := D 𝒰) A).hom.app i ≫
          φ.app i at hd
    exact hd
  change
    (pullback (gluedCoverChartMap (𝒰.pullback₁ f) i)).map
          ((pullback (baseChangeGluedMap 𝒰 f)).map
            ((glueFunctor (D := D 𝒰)).map φ)) ≫
        (EB ≪≫ (pullback (pullbackChartMap 𝒰 f i)).mapIso dB).hom =
      (EA ≪≫
          (pullback (pullbackChartMap 𝒰 f i)).mapIso dA).hom ≫
        (pullback (pullbackChartMap 𝒰 f i)).map (φ.app i)
  simp only [Iso.trans_hom]
  calc
    _ = (EA.hom ≫
          (pullback (pullbackChartMap 𝒰 f i)).map
            ((pullback (gluedCoverChartMap 𝒰 i)).map
              ((glueFunctor (D := D 𝒰)).map φ))) ≫
        (pullback (pullbackChartMap 𝒰 f i)).map dB.hom :=
      congrArg
        (fun z => z ≫
          (pullback (pullbackChartMap 𝒰 f i)).map dB.hom) hs
    _ = EA.hom ≫
        (pullback (pullbackChartMap 𝒰 f i)).map
            ((pullback (gluedCoverChartMap 𝒰 i)).map
              ((glueFunctor (D := D 𝒰)).map φ) ≫
            dB.hom) := by
      calc
        _ = EA.hom ≫
            ((pullback (pullbackChartMap 𝒰 f i)).map
                ((pullback (gluedCoverChartMap 𝒰 i)).map
                  ((glueFunctor (D := D 𝒰)).map φ) ) ≫
              (pullback (pullbackChartMap 𝒰 f i)).map dB.hom) :=
          Category.assoc _ _ _
        _ = _ :=
          congrArg
            (fun z => EA.hom ≫ z)
            ((pullback (pullbackChartMap 𝒰 f i)).map_comp
              ((pullback (gluedCoverChartMap 𝒰 i)).map
                ((glueFunctor (D := D 𝒰)).map φ))
              dB.hom).symm
    _ = EA.hom ≫
        (pullback (pullbackChartMap 𝒰 f i)).map
          (dA.hom ≫ φ.app i) :=
      congrArg
        (fun z => EA.hom ≫
          (pullback (pullbackChartMap 𝒰 f i)).map z) hd'
    _ = _ := by
      let P := pullback (pullbackChartMap 𝒰 f i)
      let α : A.chart i ⟶ B.chart i := φ.app i
      have hmap :
          P.map (dA.hom ≫ α) =
            P.map dA.hom ≫ P.map α :=
        P.map_comp dA.hom α
      calc
        EA.hom ≫ P.map (dA.hom ≫ α) =
            EA.hom ≫ (P.map dA.hom ≫ P.map α) :=
          congrArg (fun z => EA.hom ≫ z) hmap
        _ = (EA.hom ≫ P.map dA.hom) ≫ P.map α :=
          (Category.assoc _ _ _).symm

/-- Pullback of descent data, with literal chart objects. -/
noncomputable def baseChangeObject
    (A : CoverDescentData (D 𝒰)) :
    CoverDescentData (D' 𝒰 f) :=
  transport
    ((globalBaseChangeFunctor 𝒰 f).obj A)
    (fun i =>
      (pullback (pullbackChartMap 𝒰 f i)).obj (A.chart i))
    (globalBaseChangeChartIso 𝒰 f A)

/-- Pullback of module descent data along a base-changed open cover. -/
noncomputable def baseChangeFunctor :
    CoverDescentData (D 𝒰) ⥤ CoverDescentData (D' 𝒰 f) :=
  (globalBaseChangeFunctor 𝒰 f).copyObj
    (baseChangeObject 𝒰 f)
    (fun A =>
      transportIso
        ((globalBaseChangeFunctor 𝒰 f).obj A)
        (fun i =>
          (pullback (pullbackChartMap 𝒰 f i)).obj (A.chart i))
        (globalBaseChangeChartIso 𝒰 f A))

@[simp]
theorem baseChangeObject_chart
    (A : CoverDescentData (D 𝒰)) (i : 𝒰.I₀) :
    (baseChangeObject 𝒰 f A).chart i =
      (pullback (pullbackChartMap 𝒰 f i)).obj (A.chart i) :=
  rfl

@[simp]
theorem baseChangeFunctor_obj_chart
    (A : CoverDescentData (D 𝒰)) (i : 𝒰.I₀) :
    ((baseChangeFunctor 𝒰 f).obj A).chart i =
      (pullback (pullbackChartMap 𝒰 f i)).obj (A.chart i) :=
  rfl

/-- On chart morphisms, the base-change functor is literal pullback. -/
@[simp]
theorem baseChangeFunctor_map_app
    {A B : CoverDescentData (D 𝒰)}
    (φ : A ⟶ B) (i : 𝒰.I₀) :
    ((baseChangeFunctor 𝒰 f).map φ).app i =
      (pullback (pullbackChartMap 𝒰 f i)).map (φ.app i) := by
  change
    (globalBaseChangeChartIso 𝒰 f A i).inv ≫
          ((globalBaseChangeFunctor 𝒰 f).map φ).app i ≫
        (globalBaseChangeChartIso 𝒰 f B i).hom =
      (pullback (pullbackChartMap 𝒰 f i)).map (φ.app i)
  rw [globalBaseChangeChartIso_naturality]
  let E := globalBaseChangeChartIso 𝒰 f A i
  let P := pullback (pullbackChartMap 𝒰 f i)
  let α : A.chart i ⟶ B.chart i := φ.app i
  simpa only [Category.assoc] using
    E.inv_hom_id_assoc (P.map α)

/-- The global glue-pullback-restrict construction is naturally
isomorphic to the literal-chart base-change functor. -/
noncomputable def globalBaseChangeNatIso :
    globalBaseChangeFunctor 𝒰 f ≅ baseChangeFunctor 𝒰 f :=
  Functor.isoCopyObj
    (globalBaseChangeFunctor 𝒰 f)
    (baseChangeObject 𝒰 f)
    (fun A =>
      transportIso
        ((globalBaseChangeFunctor 𝒰 f).obj A)
        (fun i =>
          (pullback (pullbackChartMap 𝒰 f i)).obj (A.chart i))
        (globalBaseChangeChartIso 𝒰 f A))

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
