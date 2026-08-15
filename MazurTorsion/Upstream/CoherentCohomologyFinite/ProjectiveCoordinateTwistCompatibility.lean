/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCoordinateChartFunction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenOverlapTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeOpenImmersionTopSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistNaturalTransformation

/-!
# Compatibility of projective coordinate functions with Serre twisting

The chart expressions `(Xᵣ / Xⱼ)^N` transform by the degree-`N` Serre
unit cocycle.  This file first names the canonical comparison between
sections on a scheme-theoretic chart overlap and sections on the
corresponding ambient intersection.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

local instance coordinateTwistStandardCoverComponentIsOpenImmersion
    (i : Fin (d + 1)) : IsOpenImmersion ((cover k d).f i) :=
  (cover k d).map_prop i

/--
The ambient chart inclusion, with its source written in the indexing
used by the standard-cover glue datum.
-/
def glueChartMap
    (i : Fin (d + 1)) :
    (standardChart k i).toScheme ⟶ scheme k d :=
  (standardChart k i).ι

instance glueChartMap_isOpenImmersion
    (i : Fin (d + 1)) :
    IsOpenImmersion (glueChartMap k d i) := by
  unfold glueChartMap
  exact (cover k d).map_prop i

@[simp]
lemma standardCoverMap_opensRange
    (i : Fin (d + 1)) :
    ((cover k d).f i).opensRange =
      standardChart k i := by
  unfold cover
  apply TopologicalSpace.Opens.ext
  exact Scheme.Opens.range_ι (standardChart k i)

/--
Sections on the scheme-theoretic pair overlap are canonically sections
on the corresponding intersection of standard opens.
-/
def pairOverlapTopSectionsIso
    (i j : Fin (d + 1)) :
    Γ(typedIntegerPairOverlapScheme k d i j, ⊤) ≅
      Γ(scheme k d,
        standardChart k j ⊓ standardChart k i) :=
  ((integerPairOverlapMap k d i j).appIso ⊤).symm ≪≫
    eqToIso
      (congrArg
        (fun U => Γ(scheme k d, U))
        (by
          rw [Scheme.Hom.image_top_eq_opensRange]
          rw [integerPairOverlapMap_opensRange]
          exact inf_comm _ _))

@[simp]
lemma pairOverlapTopSectionsIso_hom
    (i j : Fin (d + 1))
    (x : Γ(typedIntegerPairOverlapScheme k d i j, ⊤)) :
    (pairOverlapTopSectionsIso k d i j).hom x =
      (eqToIso
        (congrArg
          (fun U => Γ(scheme k d, U))
          (by
            rw [Scheme.Hom.image_top_eq_opensRange]
            rw [integerPairOverlapMap_opensRange]
            exact inf_comm _ _))).hom
        (((integerPairOverlapMap k d i j).appIso ⊤).inv x) :=
  rfl

/--
Under the pair-overlap comparison, pulling a function from the first
chart is ordinary restriction of its ambient chart section.
-/
lemma pairOverlapTopSectionsIso_firstChart
    (i j : Fin (d + 1))
    (s : Γ(scheme k d, standardChart k i)) :
    (pairOverlapTopSectionsIso k d i j).hom
        ((typedIntegerFirstOverlapMap k d i j).appTop
          ((standardChart k i).topIso.inv s)) =
      (scheme k d).presheaf.map
        (homOfLE
          (show
            standardChart k j ⊓ standardChart k i ≤
              standardChart k i
            from inf_le_right)).op s := by
  letI hp : IsOpenImmersion
      (typedIntegerFirstOverlapMap k d i j) :=
    typedIntegerFirstOverlapMap_isOpenImmersion k d i j
  letI hq : IsOpenImmersion (glueChartMap k d i) :=
    glueChartMap_isOpenImmersion k d i
  letI : IsOpenImmersion
      (typedIntegerFirstOverlapMap k d i j ≫ glueChartMap k d i) :=
    @IsOpenImmersion.comp _ _ _ _ _ hp hq
  let hTop :
      integerPairOverlapMap k d i j ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
        standardChart k j ⊓ standardChart k i := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      integerPairOverlapMap_opensRange]
    exact inf_comm _ _
  let hP :
      typedIntegerFirstOverlapMap k d i j ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
        (typedIntegerFirstOverlapMap k d i j).opensRange :=
    Scheme.Hom.image_top_eq_opensRange
      (typedIntegerFirstOverlapMap k d i j)
  let hQ :
      glueChartMap k d i ''ᵁ
          (typedIntegerFirstOverlapMap k d i j).opensRange =
        standardChart k j ⊓ standardChart k i := by
    calc
      glueChartMap k d i ''ᵁ
          (typedIntegerFirstOverlapMap k d i j).opensRange =
          glueChartMap k d i ''ᵁ
            (typedIntegerFirstOverlapMap k d i j ''ᵁ ⊤) := by
        rw [Scheme.Hom.image_top_eq_opensRange]
      _ = (typedIntegerFirstOverlapMap k d i j ≫
          glueChartMap k d i) ''ᵁ ⊤ :=
        (Scheme.Hom.comp_image
          (typedIntegerFirstOverlapMap k d i j)
          (glueChartMap k d i) ⊤).symm
      _ = standardChart k j ⊓ standardChart k i := hTop
  change
    (eqToIso
      (congrArg
        (fun U => Γ(scheme k d, U)) hTop)).hom
      (((typedIntegerFirstOverlapMap k d i j ≫
          glueChartMap k d i).appIso ⊤).inv
        ((typedIntegerFirstOverlapMap k d i j).appTop
          ((standardChart k i).topIso.inv s))) =
      _
  rw [← presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom hTop]
  have hcomp :=
    appIso_inv_comp_transport_open
      (typedIntegerFirstOverlapMap k d i j) (glueChartMap k d i)
      ⊤ (typedIntegerFirstOverlapMap k d i j).opensRange
      (standardChart k j ⊓ standardChart k i)
      hP hQ hTop
      ((typedIntegerFirstOverlapMap k d i j).appTop
        ((standardChart k i).topIso.inv s))
  calc
    _ = _ := hcomp.symm
    _ = _ := by
      rw [openImmersion_appIso_inv_appTop]
      have hrestriction :
          ((standardChart k i).toScheme.presheaf.mapIso
              (eqToIso hP).op).inv.hom
            (((standardChart k i).toScheme.presheaf.map
                (homOfLE
                  (show
                    typedIntegerFirstOverlapMap k d i j ''ᵁ
                        (⊤ :
                          (typedIntegerPairOverlapScheme k d i j).Opens) ≤
                      (⊤ : (standardChart k i).toScheme.Opens)
                    from le_top)).op).hom
              ((standardChart k i).topIso.inv.hom s)) =
            (((standardChart k i).toScheme.presheaf.map
                (homOfLE
                  (show
                    (typedIntegerFirstOverlapMap k d i j).opensRange ≤
                      (⊤ : (standardChart k i).toScheme.Opens)
                    from le_top)).op).hom
              ((standardChart k i).topIso.inv.hom s)) := by
        simpa using
          (presheafMapIsoSymm_restriction
            (X := (standardChart k i).toScheme)
            (eI := rfl)
            (eJ := hP)
            (hA :=
              (show
                typedIntegerFirstOverlapMap k d i j ''ᵁ
                    (⊤ :
                      (typedIntegerPairOverlapScheme k d i j).Opens) ≤
                  (⊤ : (standardChart k i).toScheme.Opens)
                from le_top))
            (hU :=
              (show
                (typedIntegerFirstOverlapMap k d i j).opensRange ≤
                  (⊤ : (standardChart k i).toScheme.Opens)
                from le_top))
            ((standardChart k i).topIso.inv s))
      rw [hrestriction]
      rw [appIso_inv_restriction]
      have hchart :
          (((glueChartMap k d i).appIso ⊤).inv
            ((standardChart k i).topIso.inv s)) =
            (eqToIso
              (congrArg
                (fun U => Γ(scheme k d, U))
                (standardChart k i).ι_image_top)).inv s := by
        change
          (((standardChart k i).ι.appIso ⊤).inv
            ((standardChart k i).topIso.inv s)) =
            _
        let E :=
          eqToIso
            (congrArg
              (fun U => Γ(scheme k d, U))
              (standardChart k i).ι_image_top)
        have hx :
            E.hom
                (((standardChart k i).ι.appIso ⊤).inv
                  ((standardChart k i).topIso.inv s)) =
              s :=
          opens_ι_appIso_inv_topIso_inv_transport_open
            (standardChart k i) s
        exact
          (E.hom_inv_id_apply _).symm.trans
            (congrArg E.inv.hom hx)
      rw [hchart]
      have hfinal :=
        presheafMapIsoSymm_restriction
          (X := scheme k d)
          (eI := (standardChart k i).ι_image_top)
          (eJ := hQ)
          (hA :=
            Scheme.Hom.image_mono
              (glueChartMap k d i)
              (show
                (typedIntegerFirstOverlapMap k d i j).opensRange ≤
                  (⊤ : (standardChart k i).toScheme.Opens)
                from le_top))
          (hU :=
            (show
              standardChart k j ⊓ standardChart k i ≤
                standardChart k i
              from inf_le_right))
          ((eqToIso
            (congrArg
              (fun U => Γ(scheme k d, U))
              (standardChart k i).ι_image_top)).inv s)
      have hcancel :
          ((scheme k d).presheaf.mapIso
              (eqToIso
                (standardChart k i).ι_image_top).op).inv.hom
              ((eqToIso
                (congrArg
                  (fun U => Γ(scheme k d, U))
                  (standardChart k i).ι_image_top)).inv s) =
            s := by
        rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom]
        exact
          (eqToIso
            (congrArg
              (fun U => Γ(scheme k d, U))
              (standardChart k i).ι_image_top)).inv_hom_id_apply s
      rw [hcancel] at hfinal
      exact hfinal

/--
The second overlap projection, with its codomain written in the glue
datum's chart indexing.
-/
def glueSecondOverlapMap
    (i j : Fin (d + 1)) :
    typedIntegerPairOverlapScheme k d i j ⟶
      (standardChart k j).toScheme :=
  typedIntegerSecondOverlapMap k d i j

instance glueSecondOverlapMap_isOpenImmersion
    (i j : Fin (d + 1)) :
    IsOpenImmersion (glueSecondOverlapMap k d i j) := by
  unfold glueSecondOverlapMap
  infer_instance

/--
Under the pair-overlap comparison, pulling a function from the second
chart is ordinary restriction of its ambient chart section.
-/
lemma pairOverlapTopSectionsIso_secondChart
    (i j : Fin (d + 1))
    (s : Γ(scheme k d, standardChart k j)) :
    (pairOverlapTopSectionsIso k d i j).hom
        ((glueSecondOverlapMap k d i j).appTop
          ((standardChart k j).topIso.inv s)) =
      (scheme k d).presheaf.map
        (homOfLE
          (show
            standardChart k j ⊓ standardChart k i ≤
              standardChart k j
            from inf_le_left)).op s := by
  letI hp :
      IsOpenImmersion (glueSecondOverlapMap k d i j) :=
    glueSecondOverlapMap_isOpenImmersion k d i j
  letI hq : IsOpenImmersion (glueChartMap k d j) :=
    glueChartMap_isOpenImmersion k d j
  letI : IsOpenImmersion
      (glueSecondOverlapMap k d i j ≫
        glueChartMap k d j) :=
    @IsOpenImmersion.comp _ _ _ _ _ hp hq
  let hMap :
      glueSecondOverlapMap k d i j ≫
          glueChartMap k d j =
        integerPairOverlapMap k d i j := by
    change typedIntegerSecondOverlapMap k d i j ≫
        (standardChart k j).ι = integerPairOverlapMap k d i j
    exact cover_glue_condition k d i j
  let hTop :
      integerPairOverlapMap k d i j ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
        standardChart k j ⊓ standardChart k i := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      integerPairOverlapMap_opensRange]
    exact inf_comm _ _
  let hSecondTop :
      (glueSecondOverlapMap k d i j ≫
          glueChartMap k d j) ''ᵁ
            (⊤ :
              (typedIntegerPairOverlapScheme k d i j).Opens) =
        standardChart k j ⊓ standardChart k i := by
    simpa only [hMap] using hTop
  let hP :
      glueSecondOverlapMap k d i j ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
        (glueSecondOverlapMap k d i j).opensRange :=
    Scheme.Hom.image_top_eq_opensRange
      (glueSecondOverlapMap k d i j)
  let hQ :
      glueChartMap k d j ''ᵁ
          (glueSecondOverlapMap k d i j).opensRange =
        standardChart k j ⊓ standardChart k i := by
    calc
      glueChartMap k d j ''ᵁ
          (glueSecondOverlapMap k d i j).opensRange =
          glueChartMap k d j ''ᵁ
            (glueSecondOverlapMap k d i j ''ᵁ ⊤) := by
        rw [Scheme.Hom.image_top_eq_opensRange]
      _ = (glueSecondOverlapMap k d i j ≫
          glueChartMap k d j) ''ᵁ ⊤ :=
        (Scheme.Hom.comp_image
          (glueSecondOverlapMap k d i j)
          (glueChartMap k d j) ⊤).symm
      _ = standardChart k j ⊓ standardChart k i := hSecondTop
  rw [pairOverlapTopSectionsIso_hom]
  rw [← presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom hTop]
  have hcongr :=
    appIso_inv_congr_transport_open
      hMap
      (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens)
      (standardChart k j ⊓ standardChart k i)
      hSecondTop hTop
      ((glueSecondOverlapMap k d i j).appTop
        ((standardChart k j).topIso.inv s))
  have hcomp :=
    appIso_inv_comp_transport_open
      (glueSecondOverlapMap k d i j)
      (glueChartMap k d j)
      ⊤
      (glueSecondOverlapMap k d i j).opensRange
      (standardChart k j ⊓ standardChart k i)
      hP hQ hSecondTop
      ((glueSecondOverlapMap k d i j).appTop
        ((standardChart k j).topIso.inv s))
  calc
    _ = ((scheme k d).presheaf.mapIso
          (eqToIso hSecondTop).op).inv.hom
        ((((glueSecondOverlapMap k d i j ≫
            glueChartMap k d j).appIso ⊤).inv.hom
          ((glueSecondOverlapMap k d i j).appTop
            ((standardChart k j).topIso.inv s)))) :=
      hcongr.symm
    _ = _ := hcomp.symm
    _ = _ := by
      rw [openImmersion_appIso_inv_appTop]
      have hrestriction :
          ((standardChart k j).toScheme.presheaf.mapIso
              (eqToIso hP).op).inv.hom
            (((standardChart k j).toScheme.presheaf.map
                (homOfLE
                  (show
                    glueSecondOverlapMap k d i j ''ᵁ
                        (⊤ :
                          (typedIntegerPairOverlapScheme k d i j).Opens) ≤
                      (⊤ : (standardChart k j).toScheme.Opens)
                    from le_top)).op).hom
              ((standardChart k j).topIso.inv.hom s)) =
            (((standardChart k j).toScheme.presheaf.map
                (homOfLE
                  (show
                    (glueSecondOverlapMap
                        k d i j).opensRange ≤
                      (⊤ : (standardChart k j).toScheme.Opens)
                    from le_top)).op).hom
              ((standardChart k j).topIso.inv.hom s)) := by
        simpa using
          (presheafMapIsoSymm_restriction
            (X := (standardChart k j).toScheme)
            (eI := rfl)
            (eJ := hP)
            (hA :=
              (show
                glueSecondOverlapMap k d i j ''ᵁ
                    (⊤ :
                      (typedIntegerPairOverlapScheme k d i j).Opens) ≤
                  (⊤ : (standardChart k j).toScheme.Opens)
                from le_top))
            (hU :=
              (show
                (glueSecondOverlapMap
                    k d i j).opensRange ≤
                  (⊤ : (standardChart k j).toScheme.Opens)
                from le_top))
            ((standardChart k j).topIso.inv s))
      rw [hrestriction]
      rw [appIso_inv_restriction]
      have hchart :
          (((glueChartMap k d j).appIso ⊤).inv
            ((standardChart k j).topIso.inv s)) =
            (eqToIso
              (congrArg
                (fun U => Γ(scheme k d, U))
                (standardChart k j).ι_image_top)).inv s := by
        change
          (((standardChart k j).ι.appIso ⊤).inv
            ((standardChart k j).topIso.inv s)) =
            _
        let E :=
          eqToIso
            (congrArg
              (fun U => Γ(scheme k d, U))
              (standardChart k j).ι_image_top)
        have hx :
            E.hom
                (((standardChart k j).ι.appIso ⊤).inv
                  ((standardChart k j).topIso.inv s)) =
              s :=
          opens_ι_appIso_inv_topIso_inv_transport_open
            (standardChart k j) s
        exact
          (E.hom_inv_id_apply _).symm.trans
            (congrArg E.inv.hom hx)
      rw [hchart]
      have hfinal :=
        presheafMapIsoSymm_restriction
          (X := scheme k d)
          (eI := (standardChart k j).ι_image_top)
          (eJ := hQ)
          (hA :=
            Scheme.Hom.image_mono
              (glueChartMap k d j)
              (show
                (glueSecondOverlapMap
                    k d i j).opensRange ≤
                  (⊤ : (standardChart k j).toScheme.Opens)
                from le_top))
          (hU :=
            (show
              standardChart k j ⊓ standardChart k i ≤
                standardChart k j
              from inf_le_left))
          ((eqToIso
            (congrArg
              (fun U => Γ(scheme k d, U))
              (standardChart k j).ι_image_top)).inv s)
      have hcancel :
          ((scheme k d).presheaf.mapIso
              (eqToIso
                (standardChart k j).ι_image_top).op).inv.hom
              ((eqToIso
                (congrArg
                  (fun U => Γ(scheme k d, U))
                  (standardChart k j).ι_image_top)).inv s) =
            s := by
        rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom]
        exact
          (eqToIso
            (congrArg
              (fun U => Γ(scheme k d, U))
              (standardChart k j).ι_image_top)).inv_hom_id_apply s
      rw [hcancel] at hfinal
      exact hfinal

/--
The Serre overlap unit becomes the coordinate ratio `Xᵢ / Xⱼ` under
the canonical pair-overlap section comparison.
-/
lemma pairOverlapTopSectionsIso_overlapUnit
    (i j : Fin (d + 1)) :
    (pairOverlapTopSectionsIso k d i j).hom
        (overlapUnit k d i j).val =
      chartScalarOnPair k d i j
        (chartRatioElement k d i j) := by
  let hInf :
      integerPairOverlapMap k d i j ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
        standardChart k j ⊓ standardChart k i := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      integerPairOverlapMap_opensRange]
    exact inf_comm _ _
  let hProduct :
      integerPairOverlapMap k d i j ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j) :=
    integerPairOverlapMap_image_top_product_open
      k d i j
  let hB :
      standardChart k j ⊓ standardChart k i =
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j) :=
    standardChart_inf_eq_productBasicOpen
      k d i j
  let EInf :=
    eqToIso
      (congrArg
        (fun U => Γ(scheme k d, U)) hInf)
  let EB :=
    eqToIso
      (congrArg
        (fun U => Γ(scheme k d, U)) hB)
  let EProduct :=
    eqToIso
      (congrArg
        (fun U => Γ(scheme k d, U)) hProduct)
  let x :=
    ((integerPairOverlapMap k d i j).appIso ⊤).inv
      (overlapRingHom k d i j
        (awayFraction k d i j))
  let w :=
    Proj.awayToSection (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
      (awayFraction k d i j)
  have haway :
      EProduct.hom x = w := by
    dsimp only [EProduct, x, w]
    rw [← presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom]
    exact
      overlapRingHomAmbientPairSection_eq_away_open
        k d i j (awayFraction k d i j)
  have htransport :
      EB.hom (EInf.hom x) = w := by
    calc
      _ =
          (eqToIso
            (congrArg
              (fun U => Γ(scheme k d, U))
              (hInf.trans hB))).hom x := by
        exact
          ConcreteCategory.congr_hom
            (Γ_eqToIso_hom_trans hInf hB) x
      _ = EProduct.hom x := by
        congr 1
      _ = w := haway
  have hpair :=
    pairOverlapTopSectionsIso_hom k d i j
      ((overlapUnit k d i j).val :
        Γ(typedIntegerPairOverlapScheme k d i j, ⊤))
  rw [hpair, overlapUnit_val_eq,
    chartScalarOnPair_chartRatio]
  change EInf.hom x = EB.inv w
  exact
    (EB.hom_inv_id_apply _).symm.trans
      (congrArg EB.inv.hom htransport)

/-- Natural powers of the Serre overlap unit become powers of the
corresponding chart ratio. -/
lemma pairOverlapTopSectionsIso_integerCoverUnit
    (N : ℕ) (i j : Fin (d + 1)) :
    (pairOverlapTopSectionsIso k d i j).hom
        (integerCoverUnit k d (N : ℤ) i j).val =
      chartScalarOnPair k d i j
          (chartRatioElement k d i j) ^ N := by
  rw [integerCoverUnit, zpow_natCast]
  change
    (pairOverlapTopSectionsIso k d i j).hom
        ((overlapUnit k d i j).val ^ N) =
      _
  calc
    _ =
        ((pairOverlapTopSectionsIso k d i j).hom
          (overlapUnit k d i j).val) ^ N :=
      map_pow
        (pairOverlapTopSectionsIso k d i j).hom.hom
        (overlapUnit k d i j).val N
    _ = _ :=
      congrArg (fun z => z ^ N)
        (pairOverlapTopSectionsIso_overlapUnit
          k d i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
