/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentOverlapGeometry

/-!
# The second chart presentation on a Laurent pair overlap

The transition isomorphism identifies the standard pair overlap with its
presentation over the second chart.  This file packages the corresponding
open-set and section constructions without normalizing the large effective
descent comparison maps.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

local instance standardCoverComponentIsOpenImmersion
    (k : Type) [CommRing k] (d : ℕ) (i : Fin (d + 1)) :
    IsOpenImmersion ((cover k d).f i) :=
  (cover k d).map_prop i

local instance glueDataComponentIsOpenImmersion
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    IsOpenImmersion ((glueData k d).f i j) :=
  (glueData k d).f_open i j

/-- The second projection from a pair overlap to its exposed standard
chart. -/
def typedIntegerSecondOverlapMap
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    typedIntegerPairOverlapScheme k d i j ⟶
      (standardChart k j).toScheme :=
  integerSecondOverlapMap k d i j

lemma integerSecondOverlapMap_eq_pullbackSnd
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    integerSecondOverlapMap k d i j =
      pullback.snd ((cover k d).f i) ((cover k d).f j) := by
  exact pullbackSymmetry_hom_comp_fst
    ((cover k d).f i) ((cover k d).f j)

instance integerSecondOverlapMap_isOpenImmersion
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    IsOpenImmersion (integerSecondOverlapMap k d i j) := by
  letI ht : IsIso ((glueData k d).t i j) :=
    CategoryTheory.GlueData.t_isIso
      (glueData k d).toGlueData i j
  letI htOpen : IsOpenImmersion ((glueData k d).t i j) := by
    infer_instance
  letI hf : IsOpenImmersion ((glueData k d).f j i) :=
    (glueData k d).f_open j i
  dsimp only [integerSecondOverlapMap]
  exact @IsOpenImmersion.comp _ _ _ _ _
    htOpen hf

instance typedIntegerSecondOverlapMap_isOpenImmersion
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    IsOpenImmersion (typedIntegerSecondOverlapMap k d i j) := by
  dsimp only [typedIntegerSecondOverlapMap]
  exact integerSecondOverlapMap_isOpenImmersion k d i j

lemma integerSecondOverlapMap_opensRange
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    (integerSecondOverlapMap k d i j).opensRange =
      ((glueData k d).f j i).opensRange := by
  letI ht : IsIso ((glueData k d).t i j) :=
    CategoryTheory.GlueData.t_isIso
      (glueData k d).toGlueData i j
  letI hf : IsOpenImmersion ((glueData k d).f j i) :=
    (glueData k d).f_open j i
  exact Scheme.Hom.opensRange_comp_of_isIso
    ((glueData k d).t i j) ((glueData k d).f j i)

/-- The range of the exposed second overlap projection is the preimage of
the first standard chart inside the second standard chart. -/
lemma typedIntegerSecondOverlapMap_opensRange
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    (typedIntegerSecondOverlapMap k d i j).opensRange =
      (standardChart k j).ι ⁻¹ᵁ standardChart k i := by
  change
    (integerSecondOverlapMap k d i j).opensRange =
      (cover k d).f j ⁻¹ᵁ standardChart k i
  rw [integerSecondOverlapMap_opensRange]
  change
    (pullback.fst ((cover k d).f j)
      ((cover k d).f i)).opensRange =
        (cover k d).f j ⁻¹ᵁ standardChart k i
  rw [Scheme.Hom.opensRange_pullbackFst]
  exact congrArg (fun U => (cover k d).f j ⁻¹ᵁ U)
    (TopologicalSpace.Opens.ext
      (Scheme.Opens.range_ι (standardChart k i)))

lemma pairPreimageLaurentOpen_eq_secondChartPreimage
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    pairPreimageLaurentOpen d I i j =
      integerSecondOverlapMap ℚ d i.1 j.1 ⁻¹ᵁ
        chartPreimageLaurentOpen ℚ d I j := by
  unfold pairPreimageLaurentOpen
    chartPreimageLaurentOpen integerPairOverlapMap
    integerSecondOverlapMap
  change
    ((glueData ℚ d).f i.1 j.1 ≫
        (cover ℚ d).f i.1) ⁻¹ᵁ laurentOpen ℚ d I =
      (((glueData ℚ d).t i.1 j.1 ≫
          (glueData ℚ d).f j.1 i.1) ≫
        (standardChart ℚ j.1).ι) ⁻¹ᵁ
          laurentOpen ℚ d I
  exact congrArg
    (fun q => q ⁻¹ᵁ laurentOpen ℚ d I)
    (show
      ((glueData ℚ d).f i.1 j.1 ≫
          (cover ℚ d).f i.1) =
        ((glueData ℚ d).t i.1 j.1 ≫
            (glueData ℚ d).f j.1 i.1) ≫
          (standardChart ℚ j.1).ι by
      exact (cover_glue_condition ℚ d i.1 j.1).symm)

private lemma secondChartFirstOverlapMapOpensRange
    (d : ℕ) (i j : Fin (d + 1)) :
    ((glueData ℚ d).f j i).opensRange =
      (cover ℚ d).f j ⁻¹ᵁ standardChart ℚ i := by
  change
    (pullback.fst ((cover ℚ d).f j)
      ((cover ℚ d).f i)).opensRange =
        (cover ℚ d).f j ⁻¹ᵁ standardChart ℚ i
  rw [Scheme.Hom.opensRange_pullbackFst]
  exact congrArg (fun U => (cover ℚ d).f j ⁻¹ᵁ U)
    (TopologicalSpace.Opens.ext
      (Scheme.Opens.range_ι (standardChart ℚ i)))

private def secondOverlapMapImagePairPreimageRaw
    (d : ℕ) (I : Finset (Fin (d + 1))) (i j : ↥I) :=
  let f := integerSecondOverlapMap ℚ d i.1 j.1
  let U := chartPreimageLaurentOpen ℚ d I j
  have hU : U ≤ f.opensRange := by
    dsimp only [f, U]
    rw [integerSecondOverlapMap_opensRange,
      secondChartFirstOverlapMapOpensRange]
    exact Scheme.Hom.preimage_mono ((cover ℚ d).f j.1)
      (laurentOpen_le_standardChart ℚ d I i)
  (congrArg (fun V => f ''ᵁ V)
      (pairPreimageLaurentOpen_eq_secondChartPreimage d I i j)).trans
    ((Scheme.Hom.image_preimage_eq_opensRange_inf f U).trans
      (inf_eq_right.mpr hU))

lemma secondOverlapMap_image_pairPreimage
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    integerSecondOverlapMap ℚ d i.1 j.1 ''ᵁ
        pairPreimageLaurentOpen d I i j =
      chartPreimageLaurentOpen ℚ d I j := by
  exact secondOverlapMapImagePairPreimageRaw d I i j

/-- Restrict the chart-`j` pullback section to the pair overlap. -/
def integerSecondOverlapRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  (((Scheme.Modules.pullback
      ((cover ℚ d).f j.1)).obj
        (OInt ℚ d m)).restrictAppIso
          (integerSecondOverlapMap ℚ d i.1 j.1)
          (pairPreimageLaurentOpen d I i j)).inv.hom
    ((((Scheme.Modules.pullback
        ((cover ℚ d).f j.1)).obj
          (OInt ℚ d m)).presheaf.mapIso
        (eqToIso
          (secondOverlapMap_image_pairPreimage d I i j)).op).hom.hom
      (integerChartPullbackSection d m I j x))

/-- Present the second-chart restriction as a pullback along the second
overlap map. -/
def integerSecondOverlapPullbackSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  (((Scheme.Modules.restrictFunctorIsoPullback
      (integerSecondOverlapMap ℚ d i.1 j.1)).hom.app
        ((Scheme.Modules.pullback
          ((cover ℚ d).f j.1)).obj
            (OInt ℚ d m))).app
      (pairPreimageLaurentOpen d I i j)
      (integerSecondOverlapRestrictionSection d m I i j x))

/-- The section of the projective pullback written through chart `j`. -/
def integerPairOverlapSectionViaSecondChart
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((Scheme.Modules.pullback
      (integerSecondOverlapMap ℚ d i.1 j.1 ≫
        (cover ℚ d).f j.1)).obj (OInt ℚ d m),
      pairPreimageLaurentOpen d I i j) :=
  ((Scheme.Modules.pullbackComp
      (integerSecondOverlapMap ℚ d i.1 j.1)
      ((cover ℚ d).f j.1)).hom.app
        (OInt ℚ d m)).app
    (pairPreimageLaurentOpen d I i j)
    (integerSecondOverlapPullbackSection d m I i j x)

/-- Apply the chart-`j` trivialization before the second-overlap pullback
comparison. -/
def integerSecondChartUnitRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  ((Scheme.Modules.restrictFunctor
    (integerSecondOverlapMap ℚ d i.1 j.1)).map
      (integerChartIso ℚ d m j.1).hom).app
    (pairPreimageLaurentOpen d I i j)
    (integerSecondOverlapRestrictionSection d m I i j x)

lemma integerSecondChartUnitRestrictionSection_transport
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    (((standardChart ℚ j.1).toScheme.presheaf.mapIso
      (eqToIso
        (secondOverlapMap_image_pairPreimage d I i j)).op).inv.hom
        (integerSecondChartUnitRestrictionSection d m I i j x)) =
      integerChartUnitSection d m I j x := by
  unfold integerSecondChartUnitRestrictionSection
    integerSecondOverlapRestrictionSection
    integerChartUnitSection
  exact moduleHom_mapIso_inv_hom_app_mapIso_hom
    (integerChartIso ℚ d m j.1).hom
    (secondOverlapMap_image_pairPreimage d I i j)
    (integerChartPullbackSection d m I j x)

/-- Transport a pair-overlap regular function to the ambient Laurent open
through its second-chart presentation. -/
def pairUnitSectionToAmbientViaSecondChart
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ((glueData ℚ d).V (i.1, j.1),
      pairPreimageLaurentOpen d I i j)) :
    Γ(scheme ℚ d, laurentOpen ℚ d I) :=
  ((scheme ℚ d).presheaf.mapIso
      (eqToIso (chartPreimageLaurentOpen_image
        ℚ d I j)).op).inv.hom
    (((standardChart ℚ j.1).ι.appIso
      (chartPreimageLaurentOpen ℚ d I j)).inv.hom
      (((standardChart ℚ j.1).toScheme.presheaf.mapIso
        (eqToIso
          (secondOverlapMap_image_pairPreimage d I i j)).op).inv.hom
        (((integerSecondOverlapMap ℚ d i.1 j.1).appIso
          (pairPreimageLaurentOpen d I i j)).inv.hom z)))

lemma projectiveIntegerSecondChartLegCore_pullbackComp_hom_app
    (d : ℕ) (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData ℚ d).V (i, j)).Opens)
    (z : Γ((Scheme.Modules.pullback
        (integerSecondOverlapMap ℚ d i j)).obj
          ((Scheme.Modules.pullback
            ((cover ℚ d).f j)).obj (OInt ℚ d m)), W)) :
    (projectiveIntegerSecondChartLegCore ℚ d m i j).app W
        (((Scheme.Modules.pullbackComp
          (integerSecondOverlapMap ℚ d i j)
          ((cover ℚ d).f j)).hom.app
            (OInt ℚ d m)).app W z) =
      ((Scheme.Modules.pullback
        (integerSecondOverlapMap ℚ d i j)).map
          (integerChartIso ℚ d m j).hom).app W z := by
  unfold projectiveIntegerSecondChartLegCore
    integerSecondOverlapMap
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullback
      ((glueData ℚ d).t i j ≫
        (glueData ℚ d).f j i)).map
        (integerChartIso ℚ d m j).hom).app W y)
  change
    (sectionsAddEquivOfIsoAt
      ((Scheme.Modules.pullbackComp
        ((glueData ℚ d).t i j ≫
          (glueData ℚ d).f j i)
        ((cover ℚ d).f j)).app (OInt ℚ d m)) W).symm
      ((sectionsAddEquivOfIsoAt
        ((Scheme.Modules.pullbackComp
          ((glueData ℚ d).t i j ≫
            (glueData ℚ d).f j i)
          ((cover ℚ d).f j)).app (OInt ℚ d m)) W) z) = z
  exact (sectionsAddEquivOfIsoAt
    ((Scheme.Modules.pullbackComp
      ((glueData ℚ d).t i j ≫
        (glueData ℚ d).f j i)
      ((cover ℚ d).f j)).app (OInt ℚ d m)) W).symm_apply_apply z

private def projectiveSecondChartUnitSectionEqAppIsoRaw
    (d : ℕ) (m : ℤ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  let f := integerSecondOverlapMap ℚ d i.1 j.1
  let W := pairPreimageLaurentOpen d I i j
  let s := integerSecondOverlapRestrictionSection d m I i j x
  let z := integerSecondOverlapPullbackSection d m I i j x
  let t := integerSecondChartUnitRestrictionSection d m I i j x
  have hcore :=
    projectiveIntegerSecondChartLegCore_pullbackComp_hom_app
      d m i.1 j.1 W z
  have hnatural :=
    restrictFunctorIsoPullback_hom_app_naturality f
      (integerChartIso ℚ d m j.1).hom W s
  have hunit := restrictFunctorIsoPullback_unit_app f W t
  (congrArg (fun y =>
      (pullbackUnitIso f).hom.app W y) hcore).trans
    ((congrArg (fun y =>
        (pullbackUnitIso f).hom.app W y) hnatural).trans hunit)

lemma projectiveSecondChartUnitSection_eq_appIso
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    ((projectiveIntegerSecondChartLegCore
        ℚ d m i.1 j.1 ≫
      (pullbackUnitIso
        (integerSecondOverlapMap ℚ d i.1 j.1)).hom).app
        (pairPreimageLaurentOpen d I i j)
        (integerPairOverlapSectionViaSecondChart d m I i j x)) =
      ((integerSecondOverlapMap ℚ d i.1 j.1).appIso
        (pairPreimageLaurentOpen d I i j)).hom
        (integerSecondChartUnitRestrictionSection d m I i j x) := by
  exact projectiveSecondChartUnitSectionEqAppIsoRaw d m I i j x

private def projectiveSecondChartAmbientCoordinateEqChartRaw
    (d : ℕ) (m : ℤ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  let f := integerSecondOverlapMap ℚ d i.1 j.1
  let W := pairPreimageLaurentOpen d I i j
  let t := integerSecondChartUnitRestrictionSection d m I i j x
  let cast :=
    ((standardChart ℚ j.1).toScheme.presheaf.mapIso
      (eqToIso
        (secondOverlapMap_image_pairPreimage d I i j)).op).inv.hom
  let tail := fun
      z : Γ((standardChart ℚ j.1).toScheme,
        chartPreimageLaurentOpen ℚ d I j) =>
    ((scheme ℚ d).presheaf.mapIso
      (eqToIso (chartPreimageLaurentOpen_image
        ℚ d I j)).op).inv.hom
      (((standardChart ℚ j.1).ι.appIso
        (chartPreimageLaurentOpen ℚ d I j)).inv.hom z)
  have hprojective := congrArg
    (pairUnitSectionToAmbientViaSecondChart d I i j)
    (projectiveSecondChartUnitSection_eq_appIso d m I i j x)
  have hdef :
      pairUnitSectionToAmbientViaSecondChart d I i j
          ((f.appIso W).hom t) =
        tail (cast ((f.appIso W).inv ((f.appIso W).hom t))) :=
    rfl
  have hcancel :
      tail (cast ((f.appIso W).inv ((f.appIso W).hom t))) =
        tail (cast t) :=
    congrArg (fun q => tail (cast q))
      ((f.appIso W).hom_inv_id_apply t)
  have htransport :
      tail (cast t) =
        tail (integerChartUnitSection d m I j x) :=
    congrArg tail
      (integerSecondChartUnitRestrictionSection_transport
        d m I i j x)
  have hfinal :
      tail (integerChartUnitSection d m I j x) =
        integerChartLaurentSectionsAddEquiv d m I j x := by
    dsimp only [tail]
    unfold integerChartUnitSection
      integerChartPullbackSection
      ambientSectionToIntegerChartRestriction
      integerChartLaurentSectionsAddEquiv
      integerChartRestrictIso
      sectionsAddEquivOfIsoAt
      unitSectionsAddEquivAt
    rfl
  hprojective.trans
    (hdef.trans (hcancel.trans (htransport.trans hfinal)))

/-- The unscaled second-chart projective coordinate recovers the Laurent
coordinate in chart `j`. -/
lemma projectiveSecondChartAmbientCoordinate_eq_chart
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    pairUnitSectionToAmbientViaSecondChart d I i j
      ((projectiveIntegerSecondChartLegCore
          ℚ d m i.1 j.1 ≫
        (pullbackUnitIso
          (integerSecondOverlapMap ℚ d i.1 j.1)).hom).app
        (pairPreimageLaurentOpen d I i j)
        (integerPairOverlapSectionViaSecondChart d m I i j x)) =
      integerChartLaurentSectionsAddEquiv d m I j x := by
  exact projectiveSecondChartAmbientCoordinateEqChartRaw d m I i j x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
