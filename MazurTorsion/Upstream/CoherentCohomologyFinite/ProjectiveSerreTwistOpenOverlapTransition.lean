/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenCoordinateEvaluation
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarOverlapAssembly
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartRatioTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentOverlapGeometry
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentOverlapCast

/-!
# Integer-twist coordinate transitions on arbitrary chart subopens

This file transports the effective-descent overlap equation through the
two projective chart trivializations.  The proof is factored through named
restriction, pullback-congruence, scalar-evaluation, and homogeneous-fraction
lemmas so that every declaration checks at the default heartbeat limit.

The resulting transition law is valid over every commutative base ring and
on every object of the slice site of a pairwise standard-chart intersection.
-/

open CategoryTheory Opposite Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

local instance standardCoverMap_isOpenImmersion
    (i : Fin (d + 1)) :
    IsOpenImmersion (standardChart k i).ι :=
  (cover k d).map_prop i

local instance glueDataMap_isOpenImmersion
    (i j : Fin (d + 1)) :
    IsOpenImmersion (typedIntegerFirstOverlapMap k d i j) :=
  typedIntegerFirstOverlapMap_isOpenImmersion k d i j

local instance integerPairOverlapMapOpen_isOpenImmersion
    (i j : Fin (d + 1)) :
    IsOpenImmersion (integerPairOverlapMap k d i j) :=
  integerPairOverlapMap_isOpenImmersion k d i j

local instance integerSecondOverlapMapOpen_isOpenImmersion
    (i j : Fin (d + 1)) :
    IsOpenImmersion (typedIntegerSecondOverlapMap k d i j) :=
  integerSecondOverlapMap_isOpenImmersion k d i j

lemma appIso_inv_comp_transport_open
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (hV : f ''ᵁ U = V) (hW : g ''ᵁ V = W)
    (hC : (f ≫ g) ''ᵁ U = W)
    (z : Γ(X, U)) :
    (Z.presheaf.mapIso (eqToIso hW).op).inv.hom
        ((g.appIso V).inv.hom
          ((Y.presheaf.mapIso (eqToIso hV).op).inv.hom
            ((f.appIso U).inv.hom z))) =
      (Z.presheaf.mapIso (eqToIso hC).op).inv.hom
        (((f ≫ g).appIso U).inv.hom z) := by
  subst V
  subst W
  simp only [Scheme.Hom.comp_appIso, Iso.trans_inv,
    ConcreteCategory.comp_apply]
  simp

lemma appIso_inv_congr_transport_open
    {X Y : Scheme} {f g : X ⟶ Y}
    (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (U : X.Opens) (W : Y.Opens)
    (hf : f ''ᵁ U = W) (hg : g ''ᵁ U = W)
    (z : Γ(X, U)) :
    (Y.presheaf.mapIso (eqToIso hf).op).inv.hom
        ((f.appIso U).inv.hom z) =
      (Y.presheaf.mapIso (eqToIso hg).op).inv.hom
        ((g.appIso U).inv.hom z) := by
  subst g
  simp

def pairPreimageOpen
    (i j : Fin (d + 1)) (A : (scheme k d).Opens) :
    (typedIntegerPairOverlapScheme k d i j).Opens :=
  integerPairOverlapMap k d i j ⁻¹ᵁ A

lemma pairPreimageOpen_image
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hA : A ≤ standardChart k i ⊓ standardChart k j) :
    integerPairOverlapMap k d i j ''ᵁ
        pairPreimageOpen k d i j A = A := by
  unfold pairPreimageOpen
  calc
    integerPairOverlapMap k d i j ''ᵁ
          integerPairOverlapMap k d i j ⁻¹ᵁ A =
        (integerPairOverlapMap k d i j).opensRange ⊓ A :=
      Scheme.Hom.image_preimage_eq_opensRange_inf
        (integerPairOverlapMap k d i j) A
    _ = (standardChart k i ⊓ standardChart k j) ⊓ A :=
      congrArg (fun U => U ⊓ A)
        (integerPairOverlapMap_opensRange k d i j)
    _ = A := inf_eq_right.mpr hA

lemma pairPreimageOpen_eq_firstChartPreimage
    (i j : Fin (d + 1)) (A : (scheme k d).Opens) :
    pairPreimageOpen k d i j A =
      typedIntegerFirstOverlapMap k d i j ⁻¹ᵁ chartPreimageOpen k d i A := by
  unfold pairPreimageOpen chartPreimageOpen integerPairOverlapMap
  exact Scheme.Hom.comp_preimage
    (typedIntegerFirstOverlapMap k d i j)
    (standardChart k i).ι A

lemma integerFirstOverlapMap_opensRange
    (i j : Fin (d + 1)) :
    (typedIntegerFirstOverlapMap k d i j).opensRange =
      (standardChart k i).ι ⁻¹ᵁ standardChart k j := by
  change
    (pullback.fst (standardChart k i).ι
      (standardChart k j).ι).opensRange =
        (standardChart k i).ι ⁻¹ᵁ standardChart k j
  rw [Scheme.Hom.opensRange_pullbackFst]
  congr 1
  apply TopologicalSpace.Opens.ext
  exact Scheme.Opens.range_ι (standardChart k j)

lemma integerFirstOverlapMap_image_pairPreimageOpen
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAj : A ≤ standardChart k j) :
    typedIntegerFirstOverlapMap k d i j ''ᵁ pairPreimageOpen k d i j A =
      chartPreimageOpen k d i A := by
  rw [pairPreimageOpen_eq_firstChartPreimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    integerFirstOverlapMap_opensRange, inf_eq_right]
  exact Scheme.Hom.preimage_mono (standardChart k i).ι hAj

def ambientSectionToIntegerChartRestrictionOpen
    (m : ℤ) (i : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (x : Γ(OInt k d m, A)) :
    Γ((OInt k d m).restrict (standardChart k i).ι,
      chartPreimageOpen k d i A) :=
  ((OInt k d m).restrictAppIso
      (standardChart k i).ι
      (chartPreimageOpen k d i A)).inv.hom
    (((OInt k d m).presheaf.mapIso
      (eqToIso (chartPreimageOpen_image k d i A hAi)).op).hom.hom x)

def integerChartPullbackSectionOpen
    (m : ℤ) (i : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (x : Γ(OInt k d m, A)) :
    Γ((Scheme.Modules.pullback
        (standardChart k i).ι).obj (OInt k d m),
      chartPreimageOpen k d i A) :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (standardChart k i).ι).hom.app
        (OInt k d m)).app
    (chartPreimageOpen k d i A)
    (ambientSectionToIntegerChartRestrictionOpen
      k d m i A hAi x)

def integerFirstOverlapRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  (((Scheme.Modules.pullback
      (standardChart k i).ι).obj (OInt k d m)).restrictAppIso
        (typedIntegerFirstOverlapMap k d i j)
        (pairPreimageOpen k d i j A)).inv.hom
    ((((Scheme.Modules.pullback
        (standardChart k i).ι).obj (OInt k d m)).presheaf.mapIso
      (eqToIso
        (integerFirstOverlapMap_image_pairPreimageOpen
          k d i j A hAj)).op).hom.hom
      (integerChartPullbackSectionOpen k d m i A hAi x))

def integerFirstOverlapPullbackSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  (((Scheme.Modules.restrictFunctorIsoPullback
      (typedIntegerFirstOverlapMap k d i j)).hom.app
        ((Scheme.Modules.pullback
          (standardChart k i).ι).obj (OInt k d m))).app
      (pairPreimageOpen k d i j A)
      (integerFirstOverlapRestrictionSectionOpen
        k d m i j A hAi hAj x))

def integerPairOverlapSectionViaFirstChartOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    IntegerOverlapSection k d m i j
      (pairPreimageOpen k d i j A) :=
  ((Scheme.Modules.pullbackComp
      (typedIntegerFirstOverlapMap k d i j)
      (standardChart k i).ι).hom.app
        (OInt k d m)).app
    (pairPreimageOpen k d i j A)
    (integerFirstOverlapPullbackSectionOpen
      k d m i j A hAi hAj x)

def integerFirstChartUnitRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  ((Scheme.Modules.restrictFunctor
    (typedIntegerFirstOverlapMap k d i j)).map
      (integerChartIso k d m i).hom).app
    (pairPreimageOpen k d i j A)
    (integerFirstOverlapRestrictionSectionOpen
      k d m i j A hAi hAj x)

def integerChartUnitSectionOpen
    (m : ℤ) (i : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (x : Γ(OInt k d m, A)) :
    Γ(SheafOfModules.unit
        (standardChart k i).toScheme.ringCatSheaf,
      chartPreimageOpen k d i A) :=
  (integerChartIso k d m i).hom.app
    (chartPreimageOpen k d i A)
    (integerChartPullbackSectionOpen k d m i A hAi x)

lemma integerFirstChartUnitRestrictionSectionOpen_transport
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    (((standardChart k i).toScheme.presheaf.mapIso
      (eqToIso
        (integerFirstOverlapMap_image_pairPreimageOpen
          k d i j A hAj)).op).inv.hom
        (integerFirstChartUnitRestrictionSectionOpen
          k d m i j A hAi hAj x)) =
      integerChartUnitSectionOpen k d m i A hAi x := by
  unfold integerFirstChartUnitRestrictionSectionOpen
    integerFirstOverlapRestrictionSectionOpen
    integerChartUnitSectionOpen
  exact moduleHom_mapIso_inv_hom_app_mapIso_hom
    (integerChartIso k d m i).hom
    (integerFirstOverlapMap_image_pairPreimageOpen
      k d i j A hAj)
    (integerChartPullbackSectionOpen k d m i A hAi x)

def pairUnitSectionToAmbientViaFirstChartOpen
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    Γ(scheme k d, A) :=
  ((scheme k d).presheaf.mapIso
      (eqToIso (chartPreimageOpen_image k d i A hAi)).op).inv.hom
    (((standardChart k i).ι.appIso
      (chartPreimageOpen k d i A)).inv.hom
      (((standardChart k i).toScheme.presheaf.mapIso
        (eqToIso
          (integerFirstOverlapMap_image_pairPreimageOpen
            k d i j A hAj)).op).inv.hom
        (((typedIntegerFirstOverlapMap k d i j).appIso
          (pairPreimageOpen k d i j A)).inv.hom z)))

def projectiveFirstAmbientCoordinateOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    Γ(scheme k d, A) :=
  pairUnitSectionToAmbientViaFirstChartOpen
    k d i j A hAi hAj
    ((typedProjectiveIntegerFirstScalarLeg k d m i j).app
      (pairPreimageOpen k d i j A)
      (integerPairOverlapSectionViaFirstChartOpen
        k d m i j A hAi hAj x))

lemma projectiveIntegerFirstChartLeg_pullbackComp_hom_app_open
    (m : ℤ) (i j : Fin (d + 1))
    (W : (typedIntegerPairOverlapScheme k d i j).Opens)
    (z : Γ((Scheme.Modules.pullback
        (typedIntegerFirstOverlapMap k d i j)).obj
          ((Scheme.Modules.pullback
            (standardChart k i).ι).obj (OInt k d m)), W)) :
    (projectiveIntegerFirstChartLeg k d m i j).app W
        (((Scheme.Modules.pullbackComp
          (typedIntegerFirstOverlapMap k d i j)
          (standardChart k i).ι).hom.app
            (OInt k d m)).app W z) =
      ((Scheme.Modules.pullback
        (typedIntegerFirstOverlapMap k d i j)).map
          (integerChartIso k d m i).hom).app W z := by
  unfold projectiveIntegerFirstChartLeg
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullback
      (typedIntegerFirstOverlapMap k d i j)).map
        (integerChartIso k d m i).hom).app W y)
  change
    (sectionsAddEquivOfIsoAt
      ((Scheme.Modules.pullbackComp
        (typedIntegerFirstOverlapMap k d i j)
        (standardChart k i).ι).app (OInt k d m)) W).symm
      ((sectionsAddEquivOfIsoAt
        ((Scheme.Modules.pullbackComp
          (typedIntegerFirstOverlapMap k d i j)
          (standardChart k i).ι).app (OInt k d m)) W) z) = z
  exact (sectionsAddEquivOfIsoAt
    ((Scheme.Modules.pullbackComp
      (typedIntegerFirstOverlapMap k d i j)
      (standardChart k i).ι).app (OInt k d m)) W).symm_apply_apply z

lemma projectiveFirstScalarSectionOpen_eq_appIso
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    (typedProjectiveIntegerFirstScalarLeg k d m i j).app
        (pairPreimageOpen k d i j A)
        (integerPairOverlapSectionViaFirstChartOpen
          k d m i j A hAi hAj x) =
      ((typedIntegerFirstOverlapMap k d i j).appIso
        (pairPreimageOpen k d i j A)).hom
        (integerFirstChartUnitRestrictionSectionOpen
          k d m i j A hAi hAj x) := by
  unfold integerPairOverlapSectionViaFirstChartOpen
    typedProjectiveIntegerFirstScalarLeg
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  change
    (typedIntegerFirstPullbackUnitHom k d i j).app
        (pairPreimageOpen k d i j A)
        ((projectiveIntegerFirstChartLeg k d m i j).app
          (pairPreimageOpen k d i j A)
          (((Scheme.Modules.pullbackComp
            (typedIntegerFirstOverlapMap k d i j)
            (standardChart k i).ι).hom.app
              (OInt k d m)).app
            (pairPreimageOpen k d i j A)
            (integerFirstOverlapPullbackSectionOpen
              k d m i j A hAi hAj x))) = _
  rw [projectiveIntegerFirstChartLeg_pullbackComp_hom_app_open]
  unfold integerFirstOverlapPullbackSectionOpen
  have hnat :=
    restrictFunctorIsoPullback_hom_app_naturality
      (typedIntegerFirstOverlapMap k d i j)
      (integerChartIso k d m i).hom
      (pairPreimageOpen k d i j A)
      (integerFirstOverlapRestrictionSectionOpen
        k d m i j A hAi hAj x)
  exact (congrArg
    (fun z =>
      (typedIntegerFirstPullbackUnitHom k d i j).app
        (pairPreimageOpen k d i j A) z)
    hnat).trans
      (typedIntegerFirstPullbackUnitHom_app k d i j
        (pairPreimageOpen k d i j A)
        (integerFirstChartUnitRestrictionSectionOpen
          k d m i j A hAi hAj x))

private def projectiveFirstAmbientCoordinateOpenEqChartRaw
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    projectiveFirstAmbientCoordinateOpen
        k d m i j A hAi hAj x =
      integerChartAmbientSectionsAddEquiv
        k d m i A hAi x := by
  let f := typedIntegerFirstOverlapMap k d i j
  let W := pairPreimageOpen k d i j A
  let t := integerFirstChartUnitRestrictionSectionOpen
    k d m i j A hAi hAj x
  let cast :=
    ((standardChart k i).toScheme.presheaf.mapIso
      (eqToIso
        (integerFirstOverlapMap_image_pairPreimageOpen
          k d i j A hAj)).op).inv.hom
  let tail := fun
      z : Γ((standardChart k i).toScheme,
        chartPreimageOpen k d i A) =>
    ((scheme k d).presheaf.mapIso
      (eqToIso (chartPreimageOpen_image k d i A hAi)).op).inv.hom
      (((standardChart k i).ι.appIso
        (chartPreimageOpen k d i A)).inv.hom z)
  have hprojective := congrArg
    (pairUnitSectionToAmbientViaFirstChartOpen
      k d i j A hAi hAj)
    (projectiveFirstScalarSectionOpen_eq_appIso
      k d m i j A hAi hAj x)
  have hdef :
      pairUnitSectionToAmbientViaFirstChartOpen
          k d i j A hAi hAj ((f.appIso W).hom t) =
        tail (cast ((f.appIso W).inv ((f.appIso W).hom t))) :=
    rfl
  have hcancel :
      tail (cast ((f.appIso W).inv ((f.appIso W).hom t))) =
        tail (cast t) :=
    congrArg (fun q => tail (cast q))
      ((f.appIso W).hom_inv_id_apply t)
  have htransport :
      tail (cast t) =
        tail (integerChartUnitSectionOpen k d m i A hAi x) :=
    congrArg tail
      (integerFirstChartUnitRestrictionSectionOpen_transport
        k d m i j A hAi hAj x)
  have hfinal :
      tail (integerChartUnitSectionOpen k d m i A hAi x) =
        integerChartAmbientSectionsAddEquiv k d m i A hAi x := by
    dsimp only [tail]
    unfold integerChartUnitSectionOpen
      integerChartPullbackSectionOpen
      ambientSectionToIntegerChartRestrictionOpen
      integerChartAmbientSectionsAddEquiv
      sectionsAddEquivOfIsoAt
      unitSectionsAddEquivAt
    rfl
  exact hprojective.trans
    (hdef.trans (hcancel.trans (htransport.trans hfinal)))

lemma projectiveFirstAmbientCoordinateOpen_eq_chart
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    projectiveFirstAmbientCoordinateOpen
        k d m i j A hAi hAj x =
      integerChartAmbientSectionsAddEquiv
        k d m i A hAi x := by
  exact projectiveFirstAmbientCoordinateOpenEqChartRaw
    k d m i j A hAi hAj x

lemma pairPreimageOpen_eq_secondChartPreimage
    (i j : Fin (d + 1)) (A : (scheme k d).Opens) :
    pairPreimageOpen k d i j A =
      typedIntegerSecondOverlapMap k d i j ⁻¹ᵁ
        chartPreimageOpen k d j A := by
  unfold pairPreimageOpen chartPreimageOpen
    integerPairOverlapMap typedIntegerSecondOverlapMap
    integerSecondOverlapMap
  change
    (typedIntegerFirstOverlapMap k d i j ≫ (standardChart k i).ι) ⁻¹ᵁ A =
      (((glueData k d).t i j ≫
          (glueData k d).f j i) ≫
        (standardChart k j).ι) ⁻¹ᵁ A
  exact congrArg (fun q => q ⁻¹ᵁ A)
    (show
      (typedIntegerFirstOverlapMap k d i j ≫ (standardChart k i).ι) =
        ((glueData k d).t i j ≫
            (glueData k d).f j i) ≫
          (standardChart k j).ι by
      exact (cover_glue_condition k d i j).symm)

lemma integerSecondOverlapMap_image_pairPreimageOpen
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i) :
    typedIntegerSecondOverlapMap k d i j ''ᵁ
        pairPreimageOpen k d i j A =
      chartPreimageOpen k d j A := by
  rw [pairPreimageOpen_eq_secondChartPreimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    typedIntegerSecondOverlapMap_opensRange, inf_eq_right]
  exact Scheme.Hom.preimage_mono (standardChart k j).ι hAi

def integerSecondOverlapRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  (((Scheme.Modules.pullback
      (standardChart k j).ι).obj (OInt k d m)).restrictAppIso
        (typedIntegerSecondOverlapMap k d i j)
        (pairPreimageOpen k d i j A)).inv.hom
    ((((Scheme.Modules.pullback
        (standardChart k j).ι).obj (OInt k d m)).presheaf.mapIso
      (eqToIso
        (integerSecondOverlapMap_image_pairPreimageOpen
          k d i j A hAi)).op).hom.hom
      (integerChartPullbackSectionOpen k d m j A hAj x))

def integerSecondOverlapPullbackSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  (((Scheme.Modules.restrictFunctorIsoPullback
      (typedIntegerSecondOverlapMap k d i j)).hom.app
        ((Scheme.Modules.pullback
          (standardChart k j).ι).obj (OInt k d m))).app
      (pairPreimageOpen k d i j A)
      (integerSecondOverlapRestrictionSectionOpen
        k d m i j A hAi hAj x))

def integerPairOverlapSectionViaSecondChartOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    Γ((Scheme.Modules.pullback
      (typedIntegerSecondOverlapMap k d i j ≫
        (standardChart k j).ι)).obj (OInt k d m),
      pairPreimageOpen k d i j A) :=
  ((Scheme.Modules.pullbackComp
      (typedIntegerSecondOverlapMap k d i j)
      (standardChart k j).ι).hom.app
        (OInt k d m)).app
    (pairPreimageOpen k d i j A)
    (integerSecondOverlapPullbackSectionOpen
      k d m i j A hAi hAj x)

def integerSecondChartUnitRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  ((Scheme.Modules.restrictFunctor
    (typedIntegerSecondOverlapMap k d i j)).map
      (integerChartIso k d m j).hom).app
    (pairPreimageOpen k d i j A)
    (integerSecondOverlapRestrictionSectionOpen
      k d m i j A hAi hAj x)

lemma integerSecondChartUnitRestrictionSectionOpen_transport
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    (((standardChart k j).toScheme.presheaf.mapIso
      (eqToIso
        (integerSecondOverlapMap_image_pairPreimageOpen
          k d i j A hAi)).op).inv.hom
        (integerSecondChartUnitRestrictionSectionOpen
          k d m i j A hAi hAj x)) =
      integerChartUnitSectionOpen k d m j A hAj x := by
  unfold integerSecondChartUnitRestrictionSectionOpen
    integerSecondOverlapRestrictionSectionOpen
    integerChartUnitSectionOpen
  exact moduleHom_mapIso_inv_hom_app_mapIso_hom
    (integerChartIso k d m j).hom
    (integerSecondOverlapMap_image_pairPreimageOpen
      k d i j A hAi)
    (integerChartPullbackSectionOpen k d m j A hAj x)

def pairUnitSectionToAmbientViaSecondChartOpen
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    Γ(scheme k d, A) :=
  ((scheme k d).presheaf.mapIso
      (eqToIso (chartPreimageOpen_image k d j A hAj)).op).inv.hom
    (((standardChart k j).ι.appIso
      (chartPreimageOpen k d j A)).inv.hom
      (((standardChart k j).toScheme.presheaf.mapIso
        (eqToIso
          (integerSecondOverlapMap_image_pairPreimageOpen
            k d i j A hAi)).op).inv.hom
        (((typedIntegerSecondOverlapMap k d i j).appIso
          (pairPreimageOpen k d i j A)).inv.hom z)))

lemma projectiveIntegerSecondChartLegCore_pullbackComp_hom_app_open
    (m : ℤ) (i j : Fin (d + 1))
    (W : (typedIntegerPairOverlapScheme k d i j).Opens)
    (z : Γ((Scheme.Modules.pullback
        (typedIntegerSecondOverlapMap k d i j)).obj
          ((Scheme.Modules.pullback
            (standardChart k j).ι).obj (OInt k d m)), W)) :
    (projectiveIntegerSecondChartLegCore k d m i j).app W
        (((Scheme.Modules.pullbackComp
          (typedIntegerSecondOverlapMap k d i j)
          (standardChart k j).ι).hom.app
            (OInt k d m)).app W z) =
      ((Scheme.Modules.pullback
        (typedIntegerSecondOverlapMap k d i j)).map
          (integerChartIso k d m j).hom).app W z := by
  unfold projectiveIntegerSecondChartLegCore
    typedIntegerSecondOverlapMap integerSecondOverlapMap
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullback
      ((glueData k d).t i j ≫
        (glueData k d).f j i)).map
        (integerChartIso k d m j).hom).app W y)
  change
    (sectionsAddEquivOfIsoAt
      ((Scheme.Modules.pullbackComp
        ((glueData k d).t i j ≫
          (glueData k d).f j i)
        (standardChart k j).ι).app (OInt k d m)) W).symm
      ((sectionsAddEquivOfIsoAt
        ((Scheme.Modules.pullbackComp
          ((glueData k d).t i j ≫
            (glueData k d).f j i)
          (standardChart k j).ι).app (OInt k d m)) W) z) = z
  exact (sectionsAddEquivOfIsoAt
    ((Scheme.Modules.pullbackComp
      ((glueData k d).t i j ≫
        (glueData k d).f j i)
      (standardChart k j).ι).app (OInt k d m)) W).symm_apply_apply z

private def projectiveSecondChartUnitSectionOpenEqAppIsoRaw
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    ((projectiveIntegerSecondChartLegCore k d m i j ≫
      (pullbackUnitIso
        (typedIntegerSecondOverlapMap k d i j)).hom).app
        (pairPreimageOpen k d i j A)
        (integerPairOverlapSectionViaSecondChartOpen
          k d m i j A hAi hAj x)) =
      ((typedIntegerSecondOverlapMap k d i j).appIso
        (pairPreimageOpen k d i j A)).hom
        (integerSecondChartUnitRestrictionSectionOpen
          k d m i j A hAi hAj x) := by
  let f := typedIntegerSecondOverlapMap k d i j
  let W := pairPreimageOpen k d i j A
  let s := integerSecondOverlapRestrictionSectionOpen
    k d m i j A hAi hAj x
  let z := integerSecondOverlapPullbackSectionOpen
    k d m i j A hAi hAj x
  let t := integerSecondChartUnitRestrictionSectionOpen
    k d m i j A hAi hAj x
  have hcore :=
    projectiveIntegerSecondChartLegCore_pullbackComp_hom_app_open
      k d m i j W z
  have hnatural :=
    restrictFunctorIsoPullback_hom_app_naturality f
      (integerChartIso k d m j).hom W s
  have hunit := restrictFunctorIsoPullback_unit_app f W t
  exact (congrArg (fun y =>
      (pullbackUnitIso f).hom.app W y) hcore).trans
    ((congrArg (fun y =>
        (pullbackUnitIso f).hom.app W y) hnatural).trans hunit)

lemma projectiveSecondChartUnitSectionOpen_eq_appIso
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    ((projectiveIntegerSecondChartLegCore k d m i j ≫
      (pullbackUnitIso
        (typedIntegerSecondOverlapMap k d i j)).hom).app
        (pairPreimageOpen k d i j A)
        (integerPairOverlapSectionViaSecondChartOpen
          k d m i j A hAi hAj x)) =
      ((typedIntegerSecondOverlapMap k d i j).appIso
        (pairPreimageOpen k d i j A)).hom
        (integerSecondChartUnitRestrictionSectionOpen
          k d m i j A hAi hAj x) := by
  exact projectiveSecondChartUnitSectionOpenEqAppIsoRaw
    k d m i j A hAi hAj x

private def projectiveSecondChartAmbientCoordinateOpenEqChartRaw
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    pairUnitSectionToAmbientViaSecondChartOpen k d i j A hAi hAj
      ((projectiveIntegerSecondChartLegCore k d m i j ≫
        (pullbackUnitIso
          (typedIntegerSecondOverlapMap k d i j)).hom).app
        (pairPreimageOpen k d i j A)
        (integerPairOverlapSectionViaSecondChartOpen
          k d m i j A hAi hAj x)) =
      integerChartAmbientSectionsAddEquiv k d m j A hAj x := by
  let f := typedIntegerSecondOverlapMap k d i j
  let W := pairPreimageOpen k d i j A
  let t := integerSecondChartUnitRestrictionSectionOpen
    k d m i j A hAi hAj x
  let cast :=
    ((standardChart k j).toScheme.presheaf.mapIso
      (eqToIso
        (integerSecondOverlapMap_image_pairPreimageOpen
          k d i j A hAi)).op).inv.hom
  let tail := fun
      z : Γ((standardChart k j).toScheme,
        chartPreimageOpen k d j A) =>
    ((scheme k d).presheaf.mapIso
      (eqToIso (chartPreimageOpen_image k d j A hAj)).op).inv.hom
      (((standardChart k j).ι.appIso
        (chartPreimageOpen k d j A)).inv.hom z)
  have hprojective := congrArg
    (pairUnitSectionToAmbientViaSecondChartOpen
      k d i j A hAi hAj)
    (projectiveSecondChartUnitSectionOpen_eq_appIso
      k d m i j A hAi hAj x)
  have hdef :
      pairUnitSectionToAmbientViaSecondChartOpen
          k d i j A hAi hAj ((f.appIso W).hom t) =
        tail (cast ((f.appIso W).inv ((f.appIso W).hom t))) :=
    rfl
  have hcancel :
      tail (cast ((f.appIso W).inv ((f.appIso W).hom t))) =
        tail (cast t) :=
    congrArg (fun q => tail (cast q))
      ((f.appIso W).hom_inv_id_apply t)
  have htransport :
      tail (cast t) =
        tail (integerChartUnitSectionOpen k d m j A hAj x) :=
    congrArg tail
      (integerSecondChartUnitRestrictionSectionOpen_transport
        k d m i j A hAi hAj x)
  have hfinal :
      tail (integerChartUnitSectionOpen k d m j A hAj x) =
        integerChartAmbientSectionsAddEquiv k d m j A hAj x := by
    dsimp only [tail]
    unfold integerChartUnitSectionOpen
      integerChartPullbackSectionOpen
      ambientSectionToIntegerChartRestrictionOpen
      integerChartAmbientSectionsAddEquiv
      sectionsAddEquivOfIsoAt
      unitSectionsAddEquivAt
    rfl
  exact hprojective.trans
    (hdef.trans (hcancel.trans (htransport.trans hfinal)))

lemma projectiveSecondChartAmbientCoordinateOpen_eq_chart
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    pairUnitSectionToAmbientViaSecondChartOpen k d i j A hAi hAj
      ((projectiveIntegerSecondChartLegCore k d m i j ≫
        (pullbackUnitIso
          (typedIntegerSecondOverlapMap k d i j)).hom).app
        (pairPreimageOpen k d i j A)
        (integerPairOverlapSectionViaSecondChartOpen
          k d m i j A hAi hAj x)) =
      integerChartAmbientSectionsAddEquiv k d m j A hAj x := by
  exact projectiveSecondChartAmbientCoordinateOpenEqChartRaw
    k d m i j A hAi hAj x

def integerPairDirectRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    Γ((OInt k d m).restrict
        (integerPairOverlapMap k d i j),
      pairPreimageOpen k d i j A) :=
  ((OInt k d m).restrictAppIso
      (integerPairOverlapMap k d i j)
      (pairPreimageOpen k d i j A)).inv.hom
    (((OInt k d m).presheaf.mapIso
      (eqToIso
        (pairPreimageOpen_image k d i j A
          (le_inf hAi hAj))).op).hom.hom x)

def integerPairDirectPullbackSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    IntegerOverlapSection k d m i j
      (pairPreimageOpen k d i j A) :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (integerPairOverlapMap k d i j)).hom.app
        (OInt k d m)).app
    (pairPreimageOpen k d i j A)
    (integerPairDirectRestrictionSectionOpen
      k d m i j A hAi hAj x)

def integerFirstNestedRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  (((OInt k d m).restrict
    (standardChart k i).ι).restrictAppIso
      (typedIntegerFirstOverlapMap k d i j)
      (pairPreimageOpen k d i j A)).inv.hom
    ((((OInt k d m).restrict
      (standardChart k i).ι).presheaf.mapIso
        (eqToIso
          (integerFirstOverlapMap_image_pairPreimageOpen
            k d i j A hAj)).op).hom.hom
      (ambientSectionToIntegerChartRestrictionOpen
        k d m i A hAi x))

lemma firstOverlapRestrictionSectionOpen_eq_nested
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerFirstOverlapRestrictionSectionOpen
        k d m i j A hAi hAj x =
      (((Scheme.Modules.restrictFunctor
          (typedIntegerFirstOverlapMap k d i j)).map
        ((Scheme.Modules.restrictFunctorIsoPullback
          (standardChart k i).ι).hom.app
            (OInt k d m))).app
        (pairPreimageOpen k d i j A)
        (integerFirstNestedRestrictionSectionOpen
          k d m i j A hAi hAj x)) := by
  unfold integerFirstOverlapRestrictionSectionOpen
    integerFirstNestedRestrictionSectionOpen
    integerChartPullbackSectionOpen
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv]
  exact Scheme.Modules.moduleHom_mapIso_hom_app
    ((Scheme.Modules.restrictFunctorIsoPullback
      (standardChart k i).ι).hom.app (OInt k d m))
    (integerFirstOverlapMap_image_pairPreimageOpen
      k d i j A hAj)
    (ambientSectionToIntegerChartRestrictionOpen
      k d m i A hAi x)

lemma firstNestedRestrictionSectionOpen_eq_comp
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerFirstNestedRestrictionSectionOpen
        k d m i j A hAi hAj x =
      (((Scheme.Modules.restrictFunctorComp
          (typedIntegerFirstOverlapMap k d i j)
          (standardChart k i).ι).hom.app
        (OInt k d m)).app
        (pairPreimageOpen k d i j A)
        (integerPairDirectRestrictionSectionOpen
          k d m i j A hAi hAj x)) := by
  unfold integerFirstNestedRestrictionSectionOpen
    integerPairDirectRestrictionSectionOpen
    ambientSectionToIntegerChartRestrictionOpen
    integerPairOverlapMap
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change
    (OInt k d m).presheaf.map _
        ((OInt k d m).presheaf.map _ x) =
      (OInt k d m).presheaf.map _
        ((OInt k d m).presheaf.map _ x)
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg
      (fun r => (OInt k d m).presheaf.map r)
      (Subsingleton.elim _ _))
    x

lemma firstPairSectionOpen_eq_direct
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerPairOverlapSectionViaFirstChartOpen
        k d m i j A hAi hAj x =
      integerPairDirectPullbackSectionOpen
        k d m i j A hAi hAj x := by
  unfold integerPairOverlapSectionViaFirstChartOpen
    integerPairDirectPullbackSectionOpen
    integerPairOverlapMap
  rw [Scheme.Modules.restrictFunctorIsoPullback_comp_app]
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullbackComp
      (typedIntegerFirstOverlapMap k d i j)
      (standardChart k i).ι).hom.app
        (OInt k d m)).app
      (pairPreimageOpen k d i j A) y)
  unfold integerFirstOverlapPullbackSectionOpen
  apply congrArg (fun y =>
    ((Scheme.Modules.restrictFunctorIsoPullback
      (typedIntegerFirstOverlapMap k d i j)).hom.app
        ((Scheme.Modules.pullback
          (standardChart k i).ι).obj
            (OInt k d m))).app
      (pairPreimageOpen k d i j A) y)
  rw [firstOverlapRestrictionSectionOpen_eq_nested]
  apply congrArg (fun y =>
    (((Scheme.Modules.restrictFunctor
      (typedIntegerFirstOverlapMap k d i j)).map
      ((Scheme.Modules.restrictFunctorIsoPullback
        (standardChart k i).ι).hom.app
          (OInt k d m))).app
      (pairPreimageOpen k d i j A) y))
  exact firstNestedRestrictionSectionOpen_eq_comp
    k d m i j A hAi hAj x

def integerSecondPairOverlapMapOpen
    (i j : Fin (d + 1)) :
    typedIntegerPairOverlapScheme k d i j ⟶ scheme k d :=
  typedIntegerSecondOverlapMap k d i j ≫ (standardChart k j).ι

instance integerSecondPairOverlapMapOpen_isOpenImmersion
    (i j : Fin (d + 1)) :
    IsOpenImmersion (integerSecondPairOverlapMapOpen k d i j) := by
  unfold integerSecondPairOverlapMapOpen
  infer_instance

lemma integerSecondPairOverlapMapOpen_eq_first
    (i j : Fin (d + 1)) :
    integerSecondPairOverlapMapOpen k d i j =
      integerPairOverlapMap k d i j := by
  exact cover_glue_condition k d i j

lemma integerSecondPairOverlapMapOpen_image
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j) :
    integerSecondPairOverlapMapOpen k d i j ''ᵁ
      pairPreimageOpen k d i j A = A := by
  simpa only [integerSecondPairOverlapMapOpen_eq_first] using
    pairPreimageOpen_image k d i j A (le_inf hAi hAj)

def integerSecondPairDirectRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    Γ((OInt k d m).restrict
        (integerSecondPairOverlapMapOpen k d i j),
      pairPreimageOpen k d i j A) :=
  ((OInt k d m).restrictAppIso
      (integerSecondPairOverlapMapOpen k d i j)
      (pairPreimageOpen k d i j A)).inv.hom
    (((OInt k d m).presheaf.mapIso
      (eqToIso
        (integerSecondPairOverlapMapOpen_image
          k d i j A hAi hAj)).op).hom.hom x)

abbrev integerSecondPairDirectPullbackSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    Γ((Scheme.Modules.pullback
        (integerSecondPairOverlapMapOpen k d i j)).obj
          (OInt k d m),
      pairPreimageOpen k d i j A) :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (integerSecondPairOverlapMapOpen k d i j)).hom.app
        (OInt k d m)).app
    (pairPreimageOpen k d i j A)
    (integerSecondPairDirectRestrictionSectionOpen
      k d m i j A hAi hAj x)

def integerSecondNestedRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  (((OInt k d m).restrict
    (standardChart k j).ι).restrictAppIso
      (typedIntegerSecondOverlapMap k d i j)
      (pairPreimageOpen k d i j A)).inv.hom
    ((((OInt k d m).restrict
      (standardChart k j).ι).presheaf.mapIso
        (eqToIso
          (integerSecondOverlapMap_image_pairPreimageOpen
            k d i j A hAi)).op).hom.hom
      (ambientSectionToIntegerChartRestrictionOpen
        k d m j A hAj x))

lemma secondOverlapRestrictionSectionOpen_eq_nested
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerSecondOverlapRestrictionSectionOpen
        k d m i j A hAi hAj x =
      (((Scheme.Modules.restrictFunctor
          (typedIntegerSecondOverlapMap k d i j)).map
        ((Scheme.Modules.restrictFunctorIsoPullback
          (standardChart k j).ι).hom.app
            (OInt k d m))).app
        (pairPreimageOpen k d i j A)
        (integerSecondNestedRestrictionSectionOpen
          k d m i j A hAi hAj x)) := by
  unfold integerSecondOverlapRestrictionSectionOpen
    integerSecondNestedRestrictionSectionOpen
    integerChartPullbackSectionOpen
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv]
  exact Scheme.Modules.moduleHom_mapIso_hom_app
    ((Scheme.Modules.restrictFunctorIsoPullback
      (standardChart k j).ι).hom.app (OInt k d m))
    (integerSecondOverlapMap_image_pairPreimageOpen
      k d i j A hAi)
    (ambientSectionToIntegerChartRestrictionOpen
      k d m j A hAj x)

lemma secondNestedRestrictionSectionOpen_eq_comp
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerSecondNestedRestrictionSectionOpen
        k d m i j A hAi hAj x =
      (((Scheme.Modules.restrictFunctorComp
          (typedIntegerSecondOverlapMap k d i j)
          (standardChart k j).ι).hom.app
        (OInt k d m)).app
        (pairPreimageOpen k d i j A)
        (integerSecondPairDirectRestrictionSectionOpen
          k d m i j A hAi hAj x)) := by
  unfold integerSecondNestedRestrictionSectionOpen
    integerSecondPairDirectRestrictionSectionOpen
    ambientSectionToIntegerChartRestrictionOpen
    integerSecondPairOverlapMapOpen
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change
    (OInt k d m).presheaf.map _
        ((OInt k d m).presheaf.map _ x) =
      (OInt k d m).presheaf.map _
        ((OInt k d m).presheaf.map _ x)
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg
      (fun r => (OInt k d m).presheaf.map r)
      (Subsingleton.elim _ _))
    x

lemma secondPairSectionOpen_eq_direct
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerPairOverlapSectionViaSecondChartOpen
        k d m i j A hAi hAj x =
      integerSecondPairDirectPullbackSectionOpen
        k d m i j A hAi hAj x := by
  unfold integerPairOverlapSectionViaSecondChartOpen
    integerSecondPairDirectPullbackSectionOpen
    integerSecondPairOverlapMapOpen
  rw [Scheme.Modules.restrictFunctorIsoPullback_comp_app]
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullbackComp
      (typedIntegerSecondOverlapMap k d i j)
      (standardChart k j).ι).hom.app
        (OInt k d m)).app
      (pairPreimageOpen k d i j A) y)
  unfold integerSecondOverlapPullbackSectionOpen
  apply congrArg (fun y =>
    ((Scheme.Modules.restrictFunctorIsoPullback
      (typedIntegerSecondOverlapMap k d i j)).hom.app
        ((Scheme.Modules.pullback
          (standardChart k j).ι).obj
            (OInt k d m))).app
      (pairPreimageOpen k d i j A) y)
  rw [secondOverlapRestrictionSectionOpen_eq_nested]
  apply congrArg (fun y =>
    (((Scheme.Modules.restrictFunctor
      (typedIntegerSecondOverlapMap k d i j)).map
      ((Scheme.Modules.restrictFunctorIsoPullback
        (standardChart k j).ι).hom.app
          (OInt k d m))).app
      (pairPreimageOpen k d i j A) y))
  exact secondNestedRestrictionSectionOpen_eq_comp
    k d m i j A hAi hAj x

lemma restrictCongr_inv_directRestrictionSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    (((Scheme.Modules.restrictFunctorCongr
      (integerSecondPairOverlapMapOpen_eq_first
        k d i j)).inv.app
        (OInt k d m)).app
      (pairPreimageOpen k d i j A)
      (integerPairDirectRestrictionSectionOpen
        k d m i j A hAi hAj x)) =
        integerSecondPairDirectRestrictionSectionOpen
          k d m i j A hAi hAj x := by
  unfold integerPairDirectRestrictionSectionOpen
    integerSecondPairDirectRestrictionSectionOpen
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv,
    Scheme.Modules.restrictFunctorCongr_inv_app_app]
  change
    (OInt k d m).presheaf.map _
        ((OInt k d m).presheaf.map _ x) =
      (OInt k d m).presheaf.map _ x
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg
      (fun r => (OInt k d m).presheaf.map r)
      (Subsingleton.elim _ _))
    x

def pullbackCongr_inv_directRestrictionBeforeOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  Scheme.Modules.restrictFunctorIsoPullback_congr_inv_app
    (integerSecondPairOverlapMapOpen_eq_first k d i j)
    (OInt k d m)
    (pairPreimageOpen k d i j A)
    (integerPairDirectRestrictionSectionOpen
      k d m i j A hAi hAj x)

def pullbackCongr_inv_directRestrictionAfterOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg (fun y =>
    ((Scheme.Modules.restrictFunctorIsoPullback
      (integerSecondPairOverlapMapOpen k d i j)).hom.app
        (OInt k d m)).app
      (pairPreimageOpen k d i j A) y)
    (restrictCongr_inv_directRestrictionSectionOpen
      k d m i j A hAi hAj x)

private theorem eq_trans_two_open
    {α : Sort*} {a₀ a₁ a₂ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) : a₀ = a₂ :=
  h₀.trans h₁

def pullbackCongr_inv_directRestrictionComparisonOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  eq_trans_two_open
    (pullbackCongr_inv_directRestrictionBeforeOpen
      k d m i j A hAi hAj x)
    (pullbackCongr_inv_directRestrictionAfterOpen
      k d m i j A hAi hAj x)

def rawCastFirstPairSectionOpenToDirect
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (fun y =>
      ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m)).app
        (pairPreimageOpen k d i j A) y)
    (firstPairSectionOpen_eq_direct
      k d m i j A hAi hAj x)

def rawCastDirectOpenProofChange
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  Scheme.Modules.pullbackCongr_inv_app_proof_irrel
    (projectiveIntegerOverlapEquation k d i j)
    (integerSecondPairOverlapMapOpen_eq_first k d i j)
    (OInt k d m)
    (pairPreimageOpen k d i j A)
    (integerPairDirectPullbackSectionOpen
      k d m i j A hAi hAj x)

def rawCastDirectOpenToSecondPairSection
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  (pullbackCongr_inv_directRestrictionComparisonOpen
      k d m i j A hAi hAj x).trans
    (secondPairSectionOpen_eq_direct
      k d m i j A hAi hAj x).symm

def rawCastFirstOpenToSecondDirect
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  eq_trans_two_open
    (rawCastFirstPairSectionOpenToDirect
      k d m i j A hAi hAj x)
    (rawCastDirectOpenProofChange
      k d m i j A hAi hAj x)

def pairUnitSectionToAmbientDirectOpen
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    Γ(scheme k d, A) :=
  ((scheme k d).presheaf.mapIso
      (eqToIso
        (pairPreimageOpen_image k d i j A
          (le_inf hAi hAj))).op).inv.hom
    (((integerPairOverlapMap k d i j).appIso
      (pairPreimageOpen k d i j A)).inv.hom z)

lemma pairUnitSectionToAmbientViaFirstChartOpen_eq_direct
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    pairUnitSectionToAmbientViaFirstChartOpen
        k d i j A hAi hAj z =
      pairUnitSectionToAmbientDirectOpen
        k d i j A hAi hAj z := by
  unfold pairUnitSectionToAmbientViaFirstChartOpen
    pairUnitSectionToAmbientDirectOpen integerPairOverlapMap
  exact appIso_inv_comp_transport_open
    (typedIntegerFirstOverlapMap k d i j)
    (standardChart k i).ι
    (pairPreimageOpen k d i j A)
    (chartPreimageOpen k d i A)
    A
    (integerFirstOverlapMap_image_pairPreimageOpen
      k d i j A hAj)
    (chartPreimageOpen_image k d i A hAi)
    (pairPreimageOpen_image k d i j A
      (le_inf hAi hAj))
    z

def pairUnitSectionToAmbientSecondDirectOpen
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    Γ(scheme k d, A) :=
  ((scheme k d).presheaf.mapIso
      (eqToIso
        (integerSecondPairOverlapMapOpen_image
          k d i j A hAi hAj)).op).inv.hom
    (((integerSecondPairOverlapMapOpen k d i j).appIso
      (pairPreimageOpen k d i j A)).inv.hom z)

lemma pairUnitSectionToAmbientViaSecondChartOpen_eq_direct
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    pairUnitSectionToAmbientViaSecondChartOpen
        k d i j A hAi hAj z =
      pairUnitSectionToAmbientSecondDirectOpen
        k d i j A hAi hAj z := by
  unfold pairUnitSectionToAmbientViaSecondChartOpen
    pairUnitSectionToAmbientSecondDirectOpen
    integerSecondPairOverlapMapOpen
  exact appIso_inv_comp_transport_open
    (typedIntegerSecondOverlapMap k d i j)
    (standardChart k j).ι
    (pairPreimageOpen k d i j A)
    (chartPreimageOpen k d j A)
    A
    (integerSecondOverlapMap_image_pairPreimageOpen
      k d i j A hAi)
    (chartPreimageOpen_image k d j A hAj)
    (integerSecondPairOverlapMapOpen_image
      k d i j A hAi hAj)
    z

lemma pairUnitSectionToAmbientDirectOpen_eq_secondDirect
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    pairUnitSectionToAmbientDirectOpen
        k d i j A hAi hAj z =
      pairUnitSectionToAmbientSecondDirectOpen
        k d i j A hAi hAj z := by
  unfold pairUnitSectionToAmbientDirectOpen
    pairUnitSectionToAmbientSecondDirectOpen
  exact (appIso_inv_congr_transport_open
    (integerSecondPairOverlapMapOpen_eq_first k d i j)
    (pairPreimageOpen k d i j A)
    A
    (integerSecondPairOverlapMapOpen_image
      k d i j A hAi hAj)
    (pairPreimageOpen_image k d i j A
      (le_inf hAi hAj))
    z).symm

lemma pairUnitSectionToAmbientOpen_chart_independent
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    pairUnitSectionToAmbientViaFirstChartOpen
        k d i j A hAi hAj z =
      pairUnitSectionToAmbientViaSecondChartOpen
        k d i j A hAi hAj z := by
  exact
    (pairUnitSectionToAmbientViaFirstChartOpen_eq_direct
      k d i j A hAi hAj z).trans <|
      (pairUnitSectionToAmbientDirectOpen_eq_secondDirect
        k d i j A hAi hAj z).trans <|
        (pairUnitSectionToAmbientViaSecondChartOpen_eq_direct
          k d i j A hAi hAj z).symm

lemma pairUnitSectionToAmbientViaSecondChartOpen_mul
    (i j : Fin (d + 1)) (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (z w : Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A)) :
    pairUnitSectionToAmbientViaSecondChartOpen
        k d i j A hAi hAj (z * w) =
      pairUnitSectionToAmbientViaSecondChartOpen
          k d i j A hAi hAj z *
        pairUnitSectionToAmbientViaSecondChartOpen
          k d i j A hAi hAj w := by
  unfold pairUnitSectionToAmbientViaSecondChartOpen
  let F :=
    ((scheme k d).presheaf.mapIso
      (eqToIso
        (chartPreimageOpen_image k d j A hAj)).op).inv.hom.comp
      (((standardChart k j).ι.appIso
        (chartPreimageOpen k d j A)).inv.hom.comp
        (((standardChart k j).toScheme.presheaf.mapIso
          (eqToIso
            (integerSecondOverlapMap_image_pairPreimageOpen
              k d i j A hAi)).op).inv.hom.comp
          ((typedIntegerSecondOverlapMap k d i j).appIso
            (pairPreimageOpen k d i j A)).inv.hom))
  change F (z * w) = F z * F w
  exact F.map_mul z w

/-- The first scalar overlap section attached to a section on an
arbitrary ambient open contained in both charts. -/
def integerFirstScalarPairSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A) :=
  (projectiveIntegerFirstScalarLeg k d m i j).app
    (pairPreimageOpen k d i j A)
    (integerPairOverlapSectionViaFirstChartOpen
      k d m i j A hAi hAj x)

/-- The raw second-chart overlap section before the inverse transition
scalar is applied. -/
def integerRawSecondUnscaledPairSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A) :=
  (projectiveIntegerSecondChartLegCore k d m i j ≫
      (pullbackUnitIso
        (typedIntegerSecondOverlapMap k d i j)).hom).app
    (pairPreimageOpen k d i j A)
    (((Scheme.Modules.pullbackCongr
      (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m)).app
      (pairPreimageOpen k d i j A)
      (integerPairOverlapSectionViaFirstChartOpen
        k d m i j A hAi hAj x))

/-- The inverse integer transition scalar, restricted to the preimage
of an arbitrary ambient open. -/
def integerInverseTransitionSectionOnPairOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens) :
    Γ(typedIntegerPairOverlapScheme k d i j,
      pairPreimageOpen k d i j A) :=
  (typedIntegerPairOverlapScheme k d i j).presheaf.map
      (homOfLE le_top).op
    (((overlapUnit k d i j) ^ m).inv)

/-- Apply the unscaled second-chart coordinate map and then transport
the result to the ambient open. -/
def unscaledSecondAmbientOfPairSectionOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (y : Γ((Scheme.Modules.pullback
      (typedIntegerSecondOverlapMap k d i j ≫
        (standardChart k j).ι)).obj (OInt k d m),
      pairPreimageOpen k d i j A)) :
    Γ(scheme k d, A) :=
  pairUnitSectionToAmbientViaSecondChartOpen
    k d i j A hAi hAj
    ((projectiveIntegerSecondChartLegCore k d m i j ≫
      (pullbackUnitIso
        (typedIntegerSecondOverlapMap k d i j)).hom).app
      (pairPreimageOpen k d i j A) y)

def rawSecondUnscaledAmbientCastFirstToDirectOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (unscaledSecondAmbientOfPairSectionOpen
      k d m i j A hAi hAj)
    (rawCastFirstPairSectionOpenToDirect
      k d m i j A hAi hAj x)

def rawSecondUnscaledAmbientCastProofChangeOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (unscaledSecondAmbientOfPairSectionOpen
      k d m i j A hAi hAj)
    (rawCastDirectOpenProofChange
      k d m i j A hAi hAj x)

def rawSecondUnscaledAmbientCastDirectToSecondOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (unscaledSecondAmbientOfPairSectionOpen
      k d m i j A hAi hAj)
    (rawCastDirectOpenToSecondPairSection
      k d m i j A hAi hAj x)

def rawSecondUnscaledAmbientCastFirstToSecondDirectOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (unscaledSecondAmbientOfPairSectionOpen
      k d m i j A hAi hAj)
    (rawCastFirstOpenToSecondDirect
      k d m i j A hAi hAj x)

def rawSecondUnscaledAmbientCoordinateOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) : Γ(scheme k d, A) :=
  pairUnitSectionToAmbientViaSecondChartOpen
    k d i j A hAi hAj
    (integerRawSecondUnscaledPairSectionOpen
      k d m i j A hAi hAj x)

def rawSecondDirectAmbientCoordinateOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) : Γ(scheme k d, A) :=
  unscaledSecondAmbientOfPairSectionOpen
    k d m i j A hAi hAj
    (((Scheme.Modules.pullbackCongr
      (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m)).app
      (pairPreimageOpen k d i j A)
      (integerPairDirectPullbackSectionOpen
        k d m i j A hAi hAj x))

def rawSecondChartAmbientCoordinateOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) : Γ(scheme k d, A) :=
  unscaledSecondAmbientOfPairSectionOpen
    k d m i j A hAi hAj
    (integerPairOverlapSectionViaSecondChartOpen
      k d m i j A hAi hAj x)

lemma firstScalarAmbientOpen_eq_chart
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    pairUnitSectionToAmbientViaSecondChartOpen
        k d i j A hAi hAj
        (integerFirstScalarPairSectionOpen
          k d m i j A hAi hAj x) =
      integerChartAmbientSectionsAddEquiv
        k d m i A hAi x := by
  calc
    _ = projectiveFirstAmbientCoordinateOpen
        k d m i j A hAi hAj x := by
      unfold projectiveFirstAmbientCoordinateOpen
        integerFirstScalarPairSectionOpen
      exact (pairUnitSectionToAmbientOpen_chart_independent
        k d i j A hAi hAj _).symm
    _ = _ :=
      projectiveFirstAmbientCoordinateOpen_eq_chart
        k d m i j A hAi hAj x

def rawSecondUnscaledAmbientCastFirstToProofChangedOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  Eq.trans
    (rawSecondUnscaledAmbientCastFirstToDirectOpen
      k d m i j A hAi hAj x)
    (rawSecondUnscaledAmbientCastProofChangeOpen
      k d m i j A hAi hAj x)

lemma integerPairDirectPullbackSectionOpen_eq_restrict
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerPairDirectPullbackSectionOpen
        k d m i j A hAi hAj x =
      ((Scheme.Modules.restrictFunctorIsoPullback
        (integerPairOverlapMap k d i j)).hom.app
          (OInt k d m)).app
      (pairPreimageOpen k d i j A)
      (integerPairDirectRestrictionSectionOpen
        k d m i j A hAi hAj x) := by
  unfold integerPairDirectPullbackSectionOpen
  rfl

def rawCastDirectPullbackOpenNormalize
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (fun y =>
      ((Scheme.Modules.pullbackCongr
        (integerSecondPairOverlapMapOpen_eq_first
          k d i j)).inv.app
          (OInt k d m)).app
        (pairPreimageOpen k d i j A) y)
    (integerPairDirectPullbackSectionOpen_eq_restrict
      k d m i j A hAi hAj x)

def rawCastDirectPullbackOpenToSecondPairSection
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  Eq.trans
    (rawCastDirectPullbackOpenNormalize
      k d m i j A hAi hAj x)
    (rawCastDirectOpenToSecondPairSection
      k d m i j A hAi hAj x)

def rawCastFirstOpenToSecondPairSectionComplete
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  Eq.trans
    (rawCastFirstOpenToSecondDirect
      k d m i j A hAi hAj x)
    (rawCastDirectPullbackOpenToSecondPairSection
      k d m i j A hAi hAj x)

def rawSecondUnscaledAmbientCastFirstToSecondOpen
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (unscaledSecondAmbientOfPairSectionOpen
      k d m i j A hAi hAj)
    (rawCastFirstOpenToSecondPairSectionComplete
      k d m i j A hAi hAj x)

lemma unscaledSecondAmbientOfPairSectionOpen_second_eq_chart
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    unscaledSecondAmbientOfPairSectionOpen
        k d m i j A hAi hAj
        (integerPairOverlapSectionViaSecondChartOpen
          k d m i j A hAi hAj x) =
      integerChartAmbientSectionsAddEquiv
        k d m j A hAj x := by
  exact projectiveSecondChartAmbientCoordinateOpen_eq_chart
    k d m i j A hAi hAj x

def rawSecondUnscaledAmbientOpenEqChartRaw
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  Eq.trans
    (rawSecondUnscaledAmbientCastFirstToSecondOpen
      k d m i j A hAi hAj x)
    (unscaledSecondAmbientOfPairSectionOpen_second_eq_chart
      k d m i j A hAi hAj x)

lemma moduleHom_four_comp_app_open
    {X : Scheme}
    {M₀ M₁ M₂ M₃ M₄ : X.Modules}
    (f₀ : M₀ ⟶ M₁) (f₁ : M₁ ⟶ M₂)
    (f₂ : M₂ ⟶ M₃) (f₃ : M₃ ⟶ M₄)
    (U : X.Opens) (x : Γ(M₀, U)) :
    (((f₀ ≫ f₁) ≫ (f₂ ≫ f₃)).app U x) =
      f₃.app U (f₂.app U (f₁.app U (f₀.app U x))) := by
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]

lemma moduleHom_comp_app_apply_open
    {X : Scheme}
    {M₀ M₁ M₂ : X.Modules}
    (f₀ : M₀ ⟶ M₁) (f₁ : M₁ ⟶ M₂)
    (U : X.Opens) (x : Γ(M₀, U)) :
    (f₀ ≫ f₁).app U x =
      f₁.app U (f₀.app U x) := by
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]

def rawScalarAmbientOpenBeforeEvaluation
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChartOpen
      k d i j A hAi hAj)
    (projectiveIntegerFirstScalar_eq_rawSecondScalar_app
      k d m i j
      (pairPreimageOpen k d i j A)
      (integerPairOverlapSectionViaFirstChartOpen
        k d m i j A hAi hAj x))

def rawScalarAmbientOpenNormalize
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChartOpen
      k d i j A hAi hAj)
    (moduleHom_four_comp_app_open
      ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation
          k d i j)).inv.app
        (OInt k d m))
      (projectiveIntegerSecondChartLegCore
        k d m i j)
      (pullbackUnitIso
        (typedIntegerSecondOverlapMap k d i j)).hom
      (endomorphism
        (((overlapUnit k d i j) ^ m).inv))
      (pairPreimageOpen k d i j A)
      (integerPairOverlapSectionViaFirstChartOpen
        k d m i j A hAi hAj x))

def rawScalarAmbientOpenEvaluation
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChartOpen
      k d i j A hAi hAj)
    (endomorphism_app
      (((overlapUnit k d i j) ^ m).inv)
      (Opposite.op (pairPreimageOpen k d i j A))
      ((pullbackUnitIso
        (typedIntegerSecondOverlapMap k d i j)).hom.app
        (pairPreimageOpen k d i j A)
        ((projectiveIntegerSecondChartLegCore
          k d m i j).app
          (pairPreimageOpen k d i j A)
          (((Scheme.Modules.pullbackCongr
            (projectiveIntegerOverlapEquation
              k d i j)).inv.app
              (OInt k d m)).app
            (pairPreimageOpen k d i j A)
            (integerPairOverlapSectionViaFirstChartOpen
              k d m i j A hAi hAj x)))))

def rawScalarAmbientOpenUnscaledNormalize
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChartOpen
      k d i j A hAi hAj)
    (congrArg
      (fun z => z *
        integerInverseTransitionSectionOnPairOpen
          k d m i j A)
      (moduleHom_comp_app_apply_open
        (projectiveIntegerSecondChartLegCore
          k d m i j)
        (pullbackUnitIso
          (typedIntegerSecondOverlapMap k d i j)).hom
        (pairPreimageOpen k d i j A)
        (((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation
            k d i j)).inv.app
            (OInt k d m)).app
          (pairPreimageOpen k d i j A)
          (integerPairOverlapSectionViaFirstChartOpen
            k d m i j A hAi hAj x))).symm)

def rawScalarAmbientOpenMultiplication
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  pairUnitSectionToAmbientViaSecondChartOpen_mul
    k d i j A hAi hAj
    (show Γ(typedIntegerPairOverlapScheme k d i j,
        pairPreimageOpen k d i j A) from
      ((projectiveIntegerSecondChartLegCore
          k d m i j ≫
        (pullbackUnitIso
          (typedIntegerSecondOverlapMap k d i j)).hom).app
        (pairPreimageOpen k d i j A)
        (((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation
            k d i j)).inv.app
            (OInt k d m)).app
          (pairPreimageOpen k d i j A)
          (integerPairOverlapSectionViaFirstChartOpen
            k d m i j A hAi hAj x))))
    (integerInverseTransitionSectionOnPairOpen
      k d m i j A)

def rawSecondAmbientOpenMul_eq_chartMul
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  congrArg
    (fun z => z *
      pairUnitSectionToAmbientViaSecondChartOpen
        k d i j A hAi hAj
        (integerInverseTransitionSectionOnPairOpen
          k d m i j A))
    (rawSecondUnscaledAmbientOpenEqChartRaw
      k d m i j A hAi hAj x)

private theorem eq_trans_seven_open
    {α : Sort*} {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) (h₂ : a₂ = a₃)
    (h₃ : a₃ = a₄) (h₄ : a₄ = a₅) (h₅ : a₅ = a₆)
    (h₆ : a₆ = a₇) :
    a₀ = a₇ :=
  h₀.trans (h₁.trans
    (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))))

def integerChartAmbientCoordinateOpenTransitionRaw
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :=
  eq_trans_seven_open
    (firstScalarAmbientOpen_eq_chart
      k d m i j A hAi hAj x).symm
    (rawScalarAmbientOpenBeforeEvaluation
      k d m i j A hAi hAj x)
    (rawScalarAmbientOpenNormalize
      k d m i j A hAi hAj x)
    (rawScalarAmbientOpenEvaluation
      k d m i j A hAi hAj x)
    (rawScalarAmbientOpenUnscaledNormalize
      k d m i j A hAi hAj x)
    (rawScalarAmbientOpenMultiplication
      k d m i j A hAi hAj x)
    (rawSecondAmbientOpenMul_eq_chartMul
      k d m i j A hAi hAj x)

/-- Before identifying its scalar, the chart-`i` coordinate on an
arbitrary subopen is the chart-`j` coordinate times the transported
inverse integer transition. -/
theorem integerChartAmbientCoordinateOpen_eq_mul_transition
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d m, A)) :
    integerChartAmbientSectionsAddEquiv
        k d m i A hAi x =
      integerChartAmbientSectionsAddEquiv
          k d m j A hAj x *
        pairUnitSectionToAmbientViaSecondChartOpen
          k d i j A hAi hAj
          (integerInverseTransitionSectionOnPairOpen
            k d m i j A) :=
  integerChartAmbientCoordinateOpenTransitionRaw
    k d m i j A hAi hAj x

lemma integerPairOverlapMap_image_top_product_open
    (i j : Fin (d + 1)) :
    integerPairOverlapMap k d i j ''ᵁ
        (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j) := by
  rw [Scheme.Hom.image_top_eq_opensRange,
    integerPairOverlapMap_opensRange]
  change
    Proj.basicOpen (homogeneousGrading k d) (coordinate k i) ⊓
        Proj.basicOpen (homogeneousGrading k d) (coordinate k j) =
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
  exact (Proj.basicOpen_mul
    (homogeneousGrading k d)
    (coordinate k i) (coordinate k j)).symm

lemma opens_ι_appIso_inv_topIso_inv_transport_open
    {X : Scheme.{0}} (U : X.Opens) (r : Γ(X, U)) :
    (eqToIso (congrArg (fun W => Γ(X, W))
      U.ι_image_top)).hom
        ((U.ι.appIso ⊤).inv.hom (U.topIso.inv r)) = r := by
  have htop :
      (eqToIso (congrArg (fun W => Γ(X, W))
        U.ι_image_top)).hom = U.topIso.hom := by
    rw [Γ_eqToIso_hom_eq_presheaf_map U.ι_image_top]
    symm
    exact Scheme.Opens.topIso_hom U
  rw [htop, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv]
  exact U.topIso.inv_hom_id_apply r

lemma appIso_inv_iso_comp_opens_top_open
    {B X : Scheme.{0}} (U : X.Opens) (e : B ≅ U.toScheme)
    (hC :
      (e.hom ≫ U.ι) ''ᵁ (⊤ : B.Opens) = U)
    (r : Γ(X, U)) :
    (X.presheaf.mapIso (eqToIso hC).op).inv.hom
        (((e.hom ≫ U.ι).appIso ⊤).inv.hom
          (e.hom.appTop (U.topIso.inv r))) = r := by
  rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom]
  let ho :
      (e.hom ≫ U.ι) ''ᵁ (⊤ : B.Opens) =
        U.ι ''ᵁ (⊤ : U.toScheme.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso]
  have hnat :=
    appIso_inv_natural_iso_over e U.ι (U.topIso.inv r)
  calc
    _ = (eqToIso (congrArg (fun W => Γ(X, W))
          (ho.trans U.ι_image_top))).hom
        (((e.hom ≫ U.ι).appIso ⊤).inv.hom
          (e.hom.appTop (U.topIso.inv r))) := by
      rw [show hC = ho.trans U.ι_image_top from
        Subsingleton.elim _ _]
    _ = (eqToIso (congrArg (fun W => Γ(X, W))
          U.ι_image_top)).hom
        ((eqToIso (congrArg (fun W => Γ(X, W)) ho)).hom
          (((e.hom ≫ U.ι).appIso ⊤).inv.hom
            (e.hom.appTop (U.topIso.inv r)))) := by
      let z :=
        ((e.hom ≫ U.ι).appIso ⊤).inv.hom
          (e.hom.appTop (U.topIso.inv r))
      exact (ConcreteCategory.congr_hom
        (Γ_eqToIso_hom_trans ho U.ι_image_top) z).symm
    _ = (eqToIso (congrArg (fun W => Γ(X, W))
          U.ι_image_top)).hom
        ((U.ι.appIso ⊤).inv.hom (U.topIso.inv r)) := by
      exact congrArg
        (eqToIso (congrArg (fun W => Γ(X, W))
          U.ι_image_top)).hom hnat
    _ = r :=
      opens_ι_appIso_inv_topIso_inv_transport_open U r

lemma overlapRingHomAmbientPairSection_eq_away_open
    (i j : Fin (d + 1))
    (a : HomogeneousLocalization.Away
      (homogeneousGrading k d)
      (coordinate k i * coordinate k j)) :
    ((scheme k d).presheaf.mapIso
        (eqToIso
          (integerPairOverlapMap_image_top_product_open
            k d i j)).op).inv.hom
      (((integerPairOverlapMap k d i j).appIso ⊤).inv.hom
        (overlapRingHom k d i j a)) =
      Proj.awayToSection (homogeneousGrading k d)
        (coordinate k i * coordinate k j) a := by
  let B : (scheme k d).Opens :=
    Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
  let e : typedIntegerPairOverlapScheme k d i j ≅ B :=
    openOverlapToBasicOpenIso k d i j
  let w : Γ(scheme k d, B) :=
    Proj.awayToSection (homogeneousGrading k d)
      (coordinate k i * coordinate k j) a
  have hmap :
      integerPairOverlapMap k d i j = e.hom ≫ B.ι := by
    dsimp only [e, B]
    rw [openOverlapToBasicOpenIso_hom]
    exact (overlapHom_comp_ι k d i j).symm
  have hcomp :
      (e.hom ≫ B.ι) ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) = B := by
    calc
      (e.hom ≫ B.ι) ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) =
        B.ι ''ᵁ (e.hom ''ᵁ ⊤) :=
          Scheme.Hom.comp_image e.hom B.ι ⊤
      _ = B.ι ''ᵁ ⊤ := by
        congr 1
        rw [Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso]
      _ = B := B.ι_image_top
  have hsection :
      overlapRingHom k d i j a =
        e.hom.appTop (B.topIso.inv w) := by
    dsimp only [e, B, w, overlapRingHom]
    rw [openOverlapToBasicOpenIso_hom]
    rfl
  change
    ((scheme k d).presheaf.mapIso
        (eqToIso
          (integerPairOverlapMap_image_top_product_open
            k d i j)).op).inv.hom
      (((integerPairOverlapMap k d i j).appIso ⊤).inv.hom
        (overlapRingHom k d i j a)) = w
  calc
    _ = ((scheme k d).presheaf.mapIso
          (eqToIso hcomp).op).inv.hom
        (((e.hom ≫ B.ι).appIso ⊤).inv.hom
          (overlapRingHom k d i j a)) := by
      exact appIso_inv_congr_transport_open hmap
        (⊤ : (typedIntegerPairOverlapScheme k d i j).Opens) B
        (integerPairOverlapMap_image_top_product_open
          k d i j)
        hcomp (overlapRingHom k d i j a)
    _ = ((scheme k d).presheaf.mapIso
          (eqToIso hcomp).op).inv.hom
        (((e.hom ≫ B.ι).appIso ⊤).inv.hom
          (e.hom.appTop (B.topIso.inv w))) := by
      exact congrArg
        (fun z =>
          ((scheme k d).presheaf.mapIso
            (eqToIso hcomp).op).inv.hom
            (((e.hom ≫ B.ι).appIso ⊤).inv.hom z))
        hsection
    _ = w :=
      appIso_inv_iso_comp_opens_top_open B e hcomp w

lemma overlapUnit_zpow_inv_val_eq_open
    (m : ℤ) (i j : Fin (d + 1)) :
    (((overlapUnit k d i j) ^ m).inv :
      Γ(typedIntegerPairOverlapScheme k d i j, ⊤)) =
      overlapRingHom k d i j
        ((((awayUnit k d i j) ^ m)⁻¹).val) := by
  unfold overlapUnit
  change
    ((((Units.map (overlapRingHom k d i j).toMonoidHom)
        (awayUnit k d i j) ^ m)⁻¹).val) =
      ((Units.map (overlapRingHom k d i j).toMonoidHom)
        (((awayUnit k d i j) ^ m)⁻¹)).val
  rw [← map_zpow, ← map_inv]

lemma appIso_inv_global_restriction_transport_open
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) (W B : Y.Opens)
    (hW : f ''ᵁ U = W)
    (hB : f ''ᵁ (⊤ : X.Opens) = B)
    (hWB : W ≤ B) (s : Γ(X, ⊤)) :
    (Y.presheaf.mapIso (eqToIso hW).op).inv.hom
        ((f.appIso U).inv.hom
          (X.presheaf.map
            (homOfLE
              (show U ≤ (⊤ : X.Opens) from le_top)).op s)) =
      Y.presheaf.map (homOfLE hWB).op
        ((Y.presheaf.mapIso (eqToIso hB).op).inv.hom
          ((f.appIso ⊤).inv.hom s)) := by
  rw [appIso_inv_restriction]
  exact presheafMapIsoSymm_restriction
    hB hW
    (Scheme.Hom.image_mono f
      (show U ≤ (⊤ : X.Opens) from le_top))
    hWB
    ((f.appIso ⊤).inv.hom s)

lemma pairOpen_le_pairProduct
    (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j) :
    A ≤ Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j) := by
  rw [Proj.basicOpen_mul]
  exact le_inf hAi hAj

lemma inverseTransitionAmbientOpen_eq_productAwayRestriction
    (m : ℤ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j) :
    pairUnitSectionToAmbientViaSecondChartOpen
        k d i j A hAi hAj
        (integerInverseTransitionSectionOnPairOpen
          k d m i j A) =
      (scheme k d).presheaf.map
        (homOfLE
          (pairOpen_le_pairProduct
            k d i j A hAi hAj)).op
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i * coordinate k j)
          ((((awayUnit k d i j) ^ m)⁻¹).val)) := by
  let U := pairPreimageOpen k d i j A
  let B : (scheme k d).Opens :=
    Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
  let a :
      HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (coordinate k i * coordinate k j) :=
    ((((awayUnit k d i j) ^ m)⁻¹).val)
  calc
    _ = pairUnitSectionToAmbientViaFirstChartOpen
        k d i j A hAi hAj
        (integerInverseTransitionSectionOnPairOpen
          k d m i j A) :=
      (pairUnitSectionToAmbientOpen_chart_independent
        k d i j A hAi hAj _).symm
    _ = pairUnitSectionToAmbientDirectOpen
        k d i j A hAi hAj
        (integerInverseTransitionSectionOnPairOpen
          k d m i j A) :=
      pairUnitSectionToAmbientViaFirstChartOpen_eq_direct
        k d i j A hAi hAj _
    _ = (scheme k d).presheaf.map
        (homOfLE
          (pairOpen_le_pairProduct
            k d i j A hAi hAj)).op
        (((scheme k d).presheaf.mapIso
          (eqToIso
            (integerPairOverlapMap_image_top_product_open
              k d i j)).op).inv.hom
          (((integerPairOverlapMap k d i j).appIso ⊤).inv.hom
            (((overlapUnit k d i j) ^ m).inv))) := by
      unfold pairUnitSectionToAmbientDirectOpen
        integerInverseTransitionSectionOnPairOpen
      exact appIso_inv_global_restriction_transport_open
        (integerPairOverlapMap k d i j)
        U A B
        (pairPreimageOpen_image k d i j A
          (le_inf hAi hAj))
        (integerPairOverlapMap_image_top_product_open
          k d i j)
        (pairOpen_le_pairProduct k d i j A hAi hAj)
        (((overlapUnit k d i j) ^ m).inv)
    _ = (scheme k d).presheaf.map
        (homOfLE
          (pairOpen_le_pairProduct
            k d i j A hAi hAj)).op
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i * coordinate k j) a) := by
      apply congrArg
        ((scheme k d).presheaf.map
          (homOfLE
            (pairOpen_le_pairProduct
              k d i j A hAi hAj)).op).hom
      rw [overlapUnit_zpow_inv_val_eq_open]
      exact overlapRingHomAmbientPairSection_eq_away_open
        k d i j a

lemma awayUnit_zpow_neg_inv_val_open
    (N : ℕ) (i j : Fin (d + 1)) :
    ((((awayUnit k d i j) ^ (-(N : ℤ)))⁻¹).val) =
      (awayFraction k d i j) ^ N := by
  rw [zpow_neg, inv_inv, zpow_natCast]
  rfl

lemma chartPairAwaySection_restrict_open
    (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j) :
    (scheme k d).presheaf.map
        (homOfLE (le_inf hAj hAi)).op
        (chartPairAwaySection k d i j) =
      (scheme k d).presheaf.map
        (homOfLE
          (pairOpen_le_pairProduct
            k d i j A hAi hAj)).op
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i * coordinate k j)
          (awayFraction k d i j)) := by
  let hUB :=
    standardChart_inf_eq_productBasicOpen k d i j
  unfold chartPairAwaySection
  rw [Γ_eqToIso_inv_eq_presheaf_map hUB]
  change
    (scheme k d).presheaf.map
        (homOfLE (le_inf hAj hAi)).op
        ((scheme k d).presheaf.map
          (eqToHom hUB).op
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i * coordinate k j)
            (awayFraction k d i j))) =
      _
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg
      (fun r => (scheme k d).presheaf.map r)
      (Subsingleton.elim _ _))
    (Proj.awayToSection (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
      (awayFraction k d i j))

lemma inverseTransitionAmbientOpen_neg_eq_chartScalarPow
    (N : ℕ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j) :
    pairUnitSectionToAmbientViaSecondChartOpen
        k d i j A hAi hAj
        (integerInverseTransitionSectionOnPairOpen
          k d (-(N : ℤ)) i j A) =
      (scheme k d).presheaf.map
        (homOfLE (le_inf hAj hAi)).op
        (chartScalarOnPair k d i j
          (chartRatioElement k d i j) ^ N) := by
  rw [inverseTransitionAmbientOpen_eq_productAwayRestriction]
  rw [awayUnit_zpow_neg_inv_val_open]
  rw [chartScalarOnPair_chartRatio]
  simp only [map_pow]
  exact congrArg (fun z => z ^ N)
    (chartPairAwaySection_restrict_open
      k d i j A hAi hAj).symm

/-- On every ambient subopen of a pairwise chart intersection, the
negative integer-twist coordinates differ by the expected power of the
coordinate ratio. -/
theorem integerChartAmbientCoordinateOpenTransition
    (N : ℕ) (i j : Fin (d + 1))
    (A : (scheme k d).Opens)
    (hAi : A ≤ standardChart k i)
    (hAj : A ≤ standardChart k j)
    (x : Γ(OInt k d (-(N : ℤ)), A)) :
    integerChartAmbientSectionsAddEquiv
        k d (-(N : ℤ)) i A hAi x =
      (scheme k d).presheaf.map
          (homOfLE (le_inf hAj hAi)).op
          (chartScalarOnPair k d i j
            (chartRatioElement k d i j) ^ N) *
        integerChartAmbientSectionsAddEquiv
          k d (-(N : ℤ)) j A hAj x := by
  calc
    _ = integerChartAmbientSectionsAddEquiv
          k d (-(N : ℤ)) j A hAj x *
        pairUnitSectionToAmbientViaSecondChartOpen
          k d i j A hAi hAj
          (integerInverseTransitionSectionOnPairOpen
            k d (-(N : ℤ)) i j A) :=
      integerChartAmbientCoordinateOpen_eq_mul_transition
        k d (-(N : ℤ)) i j A hAi hAj x
    _ = integerChartAmbientSectionsAddEquiv
          k d (-(N : ℤ)) j A hAj x *
        (scheme k d).presheaf.map
          (homOfLE (le_inf hAj hAi)).op
          (chartScalarOnPair k d i j
            (chartRatioElement k d i j) ^ N) := by
      exact congrArg
        (fun z =>
          integerChartAmbientSectionsAddEquiv
            k d (-(N : ℤ)) j A hAj x * z)
        (inverseTransitionAmbientOpen_neg_eq_chartScalarPow
          k d N i j A hAi hAj)
    _ = _ := mul_comm _ _

/-- Integer Serre-twist chart coordinates obey their transition law over
every commutative base ring. -/
theorem integerOverChartCoordinateTransition
    (N : ℕ) :
    IntegerOverChartCoordinateTransition k d N := by
  intro j l V x
  let A : (scheme k d).Opens := V.unop.left
  let hA :
      A ≤ standardChart k j ⊓ standardChart k l :=
    leOfHom V.unop.hom
  let hAl : A ≤ standardChart k l :=
    hA.trans inf_le_right
  let hAj : A ≤ standardChart k j :=
    hA.trans inf_le_left
  have ht :=
    integerOverChartIso_hom_app_eq_ambientCoordinate
      k d (-(N : ℤ)) l
      ((Over.map
        (Opens.infLERight
          (standardChart k j) (standardChart k l))).op.obj V) x
  have hs :=
    integerOverChartIso_hom_app_eq_ambientCoordinate
      k d (-(N : ℤ)) j
      ((Over.map
        (Opens.infLELeft
          (standardChart k j) (standardChart k l))).op.obj V) x
  change
    (show Γ(scheme k d, A) from
      (integerOverChartIso k d (-(N : ℤ)) l).hom.val.app
        ((Over.map
          (Opens.infLERight
            (standardChart k j) (standardChart k l))).op.obj V) x) =
      (scheme k d).presheaf.map V.unop.hom.op
          (chartScalarOnPair k d l j
            (chartRatioElement k d l j) ^ N) *
        (show Γ(scheme k d, A) from
          (integerOverChartIso k d (-(N : ℤ)) j).hom.val.app
            ((Over.map
              (Opens.infLELeft
                (standardChart k j) (standardChart k l))).op.obj V) x)
  rw [show
      leOfHom
          (((Over.map
            (Opens.infLERight
              (standardChart k j)
              (standardChart k l))).op.obj V).unop.hom) =
        hAl
    from Subsingleton.elim _ _] at ht
  rw [show
      leOfHom
          (((Over.map
            (Opens.infLELeft
              (standardChart k j)
              (standardChart k l))).op.obj V).unop.hom) =
        hAj
    from Subsingleton.elim _ _] at hs
  rw [ht, hs]
  have htransition :=
    integerChartAmbientCoordinateOpenTransition
      k d N l j A hAl hAj x
  rw [show
    (homOfLE (le_inf hAj hAl) :
        A ⟶ standardChart k j ⊓ standardChart k l) =
      V.unop.hom
    from Subsingleton.elim _ _] at htransition
  exact htransition

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
