/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenCoordinateEvaluation
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentCoordinateTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartAnchor
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleUnitHomExt
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionHom
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionTransport

/-!
# Rational integer-twist coordinate transitions on standard-chart overlaps

The Laurent transition calculation for `𝒪(-N)` is transported to the
terminal open of each pairwise standard-chart intersection.  Extensionality
for maps out of the unit sheaf then propagates the calculation to every
slice-site object, proving `IntegerOverChartCoordinateTransition ℚ d N`.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable (d : ℕ)

def integerOverSubopenChartIso
    (m : ℤ) (i : Fin (d + 1))
    (U : (scheme ℚ d).Opens)
    (hU : U ≤ standardChart ℚ i) :
    (OInt ℚ d m).over U ≅
      SheafOfModules.unit ((scheme ℚ d).ringCatSheaf.over U) :=
  ((SheafOfModules.overFunctorMap
      (scheme ℚ d).ringCatSheaf
      (homOfLE hU)).app (OInt ℚ d m)).symm ≪≫
    (SheafOfModules.overMap
      (scheme ℚ d).ringCatSheaf
      (homOfLE hU)).mapIso
        (integerOverChartIso ℚ d m i) ≪≫
    SheafOfModules.overMapUnitIso
      (R := (scheme ℚ d).ringCatSheaf)
      (homOfLE hU)

lemma integerOverSubopenChartIso_hom_app
    (m : ℤ) (i : Fin (d + 1))
    (U : (scheme ℚ d).Opens)
    (hU : U ≤ standardChart ℚ i)
    (V : (Over U)ᵒᵖ)
    (x : (OInt ℚ d m).val.obj (op V.unop.left)) :
    (integerOverSubopenChartIso d m i U hU).hom.val.app V x =
      (integerOverChartIso ℚ d m i).hom.val.app
        ((Over.map (homOfLE hU)).op.obj V) x := by
  unfold integerOverSubopenChartIso
  simp only [Iso.trans_hom, SheafOfModules.comp_val]
  rfl

lemma integerOverSubopenChartIso_hom_app_terminal
    (m : ℤ) (i : Fin (d + 1))
    (U : (scheme ℚ d).Opens)
    (hU : U ≤ standardChart ℚ i)
    (x : Γ(OInt ℚ d m, U)) :
    (integerOverSubopenChartIso d m i U hU).hom.val.app
        (op (Over.mk (𝟙 U))) x =
      integerChartAmbientSectionsAddEquiv
        ℚ d m i U hU x := by
  let y : Γ(scheme ℚ d, U) :=
    (integerOverChartIso ℚ d m i).hom.val.app
          ((Over.map (homOfLE hU)).op.obj
            (op (Over.mk (𝟙 U)))) x
  have hleft :
      (integerOverSubopenChartIso d m i U hU).hom.val.app
          (op (Over.mk (𝟙 U))) x = y :=
    integerOverSubopenChartIso_hom_app
      d m i U hU (op (Over.mk (𝟙 U))) x
  have hright :
      y = integerChartAmbientSectionsAddEquiv
        ℚ d m i U hU x := by
    have hcoordinate :=
      integerOverChartIso_hom_app_eq_ambientCoordinate
        ℚ d m i
          ((Over.map (homOfLE hU)).op.obj
            (op (Over.mk (𝟙 U)))) x
    change y = integerChartAmbientSectionsAddEquiv
      ℚ d m i U hU x at hcoordinate
    exact hcoordinate
  exact hleft.trans hright

def openScalarEndomorphism
    (U : (scheme ℚ d).Opens) (q : Γ(scheme ℚ d, U)) :
    SheafOfModules.unit ((scheme ℚ d).ringCatSheaf.over U) ⟶
      SheafOfModules.unit ((scheme ℚ d).ringCatSheaf.over U) :=
  homOfOpenSection
    (SheafOfModules.unit (scheme ℚ d).ringCatSheaf) U q

lemma chartScalarOnPair_one
    (k : Type) [CommRing k]
    (i j : Fin (d + 1)) :
    chartScalarOnPair k d i j 1 = 1 := by
  unfold chartScalarOnPair
  dsimp only
  rw [(Scheme.ΓSpecIso (chartRing k d j)).inv.hom.map_one]
  rw [((Spec (chartRing k d j)).presheaf.map
    (PrimeSpectrum.basicOpen
      (chartRatioElement k d i j)).leTop.op).hom.map_one]
  calc
    _ = (ConcreteCategory.hom
          (eqToIso (congrArg
            (fun V => Γ(scheme k d, V))
            (standardAffineCover_image_chartRatio
              k d i j))).hom) 1 := by
      exact congrArg
        (ConcreteCategory.hom
          (eqToIso (congrArg
            (fun V => Γ(scheme k d, V))
            (standardAffineCover_image_chartRatio
              k d i j))).hom)
        ((((standardAffineOpenCover k d).f j).appIso
          (PrimeSpectrum.basicOpen
            (chartRatioElement k d i j))).inv.hom.map_one)
    _ = 1 :=
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V))
        (standardAffineCover_image_chartRatio
          k d i j))).hom.hom.map_one

lemma pairIntersection_eq_coordinatePairLaurent
    (l j : Fin (d + 1)) (hlj : l ≠ j) :
    standardChart ℚ j ⊓ standardChart ℚ l =
      laurentOpen ℚ d (coordinatePair l j) := by
  rw [standardChart_inf_eq_productBasicOpen]
  unfold laurentOpen
  rw [variableProduct_coordinatePair (k := ℚ) hlj]

lemma integerChartAmbientSectionsAddEquiv_eq_laurent
    (m : ℤ) (I : Finset (Fin (d + 1)))
    (i : ↥I) (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerChartAmbientSectionsAddEquiv
        ℚ d m i.1 (laurentOpen ℚ d I)
        (laurentOpen_le_standardChart ℚ d I i) x =
      integerChartLaurentSectionsAddEquiv d m I i x := by
  unfold integerChartAmbientSectionsAddEquiv
    integerChartLaurentSectionsAddEquiv
    chartPreimageOpen chartPreimageLaurentOpen
    integerRestrictionChartIso integerChartRestrictIso
  rfl

lemma awayUnit_zpow_neg_inv_val
    (N : ℕ) (l j : Fin (d + 1)) :
    ((((awayUnit ℚ d l j) ^ (-(N : ℤ)))⁻¹).val) =
      (awayFraction ℚ d l j) ^ N := by
  rw [zpow_neg, inv_inv, zpow_natCast]
  rfl

lemma inverseTransitionOnCoordinatePair_eq_chartScalarPow
    (N : ℕ) (l j : Fin (d + 1)) (hlj : l ≠ j) :
    pairUnitSectionToAmbientViaSecondChart d
        (coordinatePair l j)
        (coordinatePairLeft l j)
        (coordinatePairRight l j)
        (integerInverseTransitionSectionOnPair d (-(N : ℤ))
          (coordinatePair l j)
          (coordinatePairLeft l j)
          (coordinatePairRight l j)) =
      ((scheme ℚ d).presheaf.mapIso
        (eqToIso
          (pairIntersection_eq_coordinatePairLaurent
            d l j hlj)).op).inv.hom
        (chartScalarOnPair ℚ d l j
          (chartRatioElement ℚ d l j) ^ N) := by
  rw [inverseTransitionAmbient_eq_productAwayRestriction]
  rw [awayUnit_zpow_neg_inv_val]
  rw [chartScalarOnPair_chartRatio]
  unfold chartPairAwaySection
  simp only [map_pow]
  apply congrArg (fun z => z ^ N)
  dsimp only [coordinatePairLeft, coordinatePairRight]
  let U : (scheme ℚ d).Opens :=
    standardChart ℚ j ⊓ standardChart ℚ l
  let B : (scheme ℚ d).Opens :=
    Proj.basicOpen (homogeneousGrading ℚ d)
      (coordinate ℚ l * coordinate ℚ j)
  let L : (scheme ℚ d).Opens :=
    laurentOpen ℚ d (coordinatePair l j)
  let hUB : U = B :=
    standardChart_inf_eq_productBasicOpen ℚ d l j
  let hUL : U = L :=
    pairIntersection_eq_coordinatePairLaurent d l j hlj
  let hLB : L = B := hUL.symm.trans hUB
  let hle : L ≤ B :=
    laurentOpen_le_pairProduct d
      (coordinatePair l j)
      (coordinatePairLeft l j)
      (coordinatePairRight l j)
  have hmap :
      (scheme ℚ d).presheaf.map (homOfLE hle).op =
        (scheme ℚ d).presheaf.map (eqToHom hLB).op := by
    congr 1
  erw [show
    laurentOpen_le_pairProduct d
      (coordinatePair l j)
      (coordinatePairLeft l j)
      (coordinatePairRight l j) = hle
    from Subsingleton.elim _ _]
  rw [hmap]
  rw [← Γ_eqToIso_inv_eq_presheaf_map hLB]
  rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom hUL]
  rw [Γ_eqToIso_inv_eq_hom_symm hLB]
  rw [Γ_eqToIso_inv_eq_hom_symm hUB]
  rw [← Γ_eqToIso_hom_trans_apply hUB.symm hUL]
  rfl

lemma integerCoordinatePairLaurentTransition
    (N : ℕ) (l j : Fin (d + 1)) (hlj : l ≠ j)
    (x : Γ(OInt ℚ d (-(N : ℤ)),
      laurentOpen ℚ d (coordinatePair l j))) :
    integerChartLaurentSectionsAddEquiv d (-(N : ℤ))
        (coordinatePair l j) (coordinatePairLeft l j) x =
      ((scheme ℚ d).presheaf.mapIso
        (eqToIso
          (pairIntersection_eq_coordinatePairLaurent
            d l j hlj)).op).inv.hom
          (chartScalarOnPair ℚ d l j
            (chartRatioElement ℚ d l j) ^ N) *
        integerChartLaurentSectionsAddEquiv d (-(N : ℤ))
          (coordinatePair l j) (coordinatePairRight l j) x := by
  calc
    _ = integerChartLaurentSectionsAddEquiv d (-(N : ℤ))
          (coordinatePair l j) (coordinatePairRight l j) x *
        pairUnitSectionToAmbientViaSecondChart d
          (coordinatePair l j)
          (coordinatePairLeft l j)
          (coordinatePairRight l j)
          (integerInverseTransitionSectionOnPair d (-(N : ℤ))
            (coordinatePair l j)
            (coordinatePairLeft l j)
            (coordinatePairRight l j)) :=
      integerChartAmbientCoordinate_eq_mul_transition d (-(N : ℤ))
        (coordinatePair l j)
        (coordinatePairLeft l j)
        (coordinatePairRight l j) x
    _ = integerChartLaurentSectionsAddEquiv d (-(N : ℤ))
          (coordinatePair l j) (coordinatePairRight l j) x *
        ((scheme ℚ d).presheaf.mapIso
          (eqToIso
            (pairIntersection_eq_coordinatePairLaurent
              d l j hlj)).op).inv.hom
            (chartScalarOnPair ℚ d l j
              (chartRatioElement ℚ d l j) ^ N) := by
      exact congrArg
        (fun z =>
          integerChartLaurentSectionsAddEquiv d (-(N : ℤ))
            (coordinatePair l j) (coordinatePairRight l j) x * z)
        (inverseTransitionOnCoordinatePair_eq_chartScalarPow
          d N l j hlj)
    _ = _ := mul_comm _ _

lemma integerPairTopAmbientCoordinateTransition
    (N : ℕ) (l j : Fin (d + 1)) (hlj : l ≠ j)
    (x : Γ(OInt ℚ d (-(N : ℤ)),
      standardChart ℚ j ⊓ standardChart ℚ l)) :
    integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ)) l
        (standardChart ℚ j ⊓ standardChart ℚ l)
        inf_le_right x =
      chartScalarOnPair ℚ d l j
          (chartRatioElement ℚ d l j) ^ N *
        integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ)) j
          (standardChart ℚ j ⊓ standardChart ℚ l)
          inf_le_left x := by
  let U : (scheme ℚ d).Opens :=
    standardChart ℚ j ⊓ standardChart ℚ l
  let L : (scheme ℚ d).Opens :=
    laurentOpen ℚ d (coordinatePair l j)
  let hUL : U = L :=
    pairIntersection_eq_coordinatePairLaurent d l j hlj
  let e :=
    (scheme ℚ d).presheaf.mapIso (eqToIso hUL).op
  apply e.symm.commRingCatIsoToRingEquiv.injective
  rw [map_mul]
  change
    e.inv.hom
        (integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ))
          l U inf_le_right x) =
      e.inv.hom
          (chartScalarOnPair ℚ d l j
            (chartRatioElement ℚ d l j) ^ N) *
        e.inv.hom
          (integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ))
            j U inf_le_left x)
  rw [integerChartAmbientSectionsAddEquiv_eqToIso
    ℚ d (-(N : ℤ)) l hUL inf_le_right
    (laurentOpen_le_standardChart ℚ d
      (coordinatePair l j) (coordinatePairLeft l j)) x]
  rw [integerChartAmbientSectionsAddEquiv_eqToIso
    ℚ d (-(N : ℤ)) j hUL inf_le_left
    (laurentOpen_le_standardChart ℚ d
      (coordinatePair l j) (coordinatePairRight l j)) x]
  dsimp only [L]
  change
    integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ))
        (coordinatePairLeft l j).1
        (laurentOpen ℚ d (coordinatePair l j))
        (laurentOpen_le_standardChart ℚ d
          (coordinatePair l j) (coordinatePairLeft l j))
        (((OInt ℚ d (-(N : ℤ))).presheaf.mapIso
          (eqToIso hUL).op).inv.hom x) =
      e.inv.hom
          (chartScalarOnPair ℚ d l j
            (chartRatioElement ℚ d l j) ^ N) *
        integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ))
          (coordinatePairRight l j).1
          (laurentOpen ℚ d (coordinatePair l j))
          (laurentOpen_le_standardChart ℚ d
            (coordinatePair l j) (coordinatePairRight l j))
          (((OInt ℚ d (-(N : ℤ))).presheaf.mapIso
            (eqToIso hUL).op).inv.hom x)
  rw [integerChartAmbientSectionsAddEquiv_eq_laurent
      d (-(N : ℤ)) (coordinatePair l j)
        (coordinatePairLeft l j),
    integerChartAmbientSectionsAddEquiv_eq_laurent
      d (-(N : ℤ)) (coordinatePair l j)
        (coordinatePairRight l j)]
  exact integerCoordinatePairLaurentTransition d N l j hlj
    (((OInt ℚ d (-(N : ℤ))).presheaf.mapIso
      (eqToIso hUL).op).inv.hom x)

def integerPairSourceChartIso
    (N : ℕ) (j l : Fin (d + 1)) :=
  integerOverSubopenChartIso d (-(N : ℤ)) j
    (standardChart ℚ j ⊓ standardChart ℚ l) inf_le_left

def integerPairTargetChartIso
    (N : ℕ) (j l : Fin (d + 1)) :=
  integerOverSubopenChartIso d (-(N : ℤ)) l
    (standardChart ℚ j ⊓ standardChart ℚ l) inf_le_right

def integerPairTransitionScalar
    (N : ℕ) (l j : Fin (d + 1)) :
    Γ(scheme ℚ d, standardChart ℚ j ⊓ standardChart ℚ l) :=
  chartScalarOnPair ℚ d l j
    (chartRatioElement ℚ d l j) ^ N

def integerPairTopSourceSection
    (N : ℕ) (j l : Fin (d + 1)) :
    Γ(OInt ℚ d (-(N : ℤ)),
      standardChart ℚ j ⊓ standardChart ℚ l) :=
  (integerPairSourceChartIso d N j l).inv.val.app
      (op (Over.mk
        (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
    (1 : Γ(scheme ℚ d,
      standardChart ℚ j ⊓ standardChart ℚ l))

lemma integerPairSourceChartIso_hom_app
    (N : ℕ) (j l : Fin (d + 1))
    (V : (Over
      (standardChart ℚ j ⊓ standardChart ℚ l))ᵒᵖ)
    (x : (OInt ℚ d (-(N : ℤ))).val.obj
      (op V.unop.left)) :
    (integerPairSourceChartIso d N j l).hom.val.app V x =
      (integerOverChartIso ℚ d (-(N : ℤ)) j).hom.val.app
        ((Over.map
          (Opens.infLELeft
            (standardChart ℚ j)
            (standardChart ℚ l))).op.obj V) x := by
  unfold integerPairSourceChartIso
  exact integerOverSubopenChartIso_hom_app
    d (-(N : ℤ)) j
      (standardChart ℚ j ⊓ standardChart ℚ l)
      inf_le_left V x

lemma integerPairTargetChartIso_hom_app
    (N : ℕ) (j l : Fin (d + 1))
    (V : (Over
      (standardChart ℚ j ⊓ standardChart ℚ l))ᵒᵖ)
    (x : (OInt ℚ d (-(N : ℤ))).val.obj
      (op V.unop.left)) :
    (integerPairTargetChartIso d N j l).hom.val.app V x =
      (integerOverChartIso ℚ d (-(N : ℤ)) l).hom.val.app
        ((Over.map
          (Opens.infLERight
            (standardChart ℚ j)
            (standardChart ℚ l))).op.obj V) x := by
  unfold integerPairTargetChartIso
  exact integerOverSubopenChartIso_hom_app
    d (-(N : ℤ)) l
      (standardChart ℚ j ⊓ standardChart ℚ l)
      inf_le_right V x

lemma integerPairSourceChartIso_hom_app_terminal
    (N : ℕ) (j l : Fin (d + 1))
    (x : Γ(OInt ℚ d (-(N : ℤ)),
      standardChart ℚ j ⊓ standardChart ℚ l)) :
    (integerPairSourceChartIso d N j l).hom.val.app
        (op (Over.mk
          (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l)))) x =
      integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ)) j
        (standardChart ℚ j ⊓ standardChart ℚ l)
        inf_le_left x := by
  unfold integerPairSourceChartIso
  exact integerOverSubopenChartIso_hom_app_terminal
    d (-(N : ℤ)) j
      (standardChart ℚ j ⊓ standardChart ℚ l)
      inf_le_left x

lemma integerPairTargetChartIso_hom_app_terminal
    (N : ℕ) (j l : Fin (d + 1))
    (x : Γ(OInt ℚ d (-(N : ℤ)),
      standardChart ℚ j ⊓ standardChart ℚ l)) :
    (integerPairTargetChartIso d N j l).hom.val.app
        (op (Over.mk
          (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l)))) x =
      integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ)) l
        (standardChart ℚ j ⊓ standardChart ℚ l)
        inf_le_right x := by
  unfold integerPairTargetChartIso
  exact integerOverSubopenChartIso_hom_app_terminal
    d (-(N : ℤ)) l
      (standardChart ℚ j ⊓ standardChart ℚ l)
      inf_le_right x

lemma integerPairTopSourceSection_sourceCoordinate
    (N : ℕ) (j l : Fin (d + 1)) :
    integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ)) j
        (standardChart ℚ j ⊓ standardChart ℚ l)
        inf_le_left
        (integerPairTopSourceSection d N j l) = 1 := by
  have hid :
      (integerPairSourceChartIso d N j l).hom.val.app
          (op (Over.mk
            (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
          (integerPairTopSourceSection d N j l) =
        (1 : Γ(scheme ℚ d,
          standardChart ℚ j ⊓ standardChart ℚ l)) := by
    change
      ((integerPairSourceChartIso d N j l).inv ≫
        (integerPairSourceChartIso d N j l).hom).val.app
          (op (Over.mk
            (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
          (1 : Γ(scheme ℚ d,
            standardChart ℚ j ⊓ standardChart ℚ l)) =
        (1 : Γ(scheme ℚ d,
          standardChart ℚ j ⊓ standardChart ℚ l))
    rw [(integerPairSourceChartIso d N j l).inv_hom_id]
    rfl
  have hterm :=
    integerPairSourceChartIso_hom_app_terminal d N j l
      (integerPairTopSourceSection d N j l)
  exact hterm.symm.trans hid

lemma integerPairTopSourceSection_targetCoordinate
    (N : ℕ) (j l : Fin (d + 1)) (hlj : l ≠ j) :
    integerChartAmbientSectionsAddEquiv ℚ d (-(N : ℤ)) l
        (standardChart ℚ j ⊓ standardChart ℚ l)
        inf_le_right
        (integerPairTopSourceSection d N j l) =
      integerPairTransitionScalar d N l j := by
  have h :=
    integerPairTopAmbientCoordinateTransition d N l j hlj
      (integerPairTopSourceSection d N j l)
  rw [integerPairTopSourceSection_sourceCoordinate,
    mul_one] at h
  exact h

lemma integerPairTransitionScalarEndomorphism_top_one
    (N : ℕ) (j l : Fin (d + 1)) :
    (openScalarEndomorphism d
      (standardChart ℚ j ⊓ standardChart ℚ l)
      (integerPairTransitionScalar d N l j)).val.app
        (op (Over.mk
          (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
        (1 : Γ(scheme ℚ d,
          standardChart ℚ j ⊓ standardChart ℚ l)) =
      integerPairTransitionScalar d N l j := by
  let U : (scheme ℚ d).Opens :=
    standardChart ℚ j ⊓ standardChart ℚ l
  let q : Γ(scheme ℚ d, U) :=
    integerPairTransitionScalar d N l j
  have hfirst :
      (openScalarEndomorphism d U q).val.app
          (op (Over.mk (𝟙 U)))
          (1 : Γ(scheme ℚ d, U)) =
        (SheafOfModules.unit
          (scheme ℚ d).ringCatSheaf).val.map
          (homOfLE (le_refl U)).op q :=
    homOfOpenSection_app_one
      (M := SheafOfModules.unit
        (scheme ℚ d).ringCatSheaf)
      (U := U) q U (le_refl U)
  have hsecond :
      (SheafOfModules.unit
          (scheme ℚ d).ringCatSheaf).val.map
          (homOfLE (le_refl U)).op q = q := by
    change
      (scheme ℚ d).presheaf.map
        (homOfLE (le_refl U)).op q = q
    rw [show
      (homOfLE (le_refl U)).op = 𝟙 (op U)
      from Subsingleton.elim _ _]
    exact ConcreteCategory.congr_hom
      ((scheme ℚ d).presheaf.map_id (op U)) q
  exact hfirst.trans hsecond

lemma openScalarEndomorphism_app
    (U : (scheme ℚ d).Opens) (q : Γ(scheme ℚ d, U))
    (V : (Over U)ᵒᵖ)
    (r : ((scheme ℚ d).ringCatSheaf.over U).obj.obj V) :
    (openScalarEndomorphism d U q).val.app V r =
      r * (show
        ((scheme ℚ d).ringCatSheaf.over U).obj.obj V
        from (scheme ℚ d).presheaf.map V.unop.hom.op q) := by
  have h := homOfOpenSection_app
    (SheafOfModules.unit
      (scheme ℚ d).ringCatSheaf) U q V r
  change
    (openScalarEndomorphism d U q).val.app V r =
      r * (show
        ((scheme ℚ d).ringCatSheaf.over U).obj.obj V
        from (scheme ℚ d).presheaf.map V.unop.hom.op q)
    at h
  exact h

/-- The composite of the two coordinate trivializations on a pairwise
chart intersection. -/
noncomputable def integerPairCoordinateComposite
    (N : ℕ) (j l : Fin (d + 1)) :
    SheafOfModules.unit ((scheme ℚ d).ringCatSheaf.over
        (standardChart ℚ j ⊓ standardChart ℚ l)) ⟶
      SheafOfModules.unit ((scheme ℚ d).ringCatSheaf.over
        (standardChart ℚ j ⊓ standardChart ℚ l)) :=
  (integerPairSourceChartIso d N j l).inv ≫
    (integerPairTargetChartIso d N j l).hom

/-- The scalar transition endomorphism on a pairwise chart intersection. -/
noncomputable def integerPairScalarEndomorphism
    (N : ℕ) (j l : Fin (d + 1)) :
    SheafOfModules.unit ((scheme ℚ d).ringCatSheaf.over
        (standardChart ℚ j ⊓ standardChart ℚ l)) ⟶
      SheafOfModules.unit ((scheme ℚ d).ringCatSheaf.over
        (standardChart ℚ j ⊓ standardChart ℚ l)) :=
  openScalarEndomorphism d
    (standardChart ℚ j ⊓ standardChart ℚ l)
    (integerPairTransitionScalar d N l j)

/-- The composite of the two chart coordinates, evaluated at `1` on the
terminal object of the pair-intersection slice site. -/
noncomputable def integerPairCoordinateCompositeTopOne
    (N : ℕ) (j l : Fin (d + 1)) :
    Γ(scheme ℚ d, standardChart ℚ j ⊓ standardChart ℚ l) :=
  (integerPairCoordinateComposite d N j l).val.app
    (op (Over.mk
      (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
    (1 : Γ(scheme ℚ d,
      standardChart ℚ j ⊓ standardChart ℚ l))

/-- The scalar endomorphism evaluated at `1` on the terminal object of
the pair-intersection slice site. -/
noncomputable def integerPairScalarEndomorphismTopOne
    (N : ℕ) (j l : Fin (d + 1)) :
    Γ(scheme ℚ d, standardChart ℚ j ⊓ standardChart ℚ l) :=
  (integerPairScalarEndomorphism d N j l).val.app
    (op (Over.mk
      (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
    (1 : Γ(scheme ℚ d,
      standardChart ℚ j ⊓ standardChart ℚ l))

lemma integerPairCoordinateComposite_top_one_of_ne
    (N : ℕ) (j l : Fin (d + 1)) (hlj : l ≠ j) :
    integerPairCoordinateCompositeTopOne d N j l =
      integerPairScalarEndomorphismTopOne d N j l := by
  unfold integerPairCoordinateCompositeTopOne
    integerPairScalarEndomorphismTopOne
    integerPairCoordinateComposite integerPairScalarEndomorphism
  rw [show
    ((integerPairSourceChartIso d N j l).inv ≫
      (integerPairTargetChartIso d N j l).hom).val.app
        (op (Over.mk
          (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
        (1 : Γ(scheme ℚ d,
          standardChart ℚ j ⊓ standardChart ℚ l)) =
      (integerPairTargetChartIso d N j l).hom.val.app
        (op (Over.mk
          (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
        (integerPairTopSourceSection d N j l)
    from rfl]
  rw [integerPairTargetChartIso_hom_app_terminal]
  exact (integerPairTopSourceSection_targetCoordinate
    d N j l hlj).trans
      (integerPairTransitionScalarEndomorphism_top_one
        d N j l).symm

lemma integerPairCoordinateComposite_of_ne
    (N : ℕ) (j l : Fin (d + 1)) (hlj : l ≠ j) :
    (integerPairSourceChartIso d N j l).inv ≫
        (integerPairTargetChartIso d N j l).hom =
      openScalarEndomorphism d
        (standardChart ℚ j ⊓ standardChart ℚ l)
        (integerPairTransitionScalar d N l j) := by
  change integerPairCoordinateComposite d N j l =
    integerPairScalarEndomorphism d N j l
  apply Scheme.Modules.unitOver_end_hom_ext_terminal
    (X := scheme ℚ d)
    (U := standardChart ℚ j ⊓ standardChart ℚ l)
    (integerPairCoordinateComposite d N j l)
    (integerPairScalarEndomorphism d N j l)
  unfold integerPairCoordinateComposite integerPairScalarEndomorphism
  rw [show
    ((integerPairSourceChartIso d N j l).inv ≫
      (integerPairTargetChartIso d N j l).hom).val.app
        (op (Over.mk
          (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
        (1 : Γ(scheme ℚ d,
          standardChart ℚ j ⊓ standardChart ℚ l)) =
      (integerPairTargetChartIso d N j l).hom.val.app
        (op (Over.mk
          (𝟙 (standardChart ℚ j ⊓ standardChart ℚ l))))
        (integerPairTopSourceSection d N j l)
    from rfl]
  rw [integerPairTargetChartIso_hom_app_terminal]
  exact (integerPairTopSourceSection_targetCoordinate
    d N j l hlj).trans
      (integerPairTransitionScalarEndomorphism_top_one
        d N j l).symm

lemma integerPairOverlapCoordinateHomTransition_of_ne
    (N : ℕ) (l j : Fin (d + 1)) (hlj : l ≠ j) :
    (integerPairTargetChartIso d N j l).hom =
      (integerPairSourceChartIso d N j l).hom ≫
        openScalarEndomorphism d
          (standardChart ℚ j ⊓ standardChart ℚ l)
          (integerPairTransitionScalar d N l j) := by
  rw [← cancel_epi (integerPairSourceChartIso d N j l).inv]
  simp only [Iso.inv_hom_id_assoc]
  exact integerPairCoordinateComposite_of_ne d N j l hlj

lemma integerOverChartCoordinateTransition_of_ne
    (N : ℕ) (j l : Fin (d + 1)) (hlj : l ≠ j)
    (V : (Over
      (standardChart ℚ j ⊓ standardChart ℚ l))ᵒᵖ)
    (x : (OInt ℚ d (-(N : ℤ))).val.obj
      (op V.unop.left)) :
    (show Γ(scheme ℚ d, V.unop.left) from
      (integerOverChartIso ℚ d (-(N : ℤ)) l).hom.val.app
        ((Over.map
          (Opens.infLERight
            (standardChart ℚ j) (standardChart ℚ l))).op.obj V) x) =
      (scheme ℚ d).presheaf.map V.unop.hom.op
          (chartScalarOnPair ℚ d l j
            (chartRatioElement ℚ d l j) ^ N) *
        (show Γ(scheme ℚ d, V.unop.left) from
          (integerOverChartIso ℚ d (-(N : ℤ)) j).hom.val.app
            ((Over.map
              (Opens.infLELeft
                (standardChart ℚ j) (standardChart ℚ l))).op.obj V) x) := by
  have h := congrArg
    (fun f => f.val.app V x)
    (integerPairOverlapCoordinateHomTransition_of_ne
      d N l j hlj)
  change
    (integerPairTargetChartIso d N j l).hom.val.app V x =
      (openScalarEndomorphism d
        (standardChart ℚ j ⊓ standardChart ℚ l)
        (integerPairTransitionScalar d N l j)).val.app V
          ((integerPairSourceChartIso d N j l).hom.val.app V x)
    at h
  rw [integerPairTargetChartIso_hom_app,
    integerPairSourceChartIso_hom_app] at h
  have hscalar := openScalarEndomorphism_app d
    (standardChart ℚ j ⊓ standardChart ℚ l)
    (integerPairTransitionScalar d N l j) V
    ((integerOverChartIso ℚ d (-(N : ℤ)) j).hom.val.app
      ((Over.map
        (Opens.infLELeft
          (standardChart ℚ j) (standardChart ℚ l))).op.obj V) x)
  have h' := h.trans hscalar
  rw [integerPairTransitionScalar] at h'
  let cj : Γ(scheme ℚ d, V.unop.left) :=
    (integerOverChartIso ℚ d (-(N : ℤ)) j).hom.val.app
      ((Over.map
        (Opens.infLELeft
          (standardChart ℚ j) (standardChart ℚ l))).op.obj V) x
  let q : Γ(scheme ℚ d, V.unop.left) :=
    (scheme ℚ d).presheaf.map V.unop.hom.op
      (chartScalarOnPair ℚ d l j
        (chartRatioElement ℚ d l j) ^ N)
  change _ = cj * q at h'
  change _ = q * cj
  exact h'.trans (mul_comm cj q)

lemma integerOverChartCoordinateTransition_self
    (N : ℕ) (j : Fin (d + 1))
    (V : (Over
      (standardChart ℚ j ⊓ standardChart ℚ j))ᵒᵖ)
    (x : (OInt ℚ d (-(N : ℤ))).val.obj
      (op V.unop.left)) :
    (show Γ(scheme ℚ d, V.unop.left) from
      (integerOverChartIso ℚ d (-(N : ℤ)) j).hom.val.app
        ((Over.map
          (Opens.infLERight
            (standardChart ℚ j) (standardChart ℚ j))).op.obj V) x) =
      (scheme ℚ d).presheaf.map V.unop.hom.op
          (chartScalarOnPair ℚ d j j
            (chartRatioElement ℚ d j j) ^ N) *
        (show Γ(scheme ℚ d, V.unop.left) from
          (integerOverChartIso ℚ d (-(N : ℤ)) j).hom.val.app
            ((Over.map
              (Opens.infLELeft
                (standardChart ℚ j) (standardChart ℚ j))).op.obj V) x) := by
  rw [chartRatioElement_self, chartScalarOnPair_one, one_pow]
  rw [((scheme ℚ d).presheaf.map V.unop.hom.op).hom.map_one,
    one_mul]
  rw [show
    Opens.infLERight
        (standardChart ℚ j) (standardChart ℚ j) =
      Opens.infLELeft
        (standardChart ℚ j) (standardChart ℚ j)
    from Subsingleton.elim _ _]

/-- The integer Serre twist coordinate transition over the rational
base, on every subopen of every pairwise standard-chart intersection. -/
theorem integerOverChartCoordinateTransition_rat
    (N : ℕ) :
    IntegerOverChartCoordinateTransition ℚ d N := by
  intro j l V x
  by_cases hlj : l = j
  · subst l
    exact integerOverChartCoordinateTransition_self d N j V x
  · exact integerOverChartCoordinateTransition_of_ne
      d N j l hlj V x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
