/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.XZeroFortyNineEtaRationalPoints
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePointAddition

/-!
# Compatibility of the point-level and scheme-level eta maps

The eta chart has two independently checked incarnations.  The original
point-level construction sends a rational eta pair to the represented
projective cubic.  The later scheme construction first turns that pair into a
`Spec ℚ` point of the localized eta-equation scheme and then applies a regular
coordinate morphism.

This file proves that the two routes are equal.  It evaluates the represented
standard-chart coordinate ring through the eta localization, identifies the
three homogeneous coordinates as

`[4x, etaWeierstrassOrdinate, 1]`,

and applies the generic standard-chart point comparison.  Thus the scheme
upgrade preserves the existing explicit point semantics rather than merely
landing on the same cubic.

The design boundary is still equation-side.  No modular eta function, coarse
modular curve, or classifying map is constructed.  The named downstream
consumer is `openSchemeRationalPointEquiv_symm_comp_target`, the compatibility
square a future modular eta construction can rewrite directly.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

namespace MazurTorsion.XZeroFortyNine.EtaSchemeModel

private def targetStandardY :
    SchemeModel.rationalCuspStandardChartRing :=
  Ideal.Quotient.mk (standardChartIdeal curve)
    (coordinateChartRatio (K := ℚ) 2 1)

private def etaStandardChartAlgHom (P : EtaOpenPoint) :
    SchemeModel.rationalCuspStandardChartRing →ₐ[ℚ] ℚ where
  toRingHom :=
    (etaOpenPointToOpenRingHom P).comp standardChartToOpenRing
  commutes' a := by
    exact DFunLike.congr_fun
      (RingHom.ext_rat
        (((etaOpenPointToOpenRingHom P).comp
          standardChartToOpenRing).comp
            (algebraMap ℚ
              SchemeModel.rationalCuspStandardChartRing))
        (RingHom.id ℚ)) a

private theorem etaStandardChartAlgHom_X (P : EtaOpenPoint) :
    etaStandardChartAlgHom P SchemeModel.rationalCuspStandardChartX =
      4 * P.1.x := by
  change etaOpenPointToOpenRingHom P
      (standardChartToOpenRing
        SchemeModel.rationalCuspStandardChartX) = _
  rw [standardChartToOpenRing_X]
  rw [openCurveX, (etaOpenPointToOpenRingHom P).map_mul,
    map_ofNat (etaOpenPointToOpenRingHom P) 4,
    etaOpenPointToOpenRingHom_openX]

private theorem etaOpenPointToOpenRingHom_openDenominatorInverse_mul
    (P : EtaOpenPoint) :
    etaOpenPointToOpenRingHom P openDenominatorInverse *
        (P.1.x ^ 2 + 7 * P.1.x + 7) = 1 := by
  have h := congrArg (etaOpenPointToOpenRingHom P)
    openDenominator_mul_inverse
  rw [(etaOpenPointToOpenRingHom P).map_mul,
    (etaOpenPointToOpenRingHom P).map_one,
    openDenominator_eq,
    (etaOpenPointToOpenRingHom P).map_add,
    (etaOpenPointToOpenRingHom P).map_add,
    (etaOpenPointToOpenRingHom P).map_pow,
    (etaOpenPointToOpenRingHom P).map_mul,
    map_ofNat (etaOpenPointToOpenRingHom P) 7,
    etaOpenPointToOpenRingHom_openX] at h
  calc
    etaOpenPointToOpenRingHom P openDenominatorInverse *
        (P.1.x ^ 2 + 7 * P.1.x + 7) =
      (P.1.x ^ 2 + 7 * P.1.x + 7) *
        etaOpenPointToOpenRingHom P openDenominatorInverse := by ring
    _ = 1 := h

private theorem etaStandardChartAlgHom_Y (P : EtaOpenPoint) :
    etaStandardChartAlgHom P targetStandardY =
      etaWeierstrassOrdinate P.1 := by
  change etaOpenPointToOpenRingHom P
      (standardChartToOpenRing targetStandardY) = _
  rw [show targetStandardY =
      Ideal.Quotient.mk (standardChartIdeal curve)
        (coordinateChartRatio (K := ℚ) 2 1) by rfl,
    standardChartToOpenRing_Y]
  unfold openCurveY etaWeierstrassOrdinate
  simp only [(etaOpenPointToOpenRingHom P).map_mul,
    (etaOpenPointToOpenRingHom P).map_sub,
    (etaOpenPointToOpenRingHom P).map_add,
    (etaOpenPointToOpenRingHom P).map_pow,
    map_ofNat (etaOpenPointToOpenRingHom P) 8,
    map_ofNat (etaOpenPointToOpenRingHom P) 28,
    map_ofNat (etaOpenPointToOpenRingHom P) 5,
    map_ofNat (etaOpenPointToOpenRingHom P) 7,
    etaOpenPointToOpenRingHom_openX,
    etaOpenPointToOpenRingHom_openY]
  have hden := etaModelDenominator_ne_zero P.1.x
  have hinv := etaOpenPointToOpenRingHom_openDenominatorInverse_mul P
  have hinv' : etaOpenPointToOpenRingHom P openDenominatorInverse =
      1 / (P.1.x ^ 2 + 7 * P.1.x + 7) := by
    rw [eq_div_iff hden]
    exact hinv
  rw [hinv']
  field_simp [hden]
  ring

private theorem etaStandardChartCoordinates (P : EtaOpenPoint) :
    etaStandardChartAlgHom P ∘ coveringChartUniversalPoint curve true =
      ![4 * P.1.x, etaWeierstrassOrdinate P.1, 1] := by
  funext j
  fin_cases j
  · change etaStandardChartAlgHom P
      SchemeModel.rationalCuspStandardChartX = _
    exact etaStandardChartAlgHom_X P
  · change etaStandardChartAlgHom P targetStandardY = _
    exact etaStandardChartAlgHom_Y P
  · rw [show (⟨2, by omega⟩ : Fin 3) = coveringCoordinate true by rfl]
    change etaStandardChartAlgHom P
      (Ideal.Quotient.mk (standardChartIdeal curve)
        (coordinateChartRatio (K := ℚ) 2 2)) = 1
    rw [coordinateChartRatio_self]
    exact map_one _

private theorem etaStandardChartCoordinates_nonsingular
    (P : EtaOpenPoint) :
    curve.toProjective.Nonsingular
      (etaStandardChartAlgHom P ∘
        coveringChartUniversalPoint curve true) := by
  rw [etaStandardChartCoordinates]
  apply (curve.toProjective.nonsingular_some _ _).mpr
  apply curve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  have hcurve := congrArg (etaOpenPointToOpenRingHom P) openCurveY_sq
  have hX : etaOpenPointToOpenRingHom P openCurveX = 4 * P.1.x := by
    rw [openCurveX, (etaOpenPointToOpenRingHom P).map_mul,
      map_ofNat (etaOpenPointToOpenRingHom P) 4,
      etaOpenPointToOpenRingHom_openX]
  have hY : etaOpenPointToOpenRingHom P openCurveY =
      etaWeierstrassOrdinate P.1 := by
    rw [← etaStandardChartAlgHom_Y P]
    change etaOpenPointToOpenRingHom P openCurveY =
      etaOpenPointToOpenRingHom P
        (standardChartToOpenRing targetStandardY)
    rw [targetStandardY, standardChartToOpenRing_Y]
  simp only [(etaOpenPointToOpenRingHom P).map_pow,
    (etaOpenPointToOpenRingHom P).map_mul,
    (etaOpenPointToOpenRingHom P).map_add,
    map_ofNat (etaOpenPointToOpenRingHom P) 21,
    map_ofNat (etaOpenPointToOpenRingHom P) 112,
    hX, hY] at hcurve
  norm_num [curve]
  nlinarith [hcurve]

@[reassoc]
private theorem etaSchemePoint_toStandardChart (P : EtaOpenPoint) :
    (openSchemeRationalPointEquiv.symm P ≫ toAffinePresentation) ≫
      SchemeModel.rationalCuspAffinePresentationToStandardChart =
      Spec.map (CommRingCat.ofHom (etaStandardChartAlgHom P).toRingHom) := by
  rw [openSchemeRationalPointEquiv_symm_eq_specMap]
  change Spec.map (CommRingCat.ofHom (etaOpenPointToOpenRingHom P)) ≫
      Spec.map (CommRingCat.ofHom affinePresentationToOpenRing) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap SchemeModel.rationalCuspStandardChartRing
          SchemeModel.rationalCuspAffinePresentationRing)) = _
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact congrArg (etaOpenPointToOpenRingHom P)
    (affinePresentationToOpenRing_algebraMap a)

/-- The scheme-level eta coordinate change agrees exactly with the earlier
point-level map to the represented projective cubic. -/
theorem openSchemeRationalPointEquiv_symm_comp_target (P : EtaOpenPoint) :
    openSchemeRationalPointEquiv.symm P ≫ toRationalCuspOpen ≫
        SchemeModel.rationalCuspAvoidingInclusion =
      etaPointToScheme P.1 := by
  rw [toRationalCuspOpen_comp_inclusion]
  unfold SchemeModel.rationalCuspAffinePresentationMap
  rw [etaSchemePoint_toStandardChart_assoc P]
  rw [standardChartSpecMap_comp_coveringChartMap
    curve (etaStandardChartAlgHom P)
      (etaStandardChartCoordinates_nonsingular P)]
  unfold etaPointToScheme
  rw [SchemeModel.rationalPointEquiv_apply]
  unfold etaPointToCurve
  congr 1
  exact etaStandardChartCoordinates P

end MazurTorsion.XZeroFortyNine.EtaSchemeModel
