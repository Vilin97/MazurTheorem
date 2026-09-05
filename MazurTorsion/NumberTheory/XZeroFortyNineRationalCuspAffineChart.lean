/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCubicReducedBaseChange
import MazurTorsion.NumberTheory.XZeroFortyNineRationalCuspOpen

/-!
# An explicit affine presentation of the level-49 rational-cusp open

The canonical affine presentation of the projective basic open `D(X)` uses
its section ring.  This file gives a more computational presentation.  Start
with the represented `Z != 0` chart of the Weierstrass cubic, take the class
of the affine coordinate `X / Z`, and localize its quotient coordinate ring
at that element.

The homogeneous equation shows that a cubic point with `Z = 0` also has
`X = 0`.  Consequently `D(X)` lies entirely in the represented standard
chart, and the localization above has exactly the range of the actual
rational-cusp-avoiding open.  It is therefore canonically isomorphic to that
open subscheme.

The design boundary remains target-side: this file constructs neither an eta
moduli chart nor a coarse-moduli comparison.  Its named downstream consumer
is the scheme-level eta-coordinate comparison, which can now be built by a
ring homomorphism into `rationalCuspAffinePresentationRing` and transported
through `rationalCuspAffinePresentationIso`.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

namespace MazurTorsion.XZeroFortyNine.SchemeModel

private theorem coordinate_mem_degree_one (i : Fin 3) :
    MvPolynomial.X i ∈ homogeneousPieces ℚ 1 :=
  MvPolynomial.isHomogeneous_X ℚ i

/-- The quotient coordinate ring of the represented standard `Z != 0` chart
of the level-49 cubic. -/
abbrev rationalCuspStandardChartRing :=
  coveringChartCoordinateRing curve true

/-- The class of `X / Z` in the represented standard-chart coordinate ring. -/
def rationalCuspStandardChartX : rationalCuspStandardChartRing :=
  Ideal.Quotient.mk (coveringChartIdeal curve true)
    (coordinateChartRatio 2 0)

/-- The explicit coordinate ring of `D(X)`, obtained by inverting `X / Z` in
the represented standard-chart quotient. -/
abbrev rationalCuspAffinePresentationRing :=
  Localization.Away rationalCuspStandardChartX

/-- The spectrum of the explicit localized coordinate ring. -/
abbrev rationalCuspAffinePresentationScheme : Scheme :=
  Spec (.of rationalCuspAffinePresentationRing)

/-- The principal localization map into the represented standard chart. -/
def rationalCuspAffinePresentationToStandardChart :
    rationalCuspAffinePresentationScheme ⟶ coveringChartScheme curve true :=
  Spec.map (CommRingCat.ofHom
    (algebraMap rationalCuspStandardChartRing
      rationalCuspAffinePresentationRing))

instance rationalCuspAffinePresentationToStandardChart_isOpenImmersion :
    IsOpenImmersion rationalCuspAffinePresentationToStandardChart := by
  dsimp only [rationalCuspAffinePresentationToStandardChart,
    rationalCuspAffinePresentationScheme,
    rationalCuspAffinePresentationRing]
  infer_instance

/-- The localization has the principal-open range where `X / Z` is nonzero. -/
theorem rationalCuspAffinePresentationToStandardChart_opensRange :
    rationalCuspAffinePresentationToStandardChart.opensRange =
      PrimeSpectrum.basicOpen rationalCuspStandardChartX := by
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of rationalCuspStandardChartRing) rationalCuspStandardChartX

/-- The explicit affine presentation mapped into the represented projective
cubic through its standard chart. -/
def rationalCuspAffinePresentationMap :
    rationalCuspAffinePresentationScheme ⟶ scheme :=
  rationalCuspAffinePresentationToStandardChart ≫
    coveringChartMap curve true

instance rationalCuspAffinePresentationMap_isOpenImmersion :
    IsOpenImmersion rationalCuspAffinePresentationMap := by
  dsimp only [rationalCuspAffinePresentationMap]
  infer_instance

/-- Pulling `D(X)` back to the represented standard chart gives precisely the
principal open where the class of `X / Z` is nonzero. -/
theorem standardChart_preimage_rationalCuspAvoidingOpen :
    coveringChartMap curve true ⁻¹ᵁ rationalCuspAvoidingOpen =
      PrimeSpectrum.basicOpen rationalCuspStandardChartX := by
  unfold rationalCuspAvoidingOpen
  rw [← Scheme.Hom.comp_preimage, coveringChartMap_comp_inclusion]
  unfold coveringChartAmbientMap
  rw [Scheme.Hom.comp_preimage]
  unfold coveringChartAway
  simp only [coveringCoordinate]
  have hAway :
      Proj.awayι (homogeneousPieces ℚ) (MvPolynomial.X 2)
          (coordinate_mem_degree_one 2) (by omega) ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 0) =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (coordinate_mem_degree_one 2) (coordinate_mem_degree_one 0)) :=
    Proj.awayι_preimage_basicOpen (homogeneousPieces ℚ)
      (coordinate_mem_degree_one 2) (by omega)
      (coordinate_mem_degree_one 0) (by omega)
  change coveringChartQuotientInclusion curve true ⁻¹ᵁ
      (Proj.awayι (homogeneousPieces ℚ) (MvPolynomial.X 2)
          (coordinate_mem_degree_one 2) (by omega) ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 0)) =
    PrimeSpectrum.basicOpen rationalCuspStandardChartX
  have hq := congrArg
    (fun U => coveringChartQuotientInclusion curve true ⁻¹ᵁ U) hAway
  exact hq.trans (by
    ext p
    change Ideal.Quotient.mk (coveringChartIdeal curve true)
        (HomogeneousLocalization.Away.isLocalizationElem
          (coordinate_mem_degree_one 2) (coordinate_mem_degree_one 0)) ∉
          p.asIdeal ↔
      rationalCuspStandardChartX ∉ p.asIdeal
    rw [isLocalizationElem_degree_one_eq_coordinateChartRatio]
    rfl)

/-- On the projective Weierstrass cubic, the condition `X != 0` forces
`Z != 0`; the homogeneous equation at `Z = 0` reduces to `X³ = 0`. -/
theorem rationalCuspAvoidingOpen_le_standardOpen :
    rationalCuspAvoidingOpen ≤
      WeierstrassProjectiveCubic.inclusion curve ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 2) := by
  intro p hp
  change WeierstrassProjectiveCubic.inclusion curve p ∈
    Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 2)
  rw [Proj.mem_basicOpen]
  intro hZ
  change WeierstrassProjectiveCubic.inclusion curve p ∈
    Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 0) at hp
  rw [Proj.mem_basicOpen] at hp
  apply hp
  have hpCarrier :
      WeierstrassProjectiveCubic.inclusion curve p ∈ carrier curve := by
    rw [← range_inclusion]
    exact Set.mem_range_self p
  let I :=
    (WeierstrassProjectiveCubic.inclusion curve p).asHomogeneousIdeal.toIdeal
  letI : I.IsPrime :=
    (WeierstrassProjectiveCubic.inclusion curve p).isPrime
  let π : MvPolynomial (Fin 3) ℚ →+* MvPolynomial (Fin 3) ℚ ⧸ I :=
    Ideal.Quotient.mk I
  have hπZ : π (MvPolynomial.X 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hZ
  have hπpoly : π curve.toProjective.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((mem_zeroLocus_iff curve _).mp hpCarrier)
  have hπXpow : π (MvPolynomial.X 0) ^ 3 = 0 := by
    simpa [π, curve, WeierstrassCurve.Projective.polynomial, hπZ] using hπpoly
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (eq_zero_of_pow_eq_zero hπXpow)

private theorem rationalCuspAvoidingOpen_le_standardChartRange :
    rationalCuspAvoidingOpen ≤ (coveringChartMap curve true).opensRange := by
  rw [coveringChartMap_opensRange]
  have hAway :
      (coveringChartAway ℚ true).opensRange =
        Proj.basicOpen (homogeneousPieces ℚ) (MvPolynomial.X 2) := by
    unfold coveringChartAway
    simp only [coveringCoordinate]
    change (Proj.awayι (homogeneousPieces ℚ) (MvPolynomial.X 2)
      (coordinate_mem_degree_one 2) (by omega)).opensRange = _
    exact Proj.opensRange_awayι (homogeneousPieces ℚ)
      (MvPolynomial.X 2) (coordinate_mem_degree_one 2) (by omega)
  rw [hAway]
  exact rationalCuspAvoidingOpen_le_standardOpen

/-- The explicit localization map has exactly the actual `D(X)` range in the
represented projective cubic. -/
theorem rationalCuspAffinePresentationMap_opensRange :
    rationalCuspAffinePresentationMap.opensRange =
      rationalCuspAvoidingOpen := by
  unfold rationalCuspAffinePresentationMap
  rw [Scheme.Hom.opensRange_comp,
    rationalCuspAffinePresentationToStandardChart_opensRange,
    ← standardChart_preimage_rationalCuspAvoidingOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
  exact rationalCuspAvoidingOpen_le_standardChartRange

/-- The explicit localization of the standard affine Weierstrass quotient is
canonically the rational-cusp-avoiding open. -/
def rationalCuspAffinePresentationIso :
    rationalCuspAffinePresentationScheme ≅ rationalCuspAvoidingScheme :=
  IsOpenImmersion.isoOfRangeEq rationalCuspAffinePresentationMap
    rationalCuspAvoidingOpen.ι (by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        rationalCuspAffinePresentationMap_opensRange,
        Scheme.Opens.opensRange_ι])

/-- The affine-presentation isomorphism followed by the open inclusion is the
explicit localization map into the projective cubic. -/
@[reassoc]
theorem rationalCuspAffinePresentationIso_hom_comp_inclusion :
    rationalCuspAffinePresentationIso.hom ≫
        rationalCuspAvoidingInclusion =
      rationalCuspAffinePresentationMap := by
  unfold rationalCuspAvoidingInclusion
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end MazurTorsion.XZeroFortyNine.SchemeModel
