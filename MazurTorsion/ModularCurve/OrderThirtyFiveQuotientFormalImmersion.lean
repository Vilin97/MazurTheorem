/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspDifferentialArithmeticConsumers
import MazurTorsion.ModularCurve.AffineStructuralSectionQCoordinate
import MazurTorsion.ModularCurve.OrderThirtyFiveQuotientQExpansion

/-!
# The explicit level-35 quotient expansion feeds formal immersion

The quotient coordinate verified in `OrderThirtyFiveQuotientQExpansion` has
pullback

`W - 1 = -7q / (1 + q - q²)`.

This file passes that fixed expansion through the completed-local-ring
cotangent criterion.  At the auxiliary prime eleven, the coefficient `-7`
is proved nonzero from the actual residue-field tower, so no eigenvector,
Hecke operator, differential nonvanishing, or asserted linear coefficient is
an input.  The resulting formal immersion is then consumed by the existing
Néron specialization endpoint for the order-35 exclusion.

The represented integral modular chart and its comparison with the explicit
hyperelliptic model remain geometric inputs owned by the global `X₀(35)`
representability layer.  Once that comparison supplies the displayed full
expansion equality, all q-expansion and cotangent arithmetic below is checked.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open Ideal.Fiber
open MazurTorsion.ModularCurve.AffineCuspQExpansion

namespace Ideal.Fiber.AffineStructuralSection

universe u

open MazurTorsion.ModularCurve.AffineCuspPolynomialChart.AffinePresentation

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

/-- A structural affine section, bundled over the base, for use by the Néron
specialization consumers. -/
noncomputable def overSection
    (C : AffineStructuralSection (R := R) (T := T)) :
    Over.mk (𝟙 (Spec (.of R))) ⟶ sourceOver R T :=
  Over.homMk C.toSpec C.isSection

@[simp]
theorem overSection_left
    (C : AffineStructuralSection (R := R) (T := T)) :
    C.overSection.left = C.toSpec :=
  rfl

end Ideal.Fiber.AffineStructuralSection

namespace MazurTorsion.OrderThirtyFive

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open MazurTorsion.ModularCurve.AffineCuspPolynomialChart.AffinePresentation
open QuotientQExpansion
open WeierstrassCurve.Affine

universe u

private abbrev ElevenBase := atEleven.adicCompletionIntegers ℚ

private abbrev ElevenPrime : Ideal ElevenBase :=
  affineCuspSpecialFiberIdealAtEleven

/-- The denominator-cleared local identity already determines the complete
level-35 quotient expansion in the coordinate constructed from the section.

This is the bridge expected from an explicit hyperelliptic chart: it only
asks the chart comparison to prove the algebraic identity
`(W - 1)(1 + q - q²) = -7q`.  The power-series inverse and every coefficient
calculation are then derived here. -/
theorem qExpansion_eq_quotientParameterExpansion_of_cleared_localFormula
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T))
    [IsDomain (C.FiberLocalRing p)]
    [IsDiscreteValuationRing (C.FiberLocalRing p)]
    (q : C.FiberLocalRing p) (hq : Irreducible q)
    (pulledBackParameter : C.FiberLocalRing p)
    (hcleared :
      pulledBackParameter * (1 + q - q ^ 2) =
        algebraMap p.ResidueField (C.FiberLocalRing p) (-7) * q) :
    C.qCoordinate p q hq
        (completionRingHom (C.FiberLocalRing p) pulledBackParameter) =
      quotientParameterExpansion := by
  have hseries := congrArg
    (fun z => C.qCoordinate p q hq
      (completionRingHom (C.FiberLocalRing p) z)) hcleared
  have hseriesCleared :
      C.qCoordinate p q hq
          (completionRingHom (C.FiberLocalRing p) pulledBackParameter) *
          denominator =
        PowerSeries.C (-7 : p.ResidueField) * PowerSeries.X := by
    simpa only [map_mul, map_add, map_one, map_sub, map_pow,
      C.qCoordinate_uniformizer p q hq,
      C.qCoordinate_algebraMap p q hq, denominator] using hseries
  have hquotientCleared :
      quotientParameterExpansion (K := p.ResidueField) * denominator =
        PowerSeries.C (-7 : p.ResidueField) * PowerSeries.X := by
    rw [quotientParameterExpansion_eq, Algebra.smul_def]
    have hinv : (denominator (K := p.ResidueField))⁻¹ * denominator = 1 := by
      rw [mul_comm]
      exact PowerSeries.mul_inv_cancel denominator (by simp)
    calc
      PowerSeries.C (-7 : p.ResidueField) *
            (PowerSeries.X * denominator⁻¹) * denominator =
          PowerSeries.C (-7 : p.ResidueField) * PowerSeries.X *
            (denominator⁻¹ * denominator) := by ring
      _ = PowerSeries.C (-7 : p.ResidueField) * PowerSeries.X := by
        rw [hinv]
        exact _root_.mul_one _
  apply mul_right_cancel₀ (denominator_ne_zero (K := p.ResidueField))
  exact hseriesCleared.trans hquotientCleared.symm

/-- The explicit quotient parameter proves formal immersion through any
affine open of the quotient model containing the cusp image. -/
theorem isFormalImmersionAt_of_affineOpen_explicitQuotientQExpansion
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    {Y : Scheme.{u}}
    (p : Ideal R) [p.IsPrime]
    (C : AffineStructuralSection (R := R) (T := T))
    (g : S →ₐ[R] T)
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    [IsDomain (Localization.AtPrime (C.fiberPrime p))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (C.fiberPrime p))]
    (targetOpen : Spec (.of S) ⟶ Y) [IsOpenImmersion targetOpen]
    (quotientMap : Spec (.of T) ⟶ Y)
    (hfactor : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen =
      quotientMap)
    (qParameter : Localization.AtPrime (C.fiberPrime p))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime p).comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime ((C.fiberPrime p).comap (map p g))))
    (hclearedLocalFormula :
      localizedMap p g (C.fiberPrime p) sourceParameter *
          (1 + qParameter - qParameter ^ 2) =
        algebraMap p.ResidueField
          (Localization.AtPrime (C.fiberPrime p)) (-7) * qParameter)
    (hseven : (7 : p.ResidueField) ≠ 0) :
    IsFormalImmersionAt quotientMap
      (targetSpecPoint p (C.fiberPrime p)) := by
  have hcoeff : PowerSeries.coeff 1
      (quotientParameterExpansion (K := p.ResidueField)) ≠ 0 := by
    rw [coeff_one_quotientParameterExpansion]
    exact neg_ne_zero.mpr hseven
  have hqExpansion :=
    qExpansion_eq_quotientParameterExpansion_of_cleared_localFormula
      p C qParameter hqParameter
      (localizedMap p g (C.fiberPrime p) sourceParameter)
      hclearedLocalFormula
  have hlocal : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.fiberPrime p)) :=
    isFormalImmersionAtSpecMap_of_explicit_qExpansion_of_structuralSection_dvr
      p g C qParameter hqParameter sourceParameter hsourceMem
      (C.qCoordinate p qParameter hqParameter) quotientParameterExpansion
      hqExpansion hcoeff
  have hopen := isFormalImmersionAt_of_isOpenImmersion targetOpen
    ((Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.fiberPrime p)))
  have hcomposite := hlocal.comp hopen
  rw [hfactor] at hcomposite
  exact hcomposite

private theorem residueAtEleven_seven_ne_zero :
    (7 : IsLocalRing.ResidueField ElevenBase) ≠ 0 := by
  let e₁₁ : IsLocalRing.ResidueField ElevenBase ≃+* ZMod 11 :=
    (atEleven.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueElevenAlgEquiv.toRingEquiv
  intro h
  have hz : (7 : ZMod 11) = 0 := by
    calc
      (7 : ZMod 11) = e₁₁ (7 : IsLocalRing.ResidueField ElevenBase) :=
        (map_natCast e₁₁ 7).symm
      _ = e₁₁ 0 := congrArg e₁₁ h
      _ = 0 := map_zero e₁₁
  have hne : (7 : ZMod 11) ≠ 0 := by decide
  exact hne hz

private theorem elevenPrimeResidue_seven_ne_zero :
    (7 : ElevenPrime.ResidueField) ≠ 0 := by
  have hunit : IsUnit (7 : ElevenBase) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (7 : ElevenBase)).mp
      residueAtEleven_seven_ne_zero
  intro hzero
  have hmem : (7 : ElevenBase) ∈ ElevenPrime := by
    apply Ideal.algebraMap_residueField_eq_zero.mp
    calc
      algebraMap ElevenBase ElevenPrime.ResidueField (7 : ElevenBase) =
          (7 : ElevenPrime.ResidueField) := map_natCast _ 7
      _ = 0 := hzero
  exact (inferInstance : ElevenPrime.IsPrime).ne_top
    (ElevenPrime.eq_top_of_isUnit_mem hmem hunit)

/-- Seven remains nonzero in the residue field of every point of the
characteristic-eleven affine fibre. -/
theorem seven_ne_zero_in_affineCuspResidueAtEleven
    {T : Type} [CommRing T] [Algebra ElevenBase T]
    (C : AffineStructuralSection (R := ElevenBase) (T := T)) :
    (7 : IsLocalRing.ResidueField
      (Localization.AtPrime (C.fiberPrime ElevenPrime))) ≠ 0 := by
  let residueTower : ElevenPrime.ResidueField →+*
      IsLocalRing.ResidueField
        (Localization.AtPrime (C.fiberPrime ElevenPrime)) :=
    (IsLocalRing.residue
      (Localization.AtPrime (C.fiberPrime ElevenPrime))).comp
      ((algebraMap (ElevenPrime.Fiber T)
        (Localization.AtPrime (C.fiberPrime ElevenPrime))).comp
        (Algebra.TensorProduct.includeLeftRingHom
          (R := ElevenBase)
          (A := ElevenPrime.ResidueField) (B := T)))
  intro h
  apply elevenPrimeResidue_seven_ne_zero
  apply residueTower.injective
  calc
    residueTower (7 : ElevenPrime.ResidueField) =
        (7 : IsLocalRing.ResidueField
          (Localization.AtPrime (C.fiberPrime ElevenPrime))) :=
      map_natCast residueTower 7
    _ = 0 := h
    _ = residueTower 0 := (map_zero residueTower).symm

/-- The fixed level-35 quotient expansion reaches the order-35 arithmetic
exclusion through Néron specialization at eleven.

The full expansion is fixed to the verified rational function
`-7q / (1 + q - q²)`, and its tangent nonvanishing is derived internally.
The remaining hypotheses are the represented-chart comparison and the
global section-specialization data, not a formal-immersion or nonvanishing
assumption. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_explicitQuotientQExpansionNeronSpecializationAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : CommGroupScheme (Spec (.of (atEleven.adicCompletion ℚ)))}
    (Ner : NeronModel ElevenBase (atEleven.adicCompletion ℚ) A)
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (C : AffineStructuralSection (R := ElevenBase) (T := T))
    (g : S →ₐ[ElevenBase] T)
    [IsNoetherianRing (ElevenPrime.Fiber T)]
    [IsDomain (Localization.AtPrime (C.fiberPrime ElevenPrime))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (C.fiberPrime ElevenPrime))]
    (targetOpen : Spec (.of S) ⟶ Ner.model.X.left)
    [IsOpenImmersion targetOpen]
    (quotientMap : sourceOver ElevenBase T ⟶ Ner.model.X)
    (hfactor :
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen = quotientMap.left)
    (modularSection :
      Over.mk (𝟙 (Spec (.of ElevenBase))) ⟶ sourceOver ElevenBase T)
    (qParameter : Localization.AtPrime (C.fiberPrime ElevenPrime))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g))))
    (hclearedLocalFormula :
      localizedMap ElevenPrime g (C.fiberPrime ElevenPrime)
            sourceParameter *
          (1 + qParameter - qParameter ^ 2) =
        algebraMap ElevenPrime.ResidueField
          (Localization.AtPrime (C.fiberPrime ElevenPrime)) (-7) *
            qParameter)
    (hgeneric_ne :
      fractionSpecMap ElevenBase (atEleven.adicCompletion ℚ) ≫
          modularSection.left ≠
        fractionSpecMap ElevenBase (atEleven.adicCompletion ℚ) ≫
          C.overSection.left)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      restrictBaseSection (residueSpecMap ElevenBase)
          (sourceOver ElevenBase T) modularSection =
        restrictBaseSection (residueSpecMap ElevenBase)
          (sourceOver ElevenBase T) C.overSection)
    (htorsion : IsOfFinOrder
      (Ner.basePointRestriction (modularSection ≫ quotientMap) /
        Ner.basePointRestriction (C.overSection ≫ quotientMap)))
    (hinjective : ∀ z :
        Over.mk (𝟙 (Spec (.of (atEleven.adicCompletion ℚ)))) ⟶ A.X,
      IsOfFinOrder z →
        Ner.basePointSpecialization (residueSpecMap ElevenBase) z = 1 →
        z = 1)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  have hformalTarget : IsFormalImmersionAt quotientMap.left
      (targetSpecPoint ElevenPrime (C.fiberPrime ElevenPrime)) :=
    isFormalImmersionAt_of_affineOpen_explicitQuotientQExpansion ElevenPrime
      C g targetOpen quotientMap.left hfactor qParameter hqParameter
      sourceParameter hsourceMem hclearedLocalFormula
      elevenPrimeResidue_seven_ne_zero
  have hcuspPoint :
      closedFiberPointAtEleven C.overSection.left =
        targetSpecPoint ElevenPrime (C.fiberPrime ElevenPrime) := by
    change C.toSpec (IsLocalRing.closedPoint ElevenBase) =
      targetSpecPoint ElevenPrime (C.fiberPrime ElevenPrime)
    simpa only [closedFiberPointAtEleven,
      Ideal.Fiber.AffineStructuralSection.overSection_left, ElevenPrime,
      affineCuspSpecialFiberIdealAtEleven, IsLocalRing.closedPoint] using
        C.atPrime ElevenPrime
  have hformal : IsFormalImmersionAt quotientMap.left
      (closedFiberPointAtEleven C.overSection.left) := by
    rw [hcuspPoint]
    exact hformalTarget
  exact rationalPoint_orderThirtyFive_ne_of_neronSpecializationAtEleven
    Ner (sourceOver ElevenBase T) quotientMap modularSection C.overSection
    hformal hgeneric_ne hspecializes htorsion hinjective P

end MazurTorsion.OrderThirtyFive
