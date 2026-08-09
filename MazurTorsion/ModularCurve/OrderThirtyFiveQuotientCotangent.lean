/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.OrderThirtyFiveQuotientFormalImmersion

/-!
# The level-35 quotient map on the special-fibre cotangent space

At the infinity cusp of the explicit level-35 chart, the quotient parameter
has the exact local identity

`(W - 1) (1 + t - t²) = -7t`.

This file uses that finite identity directly in the localized
characteristic-eleven fibre.  Since `t` lies in the cusp maximal ideal, the
denominator is a unit; since the residue characteristic is eleven, `-7` is a
unit as well.  Thus the pullback of `W - 1` is a unit multiple of the DVR
uniformizer.  The checked cotangent criterion then proves formal immersion
without choosing a completed `q`-coordinate or assuming a power-series
expansion.

The last theorem feeds this concrete special-fibre calculation into the
existing Néron specialization consumer for the order-35 exclusion.  Its
remaining hypotheses are the represented-chart comparison, the genuine
section specialization, and the quotient-point torsion input.

The quotient formula is the one verified algebraically in
`OrderThirtyFiveQuotientQExpansion`; its primary-source provenance is
recorded there.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open Ideal.Fiber
open MazurTorsion.ModularCurve.AffineCuspQExpansion

namespace MazurTorsion.OrderThirtyFive

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open MazurTorsion.ModularCurve.AffineCuspPolynomialChart.AffinePresentation
open QuotientQExpansion
open WeierstrassCurve.Affine

private abbrev ElevenBase := atEleven.adicCompletionIntegers ℚ

private abbrev ElevenPrime : Ideal ElevenBase :=
  affineCuspSpecialFiberIdealAtEleven

/-- The denominator `1 + t - t²` is a unit at any local point where `t`
belongs to the maximal ideal. -/
theorem localDenominator_isUnit_of_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A]
    {t : A} (ht : t ∈ IsLocalRing.maximalIdeal A) :
    IsUnit (localDenominator t) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit
    (localDenominator t)).mp
  have htzero : IsLocalRing.residue A t = 0 :=
    (IsLocalRing.residue_eq_zero_iff t).mpr ht
  simp [localDenominator, htzero]

/-- The exact cleared quotient-coordinate identity detects a nonzero
cotangent vector at the characteristic-eleven cusp.

Unlike a completed `q`-expansion premise, `hcoordinate` is an equality in the
actual localized special-fibre ring.  The denominator and coefficient units,
the nonzero cotangent class of the uniformizer, and both residue-field maps
are all derived in the proof. -/
theorem isFormalImmersionAtSpecMap_of_explicitQuotientCotangentAtEleven
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (C : AffineStructuralSection (R := ElevenBase) (T := T))
    (g : S →ₐ[ElevenBase] T)
    [IsNoetherianRing (ElevenPrime.Fiber T)]
    [IsDomain (Localization.AtPrime (C.fiberPrime ElevenPrime))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (C.fiberPrime ElevenPrime))]
    (qParameter : Localization.AtPrime (C.fiberPrime ElevenPrime))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g))))
    (hcoordinate :
      localizedMap ElevenPrime g (C.fiberPrime ElevenPrime)
          sourceParameter * localDenominator qParameter =
        (-7 : Localization.AtPrime (C.fiberPrime ElevenPrime)) *
          qParameter) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint ElevenPrime (C.fiberPrime ElevenPrime)) := by
  let A := Localization.AtPrime (C.fiberPrime ElevenPrime)
  have hqMem : qParameter ∈ IsLocalRing.maximalIdeal A := by
    rw [hqParameter.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self qParameter
  have hdenominator : IsUnit (localDenominator qParameter) :=
    localDenominator_isUnit_of_mem_maximalIdeal hqMem
  let denominatorUnit : Aˣ := hdenominator.unit
  let denominatorInverse : A := ↑(denominatorUnit⁻¹)
  have hdenominatorInverse :
      localDenominator qParameter * denominatorInverse = 1 := by
    simpa only [denominatorInverse, denominatorUnit] using
      hdenominator.mul_val_inv
  have hseven : IsUnit (7 : A) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (7 : A)).mp
    have hnat : IsLocalRing.residue A (7 : A) =
        (7 : IsLocalRing.ResidueField A) :=
      map_natCast (IsLocalRing.residue A) 7
    rw [hnat]
    exact seven_ne_zero_in_affineCuspResidueAtEleven C
  have hcoefficient : IsUnit
      ((-7 : A) * denominatorInverse) :=
    hseven.neg.mul (denominatorUnit⁻¹).isUnit
  let sourcePullback : A :=
    localizedMap ElevenPrime g (C.fiberPrime ElevenPrime) sourceParameter
  have hcoordinate' :
      sourcePullback * localDenominator qParameter =
        (-7 : A) * qParameter := by
    exact hcoordinate
  have hfirstOrder' : sourcePullback =
      ((-7 : A) * denominatorInverse) * qParameter + 0 := by
    rw [add_zero]
    calc
      sourcePullback = sourcePullback * 1 :=
        (_root_.mul_one sourcePullback).symm
      _ = sourcePullback *
            (localDenominator qParameter * denominatorInverse) := by
          rw [hdenominatorInverse]
      _ = (sourcePullback * localDenominator qParameter) *
            denominatorInverse := by rw [_root_.mul_assoc]
      _ = ((-7 : A) * qParameter) * denominatorInverse := by
          rw [hcoordinate']
      _ = ((-7 : A) * denominatorInverse) * qParameter := by ring
  have hfirstOrder :
      localizedMap ElevenPrime g (C.fiberPrime ElevenPrime)
          sourceParameter =
        ((-7 : A) * denominatorInverse) * qParameter + 0 := by
    exact hfirstOrder'
  exact
    isFormalImmersionAtSpecMap_of_unit_qExpansion_of_retraction
      ElevenPrime g (C.fiberPrime ElevenPrime) qParameter
      hqParameter.maximalIdeal_eq
      (irreducible_not_mem_maximalIdeal_sq hqParameter) sourceParameter
      hsourceMem ((-7 : A) * denominatorInverse) 0 hcoefficient
      (Ideal.zero_mem _) hfirstOrder C.retraction
      (C.targetBasePrime_fiberPrime ElevenPrime)

/-- The explicit special-fibre cotangent calculation reaches formal
immersion for a quotient morphism factoring through an affine open of its
Néron model. -/
theorem isFormalImmersionAt_of_affineOpen_explicitQuotientCotangentAtEleven
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    {Y : Scheme}
    [IsNoetherianRing S] [IsNoetherianRing T]
    (C : AffineStructuralSection (R := ElevenBase) (T := T))
    (g : S →ₐ[ElevenBase] T)
    [IsNoetherianRing (ElevenPrime.Fiber T)]
    [IsDomain (Localization.AtPrime (C.fiberPrime ElevenPrime))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (C.fiberPrime ElevenPrime))]
    (targetOpen : Spec (.of S) ⟶ Y) [IsOpenImmersion targetOpen]
    (quotientMap : Spec (.of T) ⟶ Y)
    (hfactor : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen =
      quotientMap)
    (qParameter : Localization.AtPrime (C.fiberPrime ElevenPrime))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g))))
    (hcoordinate :
      localizedMap ElevenPrime g (C.fiberPrime ElevenPrime)
          sourceParameter * localDenominator qParameter =
        (-7 : Localization.AtPrime (C.fiberPrime ElevenPrime)) *
          qParameter) :
    IsFormalImmersionAt quotientMap
      (targetSpecPoint ElevenPrime (C.fiberPrime ElevenPrime)) := by
  have hlocal :=
    isFormalImmersionAtSpecMap_of_explicitQuotientCotangentAtEleven
      C g qParameter hqParameter sourceParameter hsourceMem hcoordinate
  have hopen := isFormalImmersionAt_of_isOpenImmersion targetOpen
    ((Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint ElevenPrime (C.fiberPrime ElevenPrime)))
  have hcomposite := hlocal.comp hopen
  rw [hfactor] at hcomposite
  exact hcomposite

/-- The exact level-35 quotient-coordinate identity in the localized
characteristic-eleven fibre reaches the order-35 exclusion through Néron
specialization.

There is no completed-coordinate or `hqExpansion` input.  The finite local
identity `hcoordinate` is the whole quotient-side cotangent calculation. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_explicitQuotientCotangentNeronSpecializationAtEleven
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
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen =
        quotientMap.left)
    (modularSection :
      Over.mk (𝟙 (Spec (.of ElevenBase))) ⟶ sourceOver ElevenBase T)
    (qParameter : Localization.AtPrime (C.fiberPrime ElevenPrime))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.fiberPrime ElevenPrime).comap (map ElevenPrime g))))
    (hcoordinate :
      localizedMap ElevenPrime g (C.fiberPrime ElevenPrime)
          sourceParameter * localDenominator qParameter =
        (-7 : Localization.AtPrime (C.fiberPrime ElevenPrime)) *
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
    isFormalImmersionAt_of_affineOpen_explicitQuotientCotangentAtEleven
      C g targetOpen quotientMap.left hfactor qParameter hqParameter
      sourceParameter hsourceMem hcoordinate
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
