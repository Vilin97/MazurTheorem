/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspDifferentialArithmeticConsumers

/-!
# Prime-five arithmetic consumer of the explicit Eisenstein differential

This file is the prime-order companion to the order-35 differential consumer.
The modular level is bundled as a positive natural number and is definitionally
the order excluded by the arithmetic endpoint.  The simultaneous Hecke
eigen-expansion is constructed from restricted divisor sums; the caller supplies
only its geometric realization as the quotient differential.

As at eleven, the represented cusp chart constructs the completed coordinate
and its cotangent generator.  An affine open in the Néron model transfers the
resulting formal immersion to the actual quotient map, while Néron
specialization derives the whole-section quotient collision.
-/

noncomputable section

open Algebra AlgebraicGeometry CategoryTheory Ideal.Fiber TensorProduct
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace MazurTorsion.PrimeOrder

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open MazurTorsion.ModularCurve.AffineCuspPolynomialChart
open MazurTorsion.ModularCurve.AffineCuspPolynomialChart.AffinePresentation
open WeierstrassCurve.Affine

private abbrev FiveBase := atFive.adicCompletionIntegers ℚ

private abbrev FivePrime : Ideal FiveBase :=
  affineCuspSpecialFiberIdealAtFive

/-- A represented cusp q-coordinate and the explicit Eisenstein differential at
the same prime level excluded by the conclusion reach the uniform prime-order
endpoint through Néron specialization at five. -/
theorem
    rationalPoint_primeOrder_ne_of_affineEisensteinDifferentialNeronSpecializationAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : CommGroupScheme (Spec (.of (atFive.adicCompletion ℚ)))}
    (Ner : NeronModel FiveBase (atFive.adicCompletion ℚ) A)
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra FiveBase S] [Algebra FiveBase T]
    [IsNoetherianRing S]
    (C : AffinePresentation FiveBase T)
    (g : S →ₐ[FiveBase] T)
    (targetOpen : Spec (.of S) ⟶ Ner.model.X.left)
    [IsOpenImmersion targetOpen]
    (quotientMap : sourceOver FiveBase T ⟶ Ner.model.X)
    (hfactor :
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen =
        quotientMap.left)
    (modularSection :
      Over.mk (𝟙 (Spec (.of FiveBase))) ⟶ sourceOver FiveBase T)
    (sourceParameter : Localization.AtPrime
      ((C.zeroSection.fiberPrime FivePrime).comap
        (Ideal.Fiber.map FivePrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.zeroSection.fiberPrime FivePrime).comap
          (Ideal.Fiber.map FivePrime g))))
    (level : {N : ℕ // 0 < N})
    (F U : PowerSeries FivePrime.ResidueField)
    (hqExpansion :
      C.qCoordinate FivePrime
          (completionRingHom (C.CuspLocalRing FivePrime)
            (localizedMap FivePrime g
              (C.zeroSection.fiberPrime FivePrime) sourceParameter)) = F)
    (hDifferential :
      EisensteinDifferentialQExpansion.eisensteinDifferentialExpansion level =
        U * HeckeDifferentialQExpansion.logarithmicDerivativeExpansion F)
    (hunitConstant : PowerSeries.coeff 0 U ≠ 0)
    (hprime : level.1.Prime)
    (hlevel : 11 ≤ level.1)
    (hgeneric_ne :
      fractionSpecMap FiveBase (atFive.adicCompletion ℚ) ≫
          modularSection.left ≠
        fractionSpecMap FiveBase (atFive.adicCompletion ℚ) ≫
          C.zeroSectionOver.left)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      restrictBaseSection (residueSpecMap FiveBase)
          (sourceOver FiveBase T) modularSection =
        restrictBaseSection (residueSpecMap FiveBase)
          (sourceOver FiveBase T) C.zeroSectionOver)
    (htorsion : IsOfFinOrder
      (Ner.basePointRestriction (modularSection ≫ quotientMap) /
        Ner.basePointRestriction (C.zeroSectionOver ≫ quotientMap)))
    (hinjective : ∀ z :
        Over.mk (𝟙 (Spec (.of (atFive.adicCompletion ℚ)))) ⟶ A.X,
      IsOfFinOrder z →
        Ner.basePointSpecialization (residueSpecMap FiveBase) z = 1 →
        z = 1)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ level.1 := by
  have hformalTarget : IsFormalImmersionAt quotientMap.left
      (targetSpecPoint FivePrime
        (C.zeroSection.fiberPrime FivePrime)) :=
    C.isFormalImmersionAt_of_affineOpen_eisensteinDifferential_qExpansion
      FivePrime g targetOpen quotientMap.left hfactor sourceParameter
      hsourceMem level F U hqExpansion hDifferential hunitConstant
  have hcuspPoint :
      C.zeroSectionOver.left (IsLocalRing.closedPoint FiveBase) =
        targetSpecPoint FivePrime
          (C.zeroSection.fiberPrime FivePrime) := by
    change C.zeroSection.toSpec (IsLocalRing.closedPoint FiveBase) =
      targetSpecPoint FivePrime
        (C.zeroSection.fiberPrime FivePrime)
    simpa only [zeroSectionOver_left, FivePrime,
      affineCuspSpecialFiberIdealAtFive, IsLocalRing.closedPoint] using
        C.zeroSection.atPrime FivePrime
  have hformal : IsFormalImmersionAt quotientMap.left
      (C.zeroSectionOver.left (IsLocalRing.closedPoint FiveBase)) := by
    rw [hcuspPoint]
    exact hformalTarget
  exact rationalPoint_primeOrder_ne_of_neronSpecializationAtFive
    Ner (sourceOver FiveBase T) quotientMap modularSection C.zeroSectionOver
    hformal hgeneric_ne hspecializes htorsion hinjective P level.1 hprime
    hlevel

end MazurTorsion.PrimeOrder
