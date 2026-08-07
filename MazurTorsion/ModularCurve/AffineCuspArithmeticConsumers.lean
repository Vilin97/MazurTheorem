/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFiveFormalImmersionAtEleven
import MazurTorsion.ModularCurve.AffineCuspQExpansion
import MazurTorsion.PrimeOrder.FormalImmersionNeronAtFive

/-!
# Arithmetic consumers of affine cusp q-expansions

This file connects the explicit affine-chart criterion in
`AffineCuspQExpansion` to the two theorem-critical arithmetic lanes.  In both
lanes the morphism is the genuine affine morphism `Spec.map g`, the cusp is a
prime of its special fibre, and the caller identifies that prime with the
closed point selected by the integral cusp section.

The first-order identity, the two residue-field surjections, and the
uniformizer calculation then prove formal immersion at that same cusp.  The
result is consumed by the checked formal-immersion collision and the marked
component-exponent-twelve endpoint, giving respectively the uniform
prime-order exclusion at five and the order-35 exclusion at eleven.

No represented modular curve or quotient is constructed here.  The remaining
inputs explicitly include the integral modular and cusp sections, their
specialization and quotient collision, the affine chart calculation, and the
marked component statement on the selected minimal Weierstrass equation.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry CategoryTheory

namespace MazurTorsion.PrimeOrder

open Ideal.Fiber
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine

/-- The maximal ideal defining the characteristic-five fibre of the selected
five-adic integer ring. -/
abbrev affineCuspSpecialFiberIdealAtFive :
    Ideal (atFive.adicCompletionIntegers ℚ) :=
  IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ)

/-- An explicit affine `q`-expansion at the characteristic-five cusp reaches
the uniform prime-order exclusion.

The equality `hcuspPoint` is the essential geometric handoff: it asserts that
the prime used by the affine localization is the closed point of the very cusp
section entering the modular collision. -/
theorem
    rationalPoint_primeOrder_ne_of_affineCuspQExpansionAtFive_of_componentExponentTwelve
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atFive.adicCompletionIntegers ℚ) S]
    [Algebra (atFive.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atFive.adicCompletionIntegers ℚ] T)
    (q : Ideal (affineCuspSpecialFiberIdealAtFive.Fiber T)) [q.IsPrime]
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtFive.Fiber T)]
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (hcuspPoint :
      cuspSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        targetSpecPoint affineCuspSpecialFiberIdealAtFive q)
    (hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map
        (localizedRingMap affineCuspSpecialFiberIdealAtFive g q)))
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter : Localization.AtPrime
      (q.comap (Ideal.Fiber.map affineCuspSpecialFiberIdealAtFive g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        (q.comap (Ideal.Fiber.map affineCuspSpecialFiberIdealAtFive g))))
    (unitCoefficient remainder : Localization.AtPrime q)
    (hunit : IsUnit unitCoefficient)
    (hremainder : remainder ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (hfirstOrder :
      localizedMap affineCuspSpecialFiberIdealAtFive g q sourceParameter =
        unitCoefficient * qParameter + remainder)
    (hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map
        (ambientLocalizedMap affineCuspSpecialFiberIdealAtFive g q)))
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        cuspSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point)
    (hcomponentExponent : ∀ (_hA :
      (minimalCompletionAtFive E).HasAdditiveReduction
        (atFive.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtFive E P ∈
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtFive_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtFive_map E)))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  have hformalAtTarget : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint affineCuspSpecialFiberIdealAtFive q) :=
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_unit_qExpansion
      affineCuspSpecialFiberIdealAtFive g q hresidueFiber qParameter
      hmaximal hqLinear sourceParameter hsourceMem unitCoefficient remainder
      hunit hremainder hfirstOrder hresidueAmbient
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspSection (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact rationalPoint_primeOrder_ne_of_formalImmersionAtFive_of_componentExponentTwelve
    (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection cuspSection
    hformalAtCusp hne hspecializes hquotient P hcomponentExponent N hprime hN

end MazurTorsion.PrimeOrder

namespace MazurTorsion.OrderThirtyFive

open Ideal.Fiber
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine

/-- The maximal ideal defining the characteristic-eleven fibre of the
selected eleven-adic integer ring. -/
abbrev affineCuspSpecialFiberIdealAtEleven :
    Ideal (atEleven.adicCompletionIntegers ℚ) :=
  IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ)

/-- An explicit affine `q`-expansion at the characteristic-eleven cusp reaches
the order-35 exclusion.

As in the prime lane, `hcuspPoint` prevents a cotangent calculation at an
unrelated fibre point from being used in the arithmetic collision. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_affineCuspQExpansionAtEleven_of_componentExponentTwelve
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atEleven.adicCompletionIntegers ℚ) S]
    [Algebra (atEleven.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atEleven.adicCompletionIntegers ℚ] T)
    (q : Ideal (affineCuspSpecialFiberIdealAtEleven.Fiber T)) [q.IsPrime]
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtEleven.Fiber T)]
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (hcuspPoint :
      cuspSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)) =
        targetSpecPoint affineCuspSpecialFiberIdealAtEleven q)
    (hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map
        (localizedRingMap affineCuspSpecialFiberIdealAtEleven g q)))
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter : Localization.AtPrime
      (q.comap (Ideal.Fiber.map affineCuspSpecialFiberIdealAtEleven g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        (q.comap (Ideal.Fiber.map affineCuspSpecialFiberIdealAtEleven g))))
    (unitCoefficient remainder : Localization.AtPrime q)
    (hunit : IsUnit unitCoefficient)
    (hremainder : remainder ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (hfirstOrder :
      localizedMap affineCuspSpecialFiberIdealAtEleven g q sourceParameter =
        unitCoefficient * qParameter + remainder)
    (hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map
        (ambientLocalizedMap affineCuspSpecialFiberIdealAtEleven g q)))
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)) =
        cuspSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point)
    (hcomponentExponent : ∀ (_hA :
      (minimalCompletionAtEleven E).HasAdditiveReduction
        (atEleven.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtEleven E P ∈
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) :
    addOrderOf P ≠ 35 := by
  let f : Spec (.of T) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom g.toRingHom)
  have hformalAtTarget : IsFormalImmersionAt f
      (targetSpecPoint affineCuspSpecialFiberIdealAtEleven q) :=
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_unit_qExpansion
      affineCuspSpecialFiberIdealAtEleven g q hresidueFiber qParameter
      hmaximal hqLinear sourceParameter hsourceMem unitCoefficient remainder
      hunit hremainder hfirstOrder hresidueAmbient
  have hformalAtCusp : IsFormalImmersionAt f
      (cuspSection (IsLocalRing.closedPoint
        (atEleven.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  have hj : atEleven.valuation ℚ E.j ≤ 1 := by
    by_contra hj
    apply hne
    have hpoint := hspecializes hj
    have hformalAtModular : IsFormalImmersionAt f
        (modularSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ))) := by
      simpa only [hpoint] using hformalAtCusp
    exact hformalAtModular.spec_ext_of_comp_eq_of_isNoetherian
      modularSection cuspSection hpoint (hquotient hj)
  exact
    rationalPoint_orderThirtyFive_ne_of_cuspidalReduction_of_componentExponentTwelveAtEleven
      hj P hcomponentExponent

end MazurTorsion.OrderThirtyFive
