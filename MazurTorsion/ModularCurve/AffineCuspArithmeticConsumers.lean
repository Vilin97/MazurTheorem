/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFiveFormalImmersionAtEleven
import MazurTorsion.ModularCurve.AffineCuspResidueRetraction
import MazurTorsion.PrimeOrder.FormalImmersionNeronAtFive

/-!
# Arithmetic consumers of affine cusp q-expansions

This file connects the explicit affine-chart criterion in
`AffineCuspQExpansion` to the two theorem-critical arithmetic lanes.  In both
lanes the morphism is the genuine affine morphism `Spec.map g`, the cusp is a
prime of its special fibre, and the caller identifies that prime with the
closed point selected by the integral cusp section.

The legacy adapters retain explicit residue and component-exponent premises.
The stronger Hecke adapters instead package the affine cusp as an actual
section through the chosen fibre point.  Contravariance derives its
coordinate-ring retraction and hence both residue surjections.  Their
formal-immersion collision feeds the checked weighted-depth closure of the
additive branch and the finite enumerations over `F₅` and `F₁₁`, giving
respectively the uniform prime-order exclusion at five and the order-35
exclusion at eleven.

The final structural-section adapters remove the chosen fibre point as an
input as well.  They base-change the section to the residue field and take
the kernel as the canonical cusp prime, then prove that the original section
meets precisely that point.

The local-DVR adapters further replace asserted maximal-ideal generation and
nonvanishing modulo its square by an actual DVR instance and irreducibility
of the chosen parameter.  They do not construct that local geometry or the
q-coordinate; those remain explicit application-side obligations.

No represented modular curve or quotient is constructed here.  The remaining
inputs explicitly include the integral modular and cusp sections, their
specialization and quotient collision, and the affine Hecke/q-expansion
calculation.  No represented modular curve or rank-zero quotient is inferred.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry CategoryTheory

namespace MazurTorsion.PrimeOrder

open Ideal.Fiber
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open MazurTorsion.ModularCurve.AffineCuspQExpansion
open WeierstrassCurve WeierstrassCurve.Affine

/-- The maximal ideal defining the characteristic-five fibre of the selected
five-adic integer ring. -/
abbrev affineCuspSpecialFiberIdealAtFive :
    Ideal (atFive.adicCompletionIntegers ℚ) :=
  IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ)

/-- The characteristic-five fibre point selected canonically by a structural
affine cusp section. -/
noncomputable abbrev affineCuspFiberPrimeAtFive
    {T : Type} [CommRing T]
    [Algebra (atFive.adicCompletionIntegers ℚ) T]
    (C : AffineStructuralSection
      (R := atFive.adicCompletionIntegers ℚ) (T := T)) :
    Ideal (affineCuspSpecialFiberIdealAtFive.Fiber T) :=
  C.fiberPrime affineCuspSpecialFiberIdealAtFive

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

/-- A nonzero Hecke eigen-expansion on the actual characteristic-five affine
cusp reaches the uniform prime-order exclusion.

This is the arithmetic consumer of
`isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion`: the Hecke recursion is
performed in the completed localization at the same fibre prime identified
with the integral cusp section by `hcuspPoint`. -/
theorem
    rationalPoint_primeOrder_ne_of_affineCuspHeckeQExpansionAtFive_of_componentExponentTwelve
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
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap affineCuspSpecialFiberIdealAtFive g q
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
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
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion
      affineCuspSpecialFiberIdealAtFive g q qParameter hmaximal hqLinear
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke
      eigenvalue hfirst heigen hresidueAmbient
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspSection (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact
    rationalPoint_primeOrder_ne_of_formalImmersionAtFive_of_componentExponentTwelve
      (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection cuspSection
      hformalAtCusp hne hspecializes hquotient P hcomponentExponent N hprime hN

/-- A rational affine cusp retraction and a nonzero Hecke eigen-expansion
reach the unconditional prime-order contradiction at five.

The retraction derives both residue-field surjections.  The formal-immersion
collision then gives the `j`-valuation bound, while the checked marked
weighted-depth argument and `F₅` enumeration discharge the entire local
arithmetic tail. -/
theorem
    rationalPoint_primeOrder_ne_of_affineCuspHeckeQExpansionAtFive_of_retraction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
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
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap affineCuspSpecialFiberIdealAtFive g q
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (cuspRetraction : T →ₐ[atFive.adicCompletionIntegers ℚ]
      atFive.adicCompletionIntegers ℚ)
    (hcuspClosedPoint :
      targetBasePrime affineCuspSpecialFiberIdealAtFive q =
        affineCuspSpecialFiberIdealAtFive.comap
          cuspRetraction.toRingHom)
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
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  have hformalAtTarget : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint affineCuspSpecialFiberIdealAtFive q) :=
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_retraction
      affineCuspSpecialFiberIdealAtFive g q qParameter hmaximal hqLinear
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke
      eigenvalue hfirst heigen cuspRetraction hcuspClosedPoint
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspSection (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact rationalPoint_primeOrder_ne_of_formalImmersionAtFive
    (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection cuspSection
    hformalAtCusp hne hspecializes hquotient P N hprime hN

/-- A genuine rational affine cusp section and a nonzero Hecke
eigen-expansion reach the unconditional prime-order contradiction at five.

The section law now determines the coordinate-ring retraction, and its value
at the closed point identifies the fibre prime.  This is the geometric
consumer of `AffineSectionAtFiberPoint`; neither compatibility can be chosen
independently. -/
theorem
    rationalPoint_primeOrder_ne_of_affineCuspHeckeQExpansionAtFive_of_section
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atFive.adicCompletionIntegers ℚ) S]
    [Algebra (atFive.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atFive.adicCompletionIntegers ℚ] T)
    (q : Ideal (affineCuspSpecialFiberIdealAtFive.Fiber T)) [q.IsPrime]
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtFive.Fiber T)]
    (modularSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (cuspData : AffineSectionAtFiberPoint
      affineCuspSpecialFiberIdealAtFive q)
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
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap affineCuspSpecialFiberIdealAtFive g q
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ cuspData.toSpec)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        cuspData.toSpec (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspData.toSpec ≫ Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  have hformalAtTarget : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint affineCuspSpecialFiberIdealAtFive q) :=
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_section
      affineCuspSpecialFiberIdealAtFive g q qParameter hmaximal hqLinear
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke
      eigenvalue hfirst heigen cuspData
  have hcuspPoint :
      cuspData.toSpec (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ)) =
        targetSpecPoint affineCuspSpecialFiberIdealAtFive q := by
    simpa only [IsLocalRing.closedPoint,
      affineCuspSpecialFiberIdealAtFive] using cuspData.atPrime
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspData.toSpec (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact rationalPoint_primeOrder_ne_of_formalImmersionAtFive
    (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection
    cuspData.toSpec hformalAtCusp hne hspecializes hquotient P N hprime hN

/-- A represented affine structural cusp section canonically selects its
characteristic-five fibre point and reaches the unconditional prime-order
exclusion.

Compared with the point-indexed section consumer, neither a fibre prime nor
a proof identifying the section's closed point is supplied by the caller. -/
theorem
    rationalPoint_primeOrder_ne_of_affineCuspHeckeQExpansionAtFive_of_structuralSection
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atFive.adicCompletionIntegers ℚ) S]
    [Algebra (atFive.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atFive.adicCompletionIntegers ℚ] T)
    (cuspSection : AffineStructuralSection
      (R := atFive.adicCompletionIntegers ℚ) (T := T))
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtFive.Fiber T)]
    (modularSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (qParameter : Localization.AtPrime
      (affineCuspFiberPrimeAtFive cuspSection))
    (hmaximal : IsLocalRing.maximalIdeal
        (Localization.AtPrime (affineCuspFiberPrimeAtFive cuspSection)) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉ IsLocalRing.maximalIdeal
      (Localization.AtPrime (affineCuspFiberPrimeAtFive cuspSection)) ^ 2)
    (sourceParameter : Localization.AtPrime
      ((affineCuspFiberPrimeAtFive cuspSection).comap
        (Ideal.Fiber.map affineCuspSpecialFiberIdealAtFive g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((affineCuspFiberPrimeAtFive cuspSection).comap
          (Ideal.Fiber.map affineCuspSpecialFiberIdealAtFive g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime
            (affineCuspFiberPrimeAtFive cuspSection)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime
              (affineCuspFiberPrimeAtFive cuspSection))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtFive cuspSection))))
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime
              (affineCuspFiberPrimeAtFive cuspSection))
            (localizedMap affineCuspSpecialFiberIdealAtFive g
              (affineCuspFiberPrimeAtFive cuspSection)
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtFive cuspSection)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime
            (affineCuspFiberPrimeAtFive cuspSection)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtFive cuspSection)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ cuspSection.toSpec)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        cuspSection.toSpec (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspSection.toSpec ≫
          Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N :=
  rationalPoint_primeOrder_ne_of_affineCuspHeckeQExpansionAtFive_of_section
    g (affineCuspFiberPrimeAtFive cuspSection) modularSection
    (cuspSection.atFiberPoint affineCuspSpecialFiberIdealAtFive)
    qParameter hmaximal hqLinear sourceParameter hsourceMem qCoordinate Q
    hqExpansion hQ hecke eigenvalue hfirst heigen hne hspecializes hquotient
    P N hprime hN

/-- An irreducible uniformizer in the DVR local ring at the canonical
characteristic-five cusp reaches the unconditional prime-order exclusion.

This is the arithmetic consumer of the intrinsic local-DVR adapter.  The
represented structural section constructs the cusp point and residue maps;
the DVR uniformizer derives maximal-ideal generation and its nonzero class
modulo the square.  The remaining hypotheses are the genuine Hecke
q-expansion and the established modular-section collision. -/
theorem
    rationalPoint_primeOrder_ne_of_affineCuspDVRUniformizerHeckeQExpansionAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atFive.adicCompletionIntegers ℚ) S]
    [Algebra (atFive.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atFive.adicCompletionIntegers ℚ] T)
    (cuspSection : AffineStructuralSection
      (R := atFive.adicCompletionIntegers ℚ) (T := T))
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtFive.Fiber T)]
    [IsDomain
      (Localization.AtPrime (affineCuspFiberPrimeAtFive cuspSection))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (affineCuspFiberPrimeAtFive cuspSection))]
    (modularSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (qParameter : Localization.AtPrime
      (affineCuspFiberPrimeAtFive cuspSection))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((affineCuspFiberPrimeAtFive cuspSection).comap
        (Ideal.Fiber.map affineCuspSpecialFiberIdealAtFive g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((affineCuspFiberPrimeAtFive cuspSection).comap
          (Ideal.Fiber.map affineCuspSpecialFiberIdealAtFive g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime
            (affineCuspFiberPrimeAtFive cuspSection)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime
              (affineCuspFiberPrimeAtFive cuspSection))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtFive cuspSection))))
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime
              (affineCuspFiberPrimeAtFive cuspSection))
            (localizedMap affineCuspSpecialFiberIdealAtFive g
              (affineCuspFiberPrimeAtFive cuspSection)
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtFive cuspSection)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime
            (affineCuspFiberPrimeAtFive cuspSection)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtFive cuspSection)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ cuspSection.toSpec)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        cuspSection.toSpec (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspSection.toSpec ≫
          Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  have hformalAtTarget : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint affineCuspSpecialFiberIdealAtFive
        (affineCuspFiberPrimeAtFive cuspSection)) :=
    isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_dvrUniformizer_of_structuralSection
      affineCuspSpecialFiberIdealAtFive g cuspSection qParameter hqParameter
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke
      eigenvalue hfirst heigen
  have hcuspPoint :
      cuspSection.toSpec (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ)) =
        targetSpecPoint affineCuspSpecialFiberIdealAtFive
          (affineCuspFiberPrimeAtFive cuspSection) := by
    simpa only [IsLocalRing.closedPoint,
      affineCuspSpecialFiberIdealAtFive] using
        cuspSection.atPrime affineCuspSpecialFiberIdealAtFive
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspSection.toSpec (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact rationalPoint_primeOrder_ne_of_formalImmersionAtFive
    (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection
    cuspSection.toSpec hformalAtCusp hne hspecializes hquotient P N hprime hN

end MazurTorsion.PrimeOrder

namespace MazurTorsion.OrderThirtyFive

open Ideal.Fiber
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open MazurTorsion.ModularCurve.AffineCuspQExpansion
open WeierstrassCurve WeierstrassCurve.Affine

/-- The maximal ideal defining the characteristic-eleven fibre of the
selected eleven-adic integer ring. -/
abbrev affineCuspSpecialFiberIdealAtEleven :
    Ideal (atEleven.adicCompletionIntegers ℚ) :=
  IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ)

/-- The characteristic-eleven fibre point selected canonically by a
structural affine cusp section. -/
noncomputable abbrev affineCuspFiberPrimeAtEleven
    {T : Type} [CommRing T]
    [Algebra (atEleven.adicCompletionIntegers ℚ) T]
    (C : AffineStructuralSection
      (R := atEleven.adicCompletionIntegers ℚ) (T := T)) :
    Ideal (affineCuspSpecialFiberIdealAtEleven.Fiber T) :=
  C.fiberPrime affineCuspSpecialFiberIdealAtEleven

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

/-- The same completed-local Hecke criterion at the characteristic-eleven
cusp reaches the order-35 exclusion.  This is the squarefree-level consumer
of the shared affine-fibre formal-immersion engine. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_affineCuspHeckeQExpansionAtEleven_of_componentExponentTwelve
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
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap affineCuspSpecialFiberIdealAtEleven g q
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
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
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion
      affineCuspSpecialFiberIdealAtEleven g q qParameter hmaximal hqLinear
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke
      eigenvalue hfirst heigen hresidueAmbient
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

/-- A rational affine cusp retraction and the squarefree-level Hecke
eigen-expansion reach the unconditional order-35 contradiction at eleven.

Both residue-field hypotheses and the marked component-exponent premise of
the legacy adapter are discharged by checked constructions. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_affineCuspHeckeQExpansionAtEleven_of_retraction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
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
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap affineCuspSpecialFiberIdealAtEleven g q
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (cuspRetraction : T →ₐ[atEleven.adicCompletionIntegers ℚ]
      atEleven.adicCompletionIntegers ℚ)
    (hcuspClosedPoint :
      targetBasePrime affineCuspSpecialFiberIdealAtEleven q =
        affineCuspSpecialFiberIdealAtEleven.comap
          cuspRetraction.toRingHom)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)) =
        cuspSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  have hformalAtTarget : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint affineCuspSpecialFiberIdealAtEleven q) :=
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_retraction
      affineCuspSpecialFiberIdealAtEleven g q qParameter hmaximal hqLinear
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke
      eigenvalue hfirst heigen cuspRetraction hcuspClosedPoint
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspSection (IsLocalRing.closedPoint
        (atEleven.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact rationalPoint_orderThirtyFive_ne_of_formalImmersionAtEleven
    (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection cuspSection
    hformalAtCusp hne hspecializes hquotient P

/-- A genuine rational affine cusp section and the squarefree-level Hecke
eigen-expansion reach the unconditional order-35 contradiction at eleven.

This is the second arithmetic consumer of `AffineSectionAtFiberPoint`.  It
uses the same checked section-to-retraction construction as the prime lane,
so the characteristic-five and characteristic-eleven routes share one
geometric handoff. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_affineCuspHeckeQExpansionAtEleven_of_section
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atEleven.adicCompletionIntegers ℚ) S]
    [Algebra (atEleven.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atEleven.adicCompletionIntegers ℚ] T)
    (q : Ideal (affineCuspSpecialFiberIdealAtEleven.Fiber T)) [q.IsPrime]
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtEleven.Fiber T)]
    (modularSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (cuspData : AffineSectionAtFiberPoint
      affineCuspSpecialFiberIdealAtEleven q)
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
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+*
        PowerSeries (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (Q : PowerSeries
      (IsLocalRing.ResidueField (Localization.AtPrime q)))
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap affineCuspSpecialFiberIdealAtEleven g q
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField (Localization.AtPrime q))
      (PowerSeries
        (IsLocalRing.ResidueField (Localization.AtPrime q))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField (Localization.AtPrime q))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ cuspData.toSpec)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)) =
        cuspData.toSpec (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspData.toSpec ≫ Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  have hformalAtTarget : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint affineCuspSpecialFiberIdealAtEleven q) :=
    AffineCuspQExpansion.isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_section
      affineCuspSpecialFiberIdealAtEleven g q qParameter hmaximal hqLinear
      sourceParameter hsourceMem qCoordinate Q hqExpansion hQ hecke
      eigenvalue hfirst heigen cuspData
  have hcuspPoint :
      cuspData.toSpec (IsLocalRing.closedPoint
        (atEleven.adicCompletionIntegers ℚ)) =
        targetSpecPoint affineCuspSpecialFiberIdealAtEleven q := by
    simpa only [IsLocalRing.closedPoint,
      affineCuspSpecialFiberIdealAtEleven] using cuspData.atPrime
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspData.toSpec (IsLocalRing.closedPoint
        (atEleven.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact rationalPoint_orderThirtyFive_ne_of_formalImmersionAtEleven
    (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection
    cuspData.toSpec hformalAtCusp hne hspecializes hquotient P

/-- A represented affine structural cusp section canonically selects its
characteristic-eleven fibre point and reaches the unconditional order-35
exclusion.

This is the squarefree-level companion of the characteristic-five consumer;
the fibre prime and its compatibility with the cusp section are derived from
the section law. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_affineCuspHeckeQExpansionAtEleven_of_structuralSection
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atEleven.adicCompletionIntegers ℚ) S]
    [Algebra (atEleven.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atEleven.adicCompletionIntegers ℚ] T)
    (cuspSection : AffineStructuralSection
      (R := atEleven.adicCompletionIntegers ℚ) (T := T))
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtEleven.Fiber T)]
    (modularSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (qParameter : Localization.AtPrime
      (affineCuspFiberPrimeAtEleven cuspSection))
    (hmaximal : IsLocalRing.maximalIdeal
        (Localization.AtPrime
          (affineCuspFiberPrimeAtEleven cuspSection)) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        (affineCuspFiberPrimeAtEleven cuspSection)) ^ 2)
    (sourceParameter : Localization.AtPrime
      ((affineCuspFiberPrimeAtEleven cuspSection).comap
        (Ideal.Fiber.map affineCuspSpecialFiberIdealAtEleven g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((affineCuspFiberPrimeAtEleven cuspSection).comap
          (Ideal.Fiber.map affineCuspSpecialFiberIdealAtEleven g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime
            (affineCuspFiberPrimeAtEleven cuspSection)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime
              (affineCuspFiberPrimeAtEleven cuspSection))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtEleven cuspSection))))
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime
              (affineCuspFiberPrimeAtEleven cuspSection))
            (localizedMap affineCuspSpecialFiberIdealAtEleven g
              (affineCuspFiberPrimeAtEleven cuspSection)
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtEleven cuspSection)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime
            (affineCuspFiberPrimeAtEleven cuspSection)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtEleven cuspSection)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ cuspSection.toSpec)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)) =
        cuspSection.toSpec (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspSection.toSpec ≫
          Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  rationalPoint_orderThirtyFive_ne_of_affineCuspHeckeQExpansionAtEleven_of_section
    g (affineCuspFiberPrimeAtEleven cuspSection) modularSection
    (cuspSection.atFiberPoint affineCuspSpecialFiberIdealAtEleven)
    qParameter hmaximal hqLinear sourceParameter hsourceMem qCoordinate Q
    hqExpansion hQ hecke eigenvalue hfirst heigen hne hspecializes hquotient
    P

/-- The intrinsic DVR-uniformizer adapter at the canonical
characteristic-eleven cusp reaches the order-35 exclusion.

This is the mechanical squarefree-level companion of the prime-five
consumer.  It shares the same local-DVR and irreducible-uniformizer API and
feeds the already checked order-35 formal-immersion collision. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_affineCuspDVRUniformizerHeckeQExpansionAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra (atEleven.adicCompletionIntegers ℚ) S]
    [Algebra (atEleven.adicCompletionIntegers ℚ) T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (g : S →ₐ[atEleven.adicCompletionIntegers ℚ] T)
    (cuspSection : AffineStructuralSection
      (R := atEleven.adicCompletionIntegers ℚ) (T := T))
    [IsNoetherianRing (affineCuspSpecialFiberIdealAtEleven.Fiber T)]
    [IsDomain
      (Localization.AtPrime (affineCuspFiberPrimeAtEleven cuspSection))]
    [IsDiscreteValuationRing
      (Localization.AtPrime (affineCuspFiberPrimeAtEleven cuspSection))]
    (modularSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ Spec (.of T))
    (qParameter : Localization.AtPrime
      (affineCuspFiberPrimeAtEleven cuspSection))
    (hqParameter : Irreducible qParameter)
    (sourceParameter : Localization.AtPrime
      ((affineCuspFiberPrimeAtEleven cuspSection).comap
        (Ideal.Fiber.map affineCuspSpecialFiberIdealAtEleven g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((affineCuspFiberPrimeAtEleven cuspSection).comap
          (Ideal.Fiber.map affineCuspSpecialFiberIdealAtEleven g))))
    (qCoordinate :
      LocalCompletion.Ring
          (Localization.AtPrime
            (affineCuspFiberPrimeAtEleven cuspSection)) ≃+*
        PowerSeries
          (IsLocalRing.ResidueField
            (Localization.AtPrime
              (affineCuspFiberPrimeAtEleven cuspSection))))
    (Q : PowerSeries
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtEleven cuspSection))))
    (hqExpansion :
      qCoordinate
          (completionRingHom
            (Localization.AtPrime
              (affineCuspFiberPrimeAtEleven cuspSection))
            (localizedMap affineCuspSpecialFiberIdealAtEleven g
              (affineCuspFiberPrimeAtEleven cuspSection)
              sourceParameter)) = Q)
    (hQ : Q ≠ 0)
    (hecke : ℕ → Module.End
      (IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtEleven cuspSection)))
      (PowerSeries
        (IsLocalRing.ResidueField
          (Localization.AtPrime
            (affineCuspFiberPrimeAtEleven cuspSection)))))
    (eigenvalue : ℕ →
      IsLocalRing.ResidueField
        (Localization.AtPrime
          (affineCuspFiberPrimeAtEleven cuspSection)))
    (hfirst : ∀ n, PowerSeries.coeff 1 (hecke n Q) =
      PowerSeries.coeff n Q)
    (heigen : ∀ n, hecke n Q = eigenvalue n • Q)
    (hne : modularSection ≠ cuspSection.toSpec)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)) =
        cuspSection.toSpec (IsLocalRing.closedPoint
          (atEleven.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
        cuspSection.toSpec ≫
          Spec.map (CommRingCat.ofHom g.toRingHom))
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  have hformalAtTarget : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint affineCuspSpecialFiberIdealAtEleven
        (affineCuspFiberPrimeAtEleven cuspSection)) :=
    isFormalImmersionAtSpecMap_of_heckeEigen_qExpansion_of_dvrUniformizer_of_structuralSection
      affineCuspSpecialFiberIdealAtEleven g cuspSection qParameter
      hqParameter sourceParameter hsourceMem qCoordinate Q hqExpansion hQ
      hecke eigenvalue hfirst heigen
  have hcuspPoint :
      cuspSection.toSpec (IsLocalRing.closedPoint
        (atEleven.adicCompletionIntegers ℚ)) =
        targetSpecPoint affineCuspSpecialFiberIdealAtEleven
          (affineCuspFiberPrimeAtEleven cuspSection) := by
    simpa only [IsLocalRing.closedPoint,
      affineCuspSpecialFiberIdealAtEleven] using
        cuspSection.atPrime affineCuspSpecialFiberIdealAtEleven
  have hformalAtCusp : IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (cuspSection.toSpec (IsLocalRing.closedPoint
        (atEleven.adicCompletionIntegers ℚ))) := by
    rw [hcuspPoint]
    exact hformalAtTarget
  exact rationalPoint_orderThirtyFive_ne_of_formalImmersionAtEleven
    (Spec.map (CommRingCat.ofHom g.toRingHom)) modularSection
    cuspSection.toSpec hformalAtCusp hne hspecializes hquotient P

end MazurTorsion.OrderThirtyFive
