/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspResidueRetraction
import MazurTorsion.ModularCurve.HeckeDifferentialQExpansion

/-!
# Differential q-expansions at a represented affine cusp

This file connects the mathematically correct Hecke object—a global differential sharing the
degree-one cotangent class of a pulled-back local parameter—to the checked affine-fibre
formal-immersion criterion.  The completed local function has expansion `F`; Hecke acts on a
cusp differential `Omega`.  Their degree-one coefficients agree up to the nonzero scalar supplied
by the cotangent comparison.  On an elliptic quotient, the full expansions differ by a unit.

The explicit weight-two q-expansion operator recovers every positive coefficient of `Omega` in
first position.  Since `Omega` has zero constant coefficient, a nonzero simultaneous eigenvector
forces the first coefficient of `F` to be nonzero.  This detects an actual cotangent vector and
proves formal immersion of the genuine affine `Spec.map` morphism.
-/

open Algebra TensorProduct AlgebraicGeometry
open MazurTorsion.ModularCurve
open MazurTorsion.ModularCurve.HeckeDifferentialQExpansion

namespace Ideal.Fiber

universe u

variable {K R S T : Type u} [Field K]
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- A nonzero weight-two Hecke eigen-differential detects an actual quotient-side cotangent
vector on the localized affine fibre. -/
theorem exists_detectedVector_of_weightTwoHeckeEigenDifferential_qExpansion
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing (p.Fiber T)]
    (sourceParameter : Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+* PowerSeries K)
    (F Omega : PowerSeries K)
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap p g q sourceParameter)) = F)
    (scale : K) (hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (level : {n : ℕ // 0 < n})
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (heigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n Omega =
        eigenvalue n • Omega) :
    ∃ detectedVector : IsLocalRing.CotangentSpace
        (Localization.AtPrime (q.comap (map p g))),
      IsLocalRing.cotangentMapAtResidue (localizedRingMap p g q)
        detectedVector ≠ 0 := by
  let detectedVector : IsLocalRing.CotangentSpace
      (Localization.AtPrime (q.comap (map p g))) :=
    (IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g)))).toCotangent
        ⟨sourceParameter, hsourceMem⟩
  refine ⟨detectedVector, ?_⟩
  intro hzero
  rw [IsLocalRing.cotangentMapAtResidue_apply] at hzero
  dsimp [detectedVector] at hzero
  have hpullbackSquare : localizedMap p g q sourceParameter ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2 := by
    rwa [Ideal.toCotangent_eq_zero] at hzero
  have hcoeffZero : PowerSeries.coeff 1 F = 0 := by
    rw [← hqExpansion]
    simpa only [completionRingHom] using
      QExpansionFirstCoefficient.coeff_one_completion_eq_zero_of_mem_maximalIdeal_sq
        qCoordinate hpullbackSquare
  exact
    (parameter_coeff_one_ne_zero_of_weightTwoHeckeEigenDifferential
        level F Omega scale hscale hfirstOrder hOmega hconstant eigenvalue
          heigen) hcoeffZero

end Ideal.Fiber

namespace MazurTorsion.ModularCurve.AffineCuspQExpansion

open Ideal.Fiber

universe u

variable {K R S T : Type u} [Field K]
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- A weight-two Hecke eigen-differential proves formal immersion of a represented affine cusp
map when its degree-one cotangent class matches the completed target parameter. -/
theorem isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T) (q : Ideal (p.Fiber T)) [q.IsPrime]
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (qParameter : Localization.AtPrime q)
    (hmaximal : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2)
    (sourceParameter : Localization.AtPrime (q.comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime q) ≃+* PowerSeries K)
    (F Omega : PowerSeries K)
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime q)
            (localizedMap p g q sourceParameter)) = F)
    (scale : K) (hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (level : {n : ℕ // 0 < n})
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (heigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n Omega =
        eigenvalue n • Omega)
    (hresidueAmbient : Function.Surjective
      (IsLocalRing.ResidueField.map (ambientLocalizedMap p g q))) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p q) := by
  have hresidueFiber : Function.Surjective
      (IsLocalRing.ResidueField.map (localizedRingMap p g q)) :=
    localizedResidueFieldMap_surjective_of_ambient p g q hresidueAmbient
  obtain ⟨detectedVector, hdetected⟩ :=
    exists_detectedVector_of_weightTwoHeckeEigenDifferential_qExpansion
      p g q sourceParameter hsourceMem qCoordinate F Omega hqExpansion
        scale hscale hfirstOrder hOmega hconstant level eigenvalue heigen
  exact isFormalImmersionAtSpecMap_of_qParameter p g q hresidueFiber
    qParameter hmaximal hqLinear detectedVector hdetected hresidueAmbient

/-- The structural cusp section supplies both residue-field comparisons for the differential
q-expansion criterion and canonically selects the special-fibre cusp prime. -/
theorem
    isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion_of_structuralSection
    (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (C : AffineStructuralSection (R := R) (T := T))
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsNoetherianRing (p.Fiber T)]
    (qParameter : Localization.AtPrime (C.fiberPrime p))
    (hmaximal :
      IsLocalRing.maximalIdeal (Localization.AtPrime (C.fiberPrime p)) =
        Ideal.span {qParameter})
    (hqLinear : qParameter ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime (C.fiberPrime p)) ^ 2)
    (sourceParameter : Localization.AtPrime
      ((C.fiberPrime p).comap (map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime ((C.fiberPrime p).comap (map p g))))
    (qCoordinate :
      LocalCompletion.Ring (Localization.AtPrime (C.fiberPrime p)) ≃+*
        PowerSeries K)
    (F Omega : PowerSeries K)
    (hqExpansion :
      qCoordinate
          (completionRingHom (Localization.AtPrime (C.fiberPrime p))
            (localizedMap p g (C.fiberPrime p) sourceParameter)) = F)
    (scale : K) (hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (level : {n : ℕ // 0 < n})
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (heigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n Omega =
        eigenvalue n • Omega) :
    IsFormalImmersionAt (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.fiberPrime p)) :=
  isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion
    p g (C.fiberPrime p) qParameter hmaximal hqLinear sourceParameter
      hsourceMem qCoordinate F Omega hqExpansion scale hscale hfirstOrder
      hOmega hconstant level eigenvalue heigen
      (ambientResidue_surjective_of_section p g (C.fiberPrime p)
        (C.atFiberPoint p))

end MazurTorsion.ModularCurve.AffineCuspQExpansion
