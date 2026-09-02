/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.EllipticCurve.IntegerPrimeSpecialization
import MazurTorsion.ModularCurve.AffineCuspResidueRetraction
import MazurTorsion.ModularCurve.OrderThirtyFiveInfinityChartFirstOrder
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# The order-35 infinity cusp in characteristic eleven

This file proves the intrinsic local algebra needed to feed the represented
level-35 infinity-chart quotient map to the affine formal-immersion
criterion.  The argument works in the actual special fibre of the
eleven-adic integral chart.  It identifies the cusp ideal, proves that `t`
generates the maximal ideal after localization, and detects the nonzero
class of `t` modulo its square with an explicit dual-number tangent.

No completed-power-series equality or abstract DVR identification is
assumed.  The final endpoint is formal immersion for the genuine `Spec` map
constructed in `OrderThirtyFiveInfinityChartScheme`.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry CategoryTheory
open MazurTorsion.IntegerPrimeSpecialization

namespace MazurTorsion.OrderThirtyFive.InfinityChartAtEleven

open InfinityChartScheme InfinityChartFirstOrder
open Ideal.Fiber

private abbrev ElevenBase := atEleven.adicCompletionIntegers ℚ

private abbrev ElevenPrime : Ideal ElevenBase :=
  IsLocalRing.maximalIdeal ElevenBase

private abbrev ElevenSource := SourceOpenRing ElevenBase

private abbrev ElevenTarget := TargetRing ElevenBase

private abbrev ElevenMap : ElevenTarget →ₐ[ElevenBase] ElevenSource :=
  targetToOpenRing ElevenBase

/-- The represented integral infinity cusp packaged for the affine-fibre
formal-immersion API. -/
private def infinityCuspStructuralSection :
    AffineStructuralSection (R := ElevenBase) (T := ElevenSource) where
  toSpec := cuspSection ElevenBase
  isSection := cuspSection_isSection ElevenBase

private theorem infinityCuspStructuralSection_retraction :
    infinityCuspStructuralSection.retraction =
      cuspRetraction ElevenBase := by
  apply AlgHom.ext
  intro t
  simp [AffineStructuralSection.retraction,
    infinityCuspStructuralSection, cuspSection]

private abbrev ElevenCuspPrime :
    Ideal (ElevenPrime.Fiber ElevenSource) :=
  infinityCuspStructuralSection.fiberPrime ElevenPrime

private abbrev ElevenFiber := ElevenPrime.Fiber ElevenSource

private def fiberT : ElevenFiber :=
  Algebra.TensorProduct.includeRight (openT ElevenBase)

private def fiberS : ElevenFiber :=
  Algebra.TensorProduct.includeRight (openS ElevenBase)

private def cuspIdeal : Ideal ElevenFiber :=
  Ideal.span ({fiberT, fiberS - 1} : Set ElevenFiber)

@[simp]
private theorem fiberRetraction_t :
    infinityCuspStructuralSection.fiberRetraction ElevenPrime fiberT = 0 := by
  simp [fiberT, AffineStructuralSection.fiberRetraction,
    infinityCuspStructuralSection_retraction]

@[simp]
private theorem fiberRetraction_s :
    infinityCuspStructuralSection.fiberRetraction ElevenPrime fiberS = 1 := by
  simp [fiberS, AffineStructuralSection.fiberRetraction,
    infinityCuspStructuralSection_retraction]

private theorem cuspIdeal_le_cuspPrime :
    cuspIdeal ≤ ElevenCuspPrime := by
  rw [cuspIdeal, Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · change infinityCuspStructuralSection.fiberRetraction ElevenPrime fiberT = 0
    exact fiberRetraction_t
  · change infinityCuspStructuralSection.fiberRetraction ElevenPrime
      (fiberS - 1) = 0
    simp

private abbrev ElevenResidue := ElevenPrime.ResidueField

private abbrev CuspQuotient := ElevenFiber ⧸ cuspIdeal

/-- Evaluation at the cusp descends through the explicit two-generator
quotient. -/
private def cuspQuotientRetraction : CuspQuotient →ₐ[ElevenResidue] ElevenResidue :=
  Ideal.Quotient.liftₐ cuspIdeal
    (infinityCuspStructuralSection.fiberRetraction ElevenPrime)
    fun _ hx ↦ cuspIdeal_le_cuspPrime hx

@[simp]
private theorem quotientMk_fiberT :
    Ideal.Quotient.mk cuspIdeal fiberT = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert fiberT {fiberS - 1})

@[simp]
private theorem quotientMk_fiberS :
    Ideal.Quotient.mk cuspIdeal fiberS = 1 := by
  have h : Ideal.Quotient.mk cuspIdeal (fiberS - 1) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span
      (Set.mem_insert_of_mem fiberT (Set.mem_singleton (fiberS - 1)))
  apply sub_eq_zero.mp
  simpa using h

/-- Modulo `(t,s-1)`, the source special fibre is generated only by the
residue-field scalars. -/
private theorem cuspQuotient_section_retraction :
    (Algebra.ofId ElevenResidue CuspQuotient).comp cuspQuotientRetraction =
      AlgHom.id ElevenResidue CuspQuotient := by
  apply Ideal.Quotient.algHom_ext ElevenResidue
  apply Algebra.TensorProduct.ext_ring
  apply IsLocalization.algHom_ext
    (Submonoid.powers (sourceDenominator ElevenBase))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change
      algebraMap ElevenResidue CuspQuotient
          (infinityCuspStructuralSection.fiberRetraction ElevenPrime fiberT) =
        Ideal.Quotient.mk cuspIdeal fiberT
    simp
  · change
      algebraMap ElevenResidue CuspQuotient
          (infinityCuspStructuralSection.fiberRetraction ElevenPrime fiberS) =
        Ideal.Quotient.mk cuspIdeal fiberS
    simp

private theorem cuspQuotientRetraction_injective :
    Function.Injective cuspQuotientRetraction := by
  have hleft : Function.LeftInverse
      (Algebra.ofId ElevenResidue CuspQuotient)
      cuspQuotientRetraction := by
    intro x
    change
      ((Algebra.ofId ElevenResidue CuspQuotient).comp
        cuspQuotientRetraction) x = x
    rw [cuspQuotient_section_retraction]
    rfl
  exact hleft.injective

private theorem cuspPrime_le_cuspIdeal :
    ElevenCuspPrime ≤ cuspIdeal := by
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply cuspQuotientRetraction_injective
  change infinityCuspStructuralSection.fiberRetraction ElevenPrime x = 0
  exact hx

/-- The canonical fibre point selected by the represented infinity section
is exactly the closed point `(t,s-1)` in the actual special fibre. -/
private theorem cuspPrime_eq_cuspIdeal :
    ElevenCuspPrime = cuspIdeal :=
  le_antisymm cuspPrime_le_cuspIdeal cuspIdeal_le_cuspPrime

end MazurTorsion.OrderThirtyFive.InfinityChartAtEleven
