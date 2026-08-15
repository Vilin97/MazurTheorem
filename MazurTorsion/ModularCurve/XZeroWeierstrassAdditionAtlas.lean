/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassInfinityCompatibility

/-!
# The global affine-pair atlas for Weierstrass addition

The two affine-output charts `D(x₁-x₂)` and `D(B₁₂)` do not contain inverse
pairs.  Their two denominator-cleared infinity extensions cover the missing
locus.  The coverage proof below is the honest geometric step: if all four
chart coordinates vanished at a prime, the first universal point would be a
singular point of the elliptic Weierstrass cubic.

This file assumes ellipticity only where nonsingularity is actually used.  It
does not assume a group object or a pointwise addition law.
-/

noncomputable section

open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The ordinary secant chart, the `D(B₁₂)` product-neighbourhood chart, and
their two infinity extensions cover the entire affine-pair presentation. -/
theorem affinePairAdditionCharts_cover
    (W : WeierstrassCurve K) [W.IsElliptic] :
    PrimeSpectrum.basicOpen (additionB12 W) ⊔
        (PrimeSpectrum.basicOpen (secantDenominator W) ⊔
          (PrimeSpectrum.basicOpen (antidiagonalAddYNumerator W) ⊔
            PrimeSpectrum.basicOpen (verticalAddYNumerator W))) = ⊤ := by
  apply top_unique
  intro p _
  change additionB12 W ∉ p.asIdeal ∨
    secantDenominator W ∉ p.asIdeal ∨
    antidiagonalAddYNumerator W ∉ p.asIdeal ∨
    verticalAddYNumerator W ∉ p.asIdeal
  by_contra hcover
  push Not at hcover
  rcases hcover with ⟨hB, hD, hantiY, hvertY⟩
  have hantiRight :
      additionB12 W *
          (-2 * secantPairCoefficientHom W W.a₁ * additionA12 W ^ 2 +
            additionA12 W *
              ((secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                  secantPairX₂ W) -
                secantPairCoefficientHom W W.a₁ ^ 2 + secantPairX₁ W) *
              additionB12 W +
            (secantPairCoefficientHom W W.a₁ *
                (secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                  secantPairX₂ W) -
              (secantPairY₁ W + secantPairCoefficientHom W W.a₃)) *
              additionB12 W ^ 2) ∈ p.asIdeal :=
    p.asIdeal.mul_mem_right _ hB
  have hantiSum :
      antidiagonalAddYNumerator W + additionA12 W ^ 3 ∈ p.asIdeal := by
    rw [antidiagonalAddYNumerator_add_A12_cube]
    exact hantiRight
  have hA3 : additionA12 W ^ 3 ∈ p.asIdeal := by
    simpa using p.asIdeal.sub_mem hantiSum hantiY
  have hA : additionA12 W ∈ p.asIdeal :=
    (show p.asIdeal.IsPrime from inferInstance).mem_of_pow_mem 3 hA3
  have hvertRight :
      verticalAdditionB W *
          (-2 * secantPairCoefficientHom W W.a₁ * verticalAdditionA W ^ 2 +
            verticalAdditionA W *
              ((secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                  secantPairX₂ W) -
                secantPairCoefficientHom W W.a₁ ^ 2 + secantPairX₁ W) *
              verticalAdditionB W +
            (secantPairCoefficientHom W W.a₁ *
                (secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                  secantPairX₂ W) -
              (secantPairY₁ W + secantPairCoefficientHom W W.a₃)) *
              verticalAdditionB W ^ 2) ∈ p.asIdeal := by
    apply p.asIdeal.mul_mem_right
    simpa [verticalAdditionB, secantDenominator] using hD
  have hvertSum :
      verticalAddYNumerator W + verticalAdditionA W ^ 3 ∈ p.asIdeal := by
    rw [verticalAddYNumerator_add_A_cube]
    exact hvertRight
  have hC3 : verticalAdditionA W ^ 3 ∈ p.asIdeal := by
    simpa using p.asIdeal.sub_mem hvertSum hvertY
  have hC : verticalAdditionA W ∈ p.asIdeal :=
    (show p.asIdeal.IsPrime from inferInstance).mem_of_pow_mem 3 hC3
  let S := secantPairCoordinateRing W
  let Q := S ⧸ p.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let L := FractionRing Q
  let q₀ : S →+* Q := Ideal.Quotient.mk p.asIdeal
  let q : S →+* L := (algebraMap Q L).comp q₀
  let g : K →+* L := q.comp (secantPairCoefficientHom W)
  let x₁ : L := q (secantPairX₁ W)
  let y₁ : L := q (secantPairY₁ W)
  let x₂ : L := q (secantPairX₂ W)
  let y₂ : L := q (secantPairY₂ W)
  have hequation : (W.map g).toAffine.Equation x₁ y₁ := by
    simpa [g, x₁, y₁, WeierstrassCurve.map_map] using
      (secantPair_equation_left W).map q
  have hns := ((W.map g).toAffine.equation_iff_nonsingular).mp hequation
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  have hqB : q (additionB12 W) = 0 := by
    change algebraMap Q L (q₀ (additionB12 W)) = 0
    rw [show q₀ (additionB12 W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hB, map_zero]
  have hqD : q (secantDenominator W) = 0 := by
    change algebraMap Q L (q₀ (secantDenominator W)) = 0
    rw [show q₀ (secantDenominator W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hD, map_zero]
  have hqA : q (additionA12 W) = 0 := by
    change algebraMap Q L (q₀ (additionA12 W)) = 0
    rw [show q₀ (additionA12 W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hA, map_zero]
  have hqC : q (verticalAdditionA W) = 0 := by
    change algebraMap Q L (q₀ (verticalAdditionA W)) = 0
    rw [show q₀ (verticalAdditionA W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hC, map_zero]
  have hx₂ : x₂ = x₁ := by
    dsimp only [x₁, x₂]
    exact (sub_eq_zero.mp (by simpa [secantDenominator] using hqD)).symm
  have hy₂ : y₂ = y₁ := by
    dsimp only [y₁, y₂]
    exact (sub_eq_zero.mp (by simpa [verticalAdditionA] using hqC)).symm
  have hderivativeX :
      (W.map g).a₁ * y₁ -
          (3 * x₁ ^ 2 + 2 * (W.map g).a₂ * x₁ + (W.map g).a₄) = 0 := by
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄]
    dsimp only [g, x₁, y₁, x₂, y₂] at hx₂ hy₂ ⊢
    simp only [RingHom.comp_apply]
    have h := hqA
    simp only [additionA12, map_sub, map_add, map_mul, map_pow] at h
    rw [hx₂, hy₂] at h
    linear_combination -h
  have hderivativeY :
      2 * y₁ + (W.map g).a₁ * x₁ + (W.map g).a₃ = 0 := by
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    dsimp only [g, x₁, y₁, x₂, y₂] at hy₂ ⊢
    simp only [RingHom.comp_apply]
    have h := hqB
    simp only [additionB12, map_add, map_mul] at h
    rw [hy₂] at h
    linear_combination h
  rcases hns.2 with hx | hy
  · exact hx hderivativeX
  · exact hy hderivativeY

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
