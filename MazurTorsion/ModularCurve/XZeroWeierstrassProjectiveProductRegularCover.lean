/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassInfinityPairNeighborhoodAdditionFormula
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductSecondInputOverlapCompatibility

/-!
# A regular-source cover of the projective Weierstrass pair charts

The secant triple needs no doubling replacement off the diagonal.  On either
mixed input chart, the infinity input has `Z = 0` only where the secant output
`Z` is already nonzero.  On the infinity-by-infinity chart, every prime lies
where both inputs have nonzero `Z`, where the regular slope denominator
`B∞` is nonzero, or where the secant output `Z` is nonzero.

These primewise identities isolate opens that can carry genuine addition
laws: the standard-by-standard source, the regular infinity neighborhood, and
the secant source.  The named downstream consumer
`projectiveInfinityPairStandardNeighborhoodAndSecantZOpens_cover` is the
topological input for replacing the nonvanishing-only doubling opens in the
eventual global addition atlas.  Constructing that scheme open cover and
gluing its morphisms remain downstream.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem projectivePairChartAdditionCoordinates_map_to_quotient
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (ij : Bool × Bool)
    (f : projectivePairChartCoordinateRing W ij →ₐ[K] A) :
    f ∘ projectivePairChartAdditionCoordinates W ij =
      (W.map (algebraMap K A)).toProjective.addXYZ
        (f ∘ projectivePairChartFirstUniversalPoint W ij)
        (f ∘ projectivePairChartSecondUniversalPoint W ij) := by
  have h := WeierstrassCurve.Projective.map_addXYZ
    (W' := projectivePairChartMappedCurve W ij)
    (f := f.toRingHom)
    (P := projectivePairChartFirstUniversalPoint W ij)
    (Q := projectivePairChartSecondUniversalPoint W ij)
  have hf : f.toRingHom.comp
      (algebraMap K (projectivePairChartCoordinateRing W ij)) =
        algebraMap K A := by
    ext a
    exact f.commutes a
  change ((W.map
      (algebraMap K (projectivePairChartCoordinateRing W ij))).map
        f.toRingHom).toProjective.addXYZ _ _ = _ at h
  rw [WeierstrassCurve.map_map, hf] at h
  exact h.symm

private theorem projectiveInfinityPairAdditionB12_map_eq_one
    {A : Type u} [CommRing A] (W : WeierstrassCurve K)
    (f : projectiveInfinityPairCoordinateRing W →+* A)
    (hX₁ : f (projectiveInfinityPairX₁ W) = 0)
    (hZ₁ : f (projectiveInfinityPairZ₁ W) = 0)
    (hZ₂ : f (projectiveInfinityPairZ₂ W) = 0) :
    f (projectiveInfinityPairAdditionB12 W) = 1 := by
  simp [projectiveInfinityPairAdditionB12, hX₁, hZ₁, hZ₂]

/-! ## The two mixed pair charts -/

/-- On the standard-by-infinity chart, the second input transition open and
the secant output-`Z` open already cover the whole chart. -/
theorem projectivePairStandardInfinityTransitionAndSecantZOpens_cover
    (W : WeierstrassCurve K) :
    PrimeSpectrum.basicOpen
        (projectivePairChartSecondUniversalPoint W (true, false) (2 : Fin 3)) ⊔
      PrimeSpectrum.basicOpen
        (projectivePairChartAdditionCoordinates W (true, false) (2 : Fin 3)) =
      ⊤ := by
  apply top_unique
  intro p _
  change projectivePairChartSecondUniversalPoint W (true, false)
      (2 : Fin 3) ∉ p.asIdeal ∨
    projectivePairChartAdditionCoordinates W (true, false)
      (2 : Fin 3) ∉ p.asIdeal
  by_contra hcover
  push Not at hcover
  rcases hcover with ⟨hZ₂, hAddZ⟩
  let R := projectivePairChartCoordinateRing W (true, false)
  let Q := R ⧸ p.asIdeal
  letI : CommRing Q := Ideal.Quotient.commRing p.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let q : R →+* Q := Ideal.Quotient.mk p.asIdeal
  let g : K →+* Q := q.comp (algebraMap K R)
  letI : Algebra K Q := g.toAlgebra
  let qAlg : R →ₐ[K] Q :=
    { __ := q
      commutes' := fun a ↦ rfl }
  let P₁ : Fin 3 → Q := q ∘
    projectivePairChartFirstUniversalPoint W (true, false)
  let P₂ : Fin 3 → Q := q ∘
    projectivePairChartSecondUniversalPoint W (true, false)
  have hP₂ : (W.map g).toProjective.Equation P₂ := by
    simpa [g, P₂, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartSecondUniversalPoint_equation W
        (true, false)).map q
  have hP₁Z : P₁ (2 : Fin 3) = 1 := by
    change q (projectivePairChartFirstUniversalPoint W (true, false)
      (coveringCoordinate true)) = 1
    rw [projectivePairChartFirstUniversalPoint_normalized, map_one]
  have hP₂Y : P₂ (1 : Fin 3) = 1 := by
    change q (projectivePairChartSecondUniversalPoint W (true, false)
      (coveringCoordinate false)) = 1
    rw [projectivePairChartSecondUniversalPoint_normalized, map_one]
  have hP₂Z : P₂ (2 : Fin 3) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hZ₂
  have hformula := (W.map g).toProjective.addXYZ_of_Z_eq_zero_right
    (P := P₁) (Q := P₂) hP₂ hP₂Z
  have hmap := projectivePairChartAdditionCoordinates_map_to_quotient
    W (true, false) qAlg
  have hmapCoordinate := congrFun hmap (2 : Fin 3)
  change q (projectivePairChartAdditionCoordinates W (true, false)
      (2 : Fin 3)) =
    (W.map g).toProjective.addXYZ P₁ P₂ (2 : Fin 3) at hmapCoordinate
  have hcoordinate := hmapCoordinate.trans
    (congrFun hformula (2 : Fin 3))
  have hzero : q
      (projectivePairChartAdditionCoordinates W (true, false)
        (2 : Fin 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hAddZ
  rw [Pi.smul_apply, hP₂Y, hP₁Z, one_pow, one_mul,
    smul_eq_mul, neg_one_mul] at hcoordinate
  exact (neg_ne_zero.mpr one_ne_zero) (hcoordinate.symm.trans hzero)

/-- On the infinity-by-standard chart, the first input transition open and
the secant output-`Z` open already cover the whole chart. -/
theorem projectivePairInfinityStandardTransitionAndSecantZOpens_cover
    (W : WeierstrassCurve K) :
    PrimeSpectrum.basicOpen
        (projectivePairChartFirstUniversalPoint W (false, true) (2 : Fin 3)) ⊔
      PrimeSpectrum.basicOpen
        (projectivePairChartAdditionCoordinates W (false, true) (2 : Fin 3)) =
      ⊤ := by
  apply top_unique
  intro p _
  change projectivePairChartFirstUniversalPoint W (false, true)
      (2 : Fin 3) ∉ p.asIdeal ∨
    projectivePairChartAdditionCoordinates W (false, true)
      (2 : Fin 3) ∉ p.asIdeal
  by_contra hcover
  push Not at hcover
  rcases hcover with ⟨hZ₁, hAddZ⟩
  let R := projectivePairChartCoordinateRing W (false, true)
  let Q := R ⧸ p.asIdeal
  letI : CommRing Q := Ideal.Quotient.commRing p.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let q : R →+* Q := Ideal.Quotient.mk p.asIdeal
  let g : K →+* Q := q.comp (algebraMap K R)
  letI : Algebra K Q := g.toAlgebra
  let qAlg : R →ₐ[K] Q :=
    { __ := q
      commutes' := fun a ↦ rfl }
  let P₁ : Fin 3 → Q := q ∘
    projectivePairChartFirstUniversalPoint W (false, true)
  let P₂ : Fin 3 → Q := q ∘
    projectivePairChartSecondUniversalPoint W (false, true)
  have hP₁ : (W.map g).toProjective.Equation P₁ := by
    simpa [g, P₁, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartFirstUniversalPoint_equation W
        (false, true)).map q
  have hP₁Y : P₁ (1 : Fin 3) = 1 := by
    change q (projectivePairChartFirstUniversalPoint W (false, true)
      (coveringCoordinate false)) = 1
    rw [projectivePairChartFirstUniversalPoint_normalized, map_one]
  have hP₁Z : P₁ (2 : Fin 3) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hZ₁
  have hP₂Z : P₂ (2 : Fin 3) = 1 := by
    change q (projectivePairChartSecondUniversalPoint W (false, true)
      (coveringCoordinate true)) = 1
    rw [projectivePairChartSecondUniversalPoint_normalized, map_one]
  have hformula := (W.map g).toProjective.addXYZ_of_Z_eq_zero_left
    (P := P₁) (Q := P₂) hP₁ hP₁Z
  have hmap := projectivePairChartAdditionCoordinates_map_to_quotient
    W (false, true) qAlg
  have hmapCoordinate := congrFun hmap (2 : Fin 3)
  change q (projectivePairChartAdditionCoordinates W (false, true)
      (2 : Fin 3)) =
    (W.map g).toProjective.addXYZ P₁ P₂ (2 : Fin 3) at hmapCoordinate
  have hcoordinate := hmapCoordinate.trans
    (congrFun hformula (2 : Fin 3))
  have hzero : q
      (projectivePairChartAdditionCoordinates W (false, true)
        (2 : Fin 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hAddZ
  rw [Pi.smul_apply, hP₁Y, hP₂Z, one_pow, one_mul, smul_eq_mul,
    mul_one]
    at hcoordinate
  exact one_ne_zero (hcoordinate.symm.trans hzero)

/-! ## The infinity-by-infinity pair chart -/

/-- On the infinity-by-infinity chart, the locus where both inputs enter the
standard chart, the regular slope neighborhood `D(B∞)`, and the secant
output-`Z` open jointly cover the whole chart. -/
theorem projectiveInfinityPairStandardNeighborhoodAndSecantZOpens_cover
    (W : WeierstrassCurve K) :
    PrimeSpectrum.basicOpen
        (projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W) ⊔
      (PrimeSpectrum.basicOpen (projectiveInfinityPairAdditionB12 W) ⊔
        PrimeSpectrum.basicOpen
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3))) = ⊤ := by
  apply top_unique
  intro p _
  change projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W ∉
      p.asIdeal ∨
    projectiveInfinityPairAdditionB12 W ∉ p.asIdeal ∨
    projectivePairChartAdditionCoordinates W (false, false)
      (2 : Fin 3) ∉ p.asIdeal
  by_contra hcover
  push Not at hcover
  rcases hcover with ⟨hZZ, hB, hAddZ⟩
  let R := projectiveInfinityPairCoordinateRing W
  let Q := R ⧸ p.asIdeal
  letI : CommRing Q := Ideal.Quotient.commRing p.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let q : R →+* Q := Ideal.Quotient.mk p.asIdeal
  let g : K →+* Q := q.comp (algebraMap K R)
  letI : Algebra K Q := g.toAlgebra
  let qAlg : R →ₐ[K] Q :=
    { __ := q
      commutes' := fun a ↦ rfl }
  let P₁ : Fin 3 → Q := q ∘
    projectivePairChartFirstUniversalPoint W (false, false)
  let P₂ : Fin 3 → Q := q ∘
    projectivePairChartSecondUniversalPoint W (false, false)
  have hP₁ : (W.map g).toProjective.Equation P₁ := by
    simpa [g, P₁, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartFirstUniversalPoint_equation W
        (false, false)).map q
  have hP₂ : (W.map g).toProjective.Equation P₂ := by
    simpa [g, P₂, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartSecondUniversalPoint_equation W
        (false, false)).map q
  have hP₁Y : P₁ (1 : Fin 3) = 1 := by
    change q (projectivePairChartFirstUniversalPoint W (false, false)
      (coveringCoordinate false)) = 1
    rw [projectivePairChartFirstUniversalPoint_normalized, map_one]
  have hP₂Y : P₂ (1 : Fin 3) = 1 := by
    change q (projectivePairChartSecondUniversalPoint W (false, false)
      (coveringCoordinate false)) = 1
    rw [projectivePairChartSecondUniversalPoint_normalized, map_one]
  have hproduct : P₁ (2 : Fin 3) * P₂ (2 : Fin 3) = 0 := by
    change q (projectiveInfinityPairZ₁ W *
      projectiveInfinityPairZ₂ W) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hZZ
  have hmap := projectivePairChartAdditionCoordinates_map_to_quotient
    W (false, false) qAlg
  have hmapCoordinate := congrFun hmap (2 : Fin 3)
  change q (projectivePairChartAdditionCoordinates W (false, false)
      (2 : Fin 3)) =
    (W.map g).toProjective.addXYZ P₁ P₂ (2 : Fin 3) at hmapCoordinate
  have hAddZero : q
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hAddZ
  rcases mul_eq_zero.mp hproduct with hP₁Z | hP₂Z
  · by_cases hP₂Z' : P₂ (2 : Fin 3) = 0
    · have hP₁X : P₁ (0 : Fin 3) = 0 :=
        (W.map g).toProjective.X_eq_zero_of_Z_eq_zero hP₁ hP₁Z
      have hqX₁ := hP₁X
      have hqZ₁ := hP₁Z
      have hqZ₂ := hP₂Z'
      change q (projectiveInfinityPairX₁ W) = 0 at hqX₁
      change q (projectiveInfinityPairZ₁ W) = 0 at hqZ₁
      change q (projectiveInfinityPairZ₂ W) = 0 at hqZ₂
      have hBvalue : q (projectiveInfinityPairAdditionB12 W) = 1 :=
        projectiveInfinityPairAdditionB12_map_eq_one W q hqX₁ hqZ₁ hqZ₂
      have hBzero : q (projectiveInfinityPairAdditionB12 W) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hB
      exact one_ne_zero (hBvalue.symm.trans hBzero)
    · have hformula := (W.map g).toProjective.addXYZ_of_Z_eq_zero_left
        (P := P₁) (Q := P₂) hP₁ hP₁Z
      have hcoordinate := hmapCoordinate.trans
        (congrFun hformula (2 : Fin 3))
      rw [Pi.smul_apply, hP₁Y, one_pow, one_mul, smul_eq_mul]
        at hcoordinate
      exact hP₂Z' (mul_self_eq_zero.mp
        (hcoordinate.symm.trans hAddZero))
  · by_cases hP₁Z' : P₁ (2 : Fin 3) = 0
    · have hP₁X : P₁ (0 : Fin 3) = 0 :=
        (W.map g).toProjective.X_eq_zero_of_Z_eq_zero hP₁ hP₁Z'
      have hqX₁ := hP₁X
      have hqZ₁ := hP₁Z'
      have hqZ₂ := hP₂Z
      change q (projectiveInfinityPairX₁ W) = 0 at hqX₁
      change q (projectiveInfinityPairZ₁ W) = 0 at hqZ₁
      change q (projectiveInfinityPairZ₂ W) = 0 at hqZ₂
      have hBvalue : q (projectiveInfinityPairAdditionB12 W) = 1 :=
        projectiveInfinityPairAdditionB12_map_eq_one W q hqX₁ hqZ₁ hqZ₂
      have hBzero : q (projectiveInfinityPairAdditionB12 W) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hB
      exact one_ne_zero (hBvalue.symm.trans hBzero)
    · have hformula := (W.map g).toProjective.addXYZ_of_Z_eq_zero_right
        (P := P₁) (Q := P₂) hP₂ hP₂Z
      have hcoordinate := hmapCoordinate.trans
        (congrFun hformula (2 : Fin 3))
      rw [Pi.smul_apply, hP₂Y, one_pow, one_mul, smul_eq_mul,
        neg_mul] at hcoordinate
      have hsquare : P₁ (2 : Fin 3) ^ 2 = 0 := by
        simpa only [pow_two, neg_eq_zero] using hcoordinate.symm.trans hAddZero
      exact hP₁Z' (sq_eq_zero_iff.mp hsquare)

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
