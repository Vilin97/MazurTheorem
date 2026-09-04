/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassAntidiagonalAdditionMorphism
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductAdditionCoordinates
import Mathlib.RingTheory.Localization.Ideal

/-!
# The first input overlap of projective Weierstrass pair charts

The standard `Z != 0` and infinity `Y != 0` presentations of the projective
Weierstrass cubic meet on `D(YZ)`.  This file descends that ambient overlap
through the cubic equation, proves that both restriction maps are principal
open immersions, and identifies their composites with the concrete cubic.

The design boundary then tensors this exact cubic overlap with an unchanged
second input chart.  Its named downstream consumer is
`projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition`:
the raw homogeneous addition triple changes by the square of the first-chart
transition scalar.  This supplies one source-overlap edge for later gluing; it
does not choose an invertible output coordinate or construct the global
addition morphism.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

noncomputable instance projectiveYZOverlapAlgebra :
    Algebra K (projectiveYZOverlapRing K) :=
  ((standardChartToProjectiveYZOverlapRing (K := K)).comp
    (coordinateChartConstantHom (K := K) 2)).toAlgebra

/-- The common ambient overlap is the localization of the standard ambient
chart obtained by inverting `Y / Z`. -/
noncomputable instance standardChartProjectiveYZOverlapAlgebra :
    Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2))
      (projectiveYZOverlapRing K) :=
  standardChartToProjectiveYZOverlapRing.toAlgebra

noncomputable instance projectiveYZOverlap_isLocalization_standardChart :
    IsLocalization.Away (coordinateChartRatio (K := K) 2 1)
      (projectiveYZOverlapRing K) := by
  rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (𝒜 := homogeneousPieces K)
    (f := MvPolynomial.X 2) (g := MvPolynomial.X 1)
    (MvPolynomial.isHomogeneous_X K 2)
    (MvPolynomial.isHomogeneous_X K 1) rfl (by omega)

/-- The common ambient overlap as an algebra over the infinity chart. -/
noncomputable instance infinityChartProjectiveYZOverlapAlgebra :
    Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 1))
      (projectiveYZOverlapRing K) :=
  infinityChartToProjectiveYZOverlapRing.toAlgebra

noncomputable instance projectiveYZOverlap_isLocalization_infinityChart :
    IsLocalization.Away (coordinateChartRatio (K := K) 1 2)
      (projectiveYZOverlapRing K) := by
  rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (𝒜 := homogeneousPieces K)
    (f := MvPolynomial.X 1) (g := MvPolynomial.X 2)
    (MvPolynomial.isHomogeneous_X K 1)
    (MvPolynomial.isHomogeneous_X K 2)
    (show MvPolynomial.X 2 * MvPolynomial.X 1 =
      MvPolynomial.X 1 * MvPolynomial.X 2 by ring)
    (by omega)

/-- The cubic equation inside the common ambient projective overlap. -/
def coveringChartOverlapIdeal (W : WeierstrassCurve K) :
    Ideal (projectiveYZOverlapRing K) :=
  Ideal.map standardChartToProjectiveYZOverlapRing
    (coveringChartIdeal W true)

/-- The coordinate ring of the cubic overlap `D(YZ)`. -/
abbrev coveringChartOverlapCoordinateRing (W : WeierstrassCurve K) :=
  projectiveYZOverlapRing K ⧸ coveringChartOverlapIdeal W

theorem standardChartEquation_explicit (W : WeierstrassCurve K) :
    standardChartEquation W =
      coordinateChartRatio 2 1 ^ 2 +
        (coordinateChartConstantHom 2 W.a₁ * coordinateChartRatio 2 0 +
          coordinateChartConstantHom 2 W.a₃) * coordinateChartRatio 2 1 -
        (coordinateChartRatio 2 0 ^ 3 +
          coordinateChartConstantHom 2 W.a₂ * coordinateChartRatio 2 0 ^ 2 +
          coordinateChartConstantHom 2 W.a₄ * coordinateChartRatio 2 0 +
          coordinateChartConstantHom 2 W.a₆) := by
  rw [standardChartEquation_eq_affineToStandardChart]
  simp [WeierstrassCurve.Affine.polynomial]

theorem projectiveYZOverlap_equation_transition
    (W : WeierstrassCurve K) :
    infinityChartToProjectiveYZOverlapRing
        (coveringChartEquation W false) =
      infinityChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 1 2) ^ 3 *
        standardChartToProjectiveYZOverlapRing
          (coveringChartEquation W true) := by
  change infinityChartToProjectiveYZOverlapRing
        (infinityLocalizedEquation W) =
      infinityChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 1 2) ^ 3 *
        standardChartToProjectiveYZOverlapRing
          (standardChartEquation W)
  rw [infinityLocalizedEquation_explicit,
    standardChartEquation_explicit]
  simp only [map_add, map_sub, map_mul, map_pow]
  have hX := projectiveYZOverlap_transition_outerX (K := K)
  have hZ := projectiveYZOverlap_transition_innerX (K := K)
  have ha₁ := projectiveYZOverlap_transition_constant (K := K) W.a₁
  have ha₂ := projectiveYZOverlap_transition_constant (K := K) W.a₂
  have ha₃ := projectiveYZOverlap_transition_constant (K := K) W.a₃
  have ha₄ := projectiveYZOverlap_transition_constant (K := K) W.a₄
  have ha₆ := projectiveYZOverlap_transition_constant (K := K) W.a₆
  rw [← ha₁, ← ha₂, ← ha₃, ← ha₄, ← ha₆]
  let s := infinityChartToProjectiveYZOverlapRing
    (coordinateChartRatio (K := K) 1 2)
  let t := standardChartToProjectiveYZOverlapRing
    (coordinateChartRatio (K := K) 2 1)
  let p := infinityChartToProjectiveYZOverlapRing
    (coordinateChartRatio (K := K) 1 0)
  let q := standardChartToProjectiveYZOverlapRing
    (coordinateChartRatio (K := K) 2 0)
  let a₁ := standardChartToProjectiveYZOverlapRing
    (coordinateChartConstantHom (K := K) 2 W.a₁)
  let a₂ := standardChartToProjectiveYZOverlapRing
    (coordinateChartConstantHom (K := K) 2 W.a₂)
  let a₃ := standardChartToProjectiveYZOverlapRing
    (coordinateChartConstantHom (K := K) 2 W.a₃)
  let a₄ := standardChartToProjectiveYZOverlapRing
    (coordinateChartConstantHom (K := K) 2 W.a₄)
  let a₆ := standardChartToProjectiveYZOverlapRing
    (coordinateChartConstantHom (K := K) 2 W.a₆)
  change p * t = q at hX
  change s * t = 1 at hZ
  change
    s + a₁ * p * s + a₃ * s ^ 2 -
        (p ^ 3 + a₂ * p ^ 2 * s + a₄ * p * s ^ 2 + a₆ * s ^ 3) =
      s ^ 3 *
        (t ^ 2 + (a₁ * q + a₃) * t -
          (q ^ 3 + a₂ * q ^ 2 + a₄ * q + a₆))
  have ht : IsUnit t :=
    isUnit_iff_exists_inv.mpr ⟨s, by simpa [mul_comm] using hZ⟩
  apply (ht.pow 3).mul_right_cancel
  calc
    (s + a₁ * p * s + a₃ * s ^ 2 -
          (p ^ 3 + a₂ * p ^ 2 * s + a₄ * p * s ^ 2 + a₆ * s ^ 3)) *
        t ^ 3 =
      (s * t) * t ^ 2 + a₁ * (p * t) * (s * t) * t +
          a₃ * (s * t) ^ 2 * t -
        ((p * t) ^ 3 + a₂ * (p * t) ^ 2 * (s * t) +
          a₄ * (p * t) * (s * t) ^ 2 + a₆ * (s * t) ^ 3) := by
            ring
    _ = t ^ 2 + (a₁ * q + a₃) * t -
        (q ^ 3 + a₂ * q ^ 2 + a₄ * q + a₆) := by
          rw [hX, hZ]
          ring
    _ = (s ^ 3 *
          (t ^ 2 + (a₁ * q + a₃) * t -
            (q ^ 3 + a₂ * q ^ 2 + a₄ * q + a₆))) * t ^ 3 := by
          calc
            _ = (s * t) ^ 3 *
                (t ^ 2 + (a₁ * q + a₃) * t -
                  (q ^ 3 + a₂ * q ^ 2 + a₄ * q + a₆)) := by
                    rw [hZ, one_pow, one_mul]
            _ = _ := by ring

/-- The standard and infinity equations cut out the same cubic inside
`D(YZ)`. -/
theorem coveringChartOverlapIdeal_eq_map_infinityChartIdeal
    (W : WeierstrassCurve K) :
    coveringChartOverlapIdeal W =
      Ideal.map infinityChartToProjectiveYZOverlapRing
        (coveringChartIdeal W false) := by
  have hZ := projectiveYZOverlap_transition_innerX (K := K)
  have hs : IsUnit
      (infinityChartToProjectiveYZOverlapRing
        (coordinateChartRatio (K := K) 1 2)) :=
    isUnit_iff_exists_inv.mpr
      ⟨standardChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 2 1), hZ⟩
  have heq := projectiveYZOverlap_equation_transition W
  change infinityChartToProjectiveYZOverlapRing
      (infinityLocalizedEquation W) =
    infinityChartToProjectiveYZOverlapRing
        (coordinateChartRatio (K := K) 1 2) ^ 3 *
      standardChartToProjectiveYZOverlapRing
        (standardChartEquation W) at heq
  rw [coveringChartOverlapIdeal]
  change Ideal.map standardChartToProjectiveYZOverlapRing
      (Ideal.span {standardChartEquation W}) =
    Ideal.map infinityChartToProjectiveYZOverlapRing
      (Ideal.span {infinityLocalizedEquation W})
  rw [Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton, heq]
  exact (Ideal.span_singleton_mul_left_unit (hs.pow 3) _).symm

/-- Restriction from the standard cubic chart to its `Y != 0` overlap. -/
noncomputable def standardChartToCoveringChartOverlapRing
    (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W true →+*
      coveringChartOverlapCoordinateRing W :=
  Ideal.quotientMap (coveringChartOverlapIdeal W)
    standardChartToProjectiveYZOverlapRing <| by
      exact Ideal.le_comap_map

/-- The algebra structure induced by the standard restriction map. -/
noncomputable instance coveringChartOverlapAlgebraStandardChart
    (W : WeierstrassCurve K) :
    Algebra (coveringChartCoordinateRing W true)
      (coveringChartOverlapCoordinateRing W) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (A := projectiveYZOverlapRing K)
    (R := HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 2))
    (p := standardChartIdeal W)
    (P := coveringChartOverlapIdeal W)
    Ideal.le_comap_map

/-- Restriction from the infinity cubic chart to its `Z != 0` overlap. -/
noncomputable def infinityChartToCoveringChartOverlapRing
    (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W false →+*
      coveringChartOverlapCoordinateRing W :=
  Ideal.Quotient.lift (coveringChartIdeal W false)
    ((Ideal.Quotient.mk (coveringChartOverlapIdeal W)).comp
      infinityChartToProjectiveYZOverlapRing) <| by
        intro x hx
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        change x ∈ Ideal.span {infinityLocalizedEquation W} at hx
        have hle :
            Ideal.map infinityChartToProjectiveYZOverlapRing
                (Ideal.span {infinityLocalizedEquation W}) ≤
              coveringChartOverlapIdeal W := by
          rw [Ideal.map_span]
          apply Ideal.span_le.2
          rw [Set.image_singleton, Set.singleton_subset_iff]
          have heq := projectiveYZOverlap_equation_transition W
          change infinityChartToProjectiveYZOverlapRing
              (infinityLocalizedEquation W) = _ at heq
          rw [heq]
          apply (coveringChartOverlapIdeal W).mul_mem_left
          change standardChartToProjectiveYZOverlapRing
              (standardChartEquation W) ∈
            Ideal.map standardChartToProjectiveYZOverlapRing
              (Ideal.span {standardChartEquation W})
          exact Ideal.mem_map_of_mem _
            (Ideal.subset_span (Set.mem_singleton _))
        exact hle (Ideal.mem_map_of_mem infinityChartToProjectiveYZOverlapRing hx)

/-- The algebra structure induced by the infinity restriction map. -/
noncomputable instance coveringChartOverlapAlgebraInfinityChart
    (W : WeierstrassCurve K) :
    Algebra (coveringChartCoordinateRing W false)
      (coveringChartOverlapCoordinateRing W) :=
  (infinityChartToCoveringChartOverlapRing W).toAlgebra

@[simp]
theorem standardChartToCoveringChartOverlapRing_mk
    (W : WeierstrassCurve K)
    (x : HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 2)) :
    standardChartToCoveringChartOverlapRing W
        (Ideal.Quotient.mk (coveringChartIdeal W true) x) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (standardChartToProjectiveYZOverlapRing x) := by
  exact Ideal.quotientMap_mk

theorem coveringChartOverlap_isLocalization_standardChart
    (W : WeierstrassCurve K) :
    letI := (standardChartToCoveringChartOverlapRing W).toAlgebra
    IsLocalization.Away
      (Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (K := K) 2 1))
      (coveringChartOverlapCoordinateRing W) := by
  letI : Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
          (MvPolynomial.X 2) ⧸ standardChartIdeal W)
      (projectiveYZOverlapRing K ⧸ coveringChartOverlapIdeal W) :=
    (standardChartToCoveringChartOverlapRing W).toAlgebra
  letI : Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2))
      (projectiveYZOverlapRing K) :=
    (standardChartToProjectiveYZOverlapRing (K := K)).toAlgebra
  have : IsLocalization.Away
      (coordinateChartRatio (K := K) 2 1)
      (projectiveYZOverlapRing K) :=
    projectiveYZOverlap_isLocalization_standardChart (K := K)
  change IsLocalization
    (Submonoid.powers
      (Ideal.Quotient.mk (standardChartIdeal W)
        (coordinateChartRatio (K := K) 2 1)))
    (projectiveYZOverlapRing K ⧸ coveringChartOverlapIdeal W)
  rw [← Submonoid.map_powers]
  refine IsLocalization.of_surjective
    (Submonoid.powers (coordinateChartRatio (K := K) 2 1))
    (projectiveYZOverlapRing K)
    (Ideal.Quotient.mk (standardChartIdeal W))
    Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (coveringChartOverlapIdeal W))
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra]
    rfl
  · simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra]
    change Ideal.map standardChartToProjectiveYZOverlapRing
        (standardChartIdeal W) ≤
      Ideal.map standardChartToProjectiveYZOverlapRing
        (standardChartIdeal W)
    exact le_rfl

/-- The standard restriction is the localization algebra map. -/
theorem standardChartToCoveringChartOverlapRing_eq_algebraMap
    (W : WeierstrassCurve K) :
    standardChartToCoveringChartOverlapRing W =
      algebraMap (coveringChartCoordinateRing W true)
        (coveringChartOverlapCoordinateRing W) := by
  rfl

/-- The affine scheme of the cubic chart overlap. -/
abbrev coveringChartOverlapScheme (W : WeierstrassCurve K) : Scheme.{u} :=
  Spec (.of (coveringChartOverlapCoordinateRing W))

/-- The cubic overlap as the principal open `Y / Z != 0` in the standard
chart. -/
noncomputable def coveringChartOverlapToStandardChart
    (W : WeierstrassCurve K) :
    coveringChartOverlapScheme W ⟶ coveringChartScheme W true :=
  Spec.map (CommRingCat.ofHom
    (standardChartToCoveringChartOverlapRing W))

instance coveringChartOverlapToStandardChart_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (coveringChartOverlapToStandardChart W) := by
  letI := (standardChartToCoveringChartOverlapRing W).toAlgebra
  have := coveringChartOverlap_isLocalization_standardChart W
  dsimp only [coveringChartOverlapToStandardChart]
  exact IsOpenImmersion.of_isLocalization
    (Ideal.Quotient.mk (coveringChartIdeal W true)
      (coordinateChartRatio (K := K) 2 1))

@[simp]
theorem infinityChartToCoveringChartOverlapRing_mk
    (W : WeierstrassCurve K)
    (x : HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 1)) :
    infinityChartToCoveringChartOverlapRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false) x) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (infinityChartToProjectiveYZOverlapRing x) := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem coveringChartOverlap_isLocalization_infinityChart
    (W : WeierstrassCurve K) :
    letI := (infinityChartToCoveringChartOverlapRing W).toAlgebra
    IsLocalization.Away
      (Ideal.Quotient.mk (coveringChartIdeal W false)
        (coordinateChartRatio (K := K) 1 2))
      (coveringChartOverlapCoordinateRing W) := by
  letI : Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
          (MvPolynomial.X 1) ⧸ infinityChartIdeal W)
      (projectiveYZOverlapRing K ⧸ coveringChartOverlapIdeal W) :=
    (infinityChartToCoveringChartOverlapRing W).toAlgebra
  letI : Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 1))
      (projectiveYZOverlapRing K) :=
    (infinityChartToProjectiveYZOverlapRing (K := K)).toAlgebra
  have : IsLocalization.Away
      (coordinateChartRatio (K := K) 1 2)
      (projectiveYZOverlapRing K) :=
    projectiveYZOverlap_isLocalization_infinityChart (K := K)
  change IsLocalization
    (Submonoid.powers
      (Ideal.Quotient.mk (infinityChartIdeal W)
        (coordinateChartRatio (K := K) 1 2)))
    (projectiveYZOverlapRing K ⧸ coveringChartOverlapIdeal W)
  rw [← Submonoid.map_powers]
  refine IsLocalization.of_surjective
    (Submonoid.powers (coordinateChartRatio (K := K) 1 2))
    (projectiveYZOverlapRing K)
    (Ideal.Quotient.mk (infinityChartIdeal W))
    Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (coveringChartOverlapIdeal W))
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra]
    rfl
  · simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra]
    exact (coveringChartOverlapIdeal_eq_map_infinityChartIdeal W).le

/-- The standard restriction respects the common coefficient field. -/
noncomputable def standardChartToCoveringChartOverlapAlgHom
    (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W true →ₐ[K]
      coveringChartOverlapCoordinateRing W where
  __ := standardChartToCoveringChartOverlapRing W
  commutes' a := by rfl

/-- The infinity restriction respects the common coefficient field. -/
noncomputable def infinityChartToCoveringChartOverlapAlgHom
    (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W false →ₐ[K]
      coveringChartOverlapCoordinateRing W where
  __ := infinityChartToCoveringChartOverlapRing W
  commutes' a := by
    change Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (infinityChartToProjectiveYZOverlapRing
          (coordinateChartConstantHom 1 a)) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (standardChartToProjectiveYZOverlapRing
          (coordinateChartConstantHom 2 a))
    rw [projectiveYZOverlap_transition_constant]

/-- The common cubic overlap mapped to the infinity chart. -/
noncomputable def coveringChartOverlapToInfinityChart
    (W : WeierstrassCurve K) :
    coveringChartOverlapScheme W ⟶ coveringChartScheme W false :=
  Spec.map (CommRingCat.ofHom
    (infinityChartToCoveringChartOverlapRing W))

instance coveringChartOverlapToInfinityChart_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (coveringChartOverlapToInfinityChart W) := by
  letI := (infinityChartToCoveringChartOverlapRing W).toAlgebra
  have := coveringChartOverlap_isLocalization_infinityChart W
  dsimp only [coveringChartOverlapToInfinityChart]
  exact IsOpenImmersion.of_isLocalization
    (Ideal.Quotient.mk (coveringChartIdeal W false)
      (coordinateChartRatio (K := K) 1 2))

private theorem coveringChartOverlapToStandardChart_comp_quotientInclusion
    (W : WeierstrassCurve K) :
    coveringChartOverlapToStandardChart W ≫
        coveringChartQuotientInclusion W true =
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (coveringChartOverlapIdeal W)).comp
          standardChartToProjectiveYZOverlapRing)) := by
  rw [coveringChartOverlapToStandardChart,
    coveringChartQuotientInclusion, ← Spec.map_comp]
  congr 1

private theorem coveringChartOverlapToInfinityChart_comp_quotientInclusion
    (W : WeierstrassCurve K) :
    coveringChartOverlapToInfinityChart W ≫
        coveringChartQuotientInclusion W false =
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (coveringChartOverlapIdeal W)).comp
          infinityChartToProjectiveYZOverlapRing)) := by
  rw [coveringChartOverlapToInfinityChart,
    coveringChartQuotientInclusion, ← Spec.map_comp]
  congr 1

/-- The two quotient-chart restrictions of the cubic overlap define the same
ambient projective-plane morphism. -/
theorem coveringChartOverlap_ambient_maps_eq
    (W : WeierstrassCurve K) :
    coveringChartOverlapToStandardChart W ≫
        coveringChartAmbientMap W true =
      coveringChartOverlapToInfinityChart W ≫
        coveringChartAmbientMap W false := by
  let q : projectiveYZOverlapRing K →+*
      coveringChartOverlapCoordinateRing W :=
    Ideal.Quotient.mk (coveringChartOverlapIdeal W)
  let standardMap :
      HomogeneousLocalization.Away (homogeneousPieces K)
          (MvPolynomial.X 2) →+*
        coveringChartOverlapCoordinateRing W :=
    q.comp standardChartToProjectiveYZOverlapRing
  let infinityMap :
      HomogeneousLocalization.Away (homogeneousPieces K)
          (MvPolynomial.X 1) →+*
        coveringChartOverlapCoordinateRing W :=
    q.comp infinityChartToProjectiveYZOverlapRing
  have hconstant : ∀ a : K,
      standardMap (coordinateChartConstantHom (K := K) 2 a) =
        infinityMap (coordinateChartConstantHom (K := K) 1 a) := by
    intro a
    change q (standardChartToProjectiveYZOverlapRing
        (coordinateChartConstantHom (K := K) 2 a)) =
      q (infinityChartToProjectiveYZOverlapRing
        (coordinateChartConstantHom (K := K) 1 a))
    rw [projectiveYZOverlap_transition_constant]
  have hinnerAmbient := projectiveYZOverlap_transition_innerX (K := K)
  have hstandardInnerUnit :
      IsUnit (standardMap
        (coordinateChartRatio (K := K) 2 1)) := by
    have ht : IsUnit (standardChartToProjectiveYZOverlapRing
        (coordinateChartRatio (K := K) 2 1)) :=
      isUnit_iff_exists_inv.mpr ⟨infinityChartToProjectiveYZOverlapRing
        (coordinateChartRatio (K := K) 1 2), by
          simpa [mul_comm] using hinnerAmbient⟩
    exact ht.map q
  have houter := congrArg q
    (projectiveYZOverlap_transition_outerX (K := K))
  have hinner := congrArg q hinnerAmbient
  have hambient := projectiveYZOverlap_ambient_maps_eq
    (standardMap := standardMap) (infinityMap := infinityMap)
    hconstant hstandardInnerUnit
    (by simpa only [standardMap, infinityMap, RingHom.comp_apply,
      map_mul] using houter)
    (by simpa only [standardMap, infinityMap, RingHom.comp_apply,
      map_mul, map_one] using hinner)
  rw [coveringChartAmbientMap, coveringChartAmbientMap,
    ← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc,
    coveringChartOverlapToStandardChart_comp_quotientInclusion,
    coveringChartOverlapToInfinityChart_comp_quotientInclusion]
  exact hambient

/-- The standard and infinity restrictions are the same morphism into the
concrete projective cubic. -/
theorem coveringChartOverlap_maps_eq
    (W : WeierstrassCurve K) :
    coveringChartOverlapToStandardChart W ≫ coveringChartMap W true =
      coveringChartOverlapToInfinityChart W ≫ coveringChartMap W false := by
  apply (cancel_mono (inclusion W)).1
  simpa only [CategoryTheory.Category.assoc,
    coveringChartMap_comp_inclusion] using
      coveringChartOverlap_ambient_maps_eq W

/-- The standard `Y / Z` coordinate on the cubic overlap. -/
noncomputable def coveringChartOverlapScale (W : WeierstrassCurve K) :
    coveringChartOverlapCoordinateRing W :=
  standardChartToCoveringChartOverlapRing W
    (coveringChartUniversalPoint W true 1)

@[simp]
theorem standardChartToCoveringChartOverlapRing_universalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardChartToCoveringChartOverlapRing W
        (coveringChartUniversalPoint W true j) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (standardChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 2 j)) := by
  change standardChartToCoveringChartOverlapRing W
      (Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (K := K) 2 j)) = _
  exact standardChartToCoveringChartOverlapRing_mk W _

@[simp]
theorem infinityChartToCoveringChartOverlapRing_universalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    infinityChartToCoveringChartOverlapRing W
        (coveringChartUniversalPoint W false j) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (infinityChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 1 j)) := by
  change infinityChartToCoveringChartOverlapRing W
      (Ideal.Quotient.mk (coveringChartIdeal W false)
        (coordinateChartRatio (K := K) 1 j)) = _
  exact infinityChartToCoveringChartOverlapRing_mk W _

/-- On the common overlap, the standard normalized representative is the
infinity normalized representative scaled by `Y / Z`. -/
theorem coveringChartOverlap_standardPoint_eq_smul_infinityPoint
    (W : WeierstrassCurve K) :
    standardChartToCoveringChartOverlapRing W ∘
        coveringChartUniversalPoint W true =
      coveringChartOverlapScale W •
        (infinityChartToCoveringChartOverlapRing W ∘
          coveringChartUniversalPoint W false) := by
  funext j
  change standardChartToCoveringChartOverlapRing W
      (coveringChartUniversalPoint W true j) =
    coveringChartOverlapScale W *
      infinityChartToCoveringChartOverlapRing W
        (coveringChartUniversalPoint W false j)
  fin_cases j
  · have h := congrArg (Ideal.Quotient.mk (coveringChartOverlapIdeal W))
      (projectiveYZOverlap_transition_outerX (K := K))
    rw [standardChartToCoveringChartOverlapRing_universalPoint,
      infinityChartToCoveringChartOverlapRing_universalPoint]
    rw [coveringChartOverlapScale,
      standardChartToCoveringChartOverlapRing_universalPoint]
    change Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (standardChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 2 0)) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
          (standardChartToProjectiveYZOverlapRing
            (coordinateChartRatio (K := K) 2 1)) *
        Ideal.Quotient.mk (coveringChartOverlapIdeal W)
          (infinityChartToProjectiveYZOverlapRing
            (coordinateChartRatio (K := K) 1 0))
    simpa only [map_mul, mul_comm] using h.symm
  · rw [standardChartToCoveringChartOverlapRing_universalPoint,
      infinityChartToCoveringChartOverlapRing_universalPoint]
    rw [coveringChartOverlapScale,
      standardChartToCoveringChartOverlapRing_universalPoint]
    change Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (standardChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 2 1)) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
          (standardChartToProjectiveYZOverlapRing
            (coordinateChartRatio (K := K) 2 1)) *
        Ideal.Quotient.mk (coveringChartOverlapIdeal W)
          (infinityChartToProjectiveYZOverlapRing
            (coordinateChartRatio (K := K) 1 1))
    rw [coordinateChartRatio_self, map_one, map_one, mul_one]
  · have h := congrArg (Ideal.Quotient.mk (coveringChartOverlapIdeal W))
      (projectiveYZOverlap_transition_innerX (K := K))
    rw [standardChartToCoveringChartOverlapRing_universalPoint,
      infinityChartToCoveringChartOverlapRing_universalPoint]
    rw [coveringChartOverlapScale,
      standardChartToCoveringChartOverlapRing_universalPoint]
    change Ideal.Quotient.mk (coveringChartOverlapIdeal W)
        (standardChartToProjectiveYZOverlapRing
          (coordinateChartRatio (K := K) 2 2)) =
      Ideal.Quotient.mk (coveringChartOverlapIdeal W)
          (standardChartToProjectiveYZOverlapRing
            (coordinateChartRatio (K := K) 2 1)) *
        Ideal.Quotient.mk (coveringChartOverlapIdeal W)
          (infinityChartToProjectiveYZOverlapRing
            (coordinateChartRatio (K := K) 1 2))
    rw [coordinateChartRatio_self, map_one, map_one]
    rw [map_mul, map_one] at h
    calc
      1 = Ideal.Quotient.mk (coveringChartOverlapIdeal W)
            (infinityChartToProjectiveYZOverlapRing
              (coordinateChartRatio (K := K) 1 2)) *
          Ideal.Quotient.mk (coveringChartOverlapIdeal W)
            (standardChartToProjectiveYZOverlapRing
              (coordinateChartRatio (K := K) 2 1)) := h.symm
      _ = _ := mul_comm _ _

/-! ## The first-factor overlap of adjacent product charts -/

/-- Tensor the cubic overlap with an unchanged second chart. -/
abbrev projectivePairFirstChartOverlapCoordinateRing
    (W : WeierstrassCurve K) (j : Bool) :=
  TensorProduct K (coveringChartOverlapCoordinateRing W)
    (coveringChartCoordinateRing W j)

/-- Restrict the standard-by-`j` pair chart to the first-factor overlap. -/
noncomputable def standardPairToFirstChartOverlapAlgHom
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairChartCoordinateRing W (true, j) →ₐ[K]
      projectivePairFirstChartOverlapCoordinateRing W j :=
  Algebra.TensorProduct.map
    (standardChartToCoveringChartOverlapAlgHom W)
    (AlgHom.id K (coveringChartCoordinateRing W j))

/-- Restrict the infinity-by-`j` pair chart to the first-factor overlap. -/
noncomputable def infinityPairToFirstChartOverlapAlgHom
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairChartCoordinateRing W (false, j) →ₐ[K]
      projectivePairFirstChartOverlapCoordinateRing W j :=
  Algebra.TensorProduct.map
    (infinityChartToCoveringChartOverlapAlgHom W)
    (AlgHom.id K (coveringChartCoordinateRing W j))

/-- The first-factor transition scalar in the pair-overlap ring. -/
noncomputable def projectivePairFirstChartOverlapScale
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstChartOverlapCoordinateRing W j :=
  Algebra.TensorProduct.includeLeft
    (R := K)
    (S := K)
    (A := coveringChartOverlapCoordinateRing W)
    (B := coveringChartCoordinateRing W j)
    (coveringChartOverlapScale W)

@[simp]
theorem standardPairToFirstChartOverlapAlgHom_firstUniversalPoint
    (W : WeierstrassCurve K) (j : Bool) (i : Fin 3) :
    standardPairToFirstChartOverlapAlgHom W j
        (projectivePairChartFirstUniversalPoint W (true, j) i) =
      Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W j)
        (standardChartToCoveringChartOverlapRing W
          (coveringChartUniversalPoint W true i)) := by
  have h := congrArg
    (fun f ↦ f (coveringChartUniversalPoint W true i))
    (Algebra.TensorProduct.map_comp_includeLeft
      (standardChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j)))
  exact h

@[simp]
theorem infinityPairToFirstChartOverlapAlgHom_firstUniversalPoint
    (W : WeierstrassCurve K) (j : Bool) (i : Fin 3) :
    infinityPairToFirstChartOverlapAlgHom W j
        (projectivePairChartFirstUniversalPoint W (false, j) i) =
      Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W j)
        (infinityChartToCoveringChartOverlapRing W
          (coveringChartUniversalPoint W false i)) := by
  have h := congrArg
    (fun f ↦ f (coveringChartUniversalPoint W false i))
    (Algebra.TensorProduct.map_comp_includeLeft
      (infinityChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j)))
  exact h

@[simp]
theorem standardPairToFirstChartOverlapAlgHom_secondUniversalPoint
    (W : WeierstrassCurve K) (j : Bool) (i : Fin 3) :
    standardPairToFirstChartOverlapAlgHom W j
        (projectivePairChartSecondUniversalPoint W (true, j) i) =
      Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W j)
        (coveringChartUniversalPoint W j i) := by
  change ((Algebra.TensorProduct.map
      (standardChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j))).comp
        Algebra.TensorProduct.includeRight)
      (coveringChartUniversalPoint W j i) = _
  rw [Algebra.TensorProduct.map_comp_includeRight]
  rfl

@[simp]
theorem infinityPairToFirstChartOverlapAlgHom_secondUniversalPoint
    (W : WeierstrassCurve K) (j : Bool) (i : Fin 3) :
    infinityPairToFirstChartOverlapAlgHom W j
        (projectivePairChartSecondUniversalPoint W (false, j) i) =
      Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W j)
        (coveringChartUniversalPoint W j i) := by
  change ((Algebra.TensorProduct.map
      (infinityChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j))).comp
        Algebra.TensorProduct.includeRight)
      (coveringChartUniversalPoint W j i) = _
  rw [Algebra.TensorProduct.map_comp_includeRight]
  rfl

/-- The first universal pair input obeys the expected projective transition
law on the common first-factor overlap. -/
theorem projectivePairFirstChartOverlap_standardFirstPoint_eq_smul_infinityFirstPoint
    (W : WeierstrassCurve K) (j : Bool) :
    standardPairToFirstChartOverlapAlgHom W j ∘
        projectivePairChartFirstUniversalPoint W (true, j) =
      projectivePairFirstChartOverlapScale W j •
        (infinityPairToFirstChartOverlapAlgHom W j ∘
          projectivePairChartFirstUniversalPoint W (false, j)) := by
  funext i
  change standardPairToFirstChartOverlapAlgHom W j
      (projectivePairChartFirstUniversalPoint W (true, j) i) =
    projectivePairFirstChartOverlapScale W j *
      infinityPairToFirstChartOverlapAlgHom W j
        (projectivePairChartFirstUniversalPoint W (false, j) i)
  rw [standardPairToFirstChartOverlapAlgHom_firstUniversalPoint,
    infinityPairToFirstChartOverlapAlgHom_firstUniversalPoint,
    projectivePairFirstChartOverlapScale]
  rw [← map_mul]
  exact congrArg
    (Algebra.TensorProduct.includeLeft
      (R := K)
      (S := K)
      (A := coveringChartOverlapCoordinateRing W)
      (B := coveringChartCoordinateRing W j))
    (congrFun
      (coveringChartOverlap_standardPoint_eq_smul_infinityPoint W) i)

/-- The unchanged second universal input restricts identically from the two
adjacent pair charts. -/
theorem projectivePairFirstChartOverlap_standardSecondPoint_eq_infinitySecondPoint
    (W : WeierstrassCurve K) (j : Bool) :
    standardPairToFirstChartOverlapAlgHom W j ∘
        projectivePairChartSecondUniversalPoint W (true, j) =
      infinityPairToFirstChartOverlapAlgHom W j ∘
        projectivePairChartSecondUniversalPoint W (false, j) := by
  funext i
  exact (standardPairToFirstChartOverlapAlgHom_secondUniversalPoint W j i).trans
    (infinityPairToFirstChartOverlapAlgHom_secondUniversalPoint W j i).symm

private theorem projectivePairChartAdditionCoordinates_map
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

/-- The raw secant triple is compatible with the first input-chart
transition: changing the first normalized representative multiplies all
three output coordinates by the square of the transition scalar. -/
theorem projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition
    (W : WeierstrassCurve K) (j : Bool) :
    standardPairToFirstChartOverlapAlgHom W j ∘
        projectivePairChartAdditionCoordinates W (true, j) =
      projectivePairFirstChartOverlapScale W j ^ 2 •
        (infinityPairToFirstChartOverlapAlgHom W j ∘
          projectivePairChartAdditionCoordinates W (false, j)) := by
  rw [projectivePairChartAdditionCoordinates_map,
    projectivePairChartAdditionCoordinates_map,
    projectivePairFirstChartOverlap_standardFirstPoint_eq_smul_infinityFirstPoint,
    projectivePairFirstChartOverlap_standardSecondPoint_eq_infinitySecondPoint]
  have h := (W.map (algebraMap K
      (projectivePairFirstChartOverlapCoordinateRing W j))).toProjective.addXYZ_smul
    (infinityPairToFirstChartOverlapAlgHom W j ∘
      projectivePairChartFirstUniversalPoint W (false, j))
    (infinityPairToFirstChartOverlapAlgHom W j ∘
      projectivePairChartSecondUniversalPoint W (false, j))
    (projectivePairFirstChartOverlapScale W j) 1
  simpa only [one_smul, mul_one] using h
end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
