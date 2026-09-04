/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductAdditionCoordinates

/-!
# Standard projective-pair coordinates and the affine addition atlas

The `(Z != 0, Z != 0)` member of the projective-product atlas has two
independently useful affine presentations: the tensor product of the two
standard projective chart rings, and the four-coordinate affine-pair ring on
which addition was already glued.  This file constructs their `K`-algebra
equivalence, identifies all four universal coordinates, and proves that its
contravariant spectrum map is exactly the geometric comparison already
defined by the two pullback presentations.

The final theorem transports the raw homogeneous addition polynomial through
the equivalence.  It is the coordinate bridge consumed by comparisons between
the projective-pair local formulas and the checked affine addition atlas.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

local instance secantTargetCoordinateRingCommRing
    (W : WeierstrassCurve K) : CommRing (secantTargetCoordinateRing W) :=
  Ideal.Quotient.commRing (Ideal.span {W.toAffine.polynomial})

/-- The affine Weierstrass equation ring is the standard projective chart
ring as a `K`-algebra, not only as a ring. -/
noncomputable def standardAffineChartAlgEquiv (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W ≃ₐ[K] coveringChartCoordinateRing W true where
  __ := affineEquationToStandardChartRingEquiv W
  commutes' a := by
    change affineEquationToStandardChartRingEquiv W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
          (Polynomial.C (Polynomial.C a))) =
      Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartConstantHom (coveringCoordinate true) a)
    change affineEquationToStandardChartRingEquiv W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
          (Polynomial.C (Polynomial.C a))) =
      Ideal.Quotient.mk (standardChartIdeal W)
        (coordinateChartConstantHom 2 a)
    rw [show coordinateChartConstantHom (K := K) 2 a =
        affineToStandardChart (Polynomial.C (Polynomial.C a)) by
      rw [affineToStandardChart_C_C]]
    rfl

/-- The standard-chart algebra equivalence sends the affine abscissa to
`X/Z`. -/
@[simp]
theorem standardAffineChartAlgEquiv_X (W : WeierstrassCurve K) :
    standardAffineChartAlgEquiv W (secantTargetX W) =
      coveringChartUniversalPoint W true 0 := by
  change affineEquationToStandardChartRingEquiv W (secantTargetX W) =
    Ideal.Quotient.mk (standardChartIdeal W)
      (coordinateChartRatio (K := K) 2 0)
  apply (affineEquationToStandardChartRingEquiv W).symm.injective
  rw [RingEquiv.symm_apply_apply]
  exact (standardChartQuotientEquivSymm_outerX W).symm

/-- The standard-chart algebra equivalence sends the affine ordinate to
`Y/Z`. -/
@[simp]
theorem standardAffineChartAlgEquiv_Y (W : WeierstrassCurve K) :
    standardAffineChartAlgEquiv W (secantTargetY W) =
      coveringChartUniversalPoint W true 1 := by
  change affineEquationToStandardChartRingEquiv W (secantTargetY W) =
    Ideal.Quotient.mk (standardChartIdeal W)
      (coordinateChartRatio (K := K) 2 1)
  apply (affineEquationToStandardChartRingEquiv W).symm.injective
  rw [RingEquiv.symm_apply_apply]
  exact (standardChartQuotientEquivSymm_innerX W).symm

/-- On spectra, the standard affine-chart algebra equivalence is the inverse
of the existing affine-equation comparison. -/
theorem standardAffineChartAlgEquiv_specMap (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
        (standardAffineChartAlgEquiv W).toRingHom) =
      (affineEquationSchemeIsoStandardChart W).inv := by
  rfl

/-- The four-coordinate affine-pair ring and the tensor coordinate ring of
the standard projective pair chart are equivalent as `K`-algebras. -/
noncomputable def standardPairCoordinateRingAlgEquiv
    (W : WeierstrassCurve K) :
    secantPairCoordinateRing W ≃ₐ[K]
      projectivePairChartCoordinateRing W (true, true) :=
  (secantPairTensorEquiv W).trans
    (Algebra.TensorProduct.congr
      (standardAffineChartAlgEquiv W) (standardAffineChartAlgEquiv W))

/-- The first affine abscissa is the first universal `X/Z` coordinate. -/
@[simp]
theorem standardPairCoordinateRingAlgEquiv_X₁
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W (secantPairX₁ W) =
      projectivePairChartFirstUniversalPoint W (true, true) 0 := by
  rw [standardPairCoordinateRingAlgEquiv, AlgEquiv.trans_apply,
    secantPairTensorEquiv_X₁, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  change standardAffineChartAlgEquiv W (secantTargetX W) ⊗ₜ[K] 1 =
    coveringChartUniversalPoint W true 0 ⊗ₜ[K] 1
  exact congrArg
    (fun z ↦ z ⊗ₜ[K] (1 : coveringChartCoordinateRing W true))
    (standardAffineChartAlgEquiv_X W)

/-- The first affine ordinate is the first universal `Y/Z` coordinate. -/
@[simp]
theorem standardPairCoordinateRingAlgEquiv_Y₁
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W (secantPairY₁ W) =
      projectivePairChartFirstUniversalPoint W (true, true) 1 := by
  rw [standardPairCoordinateRingAlgEquiv, AlgEquiv.trans_apply,
    secantPairTensorEquiv_Y₁, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  change standardAffineChartAlgEquiv W (secantTargetY W) ⊗ₜ[K] 1 =
    coveringChartUniversalPoint W true 1 ⊗ₜ[K] 1
  exact congrArg
    (fun z ↦ z ⊗ₜ[K] (1 : coveringChartCoordinateRing W true))
    (standardAffineChartAlgEquiv_Y W)

/-- The second affine abscissa is the second universal `X/Z` coordinate. -/
@[simp]
theorem standardPairCoordinateRingAlgEquiv_X₂
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W (secantPairX₂ W) =
      projectivePairChartSecondUniversalPoint W (true, true) 0 := by
  rw [standardPairCoordinateRingAlgEquiv, AlgEquiv.trans_apply,
    secantPairTensorEquiv_X₂, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  change 1 ⊗ₜ[K] standardAffineChartAlgEquiv W (secantTargetX W) =
    1 ⊗ₜ[K] coveringChartUniversalPoint W true 0
  exact congrArg
    (fun z ↦ (1 : coveringChartCoordinateRing W true) ⊗ₜ[K] z)
    (standardAffineChartAlgEquiv_X W)

/-- The second affine ordinate is the second universal `Y/Z` coordinate. -/
@[simp]
theorem standardPairCoordinateRingAlgEquiv_Y₂
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W (secantPairY₂ W) =
      projectivePairChartSecondUniversalPoint W (true, true) 1 := by
  rw [standardPairCoordinateRingAlgEquiv, AlgEquiv.trans_apply,
    secantPairTensorEquiv_Y₂, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  change 1 ⊗ₜ[K] standardAffineChartAlgEquiv W (secantTargetY W) =
    1 ⊗ₜ[K] coveringChartUniversalPoint W true 1
  exact congrArg
    (fun z ↦ (1 : coveringChartCoordinateRing W true) ⊗ₜ[K] z)
    (standardAffineChartAlgEquiv_Y W)

/-- The affine secant denominator becomes the difference of the two standard
universal abscissas. -/
@[simp]
theorem standardPairCoordinateRingAlgEquiv_denominator
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W (secantDenominator W) =
      projectivePairChartFirstUniversalPoint W (true, true) 0 -
        projectivePairChartSecondUniversalPoint W (true, true) 0 := by
  rw [secantDenominator, map_sub,
    standardPairCoordinateRingAlgEquiv_X₁,
    standardPairCoordinateRingAlgEquiv_X₂]

/-- On the standard pair chart, the raw addition `Z` coordinate is the cube
of the transported affine secant denominator. -/
@[simp]
theorem projectivePairChartAdditionCoordinates_standard_Z
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3) =
      (standardPairCoordinateRingAlgEquiv W (secantDenominator W)) ^ 3 := by
  have h := projectivePairChartAdditionCoordinates_Z_mul_input_Z
    W (true, true)
  have hfirst :
      projectivePairChartFirstUniversalPoint W (true, true) (2 : Fin 3) = 1 := by
    simpa [coveringCoordinate] using
      projectivePairChartFirstUniversalPoint_normalized W (true, true)
  have hsecond :
      projectivePairChartSecondUniversalPoint W (true, true) (2 : Fin 3) = 1 := by
    simpa [coveringCoordinate] using
      projectivePairChartSecondUniversalPoint_normalized W (true, true)
  rw [hfirst, hsecond] at h
  simpa using h

private theorem standardPairCoordinateRingAlgEquiv_spec_fst
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
          (standardPairCoordinateRingAlgEquiv W).toRingHom) ≫
        (secantPairSchemeIsoAffineProduct W).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeft
          (R := K)
          (A := coveringChartCoordinateRing W true)
          (B := coveringChartCoordinateRing W true)).comp
            (standardAffineChartAlgEquiv W).toAlgHom).toRingHom) := by
  have hpair : (secantPairSchemeIsoAffineProduct W).hom =
      Spec.map (CommRingCat.ofHom
        (secantPairTensorEquiv W).symm.toRingHom) ≫
        (pullbackSpecIso K (secantTargetCoordinateRing W)
          (secantTargetCoordinateRing W)).inv := rfl
  rw [hpair]
  simp only [Category.assoc]
  rw [pullbackSpecIso_inv_fst,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply DFunLike.ext _ _
  intro a
  simp [standardPairCoordinateRingAlgEquiv]

private theorem standardPairCoordinateRingAlgEquiv_spec_snd
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
          (standardPairCoordinateRingAlgEquiv W).toRingHom) ≫
        (secantPairSchemeIsoAffineProduct W).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight
          (R := K)
          (A := coveringChartCoordinateRing W true)
          (B := coveringChartCoordinateRing W true)).comp
            (standardAffineChartAlgEquiv W).toAlgHom).toRingHom) := by
  have hpair : (secantPairSchemeIsoAffineProduct W).hom =
      Spec.map (CommRingCat.ofHom
        (secantPairTensorEquiv W).symm.toRingHom) ≫
        (pullbackSpecIso K (secantTargetCoordinateRing W)
          (secantTargetCoordinateRing W)).inv := rfl
  rw [hpair]
  simp only [Category.assoc]
  rw [pullbackSpecIso_inv_snd,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply DFunLike.ext _ _
  intro a
  simp [standardPairCoordinateRingAlgEquiv]

private theorem standardPairCoordinateRingAlgEquiv_spec_leftFactor
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeft
          (R := K)
          (A := coveringChartCoordinateRing W true)
          (B := coveringChartCoordinateRing W true)).comp
            (standardAffineChartAlgEquiv W).toAlgHom).toRingHom) =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := K)
            (A := coveringChartCoordinateRing W true)
            (B := coveringChartCoordinateRing W true))) ≫
        Spec.map (CommRingCat.ofHom
          (standardAffineChartAlgEquiv W).toRingHom) := by
  rw [← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
  rfl

private theorem standardPairCoordinateRingAlgEquiv_spec_rightFactor
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight
          (R := K)
          (A := coveringChartCoordinateRing W true)
          (B := coveringChartCoordinateRing W true)).comp
            (standardAffineChartAlgEquiv W).toAlgHom).toRingHom) =
      Spec.map (CommRingCat.ofHom
          (RingHomClass.toRingHom
            (Algebra.TensorProduct.includeRight
              (R := K)
              (A := coveringChartCoordinateRing W true)
              (B := coveringChartCoordinateRing W true)))) ≫
        Spec.map (CommRingCat.ofHom
          (standardAffineChartAlgEquiv W).toRingHom) := by
  rw [← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
  rfl

/-- The spectrum map induced by the coordinate equivalence is exactly the
canonical geometric identification of the standard pair chart with the
four-coordinate affine-pair presentation. -/
@[reassoc]
theorem projectivePairChartIsoSpecTensor_hom_comp_standardPairCoordinateRingAlgEquiv_specMap
    (W : WeierstrassCurve K) :
    (projectivePairChartIsoSpecTensor W (true, true)).hom ≫
        Spec.map (CommRingCat.ofHom
          (standardPairCoordinateRingAlgEquiv W).toRingHom) =
      (standardPairIsoAffinePair W).hom := by
  rw [standardPairIsoAffinePair, Iso.trans_hom]
  apply (cancel_mono (secantPairSchemeIsoAffineProduct W).hom).1
  simp only [Category.assoc, Iso.symm_hom]
  apply pullback.hom_ext
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [standardPairCoordinateRingAlgEquiv_spec_fst,
      standardPairCoordinateRingAlgEquiv_spec_leftFactor,
      projectivePairChartIsoSpecTensor_hom_fst_assoc,
      standardAffineChartAlgEquiv_specMap,
      standardAffineProductIsoProjectivePairChart_inv_fst]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [standardPairCoordinateRingAlgEquiv_spec_snd,
      standardPairCoordinateRingAlgEquiv_spec_rightFactor,
      projectivePairChartIsoSpecTensor_hom_snd_assoc,
      standardAffineChartAlgEquiv_specMap,
      standardAffineProductIsoProjectivePairChart_inv_snd]

/-- The first affine universal point, homogenized in the `Z = 1` chart. -/
noncomputable def affinePairFirstProjectivePoint (W : WeierstrassCurve K) :
    Fin 3 → secantPairCoordinateRing W :=
  ![secantPairX₁ W, secantPairY₁ W, 1]

/-- The second affine universal point, homogenized in the `Z = 1` chart. -/
noncomputable def affinePairSecondProjectivePoint (W : WeierstrassCurve K) :
    Fin 3 → secantPairCoordinateRing W :=
  ![secantPairX₂ W, secantPairY₂ W, 1]

/-- The coordinate equivalence carries the first homogenized affine point to
the first universal point on the standard projective pair chart. -/
theorem standardPairCoordinateRingAlgEquiv_firstPoint
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W ∘ affinePairFirstProjectivePoint W =
      projectivePairChartFirstUniversalPoint W (true, true) := by
  funext j
  fin_cases j
  · simp [affinePairFirstProjectivePoint]
  · simp [affinePairFirstProjectivePoint]
  · simpa [affinePairFirstProjectivePoint, coveringCoordinate] using
      (projectivePairChartFirstUniversalPoint_normalized
        W (true, true)).symm

/-- The coordinate equivalence carries the second homogenized affine point to
the second universal point on the standard projective pair chart. -/
theorem standardPairCoordinateRingAlgEquiv_secondPoint
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W ∘ affinePairSecondProjectivePoint W =
      projectivePairChartSecondUniversalPoint W (true, true) := by
  funext j
  fin_cases j
  · simp [affinePairSecondProjectivePoint]
  · simp [affinePairSecondProjectivePoint]
  · simpa [affinePairSecondProjectivePoint, coveringCoordinate] using
      (projectivePairChartSecondUniversalPoint_normalized
        W (true, true)).symm

/-- The standard pair equivalence transports the raw homogeneous addition
triple on the affine universal inputs to the raw addition triple of the
projective-pair chart. -/
theorem standardPairCoordinateRingAlgEquiv_additionCoordinates
    (W : WeierstrassCurve K) :
    standardPairCoordinateRingAlgEquiv W ∘
        (W.map (algebraMap K (secantPairCoordinateRing W))).toProjective.addXYZ
          (affinePairFirstProjectivePoint W)
          (affinePairSecondProjectivePoint W) =
      projectivePairChartAdditionCoordinates W (true, true) := by
  have h := (WeierstrassCurve.Projective.map_addXYZ
    (W' := (W.map
      (algebraMap K (secantPairCoordinateRing W))).toProjective)
    (standardPairCoordinateRingAlgEquiv W).toRingHom
    (affinePairFirstProjectivePoint W)
    (affinePairSecondProjectivePoint W)).symm
  have hfirst :
      (standardPairCoordinateRingAlgEquiv W).toRingHom ∘
          affinePairFirstProjectivePoint W =
        projectivePairChartFirstUniversalPoint W (true, true) :=
    standardPairCoordinateRingAlgEquiv_firstPoint W
  have hsecond :
      (standardPairCoordinateRingAlgEquiv W).toRingHom ∘
          affinePairSecondProjectivePoint W =
        projectivePairChartSecondUniversalPoint W (true, true) :=
    standardPairCoordinateRingAlgEquiv_secondPoint W
  rw [hfirst, hsecond] at h
  have hcoeff :
      (standardPairCoordinateRingAlgEquiv W).toRingHom.comp
          (algebraMap K (secantPairCoordinateRing W)) =
        algebraMap K (projectivePairChartCoordinateRing W (true, true)) := by
    ext a
    exact (standardPairCoordinateRingAlgEquiv W).commutes a
  simp only [WeierstrassCurve.map_map] at h
  rw [hcoeff] at h
  simpa [projectivePairChartAdditionCoordinates,
    projectivePairChartMappedCurve] using h

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
