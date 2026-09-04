/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductInfinityAdditionCompatibility

/-!
# Global addition on the projective Weierstrass cubic

The four members of `projectivePairOpenCover` carry the standard, two mixed,
and infinity-pair addition morphisms constructed in the preceding atlas
layers.  This file proves that those four genuine chart morphisms agree on
their categorical intersections and glues them to the full projective product.

The design boundary is `projectiveAdditionMorphism`, the actual morphism from
the fibre square of the cubic to the cubic.  Its named chart restrictions are
the downstream input for the identity, inverse, associativity, and
commutativity proofs that construct the canonical commutative group scheme.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem globalPullback_morphism_compatible_self
    {U X Y : Scheme.{u}} (i : U ⟶ X) [Mono i] (f : U ⟶ Y) :
    pullback.fst i i ≫ f = pullback.snd i i ≫ f := by
  have hfst : pullback.fst i i = pullback.snd i i := by
    apply (cancel_mono i).mp
    exact pullback.condition
  exact congrArg (fun q => q ≫ f) hfst

private theorem globalPullback_morphism_compatible_symm
    {U V X Y : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X)
    (f : U ⟶ Y) (g : V ⟶ Y)
    (h : pullback.fst i j ≫ f = pullback.snd i j ≫ g) :
    pullback.fst j i ≫ g = pullback.snd j i ≫ f := by
  apply (cancel_epi (pullbackSymmetry i j).hom).mp
  calc
    _ = ((pullbackSymmetry i j).hom ≫ pullback.fst j i) ≫ g :=
      (Category.assoc _ _ _).symm
    _ = pullback.snd i j ≫ g := congrArg (fun q => q ≫ g)
      (pullbackSymmetry_hom_comp_fst i j)
    _ = pullback.fst i j ≫ f := h.symm
    _ = ((pullbackSymmetry i j).hom ≫ pullback.snd j i) ≫ f :=
      congrArg (fun q => q ≫ f) (pullbackSymmetry_hom_comp_snd i j).symm
    _ = _ := Category.assoc _ _ _

/-! ## Integral and nonempty overlap sources -/

private theorem globalSecantTargetY_ne_zero (W : WeierstrassCurve K) :
    secantTargetY W ≠ 0 := by
  change AdjoinRoot.mk W.toAffine.polynomial Polynomial.X ≠ 0
  rw [AdjoinRoot.mk_X]
  simpa [WeierstrassCurve.Affine.CoordinateRing.YClass] using
    (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero
      (W' := W.toAffine) (0 : Polynomial K))

private theorem globalStandardChartY_ne_zero (W : WeierstrassCurve K) :
    coveringChartUniversalPoint W true (1 : Fin 3) ≠ 0 := by
  rw [← standardAffineChartAlgEquiv_Y]
  simpa only [map_zero] using
    (standardAffineChartAlgEquiv W).injective.ne
      (globalSecantTargetY_ne_zero W)

private theorem globalProjectivePairFirstStandardY_ne_zero
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairChartFirstUniversalPoint W (true, j) (1 : Fin 3) ≠ 0 := by
  letI : Module.Free K (coveringChartCoordinateRing W true) :=
    Module.Free.of_divisionRing K (coveringChartCoordinateRing W true)
  letI : Module.Flat K (coveringChartCoordinateRing W true) :=
    Module.Flat.of_free
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W j)) :=
    Algebra.TensorProduct.includeLeft_injective
      (RingHom.injective (algebraMap K (coveringChartCoordinateRing W j)))
  change Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := coveringChartCoordinateRing W true)
      (B := coveringChartCoordinateRing W j)
      (coveringChartUniversalPoint W true (1 : Fin 3)) ≠ 0
  intro h
  apply globalStandardChartY_ne_zero W
  apply hinj
  exact h.trans (map_zero _).symm

private theorem globalProjectivePairSecondStandardY_ne_zero
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairChartSecondUniversalPoint W (i, true) (1 : Fin 3) ≠ 0 := by
  letI : Module.Free K (coveringChartCoordinateRing W true) :=
    Module.Free.of_divisionRing K (coveringChartCoordinateRing W true)
  letI : Module.Flat K (coveringChartCoordinateRing W true) :=
    Module.Flat.of_free
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W true)) :=
    Algebra.TensorProduct.includeRight_injective
      (RingHom.injective (algebraMap K (coveringChartCoordinateRing W i)))
  change Algebra.TensorProduct.includeRight
      (R := K)
      (A := coveringChartCoordinateRing W i)
      (B := coveringChartCoordinateRing W true)
      (coveringChartUniversalPoint W true (1 : Fin 3)) ≠ 0
  intro h
  apply globalStandardChartY_ne_zero W
  apply hinj
  exact h.trans (map_zero _).symm

private theorem globalStandardPairToFirstOverlapAlgHom_injective
    (W : WeierstrassCurve K) [W.IsElliptic] (j : Bool) :
    Function.Injective (standardPairToFirstChartOverlapAlgHom W j) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, j)) :=
    projectivePairChartCoordinateRing_isDomain W (true, j)
  letI := (standardPairToFirstChartOverlapAlgHom W j).toAlgebra
  haveI : IsLocalization.Away
      (projectivePairChartFirstUniversalPoint W (true, j) (1 : Fin 3))
      (projectivePairFirstChartOverlapCoordinateRing W j) := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairFirstChartOverlapCoordinateRing W j)
    exact projectivePairFirstOverlap_isLocalization_standardPair W j
  change Function.Injective
    (algebraMap (projectivePairChartCoordinateRing W (true, j))
      (projectivePairFirstChartOverlapCoordinateRing W j))
  exact IsLocalization.injective
    (projectivePairFirstChartOverlapCoordinateRing W j)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (globalProjectivePairFirstStandardY_ne_zero W j))

private theorem globalStandardPairToSecondOverlapAlgHom_injective
    (W : WeierstrassCurve K) [W.IsElliptic] (i : Bool) :
    Function.Injective (standardPairToSecondChartOverlapAlgHom W i) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (i, true)) :=
    projectivePairChartCoordinateRing_isDomain W (i, true)
  letI := (standardPairToSecondChartOverlapAlgHom W i).toAlgebra
  haveI : IsLocalization.Away
      (projectivePairChartSecondUniversalPoint W (i, true) (1 : Fin 3))
      (projectivePairSecondChartOverlapCoordinateRing W i) := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairSecondChartOverlapCoordinateRing W i)
    exact projectivePairSecondOverlap_isLocalization_standardPair W i
  change Function.Injective
    (algebraMap (projectivePairChartCoordinateRing W (i, true))
      (projectivePairSecondChartOverlapCoordinateRing W i))
  exact IsLocalization.injective
    (projectivePairSecondChartOverlapCoordinateRing W i)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (globalProjectivePairSecondStandardY_ne_zero W i))

private noncomputable instance globalProjectivePairFirstOverlap_isDomain
    (W : WeierstrassCurve K) [W.IsElliptic] (j : Bool) :
    IsDomain (projectivePairFirstChartOverlapCoordinateRing W j) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, j)) :=
    projectivePairChartCoordinateRing_isDomain W (true, j)
  letI := (standardPairToFirstChartOverlapAlgHom W j).toAlgebra
  haveI : IsLocalization.Away
      (projectivePairChartFirstUniversalPoint W (true, j) (1 : Fin 3))
      (projectivePairFirstChartOverlapCoordinateRing W j) := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairFirstChartOverlapCoordinateRing W j)
    exact projectivePairFirstOverlap_isLocalization_standardPair W j
  exact IsLocalization.Away.isDomain
    (projectivePairFirstChartOverlapCoordinateRing W j)
    (globalProjectivePairFirstStandardY_ne_zero W j)

private noncomputable instance globalProjectivePairSecondOverlap_isDomain
    (W : WeierstrassCurve K) [W.IsElliptic] (i : Bool) :
    IsDomain (projectivePairSecondChartOverlapCoordinateRing W i) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (i, true)) :=
    projectivePairChartCoordinateRing_isDomain W (i, true)
  letI := (standardPairToSecondChartOverlapAlgHom W i).toAlgebra
  haveI : IsLocalization.Away
      (projectivePairChartSecondUniversalPoint W (i, true) (1 : Fin 3))
      (projectivePairSecondChartOverlapCoordinateRing W i) := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairSecondChartOverlapCoordinateRing W i)
    exact projectivePairSecondOverlap_isLocalization_standardPair W i
  exact IsLocalization.Away.isDomain
    (projectivePairSecondChartOverlapCoordinateRing W i)
    (globalProjectivePairSecondStandardY_ne_zero W i)

private noncomputable instance globalProjectivePairFirstOverlap_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] (j : Bool) :
    Nonempty (projectivePairFirstChartOverlapScheme W j) := by
  letI : Nontrivial (projectivePairFirstChartOverlapCoordinateRing W j) :=
    (globalProjectivePairFirstOverlap_isDomain W j).toNontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

private noncomputable instance globalProjectivePairSecondOverlap_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] (i : Bool) :
    Nonempty (projectivePairSecondChartOverlapScheme W i) := by
  letI : Nontrivial (projectivePairSecondChartOverlapCoordinateRing W i) :=
    (globalProjectivePairSecondOverlap_isDomain W i).toNontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

private theorem globalStandardPairInputYProduct_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartFirstUniversalPoint W (true, true) (1 : Fin 3) *
        projectivePairChartSecondUniversalPoint W (true, true) (1 : Fin 3) ≠
      0 := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  exact mul_ne_zero
    (globalProjectivePairFirstStandardY_ne_zero W true)
    (globalProjectivePairSecondStandardY_ne_zero W true)

private noncomputable instance globalProjectivePairDoubleOverlap_isDomain
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDomain (projectivePairDoubleChartOverlapCoordinateRing W) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  letI := (standardPairToDoubleOverlapAlgHom W).toAlgebra
  haveI := projectivePairDoubleOverlap_isLocalization_standardPair W
  exact IsLocalization.Away.isDomain
    (projectivePairDoubleChartOverlapCoordinateRing W)
    (globalStandardPairInputYProduct_ne_zero W)

private noncomputable instance globalProjectivePairDoubleOverlap_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nonempty (projectivePairDoubleChartOverlapScheme W) := by
  letI : Nontrivial (projectivePairDoubleChartOverlapCoordinateRing W) :=
    (globalProjectivePairDoubleOverlap_isDomain W).toNontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

private noncomputable instance globalProjectivePairChart_isIntegral
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    IsIntegral (projectivePairChartScheme W ij) := by
  letI : IsDomain (projectivePairChartCoordinateRing W ij) :=
    projectivePairChartCoordinateRing_isDomain W ij
  letI : IsIntegral (Spec (.of (projectivePairChartCoordinateRing W ij))) :=
    (affine_isIntegral_iff
      (.of (projectivePairChartCoordinateRing W ij))).mpr inferInstance
  exact IsIntegral.of_isIso (projectivePairChartIsoSpecTensor W ij).inv

/-! ## Dense secant sources on the two infinity-adjacent overlaps -/

/-- The raw output-`Z` coordinate on the standard-by-infinity chart is not
the zero function. -/
theorem projectivePairStandardInfinityRawOutputZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionCoordinates W (true, false) (2 : Fin 3) ≠ 0 := by
  have hstandard :
      standardPairToSecondChartOverlapAlgHom W true
          (projectivePairChartAdditionCoordinates W (true, true)
            (2 : Fin 3)) ≠ 0 :=
    (globalStandardPairToSecondOverlapAlgHom_injective W true).ne
      (standardPairRawOutputZ_ne_zero W)
  intro hzero
  apply hstandard
  have htransition := congrFun
    (projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition
      W true) (2 : Fin 3)
  change standardPairToSecondChartOverlapAlgHom W true
      (projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3)) =
    projectivePairSecondChartOverlapScale W true ^ 2 *
      infinityPairToSecondChartOverlapAlgHom W true
        (projectivePairChartAdditionCoordinates W (true, false)
          (2 : Fin 3)) at htransition
  rw [hzero, map_zero, mul_zero] at htransition
  exact htransition

/-- The raw output-`Z` coordinate on the infinity-by-standard chart is not
the zero function. -/
theorem projectivePairInfinityStandardRawOutputZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionCoordinates W (false, true) (2 : Fin 3) ≠ 0 := by
  have hstandard :
      standardPairToFirstChartOverlapAlgHom W true
          (projectivePairChartAdditionCoordinates W (true, true)
            (2 : Fin 3)) ≠ 0 :=
    (globalStandardPairToFirstOverlapAlgHom_injective W true).ne
      (standardPairRawOutputZ_ne_zero W)
  intro hzero
  apply hstandard
  have htransition := congrFun
    (projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition
      W true) (2 : Fin 3)
  change standardPairToFirstChartOverlapAlgHom W true
      (projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3)) =
    projectivePairFirstChartOverlapScale W true ^ 2 *
      infinityPairToFirstChartOverlapAlgHom W true
        (projectivePairChartAdditionCoordinates W (false, true)
          (2 : Fin 3)) at htransition
  rw [hzero, map_zero, mul_zero] at htransition
  exact htransition

private theorem globalProjectivePairFirstOverlapInfinityRawZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    infinityPairToFirstChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)) ≠ 0 := by
  have hmixed :
      standardPairToFirstChartOverlapAlgHom W false
          (projectivePairChartAdditionCoordinates W (true, false)
            (2 : Fin 3)) ≠ 0 :=
    (globalStandardPairToFirstOverlapAlgHom_injective W false).ne
      (projectivePairStandardInfinityRawOutputZ_ne_zero W)
  intro hzero
  apply hmixed
  have htransition := congrFun
    (projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition
      W false) (2 : Fin 3)
  change standardPairToFirstChartOverlapAlgHom W false
      (projectivePairChartAdditionCoordinates W (true, false) (2 : Fin 3)) =
    projectivePairFirstChartOverlapScale W false ^ 2 *
      infinityPairToFirstChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)) at htransition
  rw [hzero, mul_zero] at htransition
  exact htransition

private theorem globalProjectivePairSecondOverlapInfinityRawZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)) ≠ 0 := by
  have hmixed :
      standardPairToSecondChartOverlapAlgHom W false
          (projectivePairChartAdditionCoordinates W (false, true)
            (2 : Fin 3)) ≠ 0 :=
    (globalStandardPairToSecondOverlapAlgHom_injective W false).ne
      (projectivePairInfinityStandardRawOutputZ_ne_zero W)
  intro hzero
  apply hmixed
  have htransition := congrFun
    (projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition
      W false) (2 : Fin 3)
  change standardPairToSecondChartOverlapAlgHom W false
      (projectivePairChartAdditionCoordinates W (false, true) (2 : Fin 3)) =
    projectivePairSecondChartOverlapScale W false ^ 2 *
      infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)) at htransition
  rw [hzero, mul_zero] at htransition
  exact htransition

private theorem globalProjectivePairFirstOverlapSecantZRingMap_injective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective
      (algebraMap (projectivePairFirstChartOverlapCoordinateRing W false)
        (projectivePairFirstOverlapAdditionOutputRing W false true)) := by
  letI : IsDomain (projectivePairFirstChartOverlapCoordinateRing W false) :=
    globalProjectivePairFirstOverlap_isDomain W false
  change Function.Injective
    (algebraMap (projectivePairFirstChartOverlapCoordinateRing W false)
      (Localization.Away
        (infinityPairToFirstChartOverlapAlgHom W false
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))))
  exact IsLocalization.injective
    (Localization.Away
      (infinityPairToFirstChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))))
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (globalProjectivePairFirstOverlapInfinityRawZ_ne_zero W))

private theorem globalProjectivePairSecondOverlapSecantZRingMap_injective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective
      (algebraMap (projectivePairSecondChartOverlapCoordinateRing W false)
        (projectivePairSecondOverlapAdditionOutputRing W false true)) := by
  letI : IsDomain (projectivePairSecondChartOverlapCoordinateRing W false) :=
    globalProjectivePairSecondOverlap_isDomain W false
  change Function.Injective
    (algebraMap (projectivePairSecondChartOverlapCoordinateRing W false)
      (Localization.Away
        (infinityPairToSecondChartOverlapAlgHom W false
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))))
  exact IsLocalization.injective
    (Localization.Away
      (infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))))
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (globalProjectivePairSecondOverlapInfinityRawZ_ne_zero W))

private noncomputable instance
    globalProjectivePairFirstOverlapSecantZ_isDominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant
      (projectivePairFirstOverlapAdditionOutputOpen W false true) := by
  constructor
  change DenseRange (PrimeSpectrum.comap
    (algebraMap (projectivePairFirstChartOverlapCoordinateRing W false)
      (projectivePairFirstOverlapAdditionOutputRing W false true)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
    (globalProjectivePairFirstOverlapSecantZRingMap_injective W)]
  exact bot_le

private noncomputable instance
    globalProjectivePairSecondOverlapSecantZ_isDominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant
      (projectivePairSecondOverlapAdditionOutputOpen W false true) := by
  constructor
  change DenseRange (PrimeSpectrum.comap
    (algebraMap (projectivePairSecondChartOverlapCoordinateRing W false)
      (projectivePairSecondOverlapAdditionOutputRing W false true)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
    (globalProjectivePairSecondOverlapSecantZRingMap_injective W)]
  exact bot_le

private theorem globalProjectivePairFirstOverlapSecantZ_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairFirstOverlapAdditionOutputOpen W false true ≫
        projectivePairFirstOverlapToStandardPair W false ≫
          projectivePairStandardInfinityAdditionMorphism W =
      projectivePairFirstOverlapAdditionOutputOpen W false true ≫
        projectivePairFirstOverlapToInfinityPair W false ≫
          projectiveInfinityPairAdditionMorphism W := by
  calc
    _ = (projectivePairFirstOverlapAdditionOutputToStandard W false true ≫
          projectivePairChartAdditionOutputOpen W (true, false) true) ≫
        projectivePairStandardInfinityAdditionMorphism W := by
          rw [projectivePairFirstOverlapAdditionOutput_standardOpen_eq,
            Category.assoc]
    _ = projectivePairFirstOverlapAdditionOutputToStandard W false true ≫
        (projectivePairChartAdditionOutputOpen W (true, false) true ≫
          projectivePairStandardInfinityAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = projectivePairFirstOverlapAdditionOutputToStandard W false true ≫
        projectivePairChartAdditionOutputMorphism W
          (true, false) true := by
            rw [projectivePairStandardInfinitySecantZOpen_comp_addition]
    _ = projectivePairFirstOverlapAdditionOutputToInfinity W false true ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true :=
      projectivePairFirstOverlapAdditionOutput_morphisms_eq W false true
    _ = projectivePairFirstOverlapAdditionOutputToInfinity W false true ≫
        (projectivePairChartAdditionOutputOpen W (false, false) true ≫
          projectiveInfinityPairAdditionMorphism W) := by
            rw [projectiveInfinityPairSecantZOpen_comp_addition]
    _ = (projectivePairFirstOverlapAdditionOutputToInfinity W false true ≫
          projectivePairChartAdditionOutputOpen W (false, false) true) ≫
        projectiveInfinityPairAdditionMorphism W :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      rw [projectivePairFirstOverlapAdditionOutput_infinityOpen_eq,
        Category.assoc]

/-- The standard-by-infinity and infinity-by-infinity chart laws agree on
their entire explicit first-factor overlap. -/
theorem projectivePairFirstOverlap_standardInfinity_infinity_addition_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairFirstOverlapToStandardPair W false ≫
        projectivePairStandardInfinityAdditionMorphism W =
      projectivePairFirstOverlapToInfinityPair W false ≫
        projectiveInfinityPairAdditionMorphism W := by
  letI : IsDomain (projectivePairFirstChartOverlapCoordinateRing W false) :=
    globalProjectivePairFirstOverlap_isDomain W false
  have hlocal := globalProjectivePairFirstOverlapSecantZ_morphisms_eq W
  have hbase :
      (projectivePairFirstOverlapToStandardPair W false ≫
          projectivePairStandardInfinityAdditionMorphism W) ≫
          structureMap W =
        (projectivePairFirstOverlapToInfinityPair W false ≫
          projectiveInfinityPairAdditionMorphism W) ≫
          structureMap W := by
    apply ext_of_isDominant
      (projectivePairFirstOverlapAdditionOutputOpen W false true)
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ structureMap W) hlocal
  apply ext_of_isDominant_of_isSeparated
    (structureMap W) hbase
    (projectivePairFirstOverlapAdditionOutputOpen W false true)
  simpa only [Category.assoc] using hlocal

private theorem globalProjectivePairSecondOverlapSecantZ_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairSecondOverlapAdditionOutputOpen W false true ≫
        projectivePairSecondOverlapToStandardPair W false ≫
          projectivePairInfinityStandardAdditionMorphism W =
      projectivePairSecondOverlapAdditionOutputOpen W false true ≫
        projectivePairSecondOverlapToInfinityPair W false ≫
          projectiveInfinityPairAdditionMorphism W := by
  calc
    _ = (projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
          projectivePairChartAdditionOutputOpen W (false, true) true) ≫
        projectivePairInfinityStandardAdditionMorphism W := by
          rw [projectivePairSecondOverlapAdditionOutput_standardOpen_eq,
            Category.assoc]
    _ = projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
        (projectivePairChartAdditionOutputOpen W (false, true) true ≫
          projectivePairInfinityStandardAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
        projectivePairChartAdditionOutputMorphism W
          (false, true) true := by
            rw [projectivePairInfinityStandardSecantZOpen_comp_addition]
    _ = projectivePairSecondOverlapAdditionOutputToInfinity W false true ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true :=
      projectivePairSecondOverlapAdditionOutput_morphisms_eq W false true
    _ = projectivePairSecondOverlapAdditionOutputToInfinity W false true ≫
        (projectivePairChartAdditionOutputOpen W (false, false) true ≫
          projectiveInfinityPairAdditionMorphism W) := by
            rw [projectiveInfinityPairSecantZOpen_comp_addition]
    _ = (projectivePairSecondOverlapAdditionOutputToInfinity W false true ≫
          projectivePairChartAdditionOutputOpen W (false, false) true) ≫
        projectiveInfinityPairAdditionMorphism W :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      rw [projectivePairSecondOverlapAdditionOutput_infinityOpen_eq,
        Category.assoc]

/-- The infinity-by-standard and infinity-by-infinity chart laws agree on
their entire explicit second-factor overlap. -/
theorem projectivePairSecondOverlap_infinityStandard_infinity_addition_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairSecondOverlapToStandardPair W false ≫
        projectivePairInfinityStandardAdditionMorphism W =
      projectivePairSecondOverlapToInfinityPair W false ≫
        projectiveInfinityPairAdditionMorphism W := by
  letI : IsDomain (projectivePairSecondChartOverlapCoordinateRing W false) :=
    globalProjectivePairSecondOverlap_isDomain W false
  have hlocal := globalProjectivePairSecondOverlapSecantZ_morphisms_eq W
  have hbase :
      (projectivePairSecondOverlapToStandardPair W false ≫
          projectivePairInfinityStandardAdditionMorphism W) ≫
          structureMap W =
        (projectivePairSecondOverlapToInfinityPair W false ≫
          projectiveInfinityPairAdditionMorphism W) ≫
          structureMap W := by
    apply ext_of_isDominant
      (projectivePairSecondOverlapAdditionOutputOpen W false true)
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ structureMap W) hlocal
  apply ext_of_isDominant_of_isSeparated
    (structureMap W) hbase
    (projectivePairSecondOverlapAdditionOutputOpen W false true)
  simpa only [Category.assoc] using hlocal

/-! ## The diagonal overlap of the two mixed charts -/

private noncomputable def
    globalSecondStandardOverlapToDoubleOverlapAlgHom
    (W : WeierstrassCurve K) :
    projectivePairSecondChartOverlapCoordinateRing W true →ₐ[K]
      projectivePairDoubleChartOverlapCoordinateRing W :=
  Algebra.TensorProduct.map
    (standardChartToCoveringChartOverlapAlgHom W)
    (AlgHom.id K (coveringChartOverlapCoordinateRing W))

private theorem globalDoubleOverlap_secondStandard_factor
    (W : WeierstrassCurve K) :
    (globalSecondStandardOverlapToDoubleOverlapAlgHom W).comp
        (standardPairToSecondChartOverlapAlgHom W true) =
      standardPairToDoubleOverlapAlgHom W := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [globalSecondStandardOverlapToDoubleOverlapAlgHom,
    standardPairToSecondChartOverlapAlgHom,
    standardPairToDoubleOverlapAlgHom,
    firstStandardOverlapToDoubleOverlapAlgHom,
    standardPairToFirstChartOverlapAlgHom]

private theorem globalDoubleOverlap_firstStandard_factor
    (W : WeierstrassCurve K) :
    (firstStandardOverlapToDoubleOverlapAlgHom W).comp
        (standardPairToFirstChartOverlapAlgHom W true) =
      standardPairToDoubleOverlapAlgHom W := by
  rfl

private noncomputable def
    globalProjectivePairDoubleOverlapToSecondStandardOverlap
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairSecondChartOverlapScheme W true :=
  Spec.map (CommRingCat.ofHom
    (globalSecondStandardOverlapToDoubleOverlapAlgHom W).toRingHom)

private noncomputable def
    globalProjectivePairDoubleOverlapToFirstStandardOverlap
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairFirstChartOverlapScheme W true :=
  Spec.map (CommRingCat.ofHom
    (firstStandardOverlapToDoubleOverlapAlgHom W).toRingHom)

private theorem
    globalProjectivePairDoubleOverlapToSecondStandardOverlap_comp_standard
    (W : WeierstrassCurve K) :
    globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
        projectivePairSecondOverlapToStandardPair W true =
      projectivePairDoubleOverlapToStandardPair W := by
  have hring :
      (globalSecondStandardOverlapToDoubleOverlapAlgHom W).toRingHom.comp
          (standardPairToSecondChartOverlapAlgHom W true).toRingHom =
        (standardPairToDoubleOverlapAlgHom W).toRingHom := by
    exact congrArg AlgHom.toRingHom
      (globalDoubleOverlap_secondStandard_factor W)
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, true)).hom).mp
  simp only [globalProjectivePairDoubleOverlapToSecondStandardOverlap,
    projectivePairSecondOverlapToStandardPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    projectivePairDoubleOverlapToStandardPair_comp_iso_hom]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private theorem
    globalProjectivePairDoubleOverlapToFirstStandardOverlap_comp_standard
    (W : WeierstrassCurve K) :
    globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
        projectivePairFirstOverlapToStandardPair W true =
      projectivePairDoubleOverlapToStandardPair W := by
  have hring :
      (firstStandardOverlapToDoubleOverlapAlgHom W).toRingHom.comp
          (standardPairToFirstChartOverlapAlgHom W true).toRingHom =
        (standardPairToDoubleOverlapAlgHom W).toRingHom := by
    exact congrArg AlgHom.toRingHom
      (globalDoubleOverlap_firstStandard_factor W)
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, true)).hom).mp
  simp only [globalProjectivePairDoubleOverlapToFirstStandardOverlap,
    projectivePairFirstOverlapToStandardPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    projectivePairDoubleOverlapToStandardPair_comp_iso_hom]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private noncomputable def projectivePairDoubleOverlapToStandardInfinity
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairChartScheme W (true, false) :=
  globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
    projectivePairSecondOverlapToInfinityPair W true

private noncomputable def projectivePairDoubleOverlapToInfinityStandard
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairChartScheme W (false, true) :=
  globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
    projectivePairFirstOverlapToInfinityPair W true

private theorem projectivePairDoubleOverlap_mixed_maps_eq
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToStandardInfinity W ≫
        projectivePairChartMap W (true, false) =
      projectivePairDoubleOverlapToInfinityStandard W ≫
        projectivePairChartMap W (false, true) := by
  calc
    _ = globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
        (projectivePairSecondOverlapToInfinityPair W true ≫
          projectivePairChartMap W (true, false)) :=
      Category.assoc _ _ _
    _ = globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
        (projectivePairSecondOverlapToStandardPair W true ≫
          projectivePairChartMap W (true, true)) := by
            rw [projectivePairSecondOverlap_maps_eq]
    _ = (globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
          projectivePairSecondOverlapToStandardPair W true) ≫
        projectivePairChartMap W (true, true) :=
      (Category.assoc _ _ _).symm
    _ = projectivePairDoubleOverlapToStandardPair W ≫
        projectivePairChartMap W (true, true) := by
          rw [globalProjectivePairDoubleOverlapToSecondStandardOverlap_comp_standard]
    _ = (globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
          projectivePairFirstOverlapToStandardPair W true) ≫
        projectivePairChartMap W (true, true) := by
          rw [globalProjectivePairDoubleOverlapToFirstStandardOverlap_comp_standard]
    _ = globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
        (projectivePairFirstOverlapToStandardPair W true ≫
          projectivePairChartMap W (true, true)) :=
      Category.assoc _ _ _
    _ = globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
        (projectivePairFirstOverlapToInfinityPair W true ≫
          projectivePairChartMap W (false, true)) := by
            rw [projectivePairFirstOverlap_maps_eq]
    _ = _ := (Category.assoc _ _ _).symm

private theorem projectivePairDoubleOverlap_mixed_addition_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairDoubleOverlapToStandardInfinity W ≫
        projectivePairStandardInfinityAdditionMorphism W =
      projectivePairDoubleOverlapToInfinityStandard W ≫
        projectivePairInfinityStandardAdditionMorphism W := by
  calc
    _ = globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
        (projectivePairSecondOverlapToInfinityPair W true ≫
          projectivePairStandardInfinityAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
        (projectivePairSecondOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) := by
            rw [projectivePairSecondOverlapToInfinityPair_comp_standardInfinityAddition]
    _ = (globalProjectivePairDoubleOverlapToSecondStandardOverlap W ≫
          projectivePairSecondOverlapToStandardPair W true) ≫
        standardPairAdditionMorphism W :=
      (Category.assoc _ _ _).symm
    _ = projectivePairDoubleOverlapToStandardPair W ≫
        standardPairAdditionMorphism W := by
          rw [globalProjectivePairDoubleOverlapToSecondStandardOverlap_comp_standard]
    _ = (globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
          projectivePairFirstOverlapToStandardPair W true) ≫
        standardPairAdditionMorphism W := by
          rw [globalProjectivePairDoubleOverlapToFirstStandardOverlap_comp_standard]
    _ = globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
        (projectivePairFirstOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = globalProjectivePairDoubleOverlapToFirstStandardOverlap W ≫
        (projectivePairFirstOverlapToInfinityPair W true ≫
          projectivePairInfinityStandardAdditionMorphism W) := by
            rw [projectivePairFirstOverlapToInfinityPair_comp_infinityStandardAddition]
    _ = _ := (Category.assoc _ _ _).symm

private instance
    globalProjectivePairDoubleOverlapToFirstStandardOverlap_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (globalProjectivePairDoubleOverlapToFirstStandardOverlap W) := by
  letI := (firstStandardOverlapToDoubleOverlapAlgHom W).toAlgebra
  haveI := doubleOverlap_isLocalization_secondStandardOverlap W
  exact IsOpenImmersion.of_isLocalization
    (Algebra.TensorProduct.includeRight
      (R := K)
      (A := coveringChartOverlapCoordinateRing W)
      (B := coveringChartCoordinateRing W true)
      (Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (K := K) 2 1)))

private instance projectivePairDoubleOverlapToInfinityStandard_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectivePairDoubleOverlapToInfinityStandard W) := by
  dsimp only [projectivePairDoubleOverlapToInfinityStandard]
  infer_instance

/-! ## Categorical intersections of the four product charts -/

private theorem globalCompatibility_of_explicit_open
    {U A B X Y S : Scheme.{u}}
    (a : U ⟶ A) (b : U ⟶ B) (i : A ⟶ X) (j : B ⟶ X)
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Y ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion i] [IsOpenImmersion j]
    [Nonempty U] [IsSeparated p] [S.IsSeparated]
    (hA : IsIntegral A)
    (hambient : a ≫ i = b ≫ j)
    (hlaw : a ≫ f = b ≫ g) :
    pullback.fst i j ≫ f = pullback.snd i j ≫ g := by
  classical
  letI : IsIntegral A := hA
  let e : U ⟶ pullback i j := pullback.lift a b hambient
  haveI : IsOpenImmersion (e ≫ pullback.fst i j) := by
    rw [show e ≫ pullback.fst i j = a by
      dsimp only [e]
      exact pullback.lift_fst _ _ _]
    infer_instance
  haveI : IsOpenImmersion e :=
    IsOpenImmersion.of_comp e (pullback.fst i j)
  cases isEmpty_or_nonempty (pullback i j : Scheme.{u}) with
  | inl hempty =>
      letI := hempty
      exact (isInitialOfIsEmpty (X := pullback i j)).hom_ext _ _
  | inr hnonempty =>
      letI := hnonempty
      letI : IsIntegral (pullback i j) :=
        isIntegral_of_isOpenImmersion (pullback.fst i j)
      letI : IsDominant e := by
        constructor
        have hopen := e.isOpenEmbedding.isOpenMap
        exact hopen.denseRange_of_isPreirreducibleSpace _
      have heq :
          e ≫ (pullback.fst i j ≫ f) =
            e ≫ (pullback.snd i j ≫ g) := by
        simpa only [← Category.assoc, e, pullback.lift_fst,
          pullback.lift_snd] using hlaw
      have hbase :
          (pullback.fst i j ≫ f) ≫ p =
            (pullback.snd i j ≫ g) ≫ p := by
        apply ext_of_isDominant e
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ p) heq
      apply ext_of_isDominant_of_isSeparated p hbase e
      exact heq

/-- The standard-by-standard and standard-by-infinity chart laws agree on
their categorical intersection in the full projective product. -/
theorem projectivePairStandardSecondTransition_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairChartMap W (true, true))
          (projectivePairChartMap W (true, false)) ≫
        standardPairAdditionMorphism W =
      pullback.snd
          (projectivePairChartMap W (true, true))
          (projectivePairChartMap W (true, false)) ≫
        projectivePairStandardInfinityAdditionMorphism W := by
  exact globalCompatibility_of_explicit_open
    (projectivePairSecondOverlapToStandardPair W true)
    (projectivePairSecondOverlapToInfinityPair W true)
    (projectivePairChartMap W (true, true))
    (projectivePairChartMap W (true, false))
    (standardPairAdditionMorphism W)
    (projectivePairStandardInfinityAdditionMorphism W)
    (structureMap W)
    (globalProjectivePairChart_isIntegral W (true, true))
    (projectivePairSecondOverlap_maps_eq W true)
    (projectivePairSecondOverlapToInfinityPair_comp_standardInfinityAddition W).symm

/-- The standard-by-standard and infinity-by-standard chart laws agree on
their categorical intersection in the full projective product. -/
theorem projectivePairStandardFirstTransition_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairChartMap W (true, true))
          (projectivePairChartMap W (false, true)) ≫
        standardPairAdditionMorphism W =
      pullback.snd
          (projectivePairChartMap W (true, true))
          (projectivePairChartMap W (false, true)) ≫
        projectivePairInfinityStandardAdditionMorphism W := by
  exact globalCompatibility_of_explicit_open
    (projectivePairFirstOverlapToStandardPair W true)
    (projectivePairFirstOverlapToInfinityPair W true)
    (projectivePairChartMap W (true, true))
    (projectivePairChartMap W (false, true))
    (standardPairAdditionMorphism W)
    (projectivePairInfinityStandardAdditionMorphism W)
    (structureMap W)
    (globalProjectivePairChart_isIntegral W (true, true))
    (projectivePairFirstOverlap_maps_eq W true)
    (projectivePairFirstOverlapToInfinityPair_comp_infinityStandardAddition W).symm

/-- The standard-by-standard and infinity-by-infinity chart laws agree on
their diagonal categorical intersection. -/
theorem projectivePairStandardInfinityDiagonal_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairChartMap W (true, true))
          (projectivePairChartMap W (false, false)) ≫
        standardPairAdditionMorphism W =
      pullback.snd
          (projectivePairChartMap W (true, true))
          (projectivePairChartMap W (false, false)) ≫
        projectiveInfinityPairAdditionMorphism W := by
  exact globalCompatibility_of_explicit_open
    (projectivePairDoubleOverlapToStandardPair W)
    (projectivePairDoubleOverlapToInfinityPair W)
    (projectivePairChartMap W (true, true))
    (projectivePairChartMap W (false, false))
    (standardPairAdditionMorphism W)
    (projectiveInfinityPairAdditionMorphism W)
    (structureMap W)
    (globalProjectivePairChart_isIntegral W (true, true))
    (projectivePairDoubleOverlap_maps_eq W)
    (projectivePairDoubleOverlapToInfinityPair_comp_addition W).symm

/-- The two mixed chart laws agree on their diagonal categorical
intersection. -/
theorem projectivePairMixedDiagonal_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairChartMap W (false, true))
          (projectivePairChartMap W (true, false)) ≫
        projectivePairInfinityStandardAdditionMorphism W =
      pullback.snd
          (projectivePairChartMap W (false, true))
          (projectivePairChartMap W (true, false)) ≫
        projectivePairStandardInfinityAdditionMorphism W := by
  exact globalCompatibility_of_explicit_open
    (projectivePairDoubleOverlapToInfinityStandard W)
    (projectivePairDoubleOverlapToStandardInfinity W)
    (projectivePairChartMap W (false, true))
    (projectivePairChartMap W (true, false))
    (projectivePairInfinityStandardAdditionMorphism W)
    (projectivePairStandardInfinityAdditionMorphism W)
    (structureMap W)
    (globalProjectivePairChart_isIntegral W (false, true))
    (projectivePairDoubleOverlap_mixed_maps_eq W).symm
    (projectivePairDoubleOverlap_mixed_addition_eq W).symm

/-- The standard-by-infinity and infinity-by-infinity chart laws agree on
their categorical first-factor intersection. -/
theorem projectivePairStandardInfinityFirstTransition_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairChartMap W (true, false))
          (projectivePairChartMap W (false, false)) ≫
        projectivePairStandardInfinityAdditionMorphism W =
      pullback.snd
          (projectivePairChartMap W (true, false))
          (projectivePairChartMap W (false, false)) ≫
        projectiveInfinityPairAdditionMorphism W := by
  exact globalCompatibility_of_explicit_open
    (projectivePairFirstOverlapToStandardPair W false)
    (projectivePairFirstOverlapToInfinityPair W false)
    (projectivePairChartMap W (true, false))
    (projectivePairChartMap W (false, false))
    (projectivePairStandardInfinityAdditionMorphism W)
    (projectiveInfinityPairAdditionMorphism W)
    (structureMap W)
    (globalProjectivePairChart_isIntegral W (true, false))
    (projectivePairFirstOverlap_maps_eq W false)
    (projectivePairFirstOverlap_standardInfinity_infinity_addition_eq W)

/-- The infinity-by-standard and infinity-by-infinity chart laws agree on
their categorical second-factor intersection. -/
theorem projectivePairInfinityStandardSecondTransition_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairChartMap W (false, true))
          (projectivePairChartMap W (false, false)) ≫
        projectivePairInfinityStandardAdditionMorphism W =
      pullback.snd
          (projectivePairChartMap W (false, true))
          (projectivePairChartMap W (false, false)) ≫
        projectiveInfinityPairAdditionMorphism W := by
  exact globalCompatibility_of_explicit_open
    (projectivePairSecondOverlapToStandardPair W false)
    (projectivePairSecondOverlapToInfinityPair W false)
    (projectivePairChartMap W (false, true))
    (projectivePairChartMap W (false, false))
    (projectivePairInfinityStandardAdditionMorphism W)
    (projectiveInfinityPairAdditionMorphism W)
    (structureMap W)
    (globalProjectivePairChart_isIntegral W (false, true))
    (projectivePairSecondOverlap_maps_eq W false)
    (projectivePairSecondOverlap_infinityStandard_infinity_addition_eq W)

/-! ## Four-chart compatibility and global gluing -/

/-- Select the genuine addition morphism on each member of the four-chart
projective-pair cover. -/
noncomputable def projectivePairAdditionChartMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∀ ij : Bool × Bool,
      projectivePairChartScheme W ij ⟶ scheme W
  | (true, true) => standardPairAdditionMorphism W
  | (true, false) => projectivePairStandardInfinityAdditionMorphism W
  | (false, true) => projectivePairInfinityStandardAdditionMorphism W
  | (false, false) => projectiveInfinityPairAdditionMorphism W

/-- The four selected chart laws satisfy the open-cover compatibility
condition on all sixteen ordered pairs of chart members. -/
theorem projectivePairAdditionChartMorphism_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : Bool × Bool) :
    pullback.fst
          (projectivePairChartMap W i)
          (projectivePairChartMap W j) ≫
        projectivePairAdditionChartMorphism W i =
      pullback.snd
          (projectivePairChartMap W i)
          (projectivePairChartMap W j) ≫
        projectivePairAdditionChartMorphism W j := by
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂
  all_goals simp only [projectivePairAdditionChartMorphism]
  · exact globalPullback_morphism_compatible_self _ _
  · exact globalPullback_morphism_compatible_symm _ _ _ _
      (projectivePairInfinityStandardSecondTransition_compatible W)
  · exact globalPullback_morphism_compatible_symm _ _ _ _
      (projectivePairStandardInfinityFirstTransition_compatible W)
  · exact globalPullback_morphism_compatible_symm _ _ _ _
      (projectivePairStandardInfinityDiagonal_compatible W)
  · exact projectivePairInfinityStandardSecondTransition_compatible W
  · exact globalPullback_morphism_compatible_self _ _
  · exact projectivePairMixedDiagonal_compatible W
  · exact globalPullback_morphism_compatible_symm _ _ _ _
      (projectivePairStandardFirstTransition_compatible W)
  · exact projectivePairStandardInfinityFirstTransition_compatible W
  · exact globalPullback_morphism_compatible_symm _ _ _ _
      (projectivePairMixedDiagonal_compatible W)
  · exact globalPullback_morphism_compatible_self _ _
  · exact globalPullback_morphism_compatible_symm _ _ _ _
      (projectivePairStandardSecondTransition_compatible W)
  · exact projectivePairStandardInfinityDiagonal_compatible W
  · exact projectivePairStandardFirstTransition_compatible W
  · exact projectivePairStandardSecondTransition_compatible W
  · exact globalPullback_morphism_compatible_self _ _

private theorem projectivePairOpenCover_addition_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : (projectivePairOpenCover W).I₀) :
    pullback.fst
          ((projectivePairOpenCover W).f i)
          ((projectivePairOpenCover W).f j) ≫
        projectivePairAdditionChartMorphism W i =
      pullback.snd
          ((projectivePairOpenCover W).f i)
          ((projectivePairOpenCover W).f j) ≫
        projectivePairAdditionChartMorphism W j := by
  exact projectivePairAdditionChartMorphism_compatible W i j

/-- The globally glued addition morphism on the full fibre square of the
projective Weierstrass cubic. -/
noncomputable def projectiveAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePair W ⟶ scheme W :=
  (projectivePairOpenCover W).glueMorphisms
    (projectivePairAdditionChartMorphism W)
    (projectivePairOpenCover_addition_compatible W)

/-- The global addition morphism restricts to the selected law on every
member of the four-chart projective-pair cover. -/
@[reassoc]
theorem projectivePairChartMap_comp_projectiveAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    projectivePairChartMap W ij ≫ projectiveAdditionMorphism W =
      projectivePairAdditionChartMorphism W ij := by
  exact (projectivePairOpenCover W).ι_glueMorphisms
    (projectivePairAdditionChartMorphism W)
    (projectivePairOpenCover_addition_compatible W) ij

/-- On the standard-by-standard chart, global addition is the previously
checked affine-atlas law. -/
@[reassoc]
theorem projectivePairStandardChart_comp_projectiveAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartMap W (true, true) ≫ projectiveAdditionMorphism W =
      standardPairAdditionMorphism W := by
  exact projectivePairChartMap_comp_projectiveAdditionMorphism W (true, true)

/-- On the standard-by-infinity chart, global addition is the glued mixed
law. -/
@[reassoc]
theorem projectivePairStandardInfinityChart_comp_projectiveAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartMap W (true, false) ≫ projectiveAdditionMorphism W =
      projectivePairStandardInfinityAdditionMorphism W := by
  exact projectivePairChartMap_comp_projectiveAdditionMorphism W (true, false)

/-- On the infinity-by-standard chart, global addition is the glued mixed
law. -/
@[reassoc]
theorem projectivePairInfinityStandardChart_comp_projectiveAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartMap W (false, true) ≫ projectiveAdditionMorphism W =
      projectivePairInfinityStandardAdditionMorphism W := by
  exact projectivePairChartMap_comp_projectiveAdditionMorphism W (false, true)

/-- On the infinity-by-infinity chart, global addition is the glued
infinity-pair law. -/
@[reassoc]
theorem projectivePairInfinityChart_comp_projectiveAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartMap W (false, false) ≫ projectiveAdditionMorphism W =
      projectiveInfinityPairAdditionMorphism W := by
  exact projectivePairChartMap_comp_projectiveAdditionMorphism W (false, false)

/-! ## Compatibility with the structural morphism -/

/-- The structural morphism of the projective pair, taken through its first
projection. -/
noncomputable def projectivePairStructureMap
    (W : WeierstrassCurve K) :
    projectivePair W ⟶ Spec (.of K) :=
  pullback.fst (structureMap W) (structureMap W) ≫ structureMap W

@[reassoc]
private theorem projectivePairChartMap_comp_projectivePairStructureMap
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartMap W ij ≫ projectivePairStructureMap W =
      pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W ij.1)) := by
  calc
    _ = (projectivePairChartMap W ij ≫
          pullback.fst (structureMap W) (structureMap W)) ≫
        structureMap W := by
          rw [projectivePairStructureMap, Category.assoc]
    _ = (pullback.fst
            (coveringChartMap W ij.1 ≫ structureMap W)
            (coveringChartMap W ij.2 ≫ structureMap W) ≫
          coveringChartMap W ij.1) ≫ structureMap W := by
            rw [projectivePairChartMap_comp_fst]
    _ = pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        (coveringChartMap W ij.1 ≫ structureMap W) :=
      Category.assoc _ _ _
    _ = _ := congrArg
      (fun q => pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫ q)
      (coveringChartMap_comp_structureMap W ij.1)

private theorem standardPairAdditionMorphism_comp_projectivePairStructureMap
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardPairAdditionMorphism W ≫ structureMap W =
      projectivePairChartMap W (true, true) ≫
        projectivePairStructureMap W := by
  rw [standardPairAdditionMorphism_comp_structureMap,
    ← projectivePairChartIsoSpecTensor_hom_comp_standardPairCoordinateRingAlgEquiv_specMap,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hring :
      (standardPairCoordinateRingAlgEquiv W).toRingHom.comp
          (algebraMap K (secantPairCoordinateRing W)) =
        algebraMap K (projectivePairChartCoordinateRing W (true, true)) := by
    apply RingHom.ext
    intro a
    exact (standardPairCoordinateRingAlgEquiv W).commutes a
  rw [hring, projectivePairChartIsoSpecTensor_hom_base,
    projectivePairChartMap_comp_projectivePairStructureMap]

private theorem globalDominant_of_nonempty_open
    {U X : Scheme.{u}} (i : U ⟶ X)
    [IsOpenImmersion i] [Nonempty U] [IsIntegral X] :
    IsDominant i := by
  constructor
  have hopen := i.isOpenEmbedding.isOpenMap
  exact hopen.denseRange_of_isPreirreducibleSpace _

private theorem
    projectivePairStandardInfinityAdditionMorphism_comp_projectivePairStructureMap
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairStandardInfinityAdditionMorphism W ≫ structureMap W =
      projectivePairChartMap W (true, false) ≫
        projectivePairStructureMap W := by
  letI : IsIntegral (projectivePairChartScheme W (true, false)) :=
    globalProjectivePairChart_isIntegral W (true, false)
  letI : IsDominant
      (projectivePairSecondOverlapToInfinityPair W true) :=
    globalDominant_of_nonempty_open
      (projectivePairSecondOverlapToInfinityPair W true)
  apply ext_of_isDominant (projectivePairSecondOverlapToInfinityPair W true)
  calc
    _ = (projectivePairSecondOverlapToInfinityPair W true ≫
          projectivePairStandardInfinityAdditionMorphism W) ≫
        structureMap W := (Category.assoc _ _ _).symm
    _ = (projectivePairSecondOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) ≫ structureMap W := by
            rw [projectivePairSecondOverlapToInfinityPair_comp_standardInfinityAddition]
    _ = projectivePairSecondOverlapToStandardPair W true ≫
        (standardPairAdditionMorphism W ≫ structureMap W) :=
      Category.assoc _ _ _
    _ = projectivePairSecondOverlapToStandardPair W true ≫
        (projectivePairChartMap W (true, true) ≫
          projectivePairStructureMap W) := by
            rw [standardPairAdditionMorphism_comp_projectivePairStructureMap]
    _ = (projectivePairSecondOverlapToStandardPair W true ≫
          projectivePairChartMap W (true, true)) ≫
        projectivePairStructureMap W := (Category.assoc _ _ _).symm
    _ = (projectivePairSecondOverlapToInfinityPair W true ≫
          projectivePairChartMap W (true, false)) ≫
        projectivePairStructureMap W := by
            rw [projectivePairSecondOverlap_maps_eq]
    _ = _ := Category.assoc _ _ _

private theorem
    projectivePairInfinityStandardAdditionMorphism_comp_projectivePairStructureMap
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairInfinityStandardAdditionMorphism W ≫ structureMap W =
      projectivePairChartMap W (false, true) ≫
        projectivePairStructureMap W := by
  letI : IsIntegral (projectivePairChartScheme W (false, true)) :=
    globalProjectivePairChart_isIntegral W (false, true)
  letI : IsDominant
      (projectivePairFirstOverlapToInfinityPair W true) :=
    globalDominant_of_nonempty_open
      (projectivePairFirstOverlapToInfinityPair W true)
  apply ext_of_isDominant (projectivePairFirstOverlapToInfinityPair W true)
  calc
    _ = (projectivePairFirstOverlapToInfinityPair W true ≫
          projectivePairInfinityStandardAdditionMorphism W) ≫
        structureMap W := (Category.assoc _ _ _).symm
    _ = (projectivePairFirstOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) ≫ structureMap W := by
            rw [projectivePairFirstOverlapToInfinityPair_comp_infinityStandardAddition]
    _ = projectivePairFirstOverlapToStandardPair W true ≫
        (standardPairAdditionMorphism W ≫ structureMap W) :=
      Category.assoc _ _ _
    _ = projectivePairFirstOverlapToStandardPair W true ≫
        (projectivePairChartMap W (true, true) ≫
          projectivePairStructureMap W) := by
            rw [standardPairAdditionMorphism_comp_projectivePairStructureMap]
    _ = (projectivePairFirstOverlapToStandardPair W true ≫
          projectivePairChartMap W (true, true)) ≫
        projectivePairStructureMap W := (Category.assoc _ _ _).symm
    _ = (projectivePairFirstOverlapToInfinityPair W true ≫
          projectivePairChartMap W (false, true)) ≫
        projectivePairStructureMap W := by
            rw [projectivePairFirstOverlap_maps_eq]
    _ = _ := Category.assoc _ _ _

private theorem
    projectiveInfinityPairAdditionMorphism_comp_projectivePairStructureMap
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveInfinityPairAdditionMorphism W ≫ structureMap W =
      projectivePairChartMap W (false, false) ≫
        projectivePairStructureMap W := by
  letI : IsIntegral (projectivePairChartScheme W (false, false)) :=
    globalProjectivePairChart_isIntegral W (false, false)
  letI : IsDominant (projectivePairDoubleOverlapToInfinityPair W) :=
    globalDominant_of_nonempty_open
      (projectivePairDoubleOverlapToInfinityPair W)
  apply ext_of_isDominant (projectivePairDoubleOverlapToInfinityPair W)
  calc
    _ = (projectivePairDoubleOverlapToInfinityPair W ≫
          projectiveInfinityPairAdditionMorphism W) ≫
        structureMap W := (Category.assoc _ _ _).symm
    _ = (projectivePairDoubleOverlapToStandardPair W ≫
          standardPairAdditionMorphism W) ≫ structureMap W := by
            rw [projectivePairDoubleOverlapToInfinityPair_comp_addition]
    _ = projectivePairDoubleOverlapToStandardPair W ≫
        (standardPairAdditionMorphism W ≫ structureMap W) :=
      Category.assoc _ _ _
    _ = projectivePairDoubleOverlapToStandardPair W ≫
        (projectivePairChartMap W (true, true) ≫
          projectivePairStructureMap W) := by
            rw [standardPairAdditionMorphism_comp_projectivePairStructureMap]
    _ = (projectivePairDoubleOverlapToStandardPair W ≫
          projectivePairChartMap W (true, true)) ≫
        projectivePairStructureMap W := (Category.assoc _ _ _).symm
    _ = (projectivePairDoubleOverlapToInfinityPair W ≫
          projectivePairChartMap W (false, false)) ≫
        projectivePairStructureMap W := by
            rw [projectivePairDoubleOverlap_maps_eq]
    _ = _ := Category.assoc _ _ _

/-- Every selected chart law is a morphism over the coefficient field, with
respect to the structural morphism inherited from the full projective pair. -/
theorem projectivePairAdditionChartMorphism_comp_structureMap
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    projectivePairAdditionChartMorphism W ij ≫ structureMap W =
      projectivePairChartMap W ij ≫ projectivePairStructureMap W := by
  rcases ij with ⟨i, j⟩
  cases i <;> cases j
  · exact projectiveInfinityPairAdditionMorphism_comp_projectivePairStructureMap W
  · exact projectivePairInfinityStandardAdditionMorphism_comp_projectivePairStructureMap W
  · exact projectivePairStandardInfinityAdditionMorphism_comp_projectivePairStructureMap W
  · exact standardPairAdditionMorphism_comp_projectivePairStructureMap W

/-- Global projective addition is a morphism over `Spec K`. -/
@[reassoc]
theorem projectiveAdditionMorphism_comp_structureMap
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveAdditionMorphism W ≫ structureMap W =
      projectivePairStructureMap W := by
  apply (projectivePairOpenCover W).hom_ext
  intro ij
  change Bool × Bool at ij
  calc
    _ = (projectivePairChartMap W ij ≫
          projectiveAdditionMorphism W) ≫ structureMap W :=
      (Category.assoc _ _ _).symm
    _ = projectivePairAdditionChartMorphism W ij ≫
        structureMap W := by
          rw [projectivePairChartMap_comp_projectiveAdditionMorphism]
    _ = projectivePairChartMap W ij ≫ projectivePairStructureMap W :=
      projectivePairAdditionChartMorphism_comp_structureMap W ij

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
