/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductSecondInputOverlap
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Source-overlap schemes for the projective Weierstrass product atlas

Localization at either transition coordinate survives tensoring with an
unchanged chart factor.  This file therefore promotes both factorwise
coordinate-ring transitions to actual open immersions between adjacent
members of the four-chart projective-pair atlas.

The design boundary is geometric equality inside the full projective product.
The named downstream consumers `projectivePairFirstOverlap_maps_eq` and
`projectivePairSecondOverlap_maps_eq` prove that the two descriptions of each
factorwise overlap have the same composite into the global pair.  Later
addition gluing can consequently compare local formulas on these explicit
common source schemes rather than on an abstractly supplied intersection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem isLocalizationAway_tensorProduct_left
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra K A] [Algebra K B] [Algebra K S]
    (f : A →ₐ[K] B) (r : A)
    (h : letI := f.toAlgebra; IsLocalization.Away r B) :
    letI := (Algebra.TensorProduct.map f (AlgHom.id K S)).toAlgebra
    IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := A) (B := S) r)
      (TensorProduct K B S) := by
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower K A B :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  letI : IsLocalization.Away r B := h
  letI : Algebra (TensorProduct K A S) (TensorProduct K B S) :=
    (Algebra.TensorProduct.map f (AlgHom.id K S)).toAlgebra
  letI : IsScalarTower A (TensorProduct K A S)
      (TensorProduct K B S) := by
    constructor
    intro a x y
    change (Algebra.TensorProduct.map f (AlgHom.id K S)) (a • x) * y =
      a • ((Algebra.TensorProduct.map f (AlgHom.id K S)) x * y)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
        change (f (a * b) ⊗ₜ[K] c) * y =
          a • ((f b ⊗ₜ[K] c) * y)
        rw [← smul_mul_assoc, TensorProduct.smul_tmul',
          Algebra.smul_def, map_mul]
        rw [RingHom.algebraMap_toAlgebra]
        rfl
    | add x z hx hz =>
        simp [smul_add, map_add, add_mul, hx, hz]
  change IsLocalization
    (Submonoid.powers
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := A) (B := S) r))
    (TensorProduct K B S)
  rw [← Submonoid.map_powers]
  refine IsLocalization.tensorProduct_tensorProduct K S
    (Submonoid.powers r) B ?_
  apply RingHom.ext
  intro x
  change (Algebra.TensorProduct.map f (AlgHom.id K S))
      (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight x
  have hx := congrArg (fun g => g x)
    (Algebra.TensorProduct.map_comp_includeRight f (AlgHom.id K S))
  exact hx

private theorem isLocalizationAway_tensorProduct_right
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra K A] [Algebra K B] [Algebra K S]
    (f : A →ₐ[K] B) (r : A)
    (h : letI := f.toAlgebra; IsLocalization.Away r B) :
    letI := (Algebra.TensorProduct.map (AlgHom.id K S) f).toAlgebra
    IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K) (A := S) (B := A) r)
      (TensorProduct K S B) := by
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower K A B :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  letI : IsLocalization.Away r B := h
  letI : Algebra (TensorProduct K S A) (TensorProduct K S B) :=
    (Algebra.TensorProduct.map (AlgHom.id K S) f).toAlgebra
  letI : IsScalarTower S (TensorProduct K S A)
      (TensorProduct K S B) := by
    constructor
    intro a x y
    change (Algebra.TensorProduct.map (AlgHom.id K S) f) (a • x) * y =
      a • ((Algebra.TensorProduct.map (AlgHom.id K S) f) x * y)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
        change ((a * b) ⊗ₜ[K] f c) * y =
          a • ((b ⊗ₜ[K] f c) * y)
        rw [← smul_mul_assoc, TensorProduct.smul_tmul']
        rfl
    | add x z hx hz =>
        simp [smul_add, map_add, add_mul, hx, hz]
  change IsLocalization
    (Submonoid.powers
      (Algebra.TensorProduct.includeRight
        (R := K) (A := S) (B := A) r))
    (TensorProduct K S B)
  rw [← Submonoid.map_powers]
  refine IsLocalization.tensorProduct_tensorProduct_right K S
    (Submonoid.powers r) B ?_
  apply RingHom.ext
  intro x
  change (Algebra.TensorProduct.map (AlgHom.id K S) f)
      (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight (f x)
  have hx := congrArg (fun g => g x)
    (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id K S) f)
  exact hx

noncomputable instance projectivePairFirstOverlapAlgebraStandardPair
    (W : WeierstrassCurve K) (j : Bool) :
    Algebra (projectivePairChartCoordinateRing W (true, j))
      (projectivePairFirstChartOverlapCoordinateRing W j) :=
  (standardPairToFirstChartOverlapAlgHom W j).toAlgebra

theorem projectivePairFirstOverlap_isLocalization_standardPair
    (W : WeierstrassCurve K) (j : Bool) :
    IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairFirstChartOverlapCoordinateRing W j) := by
  exact isLocalizationAway_tensorProduct_left
    (f := standardChartToCoveringChartOverlapAlgHom W)
    (r := Ideal.Quotient.mk (coveringChartIdeal W true)
      (coordinateChartRatio (K := K) 2 1))
    (coveringChartOverlap_isLocalization_standardChart W)

noncomputable instance projectivePairFirstOverlapAlgebraInfinityPair
    (W : WeierstrassCurve K) (j : Bool) :
    Algebra (projectivePairChartCoordinateRing W (false, j))
      (projectivePairFirstChartOverlapCoordinateRing W j) :=
  (infinityPairToFirstChartOverlapAlgHom W j).toAlgebra

theorem projectivePairFirstOverlap_isLocalization_infinityPair
    (W : WeierstrassCurve K) (j : Bool) :
    IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W false)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
      (projectivePairFirstChartOverlapCoordinateRing W j) := by
  exact isLocalizationAway_tensorProduct_left
    (f := infinityChartToCoveringChartOverlapAlgHom W)
    (r := Ideal.Quotient.mk (coveringChartIdeal W false)
      (coordinateChartRatio (K := K) 1 2))
    (coveringChartOverlap_isLocalization_infinityChart W)

noncomputable instance projectivePairSecondOverlapAlgebraStandardPair
    (W : WeierstrassCurve K) (i : Bool) :
    Algebra (projectivePairChartCoordinateRing W (i, true))
      (projectivePairSecondChartOverlapCoordinateRing W i) :=
  (standardPairToSecondChartOverlapAlgHom W i).toAlgebra

theorem projectivePairSecondOverlap_isLocalization_standardPair
    (W : WeierstrassCurve K) (i : Bool) :
    IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairSecondChartOverlapCoordinateRing W i) := by
  exact isLocalizationAway_tensorProduct_right
    (f := standardChartToCoveringChartOverlapAlgHom W)
    (r := Ideal.Quotient.mk (coveringChartIdeal W true)
      (coordinateChartRatio (K := K) 2 1))
    (coveringChartOverlap_isLocalization_standardChart W)

noncomputable instance projectivePairSecondOverlapAlgebraInfinityPair
    (W : WeierstrassCurve K) (i : Bool) :
    Algebra (projectivePairChartCoordinateRing W (i, false))
      (projectivePairSecondChartOverlapCoordinateRing W i) :=
  (infinityPairToSecondChartOverlapAlgHom W i).toAlgebra

theorem projectivePairSecondOverlap_isLocalization_infinityPair
    (W : WeierstrassCurve K) (i : Bool) :
    IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W false)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
      (projectivePairSecondChartOverlapCoordinateRing W i) := by
  exact isLocalizationAway_tensorProduct_right
    (f := infinityChartToCoveringChartOverlapAlgHom W)
    (r := Ideal.Quotient.mk (coveringChartIdeal W false)
      (coordinateChartRatio (K := K) 1 2))
    (coveringChartOverlap_isLocalization_infinityChart W)

/-! ## Actual overlap schemes and their chart maps -/

/-- The affine first-factor overlap of adjacent projective-pair charts. -/
abbrev projectivePairFirstChartOverlapScheme
    (W : WeierstrassCurve K) (j : Bool) : Scheme.{u} :=
  Spec (.of (projectivePairFirstChartOverlapCoordinateRing W j))

/-- Map the first-factor overlap into the standard-by-`j` pair chart. -/
noncomputable def projectivePairFirstOverlapToStandardPair
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstChartOverlapScheme W j ⟶
      projectivePairChartScheme W (true, j) :=
  Spec.map (CommRingCat.ofHom
      (standardPairToFirstChartOverlapAlgHom W j).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (true, j)).inv

instance projectivePairFirstOverlapToStandardPair_isOpenImmersion
    (W : WeierstrassCurve K) (j : Bool) :
    IsOpenImmersion (projectivePairFirstOverlapToStandardPair W j) := by
  letI : IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairFirstChartOverlapCoordinateRing W j) :=
    projectivePairFirstOverlap_isLocalization_standardPair W j
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (standardPairToFirstChartOverlapAlgHom W j).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
  dsimp only [projectivePairFirstOverlapToStandardPair]
  infer_instance

/-- Map the first-factor overlap into the infinity-by-`j` pair chart. -/
noncomputable def projectivePairFirstOverlapToInfinityPair
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstChartOverlapScheme W j ⟶
      projectivePairChartScheme W (false, j) :=
  Spec.map (CommRingCat.ofHom
      (infinityPairToFirstChartOverlapAlgHom W j).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (false, j)).inv

instance projectivePairFirstOverlapToInfinityPair_isOpenImmersion
    (W : WeierstrassCurve K) (j : Bool) :
    IsOpenImmersion (projectivePairFirstOverlapToInfinityPair W j) := by
  letI : IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W false)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
      (projectivePairFirstChartOverlapCoordinateRing W j) :=
    projectivePairFirstOverlap_isLocalization_infinityPair W j
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (infinityPairToFirstChartOverlapAlgHom W j).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W false)
        (B := coveringChartCoordinateRing W j)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
  dsimp only [projectivePairFirstOverlapToInfinityPair]
  infer_instance

/-- The affine second-factor overlap of adjacent projective-pair charts. -/
abbrev projectivePairSecondChartOverlapScheme
    (W : WeierstrassCurve K) (i : Bool) : Scheme.{u} :=
  Spec (.of (projectivePairSecondChartOverlapCoordinateRing W i))

/-- Map the second-factor overlap into the `i`-by-standard pair chart. -/
noncomputable def projectivePairSecondOverlapToStandardPair
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondChartOverlapScheme W i ⟶
      projectivePairChartScheme W (i, true) :=
  Spec.map (CommRingCat.ofHom
      (standardPairToSecondChartOverlapAlgHom W i).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (i, true)).inv

instance projectivePairSecondOverlapToStandardPair_isOpenImmersion
    (W : WeierstrassCurve K) (i : Bool) :
    IsOpenImmersion (projectivePairSecondOverlapToStandardPair W i) := by
  letI : IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairSecondChartOverlapCoordinateRing W i) :=
    projectivePairSecondOverlap_isLocalization_standardPair W i
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (standardPairToSecondChartOverlapAlgHom W i).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
  dsimp only [projectivePairSecondOverlapToStandardPair]
  infer_instance

/-- Map the second-factor overlap into the `i`-by-infinity pair chart. -/
noncomputable def projectivePairSecondOverlapToInfinityPair
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondChartOverlapScheme W i ⟶
      projectivePairChartScheme W (i, false) :=
  Spec.map (CommRingCat.ofHom
      (infinityPairToSecondChartOverlapAlgHom W i).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (i, false)).inv

instance projectivePairSecondOverlapToInfinityPair_isOpenImmersion
    (W : WeierstrassCurve K) (i : Bool) :
    IsOpenImmersion (projectivePairSecondOverlapToInfinityPair W i) := by
  letI : IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W false)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
      (projectivePairSecondChartOverlapCoordinateRing W i) :=
    projectivePairSecondOverlap_isLocalization_infinityPair W i
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (infinityPairToSecondChartOverlapAlgHom W i).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W false)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
  dsimp only [projectivePairSecondOverlapToInfinityPair]
  infer_instance

/-- First projection from the first-factor pair overlap to the cubic overlap. -/
noncomputable def projectivePairFirstOverlapFst
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstChartOverlapScheme W j ⟶
      coveringChartOverlapScheme W :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom
      (R := K)
      (A := coveringChartOverlapCoordinateRing W)
      (B := coveringChartCoordinateRing W j)))

/-- Second projection from the first-factor pair overlap to the unchanged
chart. -/
noncomputable def projectivePairFirstOverlapSnd
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstChartOverlapScheme W j ⟶
      coveringChartScheme W j :=
  Spec.map (CommRingCat.ofHom
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W j))))

/-- First projection from the second-factor pair overlap to the unchanged
chart. -/
noncomputable def projectivePairSecondOverlapFst
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondChartOverlapScheme W i ⟶
      coveringChartScheme W i :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom
      (R := K)
      (A := coveringChartCoordinateRing W i)
      (B := coveringChartOverlapCoordinateRing W)))

/-- Second projection from the second-factor pair overlap to the cubic
overlap. -/
noncomputable def projectivePairSecondOverlapSnd
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondChartOverlapScheme W i ⟶
      coveringChartOverlapScheme W :=
  Spec.map (CommRingCat.ofHom
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartOverlapCoordinateRing W))))

private theorem projectivePairChartIsoSpecTensor_inv_fst
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartIsoSpecTensor W ij).inv ≫
        pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom
          (R := K)
          (A := coveringChartCoordinateRing W ij.1)
          (B := coveringChartCoordinateRing W ij.2))) := by
  rw [← projectivePairChartIsoSpecTensor_hom_fst W ij]
  simp

private theorem projectivePairChartIsoSpecTensor_inv_snd
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartIsoSpecTensor W ij).inv ≫
        pullback.snd
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) =
      Spec.map (CommRingCat.ofHom
        (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := K)
            (A := coveringChartCoordinateRing W ij.1)
            (B := coveringChartCoordinateRing W ij.2)))) := by
  rw [← projectivePairChartIsoSpecTensor_hom_snd W ij]
  simp

@[reassoc]
theorem projectivePairFirstOverlapToStandardPair_comp_fst
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstOverlapToStandardPair W j ≫
        pullback.fst
          (coveringChartMap W true ≫ structureMap W)
          (coveringChartMap W j ≫ structureMap W) =
      projectivePairFirstOverlapFst W j ≫
        coveringChartOverlapToStandardChart W := by
  rw [projectivePairFirstOverlapToStandardPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_fst,
    projectivePairFirstOverlapFst,
    coveringChartOverlapToStandardChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change standardPairToFirstChartOverlapAlgHom W j
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W j) x) =
    Algebra.TensorProduct.includeLeft
      (R := K)
      (S := K)
      (A := coveringChartOverlapCoordinateRing W)
      (B := coveringChartCoordinateRing W j)
      (standardChartToCoveringChartOverlapRing W x)
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeLeft
      (standardChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j)))
  exact hx

@[reassoc]
theorem projectivePairFirstOverlapToInfinityPair_comp_fst
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstOverlapToInfinityPair W j ≫
        pullback.fst
          (coveringChartMap W false ≫ structureMap W)
          (coveringChartMap W j ≫ structureMap W) =
      projectivePairFirstOverlapFst W j ≫
        coveringChartOverlapToInfinityChart W := by
  rw [projectivePairFirstOverlapToInfinityPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_fst,
    projectivePairFirstOverlapFst,
    coveringChartOverlapToInfinityChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change infinityPairToFirstChartOverlapAlgHom W j
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W false)
        (B := coveringChartCoordinateRing W j) x) =
    Algebra.TensorProduct.includeLeft
      (R := K)
      (S := K)
      (A := coveringChartOverlapCoordinateRing W)
      (B := coveringChartCoordinateRing W j)
      (infinityChartToCoveringChartOverlapRing W x)
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeLeft
      (infinityChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j)))
  exact hx

@[reassoc]
theorem projectivePairFirstOverlapToStandardPair_comp_snd
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstOverlapToStandardPair W j ≫
        pullback.snd
          (coveringChartMap W true ≫ structureMap W)
          (coveringChartMap W j ≫ structureMap W) =
      projectivePairFirstOverlapSnd W j := by
  rw [projectivePairFirstOverlapToStandardPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_snd,
    projectivePairFirstOverlapSnd, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change standardPairToFirstChartOverlapAlgHom W j
      (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight x
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeRight
      (standardChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j)))
  exact hx

@[reassoc]
theorem projectivePairFirstOverlapToInfinityPair_comp_snd
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstOverlapToInfinityPair W j ≫
        pullback.snd
          (coveringChartMap W false ≫ structureMap W)
          (coveringChartMap W j ≫ structureMap W) =
      projectivePairFirstOverlapSnd W j := by
  rw [projectivePairFirstOverlapToInfinityPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_snd,
    projectivePairFirstOverlapSnd, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change infinityPairToFirstChartOverlapAlgHom W j
      (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight x
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeRight
      (infinityChartToCoveringChartOverlapAlgHom W)
      (AlgHom.id K (coveringChartCoordinateRing W j)))
  exact hx

@[reassoc]
theorem projectivePairSecondOverlapToStandardPair_comp_fst
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondOverlapToStandardPair W i ≫
        pullback.fst
          (coveringChartMap W i ≫ structureMap W)
          (coveringChartMap W true ≫ structureMap W) =
      projectivePairSecondOverlapFst W i := by
  rw [projectivePairSecondOverlapToStandardPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_fst,
    projectivePairSecondOverlapFst, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change standardPairToSecondChartOverlapAlgHom W i
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W true) x) =
    Algebra.TensorProduct.includeLeft
      (R := K)
      (S := K)
      (A := coveringChartCoordinateRing W i)
      (B := coveringChartOverlapCoordinateRing W) x
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeLeft
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (standardChartToCoveringChartOverlapAlgHom W))
  exact hx

@[reassoc]
theorem projectivePairSecondOverlapToInfinityPair_comp_fst
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondOverlapToInfinityPair W i ≫
        pullback.fst
          (coveringChartMap W i ≫ structureMap W)
          (coveringChartMap W false ≫ structureMap W) =
      projectivePairSecondOverlapFst W i := by
  rw [projectivePairSecondOverlapToInfinityPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_fst,
    projectivePairSecondOverlapFst, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change infinityPairToSecondChartOverlapAlgHom W i
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartCoordinateRing W false) x) =
    Algebra.TensorProduct.includeLeft
      (R := K)
      (S := K)
      (A := coveringChartCoordinateRing W i)
      (B := coveringChartOverlapCoordinateRing W) x
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeLeft
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (infinityChartToCoveringChartOverlapAlgHom W))
  exact hx

@[reassoc]
theorem projectivePairSecondOverlapToStandardPair_comp_snd
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondOverlapToStandardPair W i ≫
        pullback.snd
          (coveringChartMap W i ≫ structureMap W)
          (coveringChartMap W true ≫ structureMap W) =
      projectivePairSecondOverlapSnd W i ≫
        coveringChartOverlapToStandardChart W := by
  rw [projectivePairSecondOverlapToStandardPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_snd,
    projectivePairSecondOverlapSnd,
    coveringChartOverlapToStandardChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change standardPairToSecondChartOverlapAlgHom W i
      (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight
      (standardChartToCoveringChartOverlapRing W x)
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeRight
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (standardChartToCoveringChartOverlapAlgHom W))
  exact hx

@[reassoc]
theorem projectivePairSecondOverlapToInfinityPair_comp_snd
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondOverlapToInfinityPair W i ≫
        pullback.snd
          (coveringChartMap W i ≫ structureMap W)
          (coveringChartMap W false ≫ structureMap W) =
      projectivePairSecondOverlapSnd W i ≫
        coveringChartOverlapToInfinityChart W := by
  rw [projectivePairSecondOverlapToInfinityPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_snd,
    projectivePairSecondOverlapSnd,
    coveringChartOverlapToInfinityChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change infinityPairToSecondChartOverlapAlgHom W i
      (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight
      (infinityChartToCoveringChartOverlapRing W x)
  have hx := congrArg (fun f => f x)
    (Algebra.TensorProduct.map_comp_includeRight
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (infinityChartToCoveringChartOverlapAlgHom W))
  exact hx

@[reassoc]
theorem projectivePairChartMap_comp_fst
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartMap W ij ≫
        pullback.fst (structureMap W) (structureMap W) =
      pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        coveringChartMap W ij.1 := by
  change (Scheme.Pullback.openCoverOfLeftRight
      (coveringChartsOpenCover W) (coveringChartsOpenCover W)
      (structureMap W) (structureMap W)).f ij ≫
      pullback.fst (structureMap W) (structureMap W) = _
  change pullback.map
      (coveringChartMap W ij.1 ≫ structureMap W)
      (coveringChartMap W ij.2 ≫ structureMap W)
      (structureMap W) (structureMap W)
      (coveringChartMap W ij.1) (coveringChartMap W ij.2)
      (𝟙 _) (Category.comp_id _) (Category.comp_id _) ≫
        pullback.fst (structureMap W) (structureMap W) = _
  change pullback.lift _ _ _ ≫
      pullback.fst (structureMap W) (structureMap W) = _
  rw [pullback.lift_fst]

@[reassoc]
theorem projectivePairChartMap_comp_snd
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartMap W ij ≫
        pullback.snd (structureMap W) (structureMap W) =
      pullback.snd
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        coveringChartMap W ij.2 := by
  change (Scheme.Pullback.openCoverOfLeftRight
      (coveringChartsOpenCover W) (coveringChartsOpenCover W)
      (structureMap W) (structureMap W)).f ij ≫
      pullback.snd (structureMap W) (structureMap W) = _
  change pullback.map
      (coveringChartMap W ij.1 ≫ structureMap W)
      (coveringChartMap W ij.2 ≫ structureMap W)
      (structureMap W) (structureMap W)
      (coveringChartMap W ij.1) (coveringChartMap W ij.2)
      (𝟙 _) (Category.comp_id _) (Category.comp_id _) ≫
        pullback.snd (structureMap W) (structureMap W) = _
  change pullback.lift _ _ _ ≫
      pullback.snd (structureMap W) (structureMap W) = _
  rw [pullback.lift_snd]

/-- The two first-factor overlap restrictions are the same open subscheme of
the full projective product. -/
theorem projectivePairFirstOverlap_maps_eq
    (W : WeierstrassCurve K) (j : Bool) :
    projectivePairFirstOverlapToStandardPair W j ≫
        projectivePairChartMap W (true, j) =
      projectivePairFirstOverlapToInfinityPair W j ≫
        projectivePairChartMap W (false, j) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, projectivePairChartMap_comp_fst]
    rw [← Category.assoc,
      projectivePairFirstOverlapToStandardPair_comp_fst,
      ← Category.assoc,
      projectivePairFirstOverlapToInfinityPair_comp_fst,
      Category.assoc, Category.assoc,
      coveringChartOverlap_maps_eq]
  · simp only [Category.assoc, projectivePairChartMap_comp_snd]
    rw [← Category.assoc,
      projectivePairFirstOverlapToStandardPair_comp_snd,
      ← Category.assoc,
      projectivePairFirstOverlapToInfinityPair_comp_snd]

/-- The two second-factor overlap restrictions are the same open subscheme of
the full projective product. -/
theorem projectivePairSecondOverlap_maps_eq
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondOverlapToStandardPair W i ≫
        projectivePairChartMap W (i, true) =
      projectivePairSecondOverlapToInfinityPair W i ≫
        projectivePairChartMap W (i, false) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, projectivePairChartMap_comp_fst]
    rw [← Category.assoc,
      projectivePairSecondOverlapToStandardPair_comp_fst,
      ← Category.assoc,
      projectivePairSecondOverlapToInfinityPair_comp_fst]
  · simp only [Category.assoc, projectivePairChartMap_comp_snd]
    rw [← Category.assoc,
      projectivePairSecondOverlapToStandardPair_comp_snd,
      ← Category.assoc,
      projectivePairSecondOverlapToInfinityPair_comp_snd,
      Category.assoc, Category.assoc,
      coveringChartOverlap_maps_eq]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
