/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreStandardChartOverlapAlgebra

/-!
# Scheme overlaps in the standard product cover

The overlap of the product charts `(i,j)` and `(a,b)` is the
distinguished open in the first chart cut out by

`(Xₐ/Xᵢ) ⊗ (Y_b/Yⱼ)`.

This file identifies that open with the spectrum of the corresponding
ordinary localization.  It is the source-side geometric input needed
to glue the chartwise Segre morphisms.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The component maps of the standard product cover are open immersions. -/
instance isOpenImmersion_segreProductStandardOpenCover_f
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsOpenImmersion ((segreProductStandardOpenCover k m n).f (i, j)) := by
  change IsOpenImmersion
    (pullback.map
      ((standardAffineOpenCover k m).f i ≫ toSpec k m)
      ((standardAffineOpenCover k n).f j ≫ toSpec k n)
      (toSpec k m) (toSpec k n)
      ((standardAffineOpenCover k m).f i)
      ((standardAffineOpenCover k n).f j)
      (𝟙 (Spec (CommRingCat.of k)))
      (Category.comp_id _)
      (Category.comp_id _))
  infer_instance

/-- The range of a standard product chart is the intersection of the
inverse images of its two factor charts. -/
lemma opensRange_segreProductStandardOpenCover_f
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ((segreProductStandardOpenCover k m n).f (i, j)).opensRange =
      pullback.fst (toSpec k m) (toSpec k n) ⁻¹ᵁ
          standardChart k i ⊓
        pullback.snd (toSpec k m) (toSpec k n) ⁻¹ᵁ
          standardChart k j := by
  apply TopologicalSpace.Opens.ext
  change
    Set.range
        (pullback.map
          ((standardAffineOpenCover k m).f i ≫ toSpec k m)
          ((standardAffineOpenCover k n).f j ≫ toSpec k n)
          (toSpec k m) (toSpec k n)
          ((standardAffineOpenCover k m).f i)
          ((standardAffineOpenCover k n).f j)
          (𝟙 (Spec (CommRingCat.of k)))
          (Category.comp_id _)
          (Category.comp_id _)) =
      _
  rw [Scheme.Pullback.range_map]
  rw [← Scheme.Hom.coe_opensRange,
    ← Scheme.Hom.coe_opensRange,
    standardAffineOpenCover_opensRange,
    standardAffineOpenCover_opensRange]
  rfl

@[reassoc]
lemma segreProductStandardOpenCover_f_fst
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.fst (toSpec k m) (toSpec k n) =
      pullback.fst
          ((standardAffineCover k m).f i ≫ toSpec k m)
          ((standardAffineCover k n).f j ≫ toSpec k n) ≫
        (standardAffineCover k m).f i := by
  simp [segreProductStandardOpenCover,
    Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_fst]

@[reassoc]
lemma segreProductStandardOpenCover_f_snd
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.snd (toSpec k m) (toSpec k n) =
      pullback.snd
          ((standardAffineCover k m).f i ≫ toSpec k m)
          ((standardAffineCover k n).f j ≫ toSpec k n) ≫
        (standardAffineCover k n).f j := by
  simp [segreProductStandardOpenCover,
    Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_snd]

@[reassoc]
lemma segreProductStandardChartIsoSpec_inv_chartFst
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec k m n i j).inv ≫
        pullback.fst
          ((standardAffineCover k m).f i ≫ toSpec k m)
          ((standardAffineCover k n).f j ≫ toSpec k n) =
      Spec.map
        (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            ProjectiveCoordinateAway k m i →+*
              SegreProductChartRing k m n i j)) := by
  change
    ((pullbackSpecIso k (ProjectiveCoordinateAway k m i)
        (ProjectiveCoordinateAway k n j)).inv ≫
      (pullback.congrHom
        (standardAffineOpenCover_toSpec k m i)
        (standardAffineOpenCover_toSpec k n j)).inv) ≫
        pullback.fst
          ((standardAffineOpenCover k m).f i ≫ toSpec k m)
          ((standardAffineOpenCover k n).f j ≫ toSpec k n) =
      _
  erw [Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
    pullbackSpecIso_inv_fst]

@[reassoc]
lemma segreProductStandardChartIsoSpec_inv_chartSnd
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec k m n i j).inv ≫
        pullback.snd
          ((standardAffineCover k m).f i ≫ toSpec k m)
          ((standardAffineCover k n).f j ≫ toSpec k n) =
      Spec.map
        (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway k n j →ₐ[k]
              SegreProductChartRing k m n i j).toRingHom)) := by
  change
    ((pullbackSpecIso k (ProjectiveCoordinateAway k m i)
        (ProjectiveCoordinateAway k n j)).inv ≫
      (pullback.congrHom
        (standardAffineOpenCover_toSpec k m i)
        (standardAffineOpenCover_toSpec k n j)).inv) ≫
        pullback.snd
          ((standardAffineOpenCover k m).f i ≫ toSpec k m)
          ((standardAffineOpenCover k n).f j ≫ toSpec k n) =
      _
  erw [Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
    pullbackSpecIso_inv_snd]
  rw [AlgHom.toRingHom_eq_coe]

@[reassoc]
lemma segreProductStandardChartIsoSpec_inv_fst
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec k m n i j).inv ≫
        (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.fst (toSpec k m) (toSpec k n) =
      Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              ProjectiveCoordinateAway k m i →+*
                SegreProductChartRing k m n i j)) ≫
        (standardAffineCover k m).f i := by
  calc
    _ = (segreProductStandardChartIsoSpec k m n i j).inv ≫
          (pullback.fst
              ((standardAffineCover k m).f i ≫ toSpec k m)
              ((standardAffineCover k n).f j ≫ toSpec k n) ≫
            (standardAffineCover k m).f i) :=
      congrArg
        (fun q =>
          (segreProductStandardChartIsoSpec k m n i j).inv ≫ q)
        (segreProductStandardOpenCover_f_fst k m n i j)
    _ = _ := by
      calc
        _ = ((segreProductStandardChartIsoSpec k m n i j).inv ≫
              pullback.fst
                ((standardAffineCover k m).f i ≫ toSpec k m)
                ((standardAffineCover k n).f j ≫ toSpec k n)) ≫
              (standardAffineCover k m).f i := (Category.assoc _ _ _).symm
        _ = _ := congrArg (fun q => q ≫ (standardAffineCover k m).f i)
          (segreProductStandardChartIsoSpec_inv_chartFst k m n i j)

@[reassoc]
lemma segreProductStandardChartIsoSpec_inv_snd
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec k m n i j).inv ≫
        (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.snd (toSpec k m) (toSpec k n) =
      Spec.map
          (CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway k n j →ₐ[k]
                SegreProductChartRing k m n i j).toRingHom)) ≫
        (standardAffineCover k n).f j := by
  calc
    _ = (segreProductStandardChartIsoSpec k m n i j).inv ≫
          (pullback.snd
              ((standardAffineCover k m).f i ≫ toSpec k m)
              ((standardAffineCover k n).f j ≫ toSpec k n) ≫
            (standardAffineCover k n).f j) :=
      congrArg
        (fun q =>
          (segreProductStandardChartIsoSpec k m n i j).inv ≫ q)
        (segreProductStandardOpenCover_f_snd k m n i j)
    _ = _ := by
      calc
        _ = ((segreProductStandardChartIsoSpec k m n i j).inv ≫
              pullback.snd
                ((standardAffineCover k m).f i ≫ toSpec k m)
                ((standardAffineCover k n).f j ≫ toSpec k n)) ≫
              (standardAffineCover k n).f j := (Category.assoc _ _ _).symm
        _ = _ := congrArg (fun q => q ≫ (standardAffineCover k n).f j)
          (segreProductStandardChartIsoSpec_inv_chartSnd k m n i j)

@[simp]
lemma chartRatio_eq_projectiveCoordinateRatio
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) :
    chartRatio k d a i =
      projectiveCoordinateRatio k d i a := by
  change
    HomogeneousLocalization.Away.mk
        (homogeneousGrading k d)
        (coordinate_mem_degreeOne k i) 1
        (coordinate k a ^ 1) _ =
      HomogeneousLocalization.Away.mk
        (homogeneousGrading k d)
        (coordinate_mem_degreeOne k i) 1
        (coordinate k a) _
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, pow_one]

/-- The intersection with the `(a,b)` chart, regarded as an open of
the `(i,j)` product chart. -/
def segreProductChartOverlapOpen
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ((segreProductStandardOpenCover k m n).X (i, j)).Opens :=
  (segreProductStandardOpenCover k m n).f (i, j) ⁻¹ᵁ
    ((segreProductStandardOpenCover k m n).f (a, b)).opensRange

/-- The distinguished open cut out by the product transition
function in the affine spectrum model of the `(i,j)` chart. -/
def segreProductChartTransitionOpen
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (Spec
      (CommRingCat.of
        (SegreProductChartRing k m n i j))).Opens :=
  PrimeSpectrum.basicOpen
    (segreProductChartTransition k m n i a j b)

/-- In the affine-spectrum model of the `(i,j)` product chart, its
intersection with the `(a,b)` chart is the distinguished open of the
product transition function. -/
lemma segreProductStandardChartIsoSpec_inv_preimage
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec k m n i j).inv ⁻¹ᵁ
        segreProductChartOverlapOpen k m n i a j b =
      segreProductChartTransitionOpen k m n i a j b := by
  change
    ((segreProductStandardChartIsoSpec k m n i j).inv ≫
          (segreProductStandardOpenCover k m n).f (i, j)) ⁻¹ᵁ
        ((segreProductStandardOpenCover k m n).f (a, b)).opensRange =
      PrimeSpectrum.basicOpen
        (segreProductChartTransition k m n i a j b)
  rw [opensRange_segreProductStandardOpenCover_f,
    Scheme.Hom.preimage_inf,
    ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage]
  simp only [Category.assoc,
    segreProductStandardChartIsoSpec_inv_fst,
    segreProductStandardChartIsoSpec_inv_snd]
  rw [Scheme.Hom.comp_preimage
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          ProjectiveCoordinateAway k m i →+* SegreProductChartRing k m n i j)))
      ((standardAffineCover k m).f i) (standardChart k a),
    Scheme.Hom.comp_preimage
      (Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight :
          ProjectiveCoordinateAway k n j →ₐ[k]
            SegreProductChartRing k m n i j).toRingHom)))
      ((standardAffineCover k n).f j) (standardChart k b),
    ]
  erw [standardAffineCover_preimage_standardChart k m a i,
    standardAffineCover_preimage_standardChart k n b j]
  rw [
    SpecMap_preimage_basicOpen
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        ProjectiveCoordinateAway k m i →+* SegreProductChartRing k m n i j))
      (chartRatio k m a i),
    SpecMap_preimage_basicOpen
      (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        ProjectiveCoordinateAway k n j →ₐ[k]
          SegreProductChartRing k m n i j).toRingHom))
      (chartRatio k n b j)]
  let x : SegreProductChartRing k m n i j :=
    Algebra.TensorProduct.includeLeftRingHom (chartRatio k m a i)
  let y : SegreProductChartRing k m n i j :=
    (Algebra.TensorProduct.includeRight :
      ProjectiveCoordinateAway k n j →ₐ[k]
        SegreProductChartRing k m n i j) (chartRatio k n b j)
  change PrimeSpectrum.basicOpen x ⊓ PrimeSpectrum.basicOpen y =
    PrimeSpectrum.basicOpen (segreProductChartTransition k m n i a j b)
  rw [← PrimeSpectrum.basicOpen_mul]
  congr 1
  simp [x, y, segreProductChartTransition]

/-- The distinguished localization morphism into the affine spectrum
model of a product chart. -/
def segreProductChartLocalizationMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing k m n i a j b)) ⟶
      Spec
        (CommRingCat.of
          (SegreProductChartRing k m n i j)) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap
        (SegreProductChartRing k m n i j)
        (SegreProductChartOverlapRing k m n i a j b)))

instance isOpenImmersion_segreProductChartLocalizationMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsOpenImmersion
      (segreProductChartLocalizationMap k m n i a j b) := by
  exact
    IsOpenImmersion.of_isLocalization
      (segreProductChartTransition k m n i a j b)

lemma opensRange_segreProductChartLocalizationMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductChartLocalizationMap k m n i a j b).opensRange =
      segreProductChartTransitionOpen k m n i a j b := by
  apply TopologicalSpace.Opens.ext
  exact
    PrimeSpectrum.localization_away_comap_range
      (SegreProductChartOverlapRing k m n i a j b)
      (segreProductChartTransition k m n i a j b)

/-- The localization model of an overlap, mapped into its first
product chart. -/
def segreProductChartOverlapToChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing k m n i a j b)) ⟶
      (segreProductStandardOpenCover k m n).X (i, j) :=
  segreProductChartLocalizationMap k m n i a j b ≫
    (segreProductStandardChartIsoSpec k m n i j).inv

instance isOpenImmersion_segreProductChartOverlapToChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsOpenImmersion
      (segreProductChartOverlapToChart k m n i a j b) := by
  dsimp only [segreProductChartOverlapToChart]
  infer_instance

lemma opensRange_comp_iso_inv_eq_of_preimage
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (e : Z ≅ Y) (U : Z.Opens) (V : Y.Opens)
    (hf : f.opensRange = V)
    (he : e.inv ⁻¹ᵁ U = V) :
    (f ≫ e.inv).opensRange = U := by
  calc
    (f ≫ e.inv).opensRange =
        e.inv ''ᵁ f.opensRange :=
      Scheme.Hom.opensRange_comp f e.inv
    _ = e.inv ''ᵁ V := by rw [hf]
    _ = e.inv ''ᵁ e.inv ⁻¹ᵁ U := by rw [he]
    _ = e.inv.opensRange ⊓ U :=
      e.inv.image_preimage_eq_opensRange_inf U
    _ = ⊤ ⊓ U := by
      rw [Scheme.Hom.opensRange_of_isIso]
    _ = U := by simp

lemma opensRange_segreProductChartOverlapToChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductChartOverlapToChart k m n i a j b).opensRange =
      segreProductChartOverlapOpen k m n i a j b := by
  exact
    opensRange_comp_iso_inv_eq_of_preimage
      (segreProductChartLocalizationMap k m n i a j b)
      (segreProductStandardChartIsoSpec k m n i j)
      (segreProductChartOverlapOpen k m n i a j b)
      (segreProductChartTransitionOpen k m n i a j b)
      (opensRange_segreProductChartLocalizationMap
        k m n i a j b)
      (segreProductStandardChartIsoSpec_inv_preimage
        k m n i a j b)

/-- The actual pullback overlap of two product charts, identified with
the distinguished localization of the first chart ring. -/
def segreProductStandardOverlapIso
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback
        ((segreProductStandardOpenCover k m n).f (i, j))
        ((segreProductStandardOpenCover k m n).f (a, b)) ≅
      Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing k m n i a j b)) :=
  IsOpenImmersion.isoOfRangeEq
    (pullback.fst
      ((segreProductStandardOpenCover k m n).f (i, j))
      ((segreProductStandardOpenCover k m n).f (a, b)))
    (segreProductChartOverlapToChart k m n i a j b)
    (by
      rw [← Scheme.Hom.coe_opensRange,
        ← Scheme.Hom.coe_opensRange,
        Scheme.Hom.opensRange_pullbackFst,
        opensRange_segreProductChartOverlapToChart]
      rfl)

@[reassoc]
lemma segreProductStandardOverlapIso_hom_toChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductStandardOverlapIso k m n i a j b).hom ≫
        segreProductChartOverlapToChart k m n i a j b =
      pullback.fst
        ((segreProductStandardOpenCover k m n).f (i, j))
        ((segreProductStandardOpenCover k m n).f (a, b)) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
