/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreStandardChartEquivalence
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The standard affine cover of a product of projective spaces

The product of the standard affine covers of `ℙ^m_k` and `ℙ^n_k`
is an affine cover of their fiber product over `Spec k`.  Each member
is canonically the spectrum of the tensor product of the two standard
chart rings.  Via the explicit Segre chart algebra equivalence, it is
also canonically isomorphic to the corresponding standard chart of
the Segre image `Proj`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The standard product cover of `ℙ^m_k ×_k ℙ^n_k`. -/
abbrev segreProductStandardOpenCover
    (k : Type u) [CommRing k] (m n : ℕ) :
    (binaryProjectiveScheme k m n).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (standardAffineOpenCover k m).openCover
    (standardAffineOpenCover k n).openCover
    (toSpec k m) (toSpec k n)

/-- A standard projective chart is compatible with its structural map
to `Spec k`, expressed using the coefficient algebra of its homogeneous
localization ring. -/
lemma standardAffineOpenCover_toSpec
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    (standardAffineOpenCover k d).f i ≫ toSpec k d =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap k (ProjectiveCoordinateAway k d i))) := by
  change
    Proj.awayι
        (homogeneousGrading k d)
        (coordinate k i)
        (coordinate_mem_degreeOne k i)
        Nat.zero_lt_one ≫
      toSpec k d =
        Spec.map
          (CommRingCat.ofHom
            (algebraMap k (ProjectiveCoordinateAway k d i)))
  rw [toSpec]
  simp only [← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp]
  congr 1
  ext r
  change
    HomogeneousLocalization.val
        ((HomogeneousLocalization.fromZeroRingHom
          (homogeneousGrading k d)
          (Submonoid.powers (coordinate k i)))
            ((algebraMap k (homogeneousGrading k d 0)) r)) =
      HomogeneousLocalization.val
        ((algebraMap k
          (ProjectiveCoordinateAway k d i)) r)
  have hr :
      (HomogeneousLocalization.fromZeroRingHom
        (homogeneousGrading k d)
        (Submonoid.powers (coordinate k i)))
          ((algebraMap k (homogeneousGrading k d 0)) r) =
        (algebraMap k
          (ProjectiveCoordinateAway k d i)) r := by
    rw [homogeneousAway_algebraMap_eq_mk
      (coordinate k i)
      (coordinate_mem_degreeOne k i) r]
    rfl
  exact congrArg HomogeneousLocalization.val hr

/-- A member of the standard product cover is the spectrum of the
tensor product of the corresponding projective chart rings. -/
def segreProductStandardChartIsoSpec
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover k m n).X (i, j) ≅
      Spec
        (CommRingCat.of
          (SegreProductChartRing k m n i j)) := by
  refine
    pullback.congrHom
        (standardAffineOpenCover_toSpec k m i)
        (standardAffineOpenCover_toSpec k n j) ≪≫
      pullbackSpecIso
        k
        (ProjectiveCoordinateAway k m i)
        (ProjectiveCoordinateAway k n j)

/-- The explicit chartwise Segre morphism from a product standard
chart to the `Proj` of the Segre image. -/
def segreProductStandardChartToProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover k m n).X (i, j) ⟶
      Proj (segreImageGrading k m n) :=
  (segreProductStandardChartIsoSpec k m n i j).hom ≫
    Spec.map
      (CommRingCat.ofHom
        (segreChartForwardAlgHom k m n i j).toRingHom) ≫
    Proj.awayι
      (segreImageGrading k m n)
      (segreImageCoordinate k m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one

/-- The actual isomorphism from a product standard chart to the
corresponding standard chart of the Segre-image `Proj`. -/
def segreProductStandardChartIsoImageChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover k m n).X (i, j) ≅
      (segreImageStandardChart k m n
        (segrePairIndex m n i j)).toScheme := by
  letI :
      IsIso
        (CommRingCat.ofHom
          (segreChartForwardAlgHom k m n i j).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (segreStandardChartAlgEquiv k m n i j).bijective
  exact
    segreProductStandardChartIsoSpec k m n i j ≪≫
      asIso
        (Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom k m n i j).toRingHom)) ≪≫
      (Proj.basicOpenIsoSpec
        (segreImageGrading k m n)
        (segreImageCoordinate k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one).symm

/-- The chartwise Segre morphism is the chart isomorphism followed by
the corresponding open inclusion. -/
@[reassoc]
lemma segreProductStandardChartIsoImageChart_hom_ι
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoImageChart k m n i j).hom ≫
        (segreImageStandardChart k m n
          (segrePairIndex m n i j)).ι =
      segreProductStandardChartToProj k m n i j := by
  rfl

instance isOpenImmersion_segreProductStandardChartToProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsOpenImmersion
      (segreProductStandardChartToProj k m n i j) := by
  let chartIso :=
    segreProductStandardChartIsoSpec k m n i j
  let chartMap :
      (segreProductStandardOpenCover k m n).X (i, j) ⟶
        Spec
          (CommRingCat.of
            (SegreImageChartRing k m n i j)) :=
    chartIso.hom ≫
      Spec.map
        (CommRingCat.ofHom
          (segreChartForwardAlgHom k m n i j).toRingHom)
  letI :
      IsIso
        (CommRingCat.ofHom
          (segreChartForwardAlgHom k m n i j).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (segreStandardChartAlgEquiv k m n i j).bijective
  letI : IsIso chartMap := by
    dsimp only [chartMap, chartIso]
    infer_instance
  let targetChartMap :
      Spec
          (CommRingCat.of
            (SegreImageChartRing k m n i j)) ⟶
        Proj (segreImageGrading k m n) :=
    Proj.awayι
      (segreImageGrading k m n)
      (segreImageCoordinate k m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one
  have hchart : IsOpenImmersion chartMap := by
    infer_instance
  have htarget : IsOpenImmersion targetChartMap := by
    dsimp only [targetChartMap]
    infer_instance
  have hcomp : IsOpenImmersion (chartMap ≫ targetChartMap) :=
    MorphismProperty.IsStableUnderComposition.comp_mem
      chartMap targetChartMap hchart htarget
  simpa only [segreProductStandardChartToProj,
    chartMap, chartIso, targetChartMap, Category.assoc] using hcomp

/-- The range of a chartwise Segre morphism is the corresponding
standard Segre-image chart. -/
lemma opensRange_segreProductStandardChartToProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartToProj k m n i j).opensRange =
      segreImageStandardChart k m n
        (segrePairIndex m n i j) := by
  let chartIso :=
    segreProductStandardChartIsoSpec k m n i j
  let chartMap :
      (segreProductStandardOpenCover k m n).X (i, j) ⟶
        Spec
          (CommRingCat.of
            (SegreImageChartRing k m n i j)) :=
    chartIso.hom ≫
      Spec.map
        (CommRingCat.ofHom
          (segreChartForwardAlgHom k m n i j).toRingHom)
  letI :
      IsIso
        (CommRingCat.ofHom
          (segreChartForwardAlgHom k m n i j).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (segreStandardChartAlgEquiv k m n i j).bijective
  letI : IsIso chartMap := by
    dsimp only [chartMap, chartIso]
    infer_instance
  change
    (chartMap ≫
      Proj.awayι
        (segreImageGrading k m n)
        (segreImageCoordinate k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one).opensRange =
      Proj.basicOpen
        (segreImageGrading k m n)
        (segreImageCoordinate k m n
          (segrePairIndex m n i j))
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact
    Proj.opensRange_awayι
      (segreImageGrading k m n)
      (segreImageCoordinate k m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
