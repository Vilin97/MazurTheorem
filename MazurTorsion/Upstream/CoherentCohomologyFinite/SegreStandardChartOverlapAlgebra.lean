/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreProductStandardCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveStandardChartRatios

/-!
# Algebra on overlaps of standard Segre charts

The overlap of the standard Segre-image charts indexed by `(i,j)` and
`(a,b)` is the degree-zero homogeneous localization away from the
product of the two corresponding Segre coordinates.  Relative to the
first chart, this is localization at the ratio

`(XₐY_b)/(XᵢYⱼ)`.

Under the explicit Segre chart equivalence this ratio becomes the
product `(Xₐ/Xᵢ)(Y_b/Yⱼ)`.  Consequently the chart equivalence extends
canonically to an equivalence of overlap rings.
-/

open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The transition function on a product standard chart. -/
def segreProductChartTransition
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreProductChartRing k m n i j :=
  projectiveCoordinateRatio k m i a ⊗ₜ[k]
    projectiveCoordinateRatio k n j b

/-- The ring of the intersection of two standard charts of the
Segre-image `Proj`. -/
abbrev SegreImageChartOverlapRing
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :=
  Away
    (segreImageGrading k m n)
    (segreImageCoordinate k m n (segrePairIndex m n i j) *
      segreImageCoordinate k m n (segrePairIndex m n a b))

/-- The product-chart overlap, presented as the distinguished
localization at its transition function. -/
abbrev SegreProductChartOverlapRing
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :=
  Localization.Away
    (segreProductChartTransition k m n i a j b)

@[simp]
lemma segreChartForwardAlgHom_transition
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreChartForwardAlgHom k m n i j
        (segreImageChartRatio k m n i a j b) =
      segreProductChartTransition k m n i a j b := by
  exact segreChartForwardAlgHom_ratio k m n i a j b

lemma segreImageChartRatio_eq_isLocalizationElem
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageChartRatio k m n i a j b =
      Away.isLocalizationElem
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n a b)) := by
  change
    Away.mk _ _ 1
        (segreImageCoordinate k m n (segrePairIndex m n a b)) _ =
      Away.mk _ _ 1
        (segreImageCoordinate k m n (segrePairIndex m n a b) ^ 1) _
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, pow_one]

/-- The standard-chart Segre equivalence localized to the overlap
with a second standard chart. -/
def segreStandardChartOverlapRingEquiv
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartOverlapRing k m n i a j b ≃+*
      SegreProductChartOverlapRing k m n i a j b := by
  letI :=
    (HomogeneousLocalization.awayMap
      (segreImageGrading k m n)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))
      (rfl :
        segreImageCoordinate k m n (segrePairIndex m n i j) *
            segreImageCoordinate k m n (segrePairIndex m n a b) =
          segreImageCoordinate k m n (segrePairIndex m n i j) *
            segreImageCoordinate k m n (segrePairIndex m n a b))).toAlgebra
  letI :
      IsLocalization.Away
        (segreImageChartRatio k m n i a j b)
        (SegreImageChartOverlapRing k m n i a j b) := by
    rw [segreImageChartRatio_eq_isLocalizationElem]
    exact
      Away.isLocalization_mul
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n a b))
        rfl Nat.one_ne_zero
  exact
    IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers
        (segreImageChartRatio k m n i a j b))
      (T := Submonoid.powers
        (segreProductChartTransition k m n i a j b))
      (SegreImageChartOverlapRing k m n i a j b)
      (SegreProductChartOverlapRing k m n i a j b)
      (segreStandardChartAlgEquiv k m n i j).toRingEquiv
      (by
        rw [Submonoid.map_powers]
        have htransition :
            (segreStandardChartAlgEquiv k m n i j).toRingEquiv
                (segreImageChartRatio k m n i a j b) =
              segreProductChartTransition k m n i a j b :=
          segreChartForwardAlgHom_transition k m n i a j b
        exact
          congrArg
            (fun x : SegreProductChartRing k m n i j =>
              Submonoid.powers x)
            htransition)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
