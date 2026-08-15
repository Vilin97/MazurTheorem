/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartFiniteGenerators

/-!
# Transporting sections between standard projective charts

Sections of the restriction to a standard affine chart are the same as
sections of the original sheaf on the corresponding standard open.  On a
pairwise overlap this identifies the two chart descriptions with sections
on the intersection of the standard opens.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/-- The image of the terminal open of a standard affine chart is the
corresponding standard open in projective space. -/
lemma standardAffineCover_image_top (j : Fin (d + 1)) :
    standardChartMap k d j ''ᵁ ⊤ =
      standardChart k j := by
  change (standardAffineOpenCover k d).f j ''ᵁ ⊤ =
    standardChart k j
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact standardAffineOpenCover_opensRange k d j

/-- The image of `D(Xᵢ/Xⱼ)` from the `j`-th affine chart is the
intersection of the `j`-th and `i`-th standard opens. -/
lemma standardAffineCover_image_chartRatio
    (i j : Fin (d + 1)) :
    standardChartMap k d j ''ᵁ
        PrimeSpectrum.basicOpen (chartRatioElement k d i j) =
      standardChart k j ⊓ standardChart k i := by
  change
    (standardAffineOpenCover k d).f j ''ᵁ
        PrimeSpectrum.basicOpen (chartRatio k d i j) =
      standardChart k j ⊓ standardChart k i
  have hpre :
      (standardAffineOpenCover k d).f j ⁻¹ᵁ standardChart k i =
        PrimeSpectrum.basicOpen (chartRatio k d i j) :=
    standardAffineCover_preimage_standardChart k d i j
  calc
    _ = (standardAffineOpenCover k d).f j ''ᵁ
          ((standardAffineOpenCover k d).f j ⁻¹ᵁ
            standardChart k i) :=
      congrArg
        (fun U => (standardAffineOpenCover k d).f j ''ᵁ U)
        hpre.symm
    _ = ((standardAffineOpenCover k d).f j).opensRange ⊓
          standardChart k i :=
      Scheme.Hom.image_preimage_eq_opensRange_inf
        ((standardAffineOpenCover k d).f j) (standardChart k i)
    _ = standardChart k j ⊓ standardChart k i := by
      rw [standardAffineOpenCover_opensRange]

/-- Top sections in the affine-chart model are sections of the original
module over the corresponding standard open. -/
def chartTopSectionsIso
    (M : (scheme k d).Modules) (j : Fin (d + 1)) :
    Γ(chartModule k d M j, ⊤) ≅
      Γ(M, standardChart k j) :=
  M.restrictAppIso (standardChartMap k d j) ⊤ ≪≫
    eqToIso (congrArg (fun U => Γ(M, U))
      (standardAffineCover_image_top k d j))

/-- Sections on the ratio basic open in the affine-chart model are
sections of the original module over the corresponding pairwise
intersection. -/
def chartOverlapSectionsIso
    (M : (scheme k d).Modules)
    (i j : Fin (d + 1)) :
    Γ(chartModule k d M j,
        chartRatioOpen k d i j) ≅
      Γ(M, standardChart k j ⊓ standardChart k i) :=
  M.restrictAppIso (standardChartMap k d j)
      (chartRatioOpen k d i j) ≪≫
    eqToIso (congrArg (fun U => Γ(M, U))
      (standardAffineCover_image_chartRatio k d i j))

/-- Restrict a section from the `i`-th chart to its overlap with the
`j`-th chart, expressed in the affine coordinates of chart `j`. -/
def chartSectionOnOverlap
    (M : (scheme k d).Modules)
    (i j : Fin (d + 1))
    (s : Γ(chartModule k d M i, ⊤)) :
    Γ(chartModule k d M j,
      chartRatioOpen k d i j) :=
  (chartOverlapSectionsIso k d M i j).inv
    (M.presheaf.map (homOfLE inf_le_right).op
      ((chartTopSectionsIso k d M i).hom s))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
