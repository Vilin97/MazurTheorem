/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartExtensionData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoTopSectionEpi

/-!
# The affine spectrum model of a standard projective chart

The spectrum used for affine calculations on a standard chart is
canonically isomorphic to the corresponding open subscheme of projective
space.  We also record the induced comparison between the two successive
restriction functors.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/-- The affine-spectrum model of a standard projective chart, oriented
towards the canonical open subscheme. -/
def standardChartSchemeIso (i : Fin (d + 1)) :
    Spec (chartRing k d i) ≅
      (standardChart k i).toScheme :=
  (Proj.basicOpenIsoSpec
    (homogeneousGrading k d)
    (coordinate k i)
    (coordinate_mem_degreeOne k i)
    Nat.zero_lt_one).symm

/-- The standard affine-cover immersion factors through the canonical
open subscheme by `standardChartSchemeIso`. -/
@[reassoc]
theorem standardChartSchemeIso_hom_comp_ι
    (i : Fin (d + 1)) :
    (standardChartSchemeIso k d i).hom ≫
        (standardChart k i).ι =
      (standardAffineOpenCover k d).f i := by
  change
    (Proj.basicOpenIsoSpec
      (homogeneousGrading k d)
      (coordinate k i)
      (coordinate_mem_degreeOne k i)
      Nat.zero_lt_one).inv ≫
        (Proj.basicOpen
          (homogeneousGrading k d)
          (coordinate k i)).ι =
      Proj.awayι
        (homogeneousGrading k d)
        (coordinate k i)
        (coordinate_mem_degreeOne k i)
        Nat.zero_lt_one
  exact
    Proj.basicOpenIsoSpec_inv_ι
      (homogeneousGrading k d)
      (coordinate k i)
      (coordinate_mem_degreeOne k i)
      Nat.zero_lt_one

/-- Restriction to the affine-spectrum chart agrees, through the chart
isomorphism, with restriction first to the canonical standard open. -/
def chartModuleRestrictionIso
    (M : (scheme k d).Modules) (i : Fin (d + 1)) :
    chartModule k d M i ≅
      (M.restrict (standardChart k i).ι).restrict
        (standardChartSchemeIso k d i).hom := by
  letI hAffine : IsOpenImmersion
      ((standardAffineOpenCover k d).f i) :=
    (standardAffineOpenCover k d).map_prop i
  letI hIso : IsOpenImmersion
      (standardChartSchemeIso k d i).hom :=
    AlgebraicGeometry.IsOpenImmersion.of_isIso _
  letI hOpen : IsOpenImmersion
      (standardChart k i).ι :=
    inferInstance
  letI hComp : IsOpenImmersion
      ((standardChartSchemeIso k d i).hom ≫
        (standardChart k i).ι) :=
    @AlgebraicGeometry.IsOpenImmersion.comp
      _ _ _
      (standardChartSchemeIso k d i).hom
      (standardChart k i).ι hIso hOpen
  change
    M.restrict ((standardAffineOpenCover k d).f i) ≅
      @Scheme.Modules.restrict _ _
        (@Scheme.Modules.restrict _ _ M
          (standardChart k i).ι hOpen)
        (standardChartSchemeIso k d i).hom hIso
  exact
    (@Scheme.Modules.restrictFunctorCongr
      _ _
      ((standardAffineOpenCover k d).f i)
      ((standardChartSchemeIso k d i).hom ≫
        (standardChart k i).ι)
      (standardChartSchemeIso_hom_comp_ι k d i).symm
      hAffine hComp).app M ≪≫
      (@Scheme.Modules.restrictFunctorComp
        _ _ _
        (standardChartSchemeIso k d i).hom
        (standardChart k i).ι hIso hOpen).app M

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
