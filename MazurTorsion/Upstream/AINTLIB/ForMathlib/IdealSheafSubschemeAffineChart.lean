/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Affine charts of ideal-sheaf subschemes

The inverse image of an affine open under an ideal-sheaf subscheme inclusion is
canonically the spectrum of the corresponding quotient ring.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (J : X.IdealSheafData)

private theorem chartMap_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (J.glueData.ι U ≫ J.subschemeIso.inv) := by
  change IsOpenImmersion (J.subschemeCover.f U)
  exact J.subschemeCover.map_prop U

private theorem range_chartMap (U : X.affineOpens) :
    Set.range (J.glueData.ι U ≫ J.subschemeIso.inv) =
      (J.subschemeι ⁻¹ᵁ U.1 : Set J.subscheme) := by
  change Set.range (J.subschemeCover.f U) =
    (J.subschemeι ⁻¹ᵁ U.1 : Set J.subscheme)
  letI : IsOpenImmersion (J.subschemeCover.f U) :=
    J.subschemeCover.map_prop U
  calc
    Set.range (J.subschemeCover.f U) =
        ((J.subschemeCover.f U).opensRange : Set J.subscheme) :=
      (Scheme.Hom.coe_opensRange _).symm
    _ = (J.subschemeι ⁻¹ᵁ U.1 : Set J.subscheme) :=
      congrArg (fun V : J.subscheme.Opens => (V : Set J.subscheme))
        (J.opensRange_subschemeCover_map U)

/-- The quotient-spectrum chart is the restriction of the ideal-sheaf subscheme
to the corresponding ambient affine open. -/
noncomputable def subschemeAffineChartIso (U : X.affineOpens) :
    J.glueDataObj U ≅ (J.subschemeι ⁻¹ᵁ U.1).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (J.glueData.ι U ≫ J.subschemeIso.inv)
    (J.subschemeι ⁻¹ᵁ U.1).ι
    (J.chartMap_isOpenImmersion U)
    inferInstance
    ((J.range_chartMap U).trans (Scheme.Opens.range_ι _).symm)

@[reassoc (attr := simp)]
theorem subschemeAffineChartIso_hom_ι (U : X.affineOpens) :
    (J.subschemeAffineChartIso U).hom ≫
        (J.subschemeι ⁻¹ᵁ U.1).ι =
      J.subschemeCover.f U := by
  change (J.subschemeAffineChartIso U).hom ≫
    (J.subschemeι ⁻¹ᵁ U.1).ι =
      J.glueData.ι U ≫ J.subschemeIso.inv
  unfold subschemeAffineChartIso
  exact @IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    (J.glueData.ι U ≫ J.subschemeIso.inv)
    (J.subschemeι ⁻¹ᵁ U.1).ι
    (J.chartMap_isOpenImmersion U)
    inferInstance
    ((J.range_chartMap U).trans (Scheme.Opens.range_ι _).symm)

@[reassoc (attr := simp)]
theorem subschemeAffineChartIso_hom_restrict (U : X.affineOpens) :
    (J.subschemeAffineChartIso U).hom ≫
        (J.subschemeι ∣_ U.1) =
      J.glueDataObjι U := by
  rw [← cancel_mono U.1.ι]
  rw [Category.assoc, morphismRestrict_ι]
  rw [← Category.assoc, J.subschemeAffineChartIso_hom_ι]
  exact J.subschemeCover_map_subschemeι U

end AlgebraicGeometry.Scheme.IdealSheafData
