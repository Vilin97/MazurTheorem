/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Affine charts of an ideal-sheaf subscheme

The inverse image of an affine open under an ideal-sheaf subscheme
inclusion is canonically the spectrum of the corresponding quotient
ring.  Mathlib's ideal-sheaf gluing construction supplies both maps; this
file exports their canonical comparison isomorphism and its factorization
identity.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (J : X.IdealSheafData)

private lemma subschemeCover_range_eq (U : X.affineOpens) :
    Set.range (J.subschemeCover.f U) =
      Set.range (J.subschemeι ⁻¹ᵁ U.1).ι := by
  letI : IsOpenImmersion (J.subschemeCover.f U) :=
    J.subschemeCover.map_prop U
  rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι,
    J.opensRange_subschemeCover_map U]

/--
The quotient-spectrum chart is canonically the restriction of the
ideal-sheaf subscheme to an affine open of the ambient scheme.
-/
noncomputable def subschemeAffineChartIso (U : X.affineOpens) :
    J.glueDataObj U ≅ (J.subschemeι ⁻¹ᵁ U.1).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (J.subschemeCover.f U)
    (J.subschemeι ⁻¹ᵁ U.1).ι
    (J.subschemeCover.map_prop U) inferInstance
    (subschemeCover_range_eq J U)

/--
The affine-chart isomorphism followed by the open inclusion is the chart
map used in the construction of the global subscheme.
-/
@[reassoc (attr := simp)]
theorem subschemeAffineChartIso_hom_ι (U : X.affineOpens) :
    (J.subschemeAffineChartIso U).hom ≫
        (J.subschemeι ⁻¹ᵁ U.1).ι =
      J.subschemeCover.f U :=
  by
    exact @IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
      (J.subschemeCover.f U) (J.subschemeι ⁻¹ᵁ U.1).ι
      (J.subschemeCover.map_prop U) inferInstance
      (subschemeCover_range_eq J U)

/--
After the affine-chart identification, the restriction of the global
subscheme inclusion is the quotient-spectrum closed immersion into the
ambient affine open.
-/
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
