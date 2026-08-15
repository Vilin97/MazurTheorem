/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingMorphismBasicOpen
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingOpenSectionTransport
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Base scalars on an affine inverse image

For a morphism restricted over an affine open, the fixed-base action on
top sections is the usual action obtained from the original map on that
open.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {X Y : Scheme.{u}}

/-- The structural action of `Γ(Y,U)` on the top sections of the inverse
image scheme is restriction of the usual image of a scalar under
`f.app U`. -/
lemma algebraMapOnOpen_preimage_top
    (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (r : Γ(Y, U)) :
    letI :
        (f ⁻¹ᵁ U).toScheme.Over
          (Spec (CommRingCat.of Γ(Y, U))) :=
      ⟨morphismRestrict f U ≫ hU.isoSpec.hom⟩
    algebraMapOnOpen
        (k := Γ(Y, U))
        (X := (f ⁻¹ᵁ U).toScheme) ⊤ r =
      (f ⁻¹ᵁ U).topIso.inv.hom
        ((f.app U).hom r) := by
  letI :
      (f ⁻¹ᵁ U).toScheme.Over
        (Spec (CommRingCat.of Γ(Y, U))) :=
    ⟨morphismRestrict f U ≫ hU.isoSpec.hom⟩
  rw [algebraMapOnOpen_top]
  change
    ((morphismRestrict f U ≫
      hU.isoSpec.hom).appTop).hom
        ((Scheme.ΓSpecIso
          (CommRingCat.of Γ(Y, U))).inv.hom r) =
      _
  rw [Scheme.Hom.comp_appTop,
    hU.isoSpec_hom_appTop]
  simp only [CommRingCat.comp_apply]
  have hcancel :
      (Scheme.ΓSpecIso Γ(Y, U)).hom.hom
          ((Scheme.ΓSpecIso
            (CommRingCat.of Γ(Y, U))).inv.hom r) =
        r := by
    exact
      (Scheme.ΓSpecIso
        (CommRingCat.of Γ(Y, U))).inv_hom_id_apply r
  rw [hcancel]
  have hrestrict :
      U.topIso.inv ≫
          (morphismRestrict f U).appTop =
        f.app U ≫
          (f ⁻¹ᵁ U).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict
      (f := f) (U := U)]
    have hres :
        (f.resLE U
          (f ⁻¹ᵁ U) le_rfl).appTop =
            U.topIso.hom ≫
              f.app U ≫
                (f ⁻¹ᵁ U).topIso.inv := by
      have h := Scheme.Hom.resLE_app_top
        (f := f) (U := U)
        (V := f ⁻¹ᵁ U) (e := le_rfl)
      rw [Scheme.Hom.appLE_eq_app] at h
      exact h
    rw [hres]
    exact
      U.topIso.inv_hom_id_assoc
        (f.app U ≫
          (f ⁻¹ᵁ U).topIso.inv)
  rw [← CommRingCat.comp_apply,
    hrestrict]
  rfl

/-- The direct-image sections over an affine open are linearly
equivalent to top sections of the restricted source module, with the
fixed-base scalar structure used by `moduleSheaf`. -/
noncomputable def pushforwardSectionsLinearEquivRestrictTop
    {X₀ Y₀ : Scheme.{0}}
    (f : X₀ ⟶ Y₀) (U : Y₀.Opens)
    (hU : IsAffineOpen U) (M : X₀.Modules) :
    letI :
        (f ⁻¹ᵁ U).toScheme.Over
          (Spec (CommRingCat.of Γ(Y₀, U))) :=
      ⟨morphismRestrict f U ≫ hU.isoSpec.hom⟩
    Γ((Scheme.Modules.pushforward f).obj M, U) ≃ₗ[Γ(Y₀, U)]
      ((moduleSheaf
        (k := Γ(Y₀, U))
        (M.restrict (f ⁻¹ᵁ U).ι)).obj.obj
          (op (⊤ :
            Opens ((f ⁻¹ᵁ U).toScheme : TopCat)))) := by
  letI :
      (f ⁻¹ᵁ U).toScheme.Over
        (Spec (CommRingCat.of Γ(Y₀, U))) :=
    ⟨morphismRestrict f U ≫ hU.isoSpec.hom⟩
  refine
    { toAddEquiv :=
        MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist.sectionsRestrictTopAddEquiv
          M (f ⁻¹ᵁ U)
      map_smul' := fun r x => ?_ }
  let xu : Γ(M, f ⁻¹ᵁ U) := x
  change
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist.sectionsRestrictTopAddEquiv
        M (f ⁻¹ᵁ U)
        ((M.smul ((f.app U).hom r)).hom xu) =
      ((M.restrict (f ⁻¹ᵁ U).ι).smul
        (algebraMapOnOpen
          (k := Γ(Y₀, U))
          (X := (f ⁻¹ᵁ U).toScheme) ⊤ r)).hom
        (MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist.sectionsRestrictTopAddEquiv
          M (f ⁻¹ᵁ U) xu)
  rw [sectionsRestrictTopAddEquiv_smul]
  rw [algebraMapOnOpen_preimage_top f U hU r]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
