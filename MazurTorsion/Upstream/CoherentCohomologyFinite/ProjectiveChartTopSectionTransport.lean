/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartSchemeIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartSectionTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionEpi
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoTopSectionFormula
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleRestrictionSectionComposition
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleTopSectionIso

/-!
# Transporting affine-chart sections to standard projective opens

This file separates the three canonical transports used for a section on
an affine chart:

1. compare restriction along the affine-cover map with iterated
   restriction through the canonical open subscheme;
2. transport across the affine-chart scheme isomorphism;
3. identify the terminal section on the open subscheme with an ambient
   section over the standard projective open.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/-- A section on the affine-spectrum chart, expressed after the comparison
with iterated restriction through the canonical open subscheme. -/
def chartIteratedRestrictionTopSection
    (M : (scheme k d).Modules) (i : Fin (d + 1))
    (x : Γ(chartModule k d M i, ⊤)) :
    Γ((M.restrict (standardChart k i).ι).restrict
        (standardChartSchemeIso k d i).hom, ⊤) :=
  Scheme.Modules.moduleIsoTopSection
    (chartModuleRestrictionIso k d M i) x

/-- The corresponding terminal section on the canonical standard open
subscheme. -/
def chartOpenTopSection
    (M : (scheme k d).Modules) (i : Fin (d + 1))
    (x : Γ(chartModule k d M i, ⊤)) :
    Γ(M.restrict (standardChart k i).ι, ⊤) :=
  Scheme.Modules.isoTransportedTopSection
    (standardChartSchemeIso k d i)
    (M.restrict (standardChart k i).ι)
    (chartIteratedRestrictionTopSection k d M i x)

/-- The preceding section, viewed as an ambient section over the standard
projective open. -/
def chartTransportedAmbientSection
    (M : (scheme k d).Modules) (i : Fin (d + 1))
    (x : Γ(chartModule k d M i, ⊤)) :
    Γ(M, standardChart k i) :=
  (eqToIso
    (congrArg (fun V => Γ(M, V))
      (standardChart k i).ι_image_top)).hom
    ((M.restrictAppIso (standardChart k i).ι ⊤).hom
      (chartOpenTopSection k d M i x))

/-- The factored transport agrees with the direct chart-section
identification used throughout the projective construction. -/
theorem chartTransportedAmbientSection_eq
    (M : (scheme k d).Modules) (i : Fin (d + 1))
    (x : Γ(chartModule k d M i, ⊤)) :
    chartTransportedAmbientSection k d M i x =
      (chartTopSectionsIso k d M i).hom x := by
  letI hAffine : IsOpenImmersion
      (standardChartMap k d i) :=
    standardChartMap_isOpenImmersion k d i
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
  unfold chartTransportedAmbientSection
  rw [show
    chartOpenTopSection k d M i x =
      Scheme.Modules.directIsoTransportedTopSection
        (standardChartSchemeIso k d i)
        (M.restrict (standardChart k i).ι)
        (chartIteratedRestrictionTopSection k d M i x) from
    Scheme.Modules.isoTransportedTopSection_eq_direct
      (standardChartSchemeIso k d i)
      (M.restrict (standardChart k i).ι)
      (chartIteratedRestrictionTopSection k d M i x)]
  unfold chartIteratedRestrictionTopSection
  unfold Scheme.Modules.moduleIsoTopSection
  unfold Scheme.Modules.directIsoTransportedTopSection
  unfold chartModuleRestrictionIso
  let hfactor :
      standardChartMap k d i =
        (standardChartSchemeIso k d i).hom ≫
          (standardChart k i).ι := by
    change
      (standardAffineOpenCover k d).f i =
        (standardChartSchemeIso k d i).hom ≫
          (standardChart k i).ι
    exact (standardChartSchemeIso_hom_comp_ι k d i).symm
  let A :=
    (@Scheme.Modules.restrictFunctorCongr
      _ _
      (standardChartMap k d i)
      ((standardChartSchemeIso k d i).hom ≫
        (standardChart k i).ι)
      hfactor hAffine hComp).hom.app M
  let B :=
    (@Scheme.Modules.restrictFunctorComp
      _ _ _
      (standardChartSchemeIso k d i).hom
      (standardChart k i).ι hIso hOpen).hom.app M
  let y :=
    B.app (⊤ : (Spec (chartRing k d i)).Opens)
      (A.app (⊤ : (Spec (chartRing k d i)).Opens) x)
  refine
    (congrArg
      (fun z =>
        (eqToIso
          (congrArg (fun V => Γ(M, V))
            (standardChart k i).ι_image_top)).hom
          ((M.restrictAppIso (standardChart k i).ι ⊤).hom
            ((eqToIso
              (congrArg
                (fun V =>
                  Γ(M.restrict (standardChart k i).ι, V))
                (Scheme.Modules.iso_hom_image_top
                  (standardChartSchemeIso k d i)))).hom
              (((M.restrict (standardChart k i).ι).restrictAppIso
                (standardChartSchemeIso k d i).hom ⊤).hom z))))
      (show
        (A ≫ B).val.app
            (op (⊤ : (Spec (chartRing k d i)).Opens)) x =
          y from by
        exact SheafOfModules.comp_val_app_apply
          A B (op (⊤ : (Spec (chartRing k d i)).Opens)) x)).trans ?_
  refine
    (congrArg
      (fun z =>
        (eqToIso
          (congrArg (fun V => Γ(M, V))
            (standardChart k i).ι_image_top)).hom z)
      (@Scheme.Modules.restrictIso_comp_hom_top_section
        _ _ _
        (standardChartSchemeIso k d i)
        (standardChart k i).ι hOpen
        (standardChartMap k d i) hAffine
        hfactor M x)).trans ?_
  unfold chartTopSectionsIso
  simp only [Iso.trans_hom, CategoryTheory.comp_apply]
  rw [Scheme.Modules.eqToIso_sections_hom_eq_map M
    (standardChart k i).ι_image_top]
  rw [Scheme.Modules.eqToIso_sections_hom_eq_map M
    (@Scheme.Modules.image_top_eq_of_iso_comp
      _ _ _
      (standardChartSchemeIso k d i)
      (standardChart k i).ι hOpen
      (standardChartMap k d i) hAffine
      hfactor)]
  rw [Scheme.Modules.eqToIso_sections_hom_eq_map M
    (standardAffineCover_image_top k d i)]
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom]
  let x' : Γ(M, standardChartMap k d i ''ᵁ ⊤) := x
  change
    M.presheaf.map _
      (M.presheaf.map _ x') =
      M.presheaf.map _ x'
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact
    ConcreteCategory.congr_hom
      (congrArg
        (fun r => M.presheaf.map r)
        (Subsingleton.elim _ _))
      x'

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
