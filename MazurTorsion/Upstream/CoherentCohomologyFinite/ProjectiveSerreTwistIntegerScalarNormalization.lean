/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarComponents

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

private theorem comp_five_reassociate
    {C : Type*} [Category C] {A B C₁ D E F : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ D)
    (e : D ⟶ E) (f : E ⟶ F) :
    (a ≫ b) ≫ ((c ≫ e) ≫ f) =
      (a ≫ (b ≫ c)) ≫ (e ≫ f) := by
  simp only [Category.assoc]

theorem morphism_eq_whisker_both
    {C : Type*} [Category C] {W X Y Z : C}
    (p : W ⟶ X) {f g : X ⟶ Y} (h : f = g) (q : Y ⟶ Z) :
    (p ≫ f) ≫ q = (p ≫ g) ≫ q :=
  congrArg (fun r => (p ≫ r) ≫ q) h

theorem morphism_eq_whisker_left
    {C : Type*} [Category C] {W X Y : C}
    (p : W ⟶ X) {f g : X ⟶ Y} (h : f = g) :
    p ≫ f = p ≫ g :=
  congrArg (fun r => p ≫ r) h

/-- The raw suffix is the named descended second core followed by the
transition and the first-chart unit trivialization. -/
theorem integerRawSecondScalarSuffix_eq_named
    (m : ℤ) (i j : Fin (d + 1)) :
    integerRawSecondScalarSuffix k d m i j =
      gluedIntegerSecondChartLegCore k d m i j ≫
        (integerTransitionFamily k d m i j).inv ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom := by
  rfl

/-- Replace only the literal second projective-to-glued comparison by its
name, leaving the scalar suffix opaque. -/
theorem projectiveIntegerRawSecondComparison_normalize
    (m : ℤ) (i j : Fin (d + 1)) :
    ((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m) ≫
        (Scheme.Modules.pullbackComp
          (((glueData k d).t i j ≫
              (glueData k d).f j i) ≫
            (cover k d).f j)
          (inv (cover k d).fromGlued)).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (show
            ((((glueData k d).t i j ≫
                  (glueData k d).f j i) ≫
                  (cover k d).f j) ≫
                inv (cover k d).fromGlued) =
              ((glueData k d).t i j ≫
                (glueData k d).f j i) ≫
                (glueData k d).ι j by
            exact
              (Category.assoc _ _ _).trans
                (congrArg
                  (fun q =>
                    ((glueData k d).t i j ≫
                      (glueData k d).f j i) ≫ q)
                  (chart_comp_fromGlued_inv k d j)))).hom.app
          (effectiveGluedIntegerModule k d m)) ≫
        integerRawSecondScalarSuffix k d m i j =
      ((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m) ≫
        projectiveIntegerSecondOverlapToGlued k d m i j) ≫
          integerRawSecondScalarSuffix k d m i j := by
  exact morphism_eq_whisker_both
    ((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m))
    (projectiveIntegerSecondOverlapToGlued_eq_raw
      k d m i j).symm
    (integerRawSecondScalarSuffix k d m i j)

/-- Replace only the raw descended suffix by its named second chart core. -/
theorem projectiveIntegerNamedSecondComparison_suffix
    (m : ℤ) (i j : Fin (d + 1)) :
    ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m) ≫
        projectiveIntegerSecondOverlapToGlued k d m i j) ≫
          integerRawSecondScalarSuffix k d m i j =
      ((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m) ≫
        projectiveIntegerSecondOverlapToGlued k d m i j) ≫
          (gluedIntegerSecondChartLegCore k d m i j ≫
            (integerTransitionFamily k d m i j).inv ≫
              (pullbackUnitIso ((glueData k d).f i j)).hom) := by
  exact morphism_eq_whisker_left
    ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m) ≫
      projectiveIntegerSecondOverlapToGlued k d m i j)
    (integerRawSecondScalarSuffix_eq_named k d m i j)

/-- Reassociate the named second route so that the comparison and descended
core form the factor appearing in
`projectiveIntegerSecondChartCore_factor`. -/
theorem projectiveIntegerNamedSecondComparison_reassoc
    (m : ℤ) (i j : Fin (d + 1)) :
    ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m) ≫
        projectiveIntegerSecondOverlapToGlued k d m i j) ≫
          (gluedIntegerSecondChartLegCore k d m i j ≫
            (integerTransitionFamily k d m i j).inv ≫
              (pullbackUnitIso ((glueData k d).f i j)).hom) =
      ((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m) ≫
        (projectiveIntegerSecondOverlapToGlued k d m i j ≫
          gluedIntegerSecondChartLegCore k d m i j)) ≫
        ((integerTransitionFamily k d m i j).inv ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom) := by
  exact comp_five_reassociate
    ((Scheme.Modules.pullbackCongr
      (projectiveIntegerOverlapEquation k d i j)).inv.app
      (OInt k d m))
    (projectiveIntegerSecondOverlapToGlued k d m i j)
    (gluedIntegerSecondChartLegCore k d m i j)
    (integerTransitionFamily k d m i j).inv
    (pullbackUnitIso ((glueData k d).f i j)).hom

/-- The named comparison and descended core combine to the direct
projective second chart core. -/
theorem projectiveIntegerNamedSecondChartCore_factor
    (m : ℤ) (i j : Fin (d + 1)) :
    ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m) ≫
        (projectiveIntegerSecondOverlapToGlued k d m i j ≫
          gluedIntegerSecondChartLegCore k d m i j)) ≫
        ((integerTransitionFamily k d m i j).inv ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom) =
      ((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m) ≫
        projectiveIntegerSecondChartLegCore k d m i j) ≫
        ((integerTransitionFamily k d m i j).inv ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom) := by
  exact morphism_eq_whisker_both
    ((Scheme.Modules.pullbackCongr
      (projectiveIntegerOverlapEquation k d i j)).inv.app
      (OInt k d m))
    (projectiveIntegerSecondChartCore_factor k d m i j).symm
    ((integerTransitionFamily k d m i j).inv ≫
      (pullbackUnitIso ((glueData k d).f i j)).hom)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
