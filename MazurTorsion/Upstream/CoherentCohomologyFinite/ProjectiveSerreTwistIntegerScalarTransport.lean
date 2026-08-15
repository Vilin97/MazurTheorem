/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarDescent

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

local macro "integerRawOverlapCast%(" k:term "," d:term "," m:term ","
    i:term "," j:term ")" : term =>
  `((Scheme.Modules.pullbackCongr
      (integerCompatibilityGluedOverlapEquation $k $d $i $j)).inv.app
      (glueObject
        (glueData $k $d)
        (integerChartModules $k $d)
        (integerTransitionFamily $k $d $m)
        (integerIdentityFamily $k $d $m)
        (integerCocycleFamily $k $d $m)))

private theorem comp_four_reassociate
    {C : Type*} [Category C] {A B C₁ D E : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ D) (e : D ⟶ E) :
    a ≫ ((b ≫ c) ≫ e) = (a ≫ b) ≫ (c ≫ e) := by
  simp only [Category.assoc]

/-- The part of the raw second-chart route following the
projective/glued transport square. -/
def integerRawSecondScalarSuffix
    (m : ℤ) (i j : Fin (d + 1)) :=
  ((Scheme.Modules.pullbackComp
      ((glueData k d).t i j ≫ (glueData k d).f j i)
      ((glueData k d).ι j)).inv.app
        (glueObject
          (glueData k d)
          (integerChartModules k d)
          (integerTransitionFamily k d m)
          (integerIdentityFamily k d m)
          (integerCocycleFamily k d m)) ≫
      (Scheme.Modules.pullback
        ((glueData k d).t i j ≫
          (glueData k d).f j i)).map
          (restrictionIso
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)
            j).hom ≫
        (integerTransitionFamily k d m i j).inv) ≫
    (pullbackUnitIso ((glueData k d).f i j)).hom

/-- The raw second scalar route before reassociation at the transport
square. -/
def projectiveIntegerRawSecondScalarBeforeTransport
    (m : ℤ) (i j : Fin (d + 1)) :=
  projectiveIntegerOverlapToGlued k d m i j ≫
    ((integerRawOverlapCast%(k, d, m, i, j) ≫
        (gluedIntegerSecondChartLegCore k d m i j ≫
          (integerTransitionFamily k d m i j).inv)) ≫
      (pullbackUnitIso ((glueData k d).f i j)).hom)

/-- The same raw second scalar route, grouped at the right endpoint of
the projective/glued transport square. -/
def projectiveIntegerRawSecondScalarTransportRight
    (m : ℤ) (i j : Fin (d + 1)) :=
  (projectiveIntegerOverlapToGlued k d m i j ≫
      integerRawOverlapCast%(k, d, m, i, j)) ≫
    integerRawSecondScalarSuffix k d m i j

/-- Normalize the raw second descent route to the right endpoint of the
projective/glued transport square. -/
theorem projectiveIntegerRawSecondScalar_to_transportRight
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerOverlapToGlued k d m i j ≫
        ((integerRawOverlapCast%(k, d, m, i, j) ≫
            (gluedIntegerSecondChartLegCore k d m i j ≫
              (integerTransitionFamily k d m i j).inv)) ≫
          (pullbackUnitIso ((glueData k d).f i j)).hom) =
      projectiveIntegerRawSecondScalarTransportRight k d m i j := by
  unfold projectiveIntegerRawSecondScalarTransportRight
  unfold integerRawSecondScalarSuffix
  exact comp_four_reassociate
    (projectiveIntegerOverlapToGlued k d m i j)
    (integerRawOverlapCast%(k, d, m, i, j))
    (gluedIntegerSecondChartLegCore k d m i j ≫
      (integerTransitionFamily k d m i j).inv)
    (pullbackUnitIso ((glueData k d).f i j)).hom

private theorem projectiveIntegerOverlapToGlued_eq_raw
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerOverlapToGlued k d m i j =
      (Scheme.Modules.pullbackComp
          ((glueData k d).f i j ≫ (cover k d).f i)
          (inv (cover k d).fromGlued)).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (show
            (((glueData k d).f i j ≫ (cover k d).f i) ≫
                inv (cover k d).fromGlued) =
              (glueData k d).f i j ≫ (glueData k d).ι i by
            exact
              (Category.assoc _ _ _).trans
                (congrArg
                  (fun q => (glueData k d).f i j ≫ q)
                  (chart_comp_fromGlued_inv k d i)))).hom.app
          (effectiveGluedIntegerModule k d m) := by
  rfl

/-- Replace the named projective comparison by the exact raw endpoint used
in the transport square. -/
theorem projectiveIntegerRawSecondScalar_to_transportEndpoint
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerRawSecondScalarTransportRight k d m i j =
      (((Scheme.Modules.pullbackComp
            ((glueData k d).f i j ≫ (cover k d).f i)
            (inv (cover k d).fromGlued)).hom.app
            (effectiveGluedIntegerModule k d m) ≫
          (Scheme.Modules.pullbackCongr
            (show
              (((glueData k d).f i j ≫ (cover k d).f i) ≫
                  inv (cover k d).fromGlued) =
                (glueData k d).f i j ≫ (glueData k d).ι i by
              exact
                (Category.assoc _ _ _).trans
                  (congrArg
                    (fun q => (glueData k d).f i j ≫ q)
                    (chart_comp_fromGlued_inv k d i)))).hom.app
            (effectiveGluedIntegerModule k d m)) ≫
          integerRawOverlapCast%(k, d, m, i, j)) ≫
        integerRawSecondScalarSuffix k d m i j := by
  unfold projectiveIntegerRawSecondScalarTransportRight
  exact congrArg
    (fun q => (q ≫ integerRawOverlapCast%(k, d, m, i, j)) ≫
      integerRawSecondScalarSuffix k d m i j)
    (projectiveIntegerOverlapToGlued_eq_raw k d m i j)

/-- Reassociate the raw first-chart transport endpoint into the literal
parenthesization used by the pullback transport square. -/
theorem projectiveIntegerRawSecondScalar_transportEndpoint_reassoc
    (m : ℤ) (i j : Fin (d + 1)) :
    (((Scheme.Modules.pullbackComp
          ((glueData k d).f i j ≫ (cover k d).f i)
          (inv (cover k d).fromGlued)).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (show
            (((glueData k d).f i j ≫ (cover k d).f i) ≫
                inv (cover k d).fromGlued) =
              (glueData k d).f i j ≫ (glueData k d).ι i by
            exact
              (Category.assoc _ _ _).trans
                (congrArg
                  (fun q => (glueData k d).f i j ≫ q)
                  (chart_comp_fromGlued_inv k d i)))).hom.app
          (effectiveGluedIntegerModule k d m)) ≫
        integerRawOverlapCast%(k, d, m, i, j)) ≫
      integerRawSecondScalarSuffix k d m i j =
    ((Scheme.Modules.pullbackComp
          ((glueData k d).f i j ≫ (cover k d).f i)
          (inv (cover k d).fromGlued)).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        ((Scheme.Modules.pullbackCongr
          (show
            (((glueData k d).f i j ≫ (cover k d).f i) ≫
                inv (cover k d).fromGlued) =
              (glueData k d).f i j ≫ (glueData k d).ι i by
            exact
              (Category.assoc _ _ _).trans
                (congrArg
                  (fun q => (glueData k d).f i j ≫ q)
                  (chart_comp_fromGlued_inv k d i)))).hom.app
          (effectiveGluedIntegerModule k d m) ≫
            integerRawOverlapCast%(k, d, m, i, j))) ≫
      integerRawSecondScalarSuffix k d m i j := by
  exact congrArg
    (fun q => q ≫ integerRawSecondScalarSuffix k d m i j)
    (Category.assoc
      ((Scheme.Modules.pullbackComp
        ((glueData k d).f i j ≫ (cover k d).f i)
        (inv (cover k d).fromGlued)).hom.app
        (effectiveGluedIntegerModule k d m))
      ((Scheme.Modules.pullbackCongr
        (show
          (((glueData k d).f i j ≫ (cover k d).f i) ≫
              inv (cover k d).fromGlued) =
            (glueData k d).f i j ≫ (glueData k d).ι i by
          exact
            (Category.assoc _ _ _).trans
              (congrArg
                (fun q => (glueData k d).f i j ≫ q)
                (chart_comp_fromGlued_inv k d i)))).hom.app
        (effectiveGluedIntegerModule k d m))
      (integerRawOverlapCast%(k, d, m, i, j)))

/-- Whiskered form of the raw projective/glued transport square. -/
theorem projectiveIntegerRawSecondScalar_transport
    (m : ℤ) (i j : Fin (d + 1)) :
    ((Scheme.Modules.pullbackComp
          ((glueData k d).f i j ≫ (cover k d).f i)
          (inv (cover k d).fromGlued)).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (show
            (((glueData k d).f i j ≫ (cover k d).f i) ≫
                inv (cover k d).fromGlued) =
              (glueData k d).f i j ≫ (glueData k d).ι i by
            exact
              (Category.assoc _ _ _).trans
                (congrArg
                  (fun q => (glueData k d).f i j ≫ q)
                  (chart_comp_fromGlued_inv k d i)))).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (integerCompatibilityGluedOverlapEquation k d i j)).inv.app
          (effectiveGluedIntegerModule k d m)) ≫
      integerRawSecondScalarSuffix k d m i j =
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
        integerRawSecondScalarSuffix k d m i j := by
  exact congrArg
    (fun q => q ≫ integerRawSecondScalarSuffix k d m i j)
    (projectiveIntegerOverlapTransportSquareRaw k d m i j).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
