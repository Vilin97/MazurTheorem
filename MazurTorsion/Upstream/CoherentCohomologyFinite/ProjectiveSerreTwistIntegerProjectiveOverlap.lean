/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerOverlapCompatibility

/-!
# Integer-twist trivializations on projective chart overlaps

This file transports the effective-descent overlap legs from the glued
standard cover to projective space.  Keeping the two legs as named
morphisms makes the pseudofunctor coherence calculations small enough for
the default heartbeat budget.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- Solved pseudofunctor associativity: ungroup a twofold pullback and
then regroup its inner pair. -/
lemma pullbackComp_inv_comp_map_hom_app
    {X Y Z T : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ T) (M : T.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app
          ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackComp g h).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (Category.assoc f g h).symm).inv.app M ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M := by
  rw [Scheme.Modules.pullbackComp_comp_fst_hom_app]
  simp

/-- Congruence compatibility for the inverse regrouping map, hom side. -/
lemma pullbackComp_inv_comp_map_congr_hom_app
    {X Y Z : Scheme} (f : X ⟶ Y) {g h : Y ⟶ Z}
    (e : g = h) (M : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app M ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackCongr e).hom.app M) =
      (Scheme.Modules.pullbackCongr
        (show f ≫ g = f ≫ h by rw [e])).hom.app M ≫
        (Scheme.Modules.pullbackComp f h).inv.app M := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

/-- Moving an equality cast across the hom side of a pullback-composition
comparison. -/
lemma pullbackCongr_inv_comp_pullbackComp_hom_app
    {X Y Z : Scheme} {f g : X ⟶ Y} (e : f = g)
    (h : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app
          ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp f h).hom.app M =
      (Scheme.Modules.pullbackComp g h).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (show g ≫ h = f ≫ h by rw [e])).hom.app M := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

/-- A square made from a pullback-composition comparison and three equality
casts commutes.  This packages proof irrelevance for the two paths through
the same pseudofunctorial pullback square. -/
lemma pullbackComp_congr_square
    {X Y Z : Scheme} {f g : X ⟶ Y} (e : f = g)
    (h : Y ⟶ Z) {u v : X ⟶ Z}
    (hf : f ≫ h = u) (hg : g ≫ h = v) (huv : u = v)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app
          ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp f h).hom.app M ≫
        (Scheme.Modules.pullbackCongr hf).hom.app M =
      (Scheme.Modules.pullbackComp g h).hom.app M ≫
        (Scheme.Modules.pullbackCongr hg).hom.app M ≫
        (Scheme.Modules.pullbackCongr huv).inv.app M := by
  subst e
  subst hf
  subst hg
  simp [Scheme.Modules.pullbackCongr]

/-- The canonical comparison from the projective overlap pullback of the
integer twist to the overlap pullback of its descended model. -/
abbrev projectiveIntegerOverlapToGlued
    (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullbackComp
      (integerCompatibilityFirstMap k d i j ≫
        integerCompatibilityProjectiveChartMap k d i)
      (inv (cover k d).fromGlued)).hom.app
      (effectiveGluedIntegerModule k d m) ≫
    (Scheme.Modules.pullbackCongr
      (show
        ((integerCompatibilityFirstMap k d i j ≫
              integerCompatibilityProjectiveChartMap k d i) ≫
            inv (cover k d).fromGlued) =
          integerCompatibilityFirstMap k d i j ≫
            integerCompatibilityChartMap k d i by
        exact
          (Category.assoc _ _ _).trans
            (congrArg
              (fun q => integerCompatibilityFirstMap k d i j ≫ q)
              (chart_comp_fromGlued_inv_typed k d i)))).hom.app
      (effectiveGluedIntegerModule k d m)

/-- The analogous comparison based on the second chart. -/
abbrev projectiveIntegerSecondOverlapToGlued
    (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullbackComp
      (integerCompatibilitySecondMap k d i j ≫
        integerCompatibilityProjectiveChartMap k d j)
      (inv (cover k d).fromGlued)).hom.app
      (effectiveGluedIntegerModule k d m) ≫
    (Scheme.Modules.pullbackCongr
      (show
        ((integerCompatibilitySecondMap k d i j ≫
              integerCompatibilityProjectiveChartMap k d j) ≫
            inv (cover k d).fromGlued) =
          integerCompatibilitySecondMap k d i j ≫
            integerCompatibilityChartMap k d j by
        exact
          (Category.assoc _ _ _).trans
            (congrArg
              (fun q =>
                integerCompatibilitySecondMap k d i j ≫ q)
              (chart_comp_fromGlued_inv_typed k d j)))).hom.app
      (effectiveGluedIntegerModule k d m)

/-- Restrict the projective integer twist through chart `i` to the
scheme-theoretic overlap of charts `i` and `j`. -/
def projectiveIntegerFirstChartLeg
    (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullbackComp
      (integerCompatibilityFirstMap k d i j)
      (integerCompatibilityProjectiveChartMap k d i)).inv.app
      (OInt k d m) ≫
    (Scheme.Modules.pullback
      (integerCompatibilityFirstMap k d i j)).map
      ((Scheme.Modules.pullbackComp
          (integerCompatibilityProjectiveChartMap k d i)
          (inv (cover k d).fromGlued)).hom.app
            (gluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (chart_comp_fromGlued_inv_typed k d i)).hom.app
            (gluedIntegerModule k d m) ≫
        effectiveGluedIntegerChartHom k d m i)

/-- The projective chart-overlap equality, with the parenthesization used
by the pullback-congruence cast. -/
theorem projectiveIntegerOverlapEquation
    (i j : Fin (d + 1)) :
    integerCompatibilitySecondMap k d i j ≫
        integerCompatibilityProjectiveChartMap k d j =
      integerCompatibilityFirstMap k d i j ≫
        integerCompatibilityProjectiveChartMap k d i :=
  cover_glue_condition k d i j

/-- The equality cast identifying the chart-`j` presentation of the
projective overlap with its chart-`i` presentation. -/
abbrev projectiveIntegerOverlapCast
    (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullbackCongr
      (projectiveIntegerOverlapEquation k d i j)).inv.app (OInt k d m)

/-- The chart-`j` restriction core before the equality cast to the
chart-`i` presentation. -/
def projectiveIntegerSecondChartLegCore
    (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullbackComp
      (integerCompatibilitySecondMap k d i j)
      (integerCompatibilityProjectiveChartMap k d j)).inv.app
      (OInt k d m) ≫
    (Scheme.Modules.pullback
      (integerCompatibilitySecondMap k d i j)).map
        ((Scheme.Modules.pullbackComp
            (integerCompatibilityProjectiveChartMap k d j)
            (inv (cover k d).fromGlued)).hom.app
              (gluedIntegerModule k d m) ≫
          (Scheme.Modules.pullbackCongr
            (chart_comp_fromGlued_inv_typed k d j)).hom.app
              (gluedIntegerModule k d m) ≫
          effectiveGluedIntegerChartHom k d m j)

/-- Restrict through chart `j`, with the canonical cast to the same
overlap pullback as the first leg. -/
def projectiveIntegerSecondChartLeg
    (m : ℤ) (i j : Fin (d + 1)) :=
  projectiveIntegerOverlapCast k d m i j ≫
    projectiveIntegerSecondChartLegCore k d m i j

/-- The first projective chart leg in the structure-sheaf frame. -/
def projectiveIntegerFirstScalarLeg
    (m : ℤ) (i j : Fin (d + 1)) :=
  projectiveIntegerFirstChartLeg k d m i j ≫
    (pullbackUnitIso ((glueData k d).f i j)).hom

/-- The second projective chart leg in the first chart frame. -/
def projectiveIntegerSecondScalarLeg
    (m : ℤ) (i j : Fin (d + 1)) :=
  projectiveIntegerSecondChartLeg k d m i j ≫
    (pullbackUnitIso
      ((glueData k d).t i j ≫
        (glueData k d).f j i)).hom ≫
    endomorphism (((overlapUnit k d i j) ^ m).inv)

/-- The first projective chart leg is the descended first leg after the
canonical projective-to-glued comparison. -/
lemma projectiveIntegerFirstChartLeg_factor
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerFirstChartLeg k d m i j =
      projectiveIntegerOverlapToGlued k d m i j ≫
        gluedIntegerFirstChartLeg k d m i j := by
  dsimp only [projectiveIntegerFirstChartLeg,
    projectiveIntegerOverlapToGlued,
    gluedIntegerFirstChartLeg,
    OInt, integerModule,
    effectiveGluedIntegerModule,
    Iso.trans_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of%
    pullbackComp_inv_comp_map_hom_app
      (integerCompatibilityFirstMap k d i j)
      (integerCompatibilityProjectiveChartMap k d i)
      (inv (cover k d).fromGlued)
      (gluedIntegerModule k d m)]
  rw [reassoc_of%
    pullbackComp_inv_comp_map_congr_hom_app
      (integerCompatibilityFirstMap k d i j)
      (chart_comp_fromGlued_inv_typed k d i)
      (gluedIntegerModule k d m)]
  simp only [Scheme.Modules.pullbackCongr_hom_app_eqToHom,
    Scheme.Modules.pullbackCongr_inv_app_eqToHom,
    eqToHom_trans_assoc]

/-- The second chart route factors through its projective-to-glued
comparison before applying the descended second core leg. -/
lemma projectiveIntegerSecondChartCore_factor
    (m : ℤ) (i j : Fin (d + 1)) :
    projectiveIntegerSecondChartLegCore k d m i j =
      projectiveIntegerSecondOverlapToGlued k d m i j ≫
        gluedIntegerSecondChartLegCore k d m i j := by
  dsimp only [projectiveIntegerSecondOverlapToGlued,
    projectiveIntegerSecondChartLegCore,
    gluedIntegerSecondChartLegCore,
    OInt, integerModule,
    effectiveGluedIntegerModule,
    Iso.trans_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of%
    pullbackComp_inv_comp_map_hom_app
      (integerCompatibilitySecondMap k d i j)
      (integerCompatibilityProjectiveChartMap k d j)
      (inv (cover k d).fromGlued)
      (gluedIntegerModule k d m)]
  rw [reassoc_of%
    pullbackComp_inv_comp_map_congr_hom_app
      (integerCompatibilitySecondMap k d i j)
      (chart_comp_fromGlued_inv_typed k d j)
      (gluedIntegerModule k d m)]
  simp only [Scheme.Modules.pullbackCongr_hom_app_eqToHom,
    Scheme.Modules.pullbackCongr_inv_app_eqToHom,
    eqToHom_trans_assoc]

/-- The raw projective/glued overlap-transport square, kept opaque so
later pointwise comparisons do not normalize the cast-coherence proof. -/
theorem projectiveIntegerOverlapTransportSquareRaw
    (m : ℤ) (i j : Fin (d + 1)) :
    (Scheme.Modules.pullbackCongr
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
          (effectiveGluedIntegerModule k d m) =
      (Scheme.Modules.pullbackComp
          ((glueData k d).f i j ≫ (cover k d).f i)
          (inv (cover k d).fromGlued)).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (show
            (((glueData k d).f i j ≫
                  (cover k d).f i) ≫
                inv (cover k d).fromGlued) =
              (glueData k d).f i j ≫
                (glueData k d).ι i by
            exact
              (Category.assoc _ _ _).trans
                (congrArg
                  (fun q => (glueData k d).f i j ≫ q)
                  (chart_comp_fromGlued_inv k d i)))).hom.app
          (effectiveGluedIntegerModule k d m) ≫
        (Scheme.Modules.pullbackCongr
          (integerCompatibilityGluedOverlapEquation k d i j)).inv.app
          (glueObject
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)) :=
  pullbackComp_congr_square
    (projectiveIntegerOverlapEquation k d i j)
    (inv (cover k d).fromGlued)
    (show
      ((((glueData k d).t i j ≫ (glueData k d).f j i) ≫
            (cover k d).f j) ≫ inv (cover k d).fromGlued) =
        ((glueData k d).t i j ≫ (glueData k d).f j i) ≫
          (glueData k d).ι j by
      exact
        (Category.assoc _ _ _).trans
          (congrArg
            (fun q =>
              ((glueData k d).t i j ≫
                (glueData k d).f j i) ≫ q)
            (chart_comp_fromGlued_inv k d j)))
    (show
      (((glueData k d).f i j ≫ (cover k d).f i) ≫
          inv (cover k d).fromGlued) =
        (glueData k d).f i j ≫ (glueData k d).ι i by
      exact
        (Category.assoc _ _ _).trans
          (congrArg
            (fun q => (glueData k d).f i j ≫ q)
            (chart_comp_fromGlued_inv k d i)))
    (integerCompatibilityGluedOverlapEquation k d i j)
    (glueObject
      (glueData k d)
      (integerChartModules k d)
      (integerTransitionFamily k d m)
      (integerIdentityFamily k d m)
      (integerCocycleFamily k d m))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
