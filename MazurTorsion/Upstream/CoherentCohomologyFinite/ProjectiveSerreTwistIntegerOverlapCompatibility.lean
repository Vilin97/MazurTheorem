/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInteger
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentEffectiveBridge

/-!
# Compatibility of the integer-twist chart trivializations

The integer Serre twist is obtained by effective descent.  This file records
the overlap equation satisfied by the canonical chart trivializations.  It is
kept at the morphism level so that it can later be restricted to any smaller
standard intersection.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- The standard pair-overlap scheme, with its projective-space indices
exposed in the public type. -/
def integerCompatibilityOverlapScheme (i j : Fin (d + 1)) : Scheme :=
  (glueData k d).V (i, j)

/-- A standard affine chart with its public projective-space index. -/
def integerCompatibilityChartScheme (i : Fin (d + 1)) : Scheme :=
  (standardChart k i).toScheme

/-- The unit module on an exposed standard chart. -/
def integerCompatibilityChartUnit (i : Fin (d + 1)) :
    (integerCompatibilityChartScheme k d i).Modules :=
  SheafOfModules.unit
    (integerCompatibilityChartScheme k d i).ringCatSheaf

/-- The standard chart inclusion into projective space, with exposed index. -/
def integerCompatibilityProjectiveChartMap (i : Fin (d + 1)) :
    integerCompatibilityChartScheme k d i ⟶ scheme k d :=
  (cover k d).f i

def integerCompatibilityFirstMap (i j : Fin (d + 1)) :
    integerCompatibilityOverlapScheme k d i j ⟶
      integerCompatibilityChartScheme k d i :=
  (glueData k d).f i j

def integerCompatibilitySecondMap (i j : Fin (d + 1)) :
    integerCompatibilityOverlapScheme k d i j ⟶
      integerCompatibilityChartScheme k d j :=
  (glueData k d).t i j ≫ (glueData k d).f j i

def integerCompatibilityOverlapUnit (i j : Fin (d + 1)) :
    Γ(integerCompatibilityOverlapScheme k d i j, ⊤)ˣ :=
  overlapUnit k d i j

/-- The standard chart inclusion with the public cover chart as its
domain, shielding the definitionally equal glued-cover chart type. -/
def integerCompatibilityChartMap (i : Fin (d + 1)) :
    integerCompatibilityChartScheme k d i ⟶
      (glueData k d).glued :=
  (glueData k d).ι i

theorem chart_comp_fromGlued_inv_typed (i : Fin (d + 1)) :
    integerCompatibilityProjectiveChartMap k d i ≫
        inv (cover k d).fromGlued =
      integerCompatibilityChartMap k d i :=
  chart_comp_fromGlued_inv k d i

/-- The first canonical unit trivialization on a standard pair overlap,
kept opaque so later rewrites retain the exposed index type. -/
def integerFirstPullbackUnitIso (i j : Fin (d + 1)) :
    (Scheme.Modules.pullback
      (integerCompatibilityFirstMap k d i j)).obj
        (SheafOfModules.unit
          ((glueData k d).U i).ringCatSheaf) ≅
      SheafOfModules.unit
        (integerCompatibilityOverlapScheme k d i j).ringCatSheaf :=
  pullbackUnitIso (integerCompatibilityFirstMap k d i j)

/-- The second canonical unit trivialization on a standard pair overlap,
kept opaque so later rewrites retain the exposed index type. -/
def integerSecondPullbackUnitIso (i j : Fin (d + 1)) :
    (Scheme.Modules.pullback
      (integerCompatibilitySecondMap k d i j)).obj
        (SheafOfModules.unit
          ((glueData k d).U j).ringCatSheaf) ≅
      SheafOfModules.unit
        (integerCompatibilityOverlapScheme k d i j).ringCatSheaf :=
  pullbackUnitIso (integerCompatibilitySecondMap k d i j)

lemma integerTransition_eq_typed (m : ℤ)
    (i j : Fin (d + 1)) :
    integerTransition k d m i j =
      integerFirstPullbackUnitIso k d i j ≪≫
        unitIso ((integerCompatibilityOverlapUnit k d i j) ^ m) ≪≫
        (integerSecondPullbackUnitIso k d i j).symm := by
  rfl

private lemma transTransSymm_inv_comp_first
    {C : Type u} [Category.{v} C] {A B D E : C}
    (a : A ≅ B) (b : B ≅ D) (c : E ≅ D) :
    (a ≪≫ b ≪≫ c.symm).inv ≫ a.hom =
      c.hom ≫ b.inv := by
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The integer descended module, presented through named descent data. -/
abbrev effectiveGluedIntegerModule (m : ℤ) :
    (glueData k d).glued.Modules :=
  gluedIntegerModule k d m

/-- Its effective-descent chart trivialization. -/
abbrev effectiveGluedIntegerChartIso (m : ℤ) (i : Fin (d + 1)) :
    (Scheme.Modules.pullback ((glueData k d).ι i)).obj
        (effectiveGluedIntegerModule k d m) ≅
      integerChartModules k d i :=
  gluedIntegerChartIso k d m i

/-- The named descent presentation is definitionally the original integer
Serre-twist presentation. -/
lemma effectiveGluedIntegerModule_eq (m : ℤ) :
    effectiveGluedIntegerModule k d m =
      gluedIntegerModule k d m := by
  rfl

/-- The named effective-descent trivialization is the original chart
trivialization. -/
lemma effectiveGluedIntegerChartIso_eq (m : ℤ)
    (i : Fin (d + 1)) :
    effectiveGluedIntegerChartIso k d m i =
      gluedIntegerChartIso k d m i := by
  rfl

/-- The effective chart trivialization as a morphism whose codomain uses
the public standard-cover chart type.  Keeping this wrapper opaque prevents
the hidden glued-cover index type from reappearing during reassociation. -/
def effectiveGluedIntegerChartHom (m : ℤ) (i : Fin (d + 1)) :
    (Scheme.Modules.pullback
      (integerCompatibilityChartMap k d i)).obj
        (gluedIntegerModule k d m) ⟶
      integerCompatibilityChartUnit k d i :=
  (gluedIntegerChartIso k d m i).hom

/-- In the first chart frame, the inverse integer transition is
multiplication by the inverse integer power of the overlap ratio. -/
lemma integerTransition_inv_trivialize (m : ℤ)
    (i j : Fin (d + 1)) :
    (integerTransition k d m i j).inv ≫
        (integerFirstPullbackUnitIso k d i j).hom =
      (integerSecondPullbackUnitIso k d i j).hom ≫
        endomorphism
          (((integerCompatibilityOverlapUnit k d i j) ^ m).inv) := by
  let A := integerFirstPullbackUnitIso k d i j
  let B := unitIso
    ((integerCompatibilityOverlapUnit k d i j) ^ m)
  let C := integerSecondPullbackUnitIso k d i j
  rw [integerTransition_eq_typed]
  exact (transTransSymm_inv_comp_first A B C).trans (by rfl)

/-- The first chart-restriction leg on a pairwise overlap. -/
abbrev gluedIntegerFirstChartLeg (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullbackComp
      (integerCompatibilityFirstMap k d i j)
      (integerCompatibilityChartMap k d i)).inv.app
      (gluedIntegerModule k d m) ≫
    (Scheme.Modules.pullback
      (integerCompatibilityFirstMap k d i j)).map
      (effectiveGluedIntegerChartHom k d m i)

/-- The cast from the second chart presentation of a glued overlap to the
first chart presentation. -/
theorem integerCompatibilityGluedOverlapEquation
    (i j : Fin (d + 1)) :
    ((glueData k d).t i j ≫ (glueData k d).f j i) ≫
        (glueData k d).ι j =
      (glueData k d).f i j ≫ (glueData k d).ι i := by
  rw [Category.assoc]
  exact (glueData k d).glue_condition i j

/-- The common hom-space for the equality cast from the first glued-chart
presentation of an overlap to the second one. -/
abbrev IntegerGluedOverlapCastHom
    (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullback
      ((glueData k d).f i j ≫ (glueData k d).ι i)).obj
      (effectiveGluedIntegerModule k d m) ⟶
    (Scheme.Modules.pullback
      (((glueData k d).t i j ≫ (glueData k d).f j i) ≫
        (glueData k d).ι j)).obj
      (effectiveGluedIntegerModule k d m)

abbrev gluedIntegerOverlapCast (m : ℤ) (i j : Fin (d + 1)) :
    IntegerGluedOverlapCastHom k d m i j :=
  (Scheme.Modules.pullbackCongr
      (integerCompatibilityGluedOverlapEquation k d i j)).inv.app
        (effectiveGluedIntegerModule k d m)

/-- The second descended chart leg after the overlap cast has already
been applied. -/
abbrev gluedIntegerSecondChartLegCore
    (m : ℤ) (i j : Fin (d + 1)) :=
  (Scheme.Modules.pullbackComp
      (integerCompatibilitySecondMap k d i j)
      (integerCompatibilityChartMap k d j)).inv.app
        (gluedIntegerModule k d m) ≫
    (Scheme.Modules.pullback
      (integerCompatibilitySecondMap k d i j)).map
        (effectiveGluedIntegerChartHom k d m j)

/-- The second chart-restriction leg, before applying the transition. -/
def gluedIntegerSecondChartLeg (m : ℤ) (i j : Fin (d + 1)) :=
  gluedIntegerOverlapCast k d m i j ≫
    gluedIntegerSecondChartLegCore k d m i j

/-- The raw effective-descent overlap equation.  Its type is written in
the same presentation returned by `restrictionIso_overlap_compat`, so the
kernel does not have to unfold the named chart legs while checking it. -/
theorem gluedIntegerChartLegOverlapCompatibilityRaw
    (m : ℤ) (i j : Fin (d + 1)) :
    (Scheme.Modules.pullbackComp
        ((glueData k d).f i j) ((glueData k d).ι i)).inv.app
        (glueObject
          (glueData k d)
          (integerChartModules k d)
          (integerTransitionFamily k d m)
          (integerIdentityFamily k d m)
          (integerCocycleFamily k d m)) ≫
      (Scheme.Modules.pullback ((glueData k d).f i j)).map
        (restrictionIso
          (glueData k d)
          (integerChartModules k d)
          (integerTransitionFamily k d m)
          (integerIdentityFamily k d m)
          (integerCocycleFamily k d m)
          i).hom =
      (Scheme.Modules.pullbackCongr
        (integerCompatibilityGluedOverlapEquation k d i j)).inv.app
          (glueObject
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)) ≫
        (Scheme.Modules.pullbackComp
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
            (integerTransitionFamily k d m i j).inv :=
  restrictionIso_overlap_compat_of_eq
    (glueData k d)
    (integerChartModules k d)
    (integerTransitionFamily k d m)
    (integerIdentityFamily k d m)
    (integerCocycleFamily k d m)
    i j (integerCompatibilityGluedOverlapEquation k d i j)

/-- The first chart leg followed by the unit-module trivialization. -/
def gluedIntegerFirstScalarLeg (m : ℤ) (i j : Fin (d + 1)) :=
  gluedIntegerFirstChartLeg k d m i j ≫
    (pullbackUnitIso ((glueData k d).f i j)).hom

/-- The second chart leg followed by its unit trivialization and the overlap
scalar. -/
def gluedIntegerSecondScalarLeg (m : ℤ) (i j : Fin (d + 1)) :=
  gluedIntegerSecondChartLeg k d m i j ≫
    (pullbackUnitIso
      ((glueData k d).t i j ≫
        (glueData k d).f j i)).hom ≫
    endomorphism (((overlapUnit k d i j) ^ m).inv)

/-- The raw overlap equation after composing with the first unit-module
trivialization. -/
theorem gluedIntegerScalarLegOverlapCompatibilityRaw
    (m : ℤ) (i j : Fin (d + 1)) :
    ((Scheme.Modules.pullbackComp
          ((glueData k d).f i j) ((glueData k d).ι i)).inv.app
          (glueObject
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)) ≫
        (Scheme.Modules.pullback ((glueData k d).f i j)).map
          (restrictionIso
            (glueData k d)
            (integerChartModules k d)
            (integerTransitionFamily k d m)
            (integerIdentityFamily k d m)
            (integerCocycleFamily k d m)
            i).hom) ≫
      (pullbackUnitIso ((glueData k d).f i j)).hom =
      ((Scheme.Modules.pullbackCongr
          (integerCompatibilityGluedOverlapEquation k d i j)).inv.app
            (glueObject
              (glueData k d)
              (integerChartModules k d)
              (integerTransitionFamily k d m)
              (integerIdentityFamily k d m)
              (integerCocycleFamily k d m)) ≫
          (Scheme.Modules.pullbackComp
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
        (pullbackUnitIso ((glueData k d).f i j)).hom :=
  congrArg
    (fun q => q ≫
      (pullbackUnitIso ((glueData k d).f i j)).hom)
    (gluedIntegerChartLegOverlapCompatibilityRaw k d m i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
