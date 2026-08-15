/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerCoverDescent
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleScalarUnit

/-!
# Addition of integer Serre cocycles under descent

Multiplying the degree-`m` projective transition by the degree-`n` scalar
cocycle gives the degree-`m+n` transition.  Effective descent therefore
identifies the global scalar twist of `gluedIntegerModule m` with
`gluedIntegerModule (m+n)`.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

private theorem iso_trans_four_to_right
    {C : Type*} [Category C] {A B C₁ D E : C}
    (a : A ≅ B) (b : B ≅ C₁) (c : C₁ ≅ D) (e : D ≅ E) :
    (a ≪≫ b ≪≫ c) ≪≫ e = a ≪≫ (b ≪≫ (c ≪≫ e)) := by
  simp only [Iso.trans_assoc]

private theorem iso_trans_four_middle
    {C : Type*} [Category C] {A B C₁ D E : C}
    (a : A ≅ B) (b : B ≅ C₁) (c : C₁ ≅ D) (e : D ≅ E) :
    a ≪≫ (b ≪≫ (c ≪≫ e)) = a ≪≫ ((b ≪≫ c) ≪≫ e) := by
  simp only [Iso.trans_assoc]

/-- Scalar twisting the degree-`m` transition by the degree-`n` overlap
unit produces the degree-`m+n` transition. -/
lemma scalarTwistedIntegerTransition_add
    (m n : ℤ) (i j : Fin (d + 1)) :
    scalarTwistedTransition
        (integerCoverDescentData k d m)
        (integerCoverUnit k d n) i j =
      (integerCoverDescentData k d (m + n)).transition i j := by
  let u := overlapUnit k d i j
  let f := (glueData k d).f i j
  let g :=
    (glueData k d).t i j ≫
      (glueData k d).f j i
  change
    (pullbackUnitIso f ≪≫
          unitIso (u ^ m) ≪≫
          (pullbackUnitIso g).symm) ≪≫
        scalarIso
          ((Scheme.Modules.pullback g).obj
            (SheafOfModules.unit
              ((glueData k d).U j).ringCatSheaf))
          (u ^ n) =
      pullbackUnitIso f ≪≫
        unitIso (u ^ (m + n)) ≪≫
        (pullbackUnitIso g).symm
  calc
    (pullbackUnitIso f ≪≫
            unitIso (u ^ m) ≪≫
            (pullbackUnitIso g).symm) ≪≫
          scalarIso
            ((Scheme.Modules.pullback g).obj
              (SheafOfModules.unit
                ((glueData k d).U j).ringCatSheaf))
            (u ^ n) =
        pullbackUnitIso f ≪≫
          (unitIso (u ^ m) ≪≫
            ((pullbackUnitIso g).symm ≪≫
              scalarIso
                ((Scheme.Modules.pullback g).obj
                  (SheafOfModules.unit
                ((glueData k d).U j).ringCatSheaf))
                (u ^ n))) := by
      exact iso_trans_four_to_right
        (pullbackUnitIso f)
        (unitIso (u ^ m))
        (pullbackUnitIso g).symm
        (scalarIso
          ((Scheme.Modules.pullback g).obj
            (SheafOfModules.unit
              ((glueData k d).U j).ringCatSheaf))
          (u ^ n))
    _ =
        pullbackUnitIso f ≪≫
          (unitIso (u ^ m) ≪≫
            (scalarIso
                (SheafOfModules.unit
                  ((glueData k d).V (i, j)).ringCatSheaf)
                (u ^ n) ≪≫
              (pullbackUnitIso g).symm)) := by
      rw [← scalarIso_naturality
        (pullbackUnitIso g).symm (u ^ n)]
    _ =
        pullbackUnitIso f ≪≫
          (unitIso (u ^ m) ≪≫
              (unitIso (u ^ n) ≪≫
              (pullbackUnitIso g).symm)) := by
      exact congrArg
        (fun e =>
          pullbackUnitIso f ≪≫
            (unitIso (u ^ m) ≪≫
              (e ≪≫ (pullbackUnitIso g).symm)))
        (scalarIso_unit_eq_unitIso
          (X := (glueData k d).V (i, j)) (u ^ n))
    _ =
        pullbackUnitIso f ≪≫
          ((unitIso (u ^ m) ≪≫
              unitIso (u ^ n)) ≪≫
            (pullbackUnitIso g).symm) := by
      exact iso_trans_four_middle
        (pullbackUnitIso f)
        (unitIso (u ^ m))
        (unitIso (u ^ n))
        (pullbackUnitIso g).symm
    _ =
        pullbackUnitIso f ≪≫
          (unitIso (u ^ m * u ^ n) ≪≫
            (pullbackUnitIso g).symm) := by
      exact congrArg
        (fun e =>
          pullbackUnitIso f ≪≫
            e ≪≫ (pullbackUnitIso g).symm)
        (unitIso_mul (u ^ m) (u ^ n))
    _ =
        pullbackUnitIso f ≪≫
          unitIso (u ^ (m + n)) ≪≫
          (pullbackUnitIso g).symm := by
      rw [zpow_add]

/-- At the level of standard-cover descent data, scalar twisting a degree
`m` integer twist by degree `n` is isomorphic to the degree-`m+n` twist.
The chart components of the isomorphism are identities. -/
noncomputable def scalarTwistIntegerCoverDescentIso
    (m n : ℤ) :
    (integerScalarTwistDescentFunctor k d n).obj
          (integerCoverDescentData k d m) ≅
      integerCoverDescentData k d (m + n) := by
  let φ :
      (integerScalarTwistDescentFunctor k d n).obj
            (integerCoverDescentData k d m) ⟶
        integerCoverDescentData k d (m + n) :=
    { app := fun i =>
        𝟙 ((integerCoverDescentData k d (m + n)).chart i)
      compatible := by
        intro i j
        change Fin (d + 1) at i j
        change
          (pullback ((glueData k d).f i j)).map
                (𝟙 (integerChartModules k d i)) ≫
              (integerTransition k d (m + n) i j).hom =
            (integerTransition k d m i j ≪≫
                scalarIso
                  ((pullback
                    ((glueData k d).t i j ≫
                      (glueData k d).f j i)).obj
                    (integerChartModules k d j))
                  (integerCoverUnit k d n i j)).hom ≫
              (pullback
                ((glueData k d).t i j ≫
                  (glueData k d).f j i)).map
                (𝟙 (integerChartModules k d j))
        have htransition :
            (integerTransition k d (m + n) i j).hom =
              (integerTransition k d m i j ≪≫
                scalarIso
                  ((pullback
                    ((glueData k d).t i j ≫
                      (glueData k d).f j i)).obj
                    (integerChartModules k d j))
                  (integerCoverUnit k d n i j)).hom :=
          congrArg Iso.hom
            (scalarTwistedIntegerTransition_add
              k d m n i j).symm
        have hleft := congrArg
          (fun q => q ≫ (integerTransition k d (m + n) i j).hom)
          ((pullback ((glueData k d).f i j)).map_id
            (integerChartModules k d i))
        have hright := congrArg
          (fun q =>
            (integerTransition k d m i j ≪≫
              scalarIso
                ((pullback
                  ((glueData k d).t i j ≫
                    (glueData k d).f j i)).obj
                  (integerChartModules k d j))
                (integerCoverUnit k d n i j)).hom ≫ q)
          ((pullback
            ((glueData k d).t i j ≫
              (glueData k d).f j i)).map_id
            (integerChartModules k d j)).symm
        exact hleft.trans <| (Category.id_comp _).trans <|
          htransition.trans <| (Category.comp_id _).symm.trans hright }
  letI : ∀ i, IsIso (φ.app i) := by
    intro i
    change IsIso
      (𝟙 ((integerCoverDescentData
          k d (m + n)).chart i) :
        (integerCoverDescentData
            k d (m + n)).chart i ⟶
          (integerCoverDescentData
            k d (m + n)).chart i)
    infer_instance
  exact φ.isoOfComponents

/-- Restricting the glued degree-`m` integer module recovers its named
cover descent datum. -/
noncomputable def gluedIntegerRestrictionDescentIso
    (m : ℤ) :
    (restrictionFunctor (D := glueData k d)).obj
        (gluedIntegerModule k d m) ≅
      integerCoverDescentData k d m :=
  descentGlueRestrictionIso
    (D := glueData k d)
    (integerCoverDescentData k d m)

/-- After restriction, scalar twisting the glued degree-`m` module gives
the named degree-`m+n` descent datum. -/
noncomputable def scalarTwistMapGluedIntegerRestrictionIso
    (m n : ℤ) :
    (integerScalarTwistDescentFunctor k d n).obj
          ((restrictionFunctor
            (D := glueData k d)).obj
              (gluedIntegerModule k d m)) ≅
      (integerScalarTwistDescentFunctor k d n).obj
          (integerCoverDescentData k d m) :=
  (integerScalarTwistDescentFunctor k d n).mapIso
        (gluedIntegerRestrictionDescentIso k d m)

/-- After restriction, scalar twisting the glued degree-`m` module gives
the named degree-`m+n` descent datum. -/
noncomputable def scalarTwistedGluedIntegerRestrictionIso
    (m n : ℤ) :
    (integerScalarTwistDescentFunctor k d n).obj
          ((restrictionFunctor
            (D := glueData k d)).obj
              (gluedIntegerModule k d m)) ≅
      integerCoverDescentData k d (m + n) :=
  scalarTwistMapGluedIntegerRestrictionIso k d m n ≪≫
    scalarTwistIntegerCoverDescentIso k d m n

/-- The global scalar twist on the glued standard cover adds the two
integer Serre degrees. -/
noncomputable def gluedIntegerScalarTwistShiftIso
    (m n : ℤ) :
    (gluedIntegerScalarTwistEquivalence
        k d n).functor.obj
          (gluedIntegerModule k d m) ≅
      gluedIntegerModule k d (m + n) :=
  (glueFunctor (D := glueData k d)).mapIso
      (scalarTwistedGluedIntegerRestrictionIso
        k d m n) ≪≫
    glueIntegerCoverDescentIso k d (m + n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
