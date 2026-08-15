/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCocycleSections

/-!
# Integer Serre-twist transition functions

The positive twists use natural powers of the overlap ratios.  A finite
twisted-free presentation also needs negative twists, so here the same
descent datum is extended to integer powers in the unit groups.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- The first overlap projection in the standard glue data, with its
projective-space indices exposed in the type. -/
abbrev integerFirstOverlapMap (i j : Fin (d + 1)) :
    (glueData k d).V (i, j) ⟶ (glueData k d).U i :=
  (glueData k d).f i j

/-- The second overlap projection in the standard glue data, with its
projective-space indices exposed in the type. -/
abbrev integerSecondOverlapMap (i j : Fin (d + 1)) :
    (glueData k d).V (i, j) ⟶ (glueData k d).U j :=
  (glueData k d).t i j ≫ (glueData k d).f j i

/-- Integer-power transition from the `i`-chart frame to the `j`-chart
frame. -/
def integerTransition (m : ℤ) (i j : Fin (d + 1)) :
    (Scheme.Modules.pullback (integerFirstOverlapMap k d i j)).obj
        (SheafOfModules.unit ((glueData k d).U i).ringCatSheaf) ≅
      (Scheme.Modules.pullback
        (integerSecondOverlapMap k d i j)).obj
        (SheafOfModules.unit ((glueData k d).U j).ringCatSheaf) :=
  pullbackUnitIso (integerFirstOverlapMap k d i j) ≪≫
    unitIso ((overlapUnit k d i j) ^ m) ≪≫
    (pullbackUnitIso
      (integerSecondOverlapMap k d i j)).symm

/-- The diagonal integer transition is the canonical equality transport. -/
lemma integerTransition_self (m : ℤ) (i : Fin (d + 1)) :
    integerTransition k d m i i =
      eqToIso (congrArg
        (fun f => (Scheme.Modules.pullback f).obj
          (SheafOfModules.unit ((glueData k d).U i).ringCatSheaf))
        (show
          (glueData k d).f i i =
            (glueData k d).t i i ≫ (glueData k d).f i i by
          rw [(glueData k d).t_id i, Category.id_comp])) := by
  have hmiddle :
      unitIso ((overlapUnit k d i i) ^ m) =
        Iso.refl (SheafOfModules.unit
          (pullback ((cover k d).f i)
            ((cover k d).f i)).ringCatSheaf) := by
    rw [overlapUnit_self, one_zpow, unitIso_one]
  calc
    integerTransition k d m i i =
        pullbackUnitIso ((glueData k d).f i i) ≪≫
          unitIso ((overlapUnit k d i i) ^ m) ≪≫
          (pullbackUnitIso
            ((glueData k d).t i i ≫
              (glueData k d).f i i)).symm := rfl
    _ = pullbackUnitIso ((glueData k d).f i i) ≪≫
          (pullbackUnitIso
            ((glueData k d).t i i ≫
              (glueData k d).f i i)).symm := by
      refine (congrArg
        (fun e =>
          pullbackUnitIso ((glueData k d).f i i) ≪≫ e ≪≫
            (pullbackUnitIso
              ((glueData k d).t i i ≫
                (glueData k d).f i i)).symm)
        hmiddle).trans ?_
      exact congrArg
        (fun e => pullbackUnitIso ((glueData k d).f i i) ≪≫ e)
        (Iso.refl_trans _)
    _ = eqToIso (congrArg
          (fun f => (Scheme.Modules.pullback f).obj
            (SheafOfModules.unit
              ((glueData k d).U i).ringCatSheaf))
          (show
            (glueData k d).f i i =
              (glueData k d).t i i ≫
                (glueData k d).f i i by
            rw [(glueData k d).t_id i, Category.id_comp])) := by
      exact pullbackUnitIso_trans_symm_eqToIso
        (show
          (glueData k d).f i i =
            (glueData k d).t i i ≫
              (glueData k d).f i i by
          rw [(glueData k d).t_id i, Category.id_comp])

private def appTopUnitsMap {X Y : Scheme}
    (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ :=
  Units.map (Scheme.Hom.appTop f).hom.toMonoidHom

private lemma integerCompFourEqThreeComp
    {C : Type*} [Category C] {W X Y Z T : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (e : Z ⟶ T) :
    a ≫ b ≫ c ≫ e = (a ≫ b ≫ c) ≫ e := by
  simp only [Category.assoc]

/-- The overlap-unit cocycle remains multiplicative after taking any
integer power. -/
lemma overlapUnit_cocycle_transport_zpow
    (m : ℤ) (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        (((overlapUnit k d i j) ^ m).val) *
      Scheme.Hom.appTop
        (jkBridge k d i j l)
        (((overlapUnit k d j l) ^ m).val) =
      Scheme.Hom.appTop
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l))
        (((overlapUnit k d i l) ^ m).val) := by
  let F := appTopUnitsMap
    (pullback.fst ((glueData k d).f i j)
      ((glueData k d).f i l))
  let G := appTopUnitsMap
    (jkBridge k d i j l)
  let H := appTopUnitsMap
    (pullback.snd ((glueData k d).f i j)
      ((glueData k d).f i l))
  have hbase :
      F (overlapUnit k d i j) *
          G (overlapUnit k d j l) =
        H (overlapUnit k d i l) := by
    apply Units.ext
    exact overlapUnit_cocycle_transport k d i j l
  have hz :
      F ((overlapUnit k d i j) ^ m) *
          G ((overlapUnit k d j l) ^ m) =
        H ((overlapUnit k d i l) ^ m) := by
    calc
      _ = (F (overlapUnit k d i j)) ^ m *
          (G (overlapUnit k d j l)) ^ m :=
        congrArg₂ (· * ·)
          (map_zpow F (overlapUnit k d i j) m)
          (map_zpow G (overlapUnit k d j l) m)
      _ = (F (overlapUnit k d i j) *
          G (overlapUnit k d j l)) ^ m :=
        (mul_zpow _ _ _).symm
      _ = (H (overlapUnit k d i l)) ^ m :=
        congrArg (· ^ m) hbase
      _ = _ := (map_zpow H (overlapUnit k d i l) m).symm
  exact congrArg Units.val hz

lemma pullbackTransport_jkBridge_integerTransition_hom
    (m : ℤ) (i j l : Fin (d + 1)) :
    (pullbackTransport (jkBridge k d i j l)
      ((glueData k d).f j l)
      ((glueData k d).t j l ≫ (glueData k d).f l j)
      (integerTransition k d m j l)).hom =
        (pullbackUnitIso
          (jkBridge k d i j l ≫ (glueData k d).f j l)).hom ≫
        endomorphism
          ((jkBridge k d i j l).appTop
            (overlapUnit k d j l ^ m).val) ≫
        (pullbackUnitIso
          (jkBridge k d i j l ≫
            (glueData k d).t j l ≫ (glueData k d).f l j)).inv := by
  exact pullbackTransport_unitIso
    (jkBridge k d i j l) ((glueData k d).f j l)
    ((glueData k d).t j l ≫ (glueData k d).f l j)
    (overlapUnit k d j l ^ m)

@[reassoc]
lemma integerTransition_hom_bridgeMiddle_unit
    (m : ℤ) (i j l : Fin (d + 1)) :
    (pullbackTransport
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i j)
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        (integerTransition k d m i j)).hom ≫
      ((Scheme.Modules.pullbackCongr
        (bridgeMiddle_jkBridge k d i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U j).ringCatSheaf)).hom ≫
      (pullbackUnitIso
        (jkBridge k d i j l ≫ (glueData k d).f j l)).hom =
    (pullbackUnitIso
      (pullback.fst ((glueData k d).f i j)
        ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
      endomorphism
        ((pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l)).appTop
            (overlapUnit k d i j ^ m).val) := by
  simp only [integerTransition]
  rw [pullbackTransport_unitIso
      (pullback.fst ((glueData k d).f i j) ((glueData k d).f i l))
      ((glueData k d).f i j)
      ((glueData k d).t i j ≫ (glueData k d).f j i)
      (overlapUnit k d i j ^ m)]
  calc
    _ = ((pullbackUnitIso
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
        endomorphism
          ((pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l)).appTop
              (overlapUnit k d i j ^ m).val)) ≫
        ((pullbackUnitIso
          (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
            ((glueData k d).t i j ≫ (glueData k d).f j i))).inv ≫
          ((Scheme.Modules.pullbackCongr
            (bridgeMiddle_jkBridge k d i j l)).app
              (SheafOfModules.unit
                ((glueData k d).U j).ringCatSheaf)).hom ≫
          (pullbackUnitIso
            (jkBridge k d i j l ≫ (glueData k d).f j l)).hom) :=
      (Category.assoc _ _ _).trans
        ((CategoryTheory.whisker_eq _ (Category.assoc _ _ _)).trans
          (Category.assoc _ _ _).symm)
    _ = ((pullbackUnitIso
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
        endomorphism
          ((pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l)).appTop
              (overlapUnit k d i j ^ m).val)) ≫ 𝟙 _ :=
      CategoryTheory.whisker_eq _
        (pullbackUnitIso_inv_congr_hom
          (bridgeMiddle_jkBridge k d i j l))
    _ = _ := Category.comp_id _

lemma jkBridge_integerTransition_hom_bridgeTarget
    (m : ℤ) (i j l : Fin (d + 1)) :
    (pullbackTransport
        (jkBridge k d i j l)
        ((glueData k d).f j l)
        ((glueData k d).t j l ≫ (glueData k d).f l j)
        (integerTransition k d m j l)).hom ≫
      ((Scheme.Modules.pullbackCongr
        (bridgeTarget_jkBridge k d i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U l).ringCatSheaf)).hom =
    (pullbackUnitIso
      (jkBridge k d i j l ≫ (glueData k d).f j l)).hom ≫
      endomorphism
        ((jkBridge k d i j l).appTop
          (overlapUnit k d j l ^ m).val) ≫
      (pullbackUnitIso
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          ((glueData k d).t i l ≫ (glueData k d).f l i))).inv := by
  rw [pullbackTransport_jkBridge_integerTransition_hom]
  calc
    _ = ((pullbackUnitIso
        (jkBridge k d i j l ≫ (glueData k d).f j l)).hom ≫
        endomorphism
          ((jkBridge k d i j l).appTop
            (overlapUnit k d j l ^ m).val)) ≫
        ((pullbackUnitIso
          (jkBridge k d i j l ≫
            (glueData k d).t j l ≫ (glueData k d).f l j)).inv ≫
          ((Scheme.Modules.pullbackCongr
            (bridgeTarget_jkBridge k d i j l)).app
              (SheafOfModules.unit
                ((glueData k d).U l).ringCatSheaf)).hom) :=
      (Category.assoc _ _ _).trans
        ((CategoryTheory.whisker_eq _ (Category.assoc _ _ _)).trans
          (Category.assoc _ _ _).symm)
    _ = ((pullbackUnitIso
        (jkBridge k d i j l ≫ (glueData k d).f j l)).hom ≫
        endomorphism
          ((jkBridge k d i j l).appTop
            (overlapUnit k d j l ^ m).val)) ≫
        (pullbackUnitIso
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
            ((glueData k d).t i l ≫ (glueData k d).f l i))).inv :=
      CategoryTheory.whisker_eq _
        (pullbackUnitIso_inv_congr
          (bridgeTarget_jkBridge k d i j l))
    _ = _ := Category.assoc _ _ _

lemma bridgeSource_integerTransition_hom
    (m : ℤ) (i j l : Fin (d + 1)) :
    ((Scheme.Modules.pullbackCongr
        (bridgeSource (glueData k d) i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U i).ringCatSheaf)).hom ≫
      (pullbackTransport
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i l)
        ((glueData k d).t i l ≫ (glueData k d).f l i)
        (integerTransition k d m i l)).hom =
    (pullbackUnitIso
      (pullback.fst ((glueData k d).f i j)
        ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
      endomorphism
        ((pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l)).appTop
            (overlapUnit k d i l ^ m).val) ≫
      (pullbackUnitIso
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          ((glueData k d).t i l ≫ (glueData k d).f l i))).inv := by
  simp only [integerTransition]
  rw [pullbackTransport_unitIso
      (pullback.snd ((glueData k d).f i j) ((glueData k d).f i l))
      ((glueData k d).f i l)
      ((glueData k d).t i l ≫ (glueData k d).f l i)
      (overlapUnit k d i l ^ m)]
  calc
    _ = (((Scheme.Modules.pullbackCongr
          (bridgeSource (glueData k d) i j l)).app
            (SheafOfModules.unit
              ((glueData k d).U i).ringCatSheaf)).hom ≫
        (pullbackUnitIso
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫ (glueData k d).f i l)).hom) ≫
      (endomorphism
        ((pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l)).appTop
            (overlapUnit k d i l ^ m).val) ≫
        (pullbackUnitIso
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
            ((glueData k d).t i l ≫ (glueData k d).f l i))).inv) :=
      (Category.assoc _ _ _).symm
    _ = (pullbackUnitIso
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
      (endomorphism
        ((pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l)).appTop
            (overlapUnit k d i l ^ m).val) ≫
        (pullbackUnitIso
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
            ((glueData k d).t i l ≫ (glueData k d).f l i))).inv) :=
      CategoryTheory.eq_whisker
        (pullbackCongr_hom_unit
          (bridgeSource (glueData k d) i j l)) _
    _ = _ := rfl

lemma reduced_integerTransition_cocycle_hom
    (m : ℤ) (i j l : Fin (d + 1)) :
    (pullbackTransport
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i j)
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        (integerTransition k d m i j)).hom ≫
      ((Scheme.Modules.pullbackCongr
        (bridgeMiddle_jkBridge k d i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U j).ringCatSheaf)).hom ≫
      (pullbackUnitIso
        (jkBridge k d i j l ≫ (glueData k d).f j l)).hom ≫
      endomorphism
        ((jkBridge k d i j l).appTop
          (overlapUnit k d j l ^ m).val) ≫
      (pullbackUnitIso
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          ((glueData k d).t i l ≫ (glueData k d).f l i))).inv =
    (pullbackUnitIso
      (pullback.fst ((glueData k d).f i j)
        ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
      endomorphism
        ((pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l)).appTop
            (overlapUnit k d i l ^ m).val) ≫
      (pullbackUnitIso
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          ((glueData k d).t i l ≫ (glueData k d).f l i))).inv := by
  calc
    _ = ((pullbackTransport
          (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l))
          ((glueData k d).f i j)
          ((glueData k d).t i j ≫ (glueData k d).f j i)
          (integerTransition k d m i j)).hom ≫
        ((Scheme.Modules.pullbackCongr
          (bridgeMiddle_jkBridge k d i j l)).app
            (SheafOfModules.unit
              ((glueData k d).U j).ringCatSheaf)).hom ≫
        (pullbackUnitIso
          (jkBridge k d i j l ≫ (glueData k d).f j l)).hom) ≫
      (endomorphism
        ((jkBridge k d i j l).appTop
          (overlapUnit k d j l ^ m).val) ≫
        (pullbackUnitIso
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
            ((glueData k d).t i l ≫ (glueData k d).f l i))).inv) :=
      integerCompFourEqThreeComp _ _ _ _
    _ = ((pullbackUnitIso
          (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
        endomorphism
          ((pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l)).appTop
              (overlapUnit k d i j ^ m).val)) ≫
      (endomorphism
        ((jkBridge k d i j l).appTop
          (overlapUnit k d j l ^ m).val) ≫
        (pullbackUnitIso
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
            ((glueData k d).t i l ≫ (glueData k d).f l i))).inv) :=
      CategoryTheory.eq_whisker
        (integerTransition_hom_bridgeMiddle_unit k d m i j l) _
    _ = (pullbackUnitIso
          (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l) ≫ (glueData k d).f i j)).hom ≫
        endomorphism
          ((pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l)).appTop
              (overlapUnit k d i j ^ m).val) ≫
        endomorphism
          ((jkBridge k d i j l).appTop
            (overlapUnit k d j l ^ m).val) ≫
        (pullbackUnitIso
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
            ((glueData k d).t i l ≫ (glueData k d).f l i))).inv :=
      Category.assoc _ _ _
    _ = _ := by
      have hendo :
          endomorphism
              ((pullback.fst ((glueData k d).f i j)
                ((glueData k d).f i l)).appTop
                  (overlapUnit k d i j ^ m).val) ≫
            endomorphism
              ((jkBridge k d i j l).appTop
                (overlapUnit k d j l ^ m).val) =
          endomorphism
              ((pullback.snd ((glueData k d).f i j)
                ((glueData k d).f i l)).appTop
                  (overlapUnit k d i l ^ m).val) := by
        rw [endomorphism_comp,
          overlapUnit_cocycle_transport_zpow]
      exact CategoryTheory.whisker_eq _
        ((Category.assoc _ _ _).symm.trans
          (CategoryTheory.eq_whisker hendo _))

/-- Integer transition functions satisfy the descent cocycle. -/
lemma integerTransition_cocycle (m : ℤ)
    (i j l : Fin (d + 1)) :
    pullbackTransport
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i j)
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        (integerTransition k d m i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeMiddle_jkBridge k d i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U j).ringCatSheaf) ≪≫
      pullbackTransport
        (jkBridge k d i j l)
        ((glueData k d).f j l)
        ((glueData k d).t j l ≫ (glueData k d).f l j)
        (integerTransition k d m j l) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeTarget_jkBridge k d i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U l).ringCatSheaf) =
    (Scheme.Modules.pullbackCongr
      (bridgeSource (glueData k d) i j l)).app
        (SheafOfModules.unit
          ((glueData k d).U i).ringCatSheaf) ≪≫
      pullbackTransport
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i l)
        ((glueData k d).t i l ≫ (glueData k d).f l i)
        (integerTransition k d m i l) := by
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [jkBridge_integerTransition_hom_bridgeTarget]
  rw [bridgeSource_integerTransition_hom]
  exact reduced_integerTransition_cocycle_hom k d m i j l

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
