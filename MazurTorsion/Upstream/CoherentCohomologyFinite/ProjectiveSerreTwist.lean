/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCocycleSections

/-!
# The Serre twisting module on projective space

The chartwise unit modules with transition functions
`(Xᵢ/Xⱼ)^m` satisfy the descent cocycle.  Their equalizer of pushforwards
defines `𝒪(m)` on the glued cover, and pullback along the canonical cover
isomorphism puts it on projective space itself.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

private lemma comp_four_eq_three_comp
    {C : Type*} [Category C] {W X Y Z T : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (e : Z ⟶ T) :
    a ≫ b ≫ c ≫ e = (a ≫ b ≫ c) ≫ e := by
  simp only [Category.assoc]

lemma pullbackTransport_jkBridge_transition_hom
    (m : ℕ) (i j l : Fin (d + 1)) :
    (pullbackTransport (jkBridge k d i j l)
      ((glueData k d).f j l)
      ((glueData k d).t j l ≫ (glueData k d).f l j)
      (transition k d m j l)).hom =
        (pullbackUnitIso
          (jkBridge k d i j l ≫ (glueData k d).f j l)).hom ≫
        endomorphism
          ((jkBridge k d i j l).appTop (overlapUnit k d j l ^ m).val) ≫
        (pullbackUnitIso
          (jkBridge k d i j l ≫
            (glueData k d).t j l ≫ (glueData k d).f l j)).inv := by
  exact pullbackTransport_unitIso
    (jkBridge k d i j l) ((glueData k d).f j l)
    ((glueData k d).t j l ≫ (glueData k d).f l j)
    (overlapUnit k d j l ^ m)

@[reassoc]
lemma transition_hom_bridgeMiddle_unit
    (m : ℕ) (i j l : Fin (d + 1)) :
    (pullbackTransport
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i j)
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        (transition k d m i j)).hom ≫
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
  simp only [transition]
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

lemma jkBridge_transition_hom_bridgeTarget
    (m : ℕ) (i j l : Fin (d + 1)) :
    (pullbackTransport
        (jkBridge k d i j l)
        ((glueData k d).f j l)
        ((glueData k d).t j l ≫ (glueData k d).f l j)
        (transition k d m j l)).hom ≫
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
  rw [pullbackTransport_jkBridge_transition_hom]
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

lemma bridgeSource_transition_hom
    (m : ℕ) (i j l : Fin (d + 1)) :
    ((Scheme.Modules.pullbackCongr
        (bridgeSource (glueData k d) i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U i).ringCatSheaf)).hom ≫
      (pullbackTransport
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i l)
        ((glueData k d).t i l ≫ (glueData k d).f l i)
        (transition k d m i l)).hom =
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
  simp only [transition]
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

lemma reduced_transition_cocycle_hom
    (m : ℕ) (i j l : Fin (d + 1)) :
    (pullbackTransport
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i j)
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        (transition k d m i j)).hom ≫
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
          (transition k d m i j)).hom ≫
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
      comp_four_eq_three_comp _ _ _ _
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
        (transition_hom_bridgeMiddle_unit k d m i j l) _
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
          overlapUnit_cocycle_transport_pow]
      exact CategoryTheory.whisker_eq _
        ((Category.assoc _ _ _).symm.trans
          (CategoryTheory.eq_whisker hendo _))

/-- The transition maps satisfy the descent cocycle on every triple
overlap. -/
lemma transition_cocycle (m : ℕ)
    (i j l : Fin (d + 1)) :
    pullbackTransport
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((glueData k d).f i j)
        ((glueData k d).t i j ≫ (glueData k d).f j i)
        (transition k d m i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeMiddle_jkBridge k d i j l)).app
          (SheafOfModules.unit
            ((glueData k d).U j).ringCatSheaf) ≪≫
      pullbackTransport
        (jkBridge k d i j l)
        ((glueData k d).f j l)
        ((glueData k d).t j l ≫ (glueData k d).f l j)
        (transition k d m j l) ≪≫
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
        (transition k d m i l) := by
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [jkBridge_transition_hom_bridgeTarget]
  rw [bridgeSource_transition_hom]
  exact reduced_transition_cocycle_hom k d m i j l

/-- The Serre twist on the scheme obtained by gluing the standard charts. -/
def gluedModule (m : ℕ) : (glueData k d).glued.Modules :=
  glueObject (glueData k d)
    (fun i =>
      SheafOfModules.unit ((glueData k d).U i).ringCatSheaf)
    (fun i j => transition k d m i j)
    (fun i => transition_self k d m i)
    (fun i j l => transition_cocycle k d m i j l)

/-- The Serre twisting module `𝒪(m)` on projective `d`-space over `k`. -/
def module (m : ℕ) : (scheme k d).Modules :=
  (Scheme.Modules.pullback (inv (cover k d).fromGlued)).obj
    (gluedModule k d m)

/-- Readable notation-free alias for the Serre twisting module. -/
abbrev O (m : ℕ) : (scheme k d).Modules :=
  module k d m

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
