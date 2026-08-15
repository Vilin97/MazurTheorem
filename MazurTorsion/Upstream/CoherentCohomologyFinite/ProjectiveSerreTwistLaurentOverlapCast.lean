/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentSecondOverlapGeometry
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModulePullbackCongruenceSections

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-- The second standard-chart inclusion, named to expose its `Fin` index
without unfolding the standard cover. -/
def laurentSecondChartMap (d : ℕ) (j : Fin (d + 1)) :
    (glueData ℚ d).U j ⟶ scheme ℚ d :=
  (cover ℚ d).f j

instance laurentSecondChartMap_isOpenImmersion
    (d : ℕ) (j : Fin (d + 1)) :
    IsOpenImmersion (laurentSecondChartMap d j) := by
  unfold laurentSecondChartMap
  exact (cover ℚ d).map_prop j

local instance laurentPairOverlapMap_isOpenImmersion
    (d : ℕ) (i j : Fin (d + 1)) :
    IsOpenImmersion (integerPairOverlapMap ℚ d i j) :=
  integerPairOverlapMap_isOpenImmersion ℚ d i j

def integerPairDirectRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((OInt ℚ d m).restrict
        (integerPairOverlapMap ℚ d i.1 j.1),
      pairPreimageLaurentOpen d I i j) :=
  ((OInt ℚ d m).restrictAppIso
      (integerPairOverlapMap ℚ d i.1 j.1)
      (pairPreimageLaurentOpen d I i j)).inv.hom
    (((OInt ℚ d m).presheaf.mapIso
      (eqToIso
        (pairPreimageLaurentOpen_image d I i j)).op).hom.hom x)

abbrev integerPairDirectPullbackSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    IntegerOverlapSection ℚ d m i.1 j.1
      (pairPreimageLaurentOpen d I i j) :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (integerPairOverlapMap ℚ d i.1 j.1)).hom.app
        (OInt ℚ d m)).app
    (pairPreimageLaurentOpen d I i j)
    (integerPairDirectRestrictionSection d m I i j x)

def integerFirstNestedRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  (((OInt ℚ d m).restrict
    (standardChart ℚ i.1).ι).restrictAppIso
      (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
      (pairPreimageLaurentOpen d I i j)).inv.hom
    ((((OInt ℚ d m).restrict
      (standardChart ℚ i.1).ι).presheaf.mapIso
        (eqToIso
          (firstOverlapMap_image_pairPreimage d I i j)).op).hom.hom
      (ambientSectionToIntegerChartRestriction d m I i x))

lemma firstOverlapRestrictionSection_eq_nested
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerFirstOverlapRestrictionSection d m I i j x =
      (((Scheme.Modules.restrictFunctor
          (typedIntegerFirstOverlapMap ℚ d i.1 j.1)).map
        ((Scheme.Modules.restrictFunctorIsoPullback
          (standardChart ℚ i.1).ι).hom.app
            (OInt ℚ d m))).app
        (pairPreimageLaurentOpen d I i j)
        (integerFirstNestedRestrictionSection d m I i j x)) := by
  unfold integerFirstOverlapRestrictionSection
    integerFirstNestedRestrictionSection
    integerChartPullbackSection
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv]
  exact Scheme.Modules.moduleHom_mapIso_hom_app
    ((Scheme.Modules.restrictFunctorIsoPullback
      (standardChart ℚ i.1).ι).hom.app (OInt ℚ d m))
    (firstOverlapMap_image_pairPreimage d I i j)
    (ambientSectionToIntegerChartRestriction d m I i x)

lemma firstNestedRestrictionSection_eq_comp
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerFirstNestedRestrictionSection d m I i j x =
      (((Scheme.Modules.restrictFunctorComp
          (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
          (standardChart ℚ i.1).ι).hom.app
        (OInt ℚ d m)).app
        (pairPreimageLaurentOpen d I i j)
        (integerPairDirectRestrictionSection d m I i j x)) := by
  unfold integerFirstNestedRestrictionSection
    integerPairDirectRestrictionSection
    ambientSectionToIntegerChartRestriction
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  dsimp only [integerPairOverlapMap]
  change
    (OInt ℚ d m).presheaf.map _
        ((OInt ℚ d m).presheaf.map _ x) =
      (OInt ℚ d m).presheaf.map _
        ((OInt ℚ d m).presheaf.map _ x)
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg
      (fun r => (OInt ℚ d m).presheaf.map r)
      (Subsingleton.elim _ _))
    x

lemma firstPairSection_eq_direct
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerPairOverlapSectionViaFirstChart d m I i j x =
      ((Scheme.Modules.restrictFunctorIsoPullback
        (integerPairOverlapMap ℚ d i.1 j.1)).hom.app
          (OInt ℚ d m)).app
        (pairPreimageLaurentOpen d I i j)
        (integerPairDirectRestrictionSection d m I i j x) := by
  unfold integerPairOverlapSectionViaFirstChart
    integerPairOverlapMap
  rw [Scheme.Modules.restrictFunctorIsoPullback_comp_app]
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullbackComp
      (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
      (standardChart ℚ i.1).ι).hom.app
        (OInt ℚ d m)).app
      (pairPreimageLaurentOpen d I i j) y)
  unfold integerFirstOverlapPullbackSection
  apply congrArg (fun y =>
    ((Scheme.Modules.restrictFunctorIsoPullback
      (typedIntegerFirstOverlapMap ℚ d i.1 j.1)).hom.app
        ((Scheme.Modules.pullback
          (standardChart ℚ i.1).ι).obj
            (OInt ℚ d m))).app
      (pairPreimageLaurentOpen d I i j) y)
  rw [firstOverlapRestrictionSection_eq_nested]
  apply congrArg (fun y =>
    (((Scheme.Modules.restrictFunctor
      (typedIntegerFirstOverlapMap ℚ d i.1 j.1)).map
      ((Scheme.Modules.restrictFunctorIsoPullback
        (standardChart ℚ i.1).ι).hom.app
          (OInt ℚ d m))).app
      (pairPreimageLaurentOpen d I i j) y))
  exact firstNestedRestrictionSection_eq_comp d m I i j x

def integerSecondPairOverlapMap
    (d : ℕ) (i j : Fin (d + 1)) :
    typedIntegerPairOverlapScheme ℚ d i j ⟶ scheme ℚ d :=
  typedIntegerSecondOverlapMap ℚ d i j ≫
    (standardChart ℚ j).ι

instance integerSecondPairOverlapMap_isOpenImmersion
    (d : ℕ) (i j : Fin (d + 1)) :
    IsOpenImmersion (integerSecondPairOverlapMap d i j) := by
  unfold integerSecondPairOverlapMap
  infer_instance

lemma integerSecondPairOverlapMap_eq_first
    (d : ℕ) (i j : Fin (d + 1)) :
    integerSecondPairOverlapMap d i j =
      integerPairOverlapMap ℚ d i j := by
  exact cover_glue_condition ℚ d i j

lemma integerSecondPairOverlapMap_image
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    integerSecondPairOverlapMap d i.1 j.1 ''ᵁ
      pairPreimageLaurentOpen d I i j =
      laurentOpen ℚ d I := by
  apply TopologicalSpace.Opens.ext
  change
    (integerSecondPairOverlapMap d i.1 j.1).base ''
        (pairPreimageLaurentOpen d I i j : Set _) =
      (laurentOpen ℚ d I : Set _)
  have hbase := congrArg
    (fun f : typedIntegerPairOverlapScheme ℚ d i.1 j.1 ⟶
      scheme ℚ d => f.base)
    (integerSecondPairOverlapMap_eq_first d i.1 j.1)
  rw [hbase]
  exact congrArg SetLike.coe
    (pairPreimageLaurentOpen_image d I i j)

def integerSecondPairDirectRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((OInt ℚ d m).restrict
        (integerSecondPairOverlapMap d i.1 j.1),
      pairPreimageLaurentOpen d I i j) :=
  ((OInt ℚ d m).restrictAppIso
      (integerSecondPairOverlapMap d i.1 j.1)
      (pairPreimageLaurentOpen d I i j)).inv.hom
    (((OInt ℚ d m).presheaf.mapIso
      (eqToIso
        (integerSecondPairOverlapMap_image d I i j)).op).hom.hom x)

abbrev integerSecondPairDirectPullbackSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((Scheme.Modules.pullback
        (integerSecondPairOverlapMap d i.1 j.1)).obj
          (OInt ℚ d m),
      pairPreimageLaurentOpen d I i j) :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (integerSecondPairOverlapMap d i.1 j.1)).hom.app
        (OInt ℚ d m)).app
    (pairPreimageLaurentOpen d I i j)
    (integerSecondPairDirectRestrictionSection d m I i j x)

def integerSecondNestedRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  (((OInt ℚ d m).restrict
    (standardChart ℚ j.1).ι).restrictAppIso
      (typedIntegerSecondOverlapMap ℚ d i.1 j.1)
      (pairPreimageLaurentOpen d I i j)).inv.hom
    ((((OInt ℚ d m).restrict
      (standardChart ℚ j.1).ι).presheaf.mapIso
        (eqToIso
          (secondOverlapMap_image_pairPreimage d I i j)).op).hom.hom
      (ambientSectionToIntegerChartRestriction d m I j x))

lemma secondOverlapRestrictionSection_eq_nested
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerSecondOverlapRestrictionSection d m I i j x =
      (((Scheme.Modules.restrictFunctor
          (typedIntegerSecondOverlapMap ℚ d i.1 j.1)).map
        ((Scheme.Modules.restrictFunctorIsoPullback
          (standardChart ℚ j.1).ι).hom.app
            (OInt ℚ d m))).app
        (pairPreimageLaurentOpen d I i j)
        (integerSecondNestedRestrictionSection d m I i j x)) := by
  unfold integerSecondOverlapRestrictionSection
    integerSecondNestedRestrictionSection
    integerChartPullbackSection
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv]
  exact Scheme.Modules.moduleHom_mapIso_hom_app
    ((Scheme.Modules.restrictFunctorIsoPullback
      (standardChart ℚ j.1).ι).hom.app (OInt ℚ d m))
    (secondOverlapMap_image_pairPreimage d I i j)
    (ambientSectionToIntegerChartRestriction d m I j x)

lemma secondNestedRestrictionSection_eq_comp
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerSecondNestedRestrictionSection d m I i j x =
      (((Scheme.Modules.restrictFunctorComp
          (typedIntegerSecondOverlapMap ℚ d i.1 j.1)
          (standardChart ℚ j.1).ι).hom.app
        (OInt ℚ d m)).app
        (pairPreimageLaurentOpen d I i j)
        (integerSecondPairDirectRestrictionSection d m I i j x)) := by
  unfold integerSecondNestedRestrictionSection
    integerSecondPairDirectRestrictionSection
    ambientSectionToIntegerChartRestriction
    integerSecondPairOverlapMap
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change
    (OInt ℚ d m).presheaf.map _
        ((OInt ℚ d m).presheaf.map _ x) =
      (OInt ℚ d m).presheaf.map _
        ((OInt ℚ d m).presheaf.map _ x)
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rw [← CategoryTheory.comp_apply]
  apply ConcreteCategory.congr_hom
  exact
    (congrArg
      (fun r => (OInt ℚ d m).presheaf.map r)
      (Subsingleton.elim _ _)).trans
        ((OInt ℚ d m).presheaf.map_comp _ _)

lemma secondPairSection_eq_direct
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerPairOverlapSectionViaSecondChart d m I i j x =
      ((Scheme.Modules.restrictFunctorIsoPullback
        (integerSecondPairOverlapMap d i.1 j.1)).hom.app
          (OInt ℚ d m)).app
        (pairPreimageLaurentOpen d I i j)
        (integerSecondPairDirectRestrictionSection d m I i j x) := by
  unfold integerPairOverlapSectionViaSecondChart
    integerSecondPairOverlapMap
  rw [Scheme.Modules.restrictFunctorIsoPullback_comp_app]
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullbackComp
      (typedIntegerSecondOverlapMap ℚ d i.1 j.1)
      (standardChart ℚ j.1).ι).hom.app
        (OInt ℚ d m)).app
      (pairPreimageLaurentOpen d I i j) y)
  unfold integerSecondOverlapPullbackSection
  apply congrArg (fun y =>
    ((Scheme.Modules.restrictFunctorIsoPullback
      (typedIntegerSecondOverlapMap ℚ d i.1 j.1)).hom.app
        ((Scheme.Modules.pullback
          (standardChart ℚ j.1).ι).obj
            (OInt ℚ d m))).app
      (pairPreimageLaurentOpen d I i j) y)
  rw [secondOverlapRestrictionSection_eq_nested]
  apply congrArg (fun y =>
    (((Scheme.Modules.restrictFunctor
      (typedIntegerSecondOverlapMap ℚ d i.1 j.1)).map
      ((Scheme.Modules.restrictFunctorIsoPullback
        (standardChart ℚ j.1).ι).hom.app
          (OInt ℚ d m))).app
      (pairPreimageLaurentOpen d I i j) y))
  exact secondNestedRestrictionSection_eq_comp d m I i j x

lemma restrictCongr_inv_directRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    (((Scheme.Modules.restrictFunctorCongr
      (integerSecondPairOverlapMap_eq_first d i.1 j.1)).inv.app
        (OInt ℚ d m)).app
      (pairPreimageLaurentOpen d I i j)
      (integerPairDirectRestrictionSection d m I i j x)) =
        integerSecondPairDirectRestrictionSection d m I i j x := by
  unfold integerPairDirectRestrictionSection
    integerSecondPairDirectRestrictionSection
  simp only [Scheme.Modules.restrictAppIso,
    Iso.refl_inv,
    Scheme.Modules.restrictFunctorCongr_inv_app_app]
  change
    (OInt ℚ d m).presheaf.map _
        ((OInt ℚ d m).presheaf.map _ x) =
      (OInt ℚ d m).presheaf.map _ x
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact ConcreteCategory.congr_hom
    (congrArg
      (fun r => (OInt ℚ d m).presheaf.map r)
      (Subsingleton.elim _ _))
    x

lemma pullbackCongr_inv_directRestrictionComparison
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    (((Scheme.Modules.pullbackCongr
      (integerSecondPairOverlapMap_eq_first d i.1 j.1)).inv.app
        (OInt ℚ d m)).app
      (pairPreimageLaurentOpen d I i j)
      (((Scheme.Modules.restrictFunctorIsoPullback
        (integerPairOverlapMap ℚ d i.1 j.1)).hom.app
          (OInt ℚ d m)).app
        (pairPreimageLaurentOpen d I i j)
        (integerPairDirectRestrictionSection d m I i j x))) =
      ((Scheme.Modules.restrictFunctorIsoPullback
        (integerSecondPairOverlapMap d i.1 j.1)).hom.app
          (OInt ℚ d m)).app
        (pairPreimageLaurentOpen d I i j)
        (integerSecondPairDirectRestrictionSection d m I i j x) := by
  rw [Scheme.Modules.restrictFunctorIsoPullback_congr_inv_app]
  apply congrArg (fun y =>
    ((Scheme.Modules.restrictFunctorIsoPullback
      (integerSecondPairOverlapMap d i.1 j.1)).hom.app
        (OInt ℚ d m)).app
      (pairPreimageLaurentOpen d I i j) y)
  exact restrictCongr_inv_directRestrictionSection d m I i j x

def rawCastFirstPairSectionToDirect
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  congrArg
    (fun y =>
      ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation ℚ d i.1 j.1)).inv.app
          (OInt ℚ d m)).app
        (pairPreimageLaurentOpen d I i j) y)
    (firstPairSection_eq_direct d m I i j x)

def rawCastDirectProofChange
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  Scheme.Modules.pullbackCongr_inv_app_proof_irrel
    (projectiveIntegerOverlapEquation ℚ d i.1 j.1)
    (integerSecondPairOverlapMap_eq_first d i.1 j.1)
    (OInt ℚ d m)
    (pairPreimageLaurentOpen d I i j)
    (((Scheme.Modules.restrictFunctorIsoPullback
      (integerPairOverlapMap ℚ d i.1 j.1)).hom.app
        (OInt ℚ d m)).app
      (pairPreimageLaurentOpen d I i j)
      (integerPairDirectRestrictionSection d m I i j x))

def rawCastDirectToSecondPairSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  (pullbackCongr_inv_directRestrictionComparison
      d m I i j x).trans
    (secondPairSection_eq_direct d m I i j x).symm

private theorem eq_trans_three
    {α : Sort*} {a₀ a₁ a₂ a₃ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) (h₂ : a₂ = a₃) :
    a₀ = a₃ :=
  h₀.trans (h₁.trans h₂)

def rawCast_firstPairSection_eq_secondPairSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  eq_trans_three
    (rawCastFirstPairSectionToDirect d m I i j x)
    (rawCastDirectProofChange d m I i j x)
    (rawCastDirectToSecondPairSection d m I i j x)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
