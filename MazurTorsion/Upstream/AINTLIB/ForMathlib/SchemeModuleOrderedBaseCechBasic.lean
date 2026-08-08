/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Products
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechBasic

/-!
# Ordered base-linear Cech complex core

For a linearly ordered finite open cover, this file defines the Cech complex indexed by
strictly increasing tuples. Unlike the native all-tuples Cech complex, this complex is
bounded by the cardinality of the cover. Its terms retain their module structure over
global functions on the base. The flatness and Picard-specific tail is intentionally separate.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Strictly increasing tuples indexing the ordered Cech complex in degree `n`. -/
def OrderedCechIndex (ι : Type u) [Preorder ι] (n : ℕ) :=
  {i : Fin (n + 1) → ι // StrictMono i}

/-- Deleting an entry from a strictly increasing tuple preserves strict increase. -/
def OrderedCechIndex.delete {ι : Type u} [Preorder ι] {n : ℕ}
    (i : OrderedCechIndex ι (n + 1)) (k : Fin (n + 2)) :
    OrderedCechIndex ι n :=
  ⟨i.1 ∘ (SimplexCategory.δ k).toOrderHom,
    i.2.comp ((SimplexCategory.δ k).toOrderHom.monotone.strictMono_of_injective
      (by
        simpa [SimplexCategory.δ] using
          (Fin.succAboveOrderEmb k).injective))⟩

@[simp]
private theorem OrderedCechIndex.delete_delete {ι : Type u} [Preorder ι] {n : ℕ}
    (k : OrderedCechIndex ι (n + 1 + 1)) {i j : Fin (n + 2)} (hij : i ≤ j) :
    (k.delete j.succ).delete i = (k.delete i.castSucc).delete j := by
  apply Subtype.ext
  funext a
  have hδ := ConcreteCategory.congr_hom
    (SimplexCategory.δ_comp_δ hij)
  exact congrArg k.1 (hδ a)

/-- There are no ordered Cech indices in degrees at least the size of a finite cover. -/
private theorem isEmpty_orderedCechIndex_of_card_le
    (ι : Type u) [Fintype ι] [Preorder ι] (n : ℕ) (h : Fintype.card ι ≤ n) :
    IsEmpty (OrderedCechIndex ι n) := by
  constructor
  intro i
  have hi : n + 1 ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective i.1 i.2.injective
  omega

/-- The formal coproduct of intersections indexed by strictly increasing tuples. -/
noncomputable def orderedCechFormalObject {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    FormalCoproduct X.Opens where
  I := OrderedCechIndex ι n
  obj i := ∏ᶜ fun k : Fin (n + 1) => U (i.1 k)

/-- Deleting one entry induces a face map between ordered intersection families. -/
noncomputable def orderedCechFace {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    orderedCechFormalObject U (n + 1) ⟶ orderedCechFormalObject U n where
  f i := i.delete k
  φ i := (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)

theorem orderedCechFace_comp {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    orderedCechFace U (n + 1) j.succ ≫ orderedCechFace U n i =
      orderedCechFace U (n + 1) i.castSucc ≫ orderedCechFace U n j := by
  let V : FormalCoproduct X.Opens := FormalCoproduct.mk _ U
  have hmap :
      V.mapPower (SimplexCategory.δ j.succ).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ i).toOrderHom.toFun =
        V.mapPower (SimplexCategory.δ i.castSucc).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ j).toOrderHom.toFun := by
    rw [← FormalCoproduct.mapPower_comp,
      ← FormalCoproduct.mapPower_comp]
    congr 1
    exact funext (ConcreteCategory.congr_hom
      (SimplexCategory.δ_comp_δ hij))
  let hf :
      (orderedCechFace U (n + 1) j.succ ≫ orderedCechFace U n i).f =
        (orderedCechFace U (n + 1) i.castSucc ≫ orderedCechFace U n j).f :=
    funext fun k => OrderedCechIndex.delete_delete k hij
  apply FormalCoproduct.hom_ext hf
  intro k
  have hk := ((FormalCoproduct.hom_ext_iff _ _).1 hmap).2 k.1
  change
    ((V.mapPower (SimplexCategory.δ j.succ).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ i).toOrderHom.toFun).φ k.1 ≫
        eqToHom _) =
      (V.mapPower (SimplexCategory.δ i.castSucc).toOrderHom.toFun ≫
        V.mapPower (SimplexCategory.δ j).toOrderHom.toFun).φ k.1
  simpa only using hk

/-- A term of the ordered base-linear Cech complex. -/
abbrev orderedBaseCechTerm {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) :=
  ∀ i : OrderedCechIndex ι n, baseCechFactor π M U n i.1

/-- Ordered Cech cochains as a module over global functions on the base. -/
noncomputable def orderedBaseCechObject
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
      (baseModulePresheaf π M)).obj (op (orderedCechFormalObject U n))

/-- Ordered Cech cochains are the concrete dependent product of their
intersection-section factors. -/
noncomputable def orderedBaseCechObjectIsoPi
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechObject π M U n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens)) (orderedBaseCechTerm π M U n) :=
  ModuleCat.piIsoPi _

/-- The `k`th ordered Cech coface. -/
noncomputable def orderedBaseCechCoface
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    orderedBaseCechObject π M U n ⟶
      orderedBaseCechObject π M U (n + 1) :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
      (baseModulePresheaf π M)).map (orderedCechFace U n k).op

private theorem orderedBaseCechCoface_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (k : Fin (n + 2)) (i : OrderedCechIndex ι (n + 1)) :
    orderedBaseCechCoface π M U n k ≫
        Pi.π (fun j : OrderedCechIndex ι (n + 1) =>
          baseCechFactor π M U (n + 1) j.1) i =
      Pi.π (fun j : OrderedCechIndex ι n =>
        baseCechFactor π M U n j.1) (i.delete k) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op := by
  change (Pi.lift fun j : OrderedCechIndex ι (n + 1) =>
      Pi.π (fun l : OrderedCechIndex ι n =>
        baseCechFactor π M U n l.1) (j.delete k) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ j.1).op) ≫ _ = _
  exact Pi.lift_π _ i

private theorem orderedBaseCechCoface_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    orderedBaseCechCoface π M U n i ≫
        orderedBaseCechCoface π M U (n + 1) j.succ =
      orderedBaseCechCoface π M U n j ≫
        orderedBaseCechCoface π M U (n + 1) i.castSucc := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    ((FormalCoproduct.evalOp.{u} X.Opens
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
        (baseModulePresheaf π M))
  change F.map (orderedCechFace U n i).op ≫
      F.map (orderedCechFace U (n + 1) j.succ).op =
    F.map (orderedCechFace U n j).op ≫
      F.map (orderedCechFace U (n + 1) i.castSucc).op
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
    orderedCechFace_comp U n hij]

private theorem orderedBaseCechCoface_comp'
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    {i : Fin (n + 3)} {j : Fin (n + 2)} (hij : i ≤ j.castSucc) :
    orderedBaseCechCoface π M U n
          (i.castLT (lt_of_le_of_lt hij j.is_lt)) ≫
        orderedBaseCechCoface π M U (n + 1) j.succ =
      orderedBaseCechCoface π M U n j ≫
        orderedBaseCechCoface π M U (n + 1) i := by
  have hle : i.castLT (lt_of_le_of_lt hij j.is_lt) ≤ j := by
    rw [Fin.le_iff_val_le_val] at hij ⊢
    exact hij
  simpa using orderedBaseCechCoface_comp π M U n hle

/-- The alternating differential on ordered Cech cochains. -/
noncomputable def orderedBaseCechDifferential
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechObject π M U n ⟶
      orderedBaseCechObject π M U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    orderedBaseCechCoface π M U n k

private theorem orderedBaseCechDifferential_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : OrderedCechIndex ι (n + 1)) :
    orderedBaseCechDifferential π M U n ≫
        Pi.π (fun j : OrderedCechIndex ι (n + 1) =>
          baseCechFactor π M U (n + 1) j.1) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (Pi.π (fun j : OrderedCechIndex ι n =>
          baseCechFactor π M U n j.1) (i.delete k) ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op) := by
  let p : orderedBaseCechObject π M U (n + 1) ⟶
      baseCechFactor π M U (n + 1) i.1 :=
    Pi.π (fun j : OrderedCechIndex ι (n + 1) =>
      baseCechFactor π M U (n + 1) j.1) i
  change orderedBaseCechDifferential π M U n ≫ p = _
  rw [orderedBaseCechDifferential, sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsmul_comp, orderedBaseCechCoface_comp_π]
  rfl

private theorem orderedBaseCechDifferential_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechDifferential π M U n ≫
      orderedBaseCechDifferential π M U (n + 1) = 0 := by
  dsimp [orderedBaseCechDifferential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 3) × Fin (n + 2)
  let T : Finset P := {ij : P | (ij.1 : ℕ) ≤ (ij.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ T → P := fun ij hij =>
    (ij.2.succ, Fin.castLT ij.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.2)))
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ,
      not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT, pow_add, pow_one,
        mul_neg, neg_mul, neg_neg, mul_one]
      apply mul_comm
    · rw [orderedBaseCechCoface_comp' π M U n]
      simpa [T] using! hij

/-- The bounded ordered Cech cochain complex. -/
noncomputable def orderedBaseCechComplex
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ :=
  CochainComplex.of (orderedBaseCechObject π M U)
    (orderedBaseCechDifferential π M U)
    (orderedBaseCechDifferential_comp π M U)

@[simp]
private theorem orderedBaseCechComplex_X
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedBaseCechComplex π M U).X n = orderedBaseCechObject π M U n :=
  rfl

@[simp]
theorem orderedBaseCechComplex_d
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedBaseCechComplex π M U).d n (n + 1) =
      orderedBaseCechDifferential π M U n := by
  simp [orderedBaseCechComplex]

/-- The linear differential underlying the ordered Cech complex. -/
private noncomputable abbrev orderedBaseCechLinearDifferential
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :=
  (orderedBaseCechDifferential π M U n).hom

private theorem orderedBaseCechLinearDifferential_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedBaseCechLinearDifferential π M U (n + 1)).comp
      (orderedBaseCechLinearDifferential π M U n) = 0 := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (orderedBaseCechDifferential_comp π M U n) x

end

end AlgebraicGeometry.Scheme.Modules
