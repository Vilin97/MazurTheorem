/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechComparison

/-!
# Alternating extension of ordered Cech cochains

This file constructs the alternating degreewise section from the bounded Cech complex indexed by
strictly increasing tuples to the native Cech complex indexed by all tuples. Restricting the
alternating extension back to increasing tuples is the identity.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The permutation relating the two faces obtained by deleting `k` and `l`. -/
private def cechDeleteSwapFullPerm {n : ℕ} (k l : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  (k.cycleRange.symm.trans (Equiv.swap k l)).trans l.cycleRange

/-- The restriction of `cechDeleteSwapFullPerm` to the positive indices. -/
private def cechDeleteSwapPerm {n : ℕ} (k l : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.decomposeFin (cechDeleteSwapFullPerm k l)).2

private theorem cechDeleteSwapFullPerm_apply_zero {n : ℕ} (k l : Fin (n + 2)) :
    cechDeleteSwapFullPerm k l 0 = 0 := by
  simp [cechDeleteSwapFullPerm]

private theorem cechDeleteSwapFullPerm_eq_decomposeFin {n : ℕ}
    (k l : Fin (n + 2)) :
    cechDeleteSwapFullPerm k l =
      Equiv.Perm.decomposeFin.symm (0, cechDeleteSwapPerm k l) := by
  apply Equiv.Perm.decomposeFin.injective
  apply Prod.ext
  · simpa [Equiv.Perm.decomposeFin] using
      cechDeleteSwapFullPerm_apply_zero k l
  · rfl

private theorem cechDeleteSwapFullPerm_apply_succ {n : ℕ}
    (k l : Fin (n + 2)) (x : Fin (n + 1)) :
    cechDeleteSwapFullPerm k l x.succ = (cechDeleteSwapPerm k l x).succ := by
  rw [cechDeleteSwapFullPerm_eq_decomposeFin]
  simp

private theorem succAbove_cechDeleteSwapPerm {n : ℕ}
    (k l : Fin (n + 2)) (x : Fin (n + 1)) :
    l.succAbove (cechDeleteSwapPerm k l x) =
      Equiv.swap k l (k.succAbove x) := by
  apply l.cycleRange.injective
  rw [Fin.cycleRange_succAbove]
  rw [← cechDeleteSwapFullPerm_apply_succ k l x]
  simp [cechDeleteSwapFullPerm]

private theorem comp_succAbove_cechDeleteSwapPerm_of_eq {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hkl : i k = i l) :
    (i ∘ l.succAbove) ∘ cechDeleteSwapPerm k l =
      i ∘ k.succAbove := by
  funext x
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
    succAbove_cechDeleteSwapPerm]
  exact Equiv.apply_swap_eq_self hkl _

private theorem cechDeleteSwapPerm_sign {n : ℕ}
    (k l : Fin (n + 2)) (hkl : k ≠ l) :
    (Equiv.Perm.sign (cechDeleteSwapPerm k l) : ℤ) =
      -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) := by
  have hsign := congrArg Equiv.Perm.sign
    (cechDeleteSwapFullPerm_eq_decomposeFin k l)
  simp only [Equiv.Perm.decomposeFin.symm_sign, if_pos, one_mul] at hsign
  rw [← hsign]
  simp [cechDeleteSwapFullPerm, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_swap hkl, Units.val_mul, mul_comm]

/-- The permutation induced on a tuple after deleting `r` and applying `σ`. -/
private def cechPermDeleteFull {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (r.cycleRange.symm.trans σ).trans (σ r).cycleRange

/-- The restriction of `cechPermDeleteFull` to the positive indices. -/
private def cechPermDelete {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 2)) : Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.decomposeFin (cechPermDeleteFull σ r)).2

private theorem cechPermDeleteFull_apply_zero {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechPermDeleteFull σ r 0 = 0 := by
  simp [cechPermDeleteFull]

private theorem cechPermDeleteFull_eq_decomposeFin {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechPermDeleteFull σ r =
      Equiv.Perm.decomposeFin.symm (0, cechPermDelete σ r) := by
  apply Equiv.Perm.decomposeFin.injective
  apply Prod.ext
  · simpa [Equiv.Perm.decomposeFin] using
      cechPermDeleteFull_apply_zero σ r
  · rfl

private theorem cechPermDeleteFull_apply_succ {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2))
    (x : Fin (n + 1)) :
    cechPermDeleteFull σ r x.succ = (cechPermDelete σ r x).succ := by
  rw [cechPermDeleteFull_eq_decomposeFin]
  simp

private theorem succAbove_cechPermDelete {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2))
    (x : Fin (n + 1)) :
    (σ r).succAbove (cechPermDelete σ r x) = σ (r.succAbove x) := by
  apply (σ r).cycleRange.injective
  rw [Fin.cycleRange_succAbove]
  rw [← cechPermDeleteFull_apply_succ σ r x]
  simp [cechPermDeleteFull]

private theorem cechPermDelete_sign {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    (Equiv.Perm.sign (cechPermDelete σ r) : ℤ) =
      (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ) *
        (-1 : ℤ) ^ (σ r : ℕ) := by
  have hsign := congrArg Equiv.Perm.sign
    (cechPermDeleteFull_eq_decomposeFin σ r)
  simp only [Equiv.Perm.decomposeFin.symm_sign, if_pos, one_mul] at hsign
  rw [← hsign]
  simp [cechPermDeleteFull, Equiv.Perm.sign_trans, Units.val_mul,
    mul_comm, mul_left_comm]

private theorem cechPermDelete_signed_coefficient {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign (cechPermDelete σ r) : ℤ) =
      (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (σ r : ℕ) := by
  rw [cechPermDelete_sign]
  have hr : (-1 : ℤ) ^ (r : ℕ) * (-1 : ℤ) ^ (r : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (r : ℕ)).neg_one_pow]
  rw [← mul_assoc ((-1 : ℤ) ^ (r : ℕ))
      (((-1 : ℤ) ^ (r : ℕ)) * (Equiv.Perm.sign σ : ℤ))
      ((-1 : ℤ) ^ (σ r : ℕ)),
    ← mul_assoc ((-1 : ℤ) ^ (r : ℕ))
      ((-1 : ℤ) ^ (r : ℕ)) (Equiv.Perm.sign σ : ℤ),
    hr, one_mul]

private theorem exists_eq_ne_of_not_injective
    {α β : Type*} (f : α → β) (hf : ¬ Function.Injective f) :
    ∃ a b, f a = f b ∧ a ≠ b := by
  by_contra h
  apply hf
  intro a b hab
  by_contra hne
  exact h ⟨a, b, hab, hne⟩

private theorem exists_partner_of_delete_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (hi : ¬ Function.Injective i)
    (k : Fin (n + 2)) (hk : Function.Injective (i ∘ k.succAbove)) :
    ∃ l, l ≠ k ∧ i l = i k := by
  obtain ⟨a, b, hab, hne⟩ := exists_eq_ne_of_not_injective i hi
  by_cases ha : a = k
  · subst a
    exact ⟨b, hne.symm, hab.symm⟩
  by_cases hb : b = k
  · subst b
    exact ⟨a, ha, hab⟩
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq ha
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hb
  exfalso
  apply hne
  rw [← ha', ← hb']
  exact congrArg k.succAbove (hk (by simpa [ha', hb'] using hab))

private theorem eq_partner_of_delete_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l x : Fin (n + 2))
    (hk : Function.Injective (i ∘ k.succAbove))
    (hlk : l ≠ k) (hxk : x ≠ k) (hil : i l = i k) (hix : i x = i k) :
    x = l := by
  obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq hxk
  obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq hlk
  rw [← hx', ← hl']
  apply congrArg k.succAbove
  apply hk
  simp [hx', hl', hix, hil]

private theorem delete_partner_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hk : Function.Injective (i ∘ k.succAbove))
    (hlk : l ≠ k) (hil : i l = i k) :
    Function.Injective (i ∘ l.succAbove) := by
  intro a b hab
  apply (Fin.succAbove_right_injective (p := l))
  let x := l.succAbove a
  let y := l.succAbove b
  change x = y
  by_cases hxk : x = k
  · by_cases hyk : y = k
    · exact hxk.trans hyk.symm
    · have hyl : y = l := eq_partner_of_delete_injective
        i k l y hk hlk hyk hil (by simpa [x, y, hxk] using hab.symm)
      exact (l.succAbove_ne b hyl).elim
  · by_cases hyk : y = k
    · have hxl : x = l := eq_partner_of_delete_injective
        i k l x hk hlk hxk hil (by simpa [x, y, hyk] using hab)
      exact (l.succAbove_ne a hxl).elim
    · obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hxk
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hyk
      rw [← ha', ← hb']
      exact congrArg k.succAbove (hk (by simpa [x, y, ha', hb'] using hab))

private theorem delete_not_injective_of_ne {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l m : Fin (n + 2))
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (hil : i l = i k) :
    ¬ Function.Injective (i ∘ m.succAbove) := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hkm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hlm
  intro hm
  apply hkl
  rw [← ha, ← hb]
  exact congrArg m.succAbove (hm (by simpa [ha, hb] using hil.symm))

/-- Reindex native Cech cochains by a permutation of tuple positions. -/
private noncomputable def baseCechPermutationF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (baseCechComplex π M U).X n ⟶ (baseCechComplex π M U).X n :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
      (baseModulePresheaf π M)).map
        ((FormalCoproduct.mk _ U).mapPower σ).op

private theorem baseCechPermutationF_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ τ : Equiv.Perm (Fin (n + 1))) :
    baseCechPermutationF π M U n σ ≫
        baseCechPermutationF π M U n τ =
      baseCechPermutationF π M U n (σ.trans τ) := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    ((FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
        (baseModulePresheaf π M))
  change F.map ((FormalCoproduct.mk _ U).mapPower σ).op ≫
      F.map ((FormalCoproduct.mk _ U).mapPower τ).op =
    F.map ((FormalCoproduct.mk _ U).mapPower (σ.trans τ)).op
  rw [← F.map_comp, ← op_comp]
  congr 1

private theorem baseCechCoface_comp_permutation
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    baseCechCoface π M U n r ≫
        baseCechPermutationF π M U (n + 1) σ =
      baseCechPermutationF π M U n (cechPermDelete σ r) ≫
        baseCechCoface π M U n (σ r) := by
  let V := FormalCoproduct.mk _ U
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    ((FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
        (baseModulePresheaf π M))
  change F.map (V.mapPower r.succAbove).op ≫
      F.map (V.mapPower σ).op =
    F.map (V.mapPower (cechPermDelete σ r)).op ≫
      F.map (V.mapPower (σ r).succAbove).op
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  congr 1
  rw [← FormalCoproduct.mapPower_comp,
    ← FormalCoproduct.mapPower_comp]
  have hfun : σ ∘ r.succAbove =
      (σ r).succAbove ∘ cechPermDelete σ r := by
    funext x
    exact (succAbove_cechPermDelete σ r x).symm
  exact congrArg (fun q => q.op) (congrArg
    (fun f : Fin (n + 1) → Fin (n + 2) => V.mapPower f) hfun)

private theorem baseCechPermutationF_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1) → ι) :
    baseCechPermutationF π M U n σ ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) (i ∘ σ) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower σ).φ i).op := by
  change (Pi.lift fun j : Fin (n + 1) → ι =>
      Pi.π (fun k : Fin (n + 1) → ι => baseCechFactor π M U n k) (j ∘ σ) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower σ).φ j).op) ≫ _ = _
  exact Pi.lift_π _ i

theorem baseCechXIsoPi_hom_comp_proj
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechXIsoPi π M U n).hom ≫
        ModuleCat.ofHom
          (LinearMap.proj i :
            (∀ j : Fin (n + 1) → ι, baseCechFactor π M U n j) →ₗ[
              Γ(S, (⊤ : S.Opens))] baseCechFactor π M U n i) =
      Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i := by
  exact ModuleCat.piIsoPi_hom_ker_subtype _ i

private theorem orderedBaseCechZeroExtendLinearMap_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : orderedBaseCechTerm π M U n) (i : Fin (n + 1) → ι) :
    orderedBaseCechZeroExtendLinearMap π M U n x i =
      if h : StrictMono i then x ⟨i, h⟩ else 0 := by
  rfl

private theorem orderedToBaseCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ ≠ 1) :
    orderedToBaseCechZeroExtensionF π M U n ≫
        baseCechPermutationF π M U n σ ≫
          baseCechToOrderedF π M U n = 0 := by
  apply (cancel_epi (orderedBaseCechObjectIsoPi π M U n).inv).1
  apply (cancel_mono (orderedBaseCechObjectIsoPi π M U n).hom).1
  rw [comp_zero, zero_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi : ¬ StrictMono (i.1 ∘ σ) := by
    intro h
    have hmono : Monotone σ := fun a b hab =>
      i.2.le_iff_le.mp (h.monotone hab)
    exact hσ ((Equiv.Perm.monotone_iff σ).mp hmono)
  have hcomp :
      (orderedBaseCechObjectIsoPi π M U n).inv ≫
        orderedToBaseCechZeroExtensionF π M U n ≫
            baseCechPermutationF π M U n σ ≫
              baseCechToOrderedF π M U n ≫
                (orderedBaseCechObjectIsoPi π M U n).hom ≫
                  ModuleCat.ofHom (LinearMap.proj i) = 0 := by
    rw [orderedBaseCechObjectIsoPi_hom_comp_proj π M U n i,
      baseCechToOrderedF_comp_π π M U n i,
      baseCechPermutationF_comp_π π M U n σ i.1]
    let e := Pi.π (fun j : Fin (n + 1) → ι =>
      baseCechFactor π M U n j) (i.1 ∘ σ)
    let r : baseCechFactor π M U n (i.1 ∘ σ) ⟶
        baseCechFactor π M U n i.1 :=
      (baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower σ).φ i.1).op
    change (orderedBaseCechObjectIsoPi π M U n).inv ≫
      orderedToBaseCechZeroExtensionF π M U n ≫ e ≫ r = 0
    rw [orderedToBaseCechZeroExtensionF]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hprefix :
        ModuleCat.ofHom (orderedBaseCechZeroExtendLinearMap π M U n) ≫
            (baseCechXIsoPi π M U n).inv ≫ e = 0 := by
      dsimp only [e]
      rw [baseCechXIsoPi_inv_comp_proj π M U n (i.1 ∘ σ)]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change orderedBaseCechZeroExtendLinearMap π M U n y (i.1 ∘ σ) = 0
      rw [orderedBaseCechZeroExtendLinearMap_apply, dif_neg hi]
    let a := ModuleCat.ofHom (orderedBaseCechZeroExtendLinearMap π M U n)
    calc
      a ≫ ((baseCechXIsoPi π M U n).inv ≫ (e ≫ r)) =
          a ≫ (((baseCechXIsoPi π M U n).inv ≫ e) ≫ r) :=
        congrArg (fun q => a ≫ q)
          (Category.assoc (baseCechXIsoPi π M U n).inv e r).symm
      _ = (a ≫ ((baseCechXIsoPi π M U n).inv ≫ e)) ≫ r :=
        (Category.assoc a ((baseCechXIsoPi π M U n).inv ≫ e) r).symm
      _ = 0 := by rw [hprefix, zero_comp]
  have hx := ConcreteCategory.congr_hom hcomp x
  exact hx

private theorem orderedToBaseCechZeroExtensionF_comp_π_of_not_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : ¬ StrictMono i) :
    orderedToBaseCechZeroExtensionF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i = 0 := by
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  change orderedToBaseCechZeroExtensionF π M U n ≫ p = 0
  have hlinear :
      ModuleCat.ofHom (orderedBaseCechZeroExtendLinearMap π M U n) ≫
          (baseCechXIsoPi π M U n).inv ≫ p = 0 := by
    dsimp only [p]
    rw [baseCechXIsoPi_inv_comp_proj]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change orderedBaseCechZeroExtendLinearMap π M U n x i = 0
    rw [orderedBaseCechZeroExtendLinearMap_apply, dif_neg hi]
  rw [orderedToBaseCechZeroExtensionF]
  simp only [Category.assoc, hlinear, comp_zero]

private theorem orderedToBaseCechZeroExtensionF_comp_π_of_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    orderedToBaseCechZeroExtensionF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      Pi.π (fun j : OrderedCechIndex ι n =>
        baseCechFactor π M U n j.1) ⟨i, hi⟩ := by
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  let q : orderedBaseCechObject π M U n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1) ⟨i, hi⟩
  have hp : baseCechToOrderedF π M U n ≫ q = p := by
    dsimp only [p, q]
    exact baseCechToOrderedF_comp_π π M U n ⟨i, hi⟩
  change orderedToBaseCechZeroExtensionF π M U n ≫ p = q
  calc
    orderedToBaseCechZeroExtensionF π M U n ≫ p =
        orderedToBaseCechZeroExtensionF π M U n ≫
          (baseCechToOrderedF π M U n ≫ q) :=
      congrArg (orderedToBaseCechZeroExtensionF π M U n ≫ ·) hp.symm
    _ = (orderedToBaseCechZeroExtensionF π M U n ≫
          baseCechToOrderedF π M U n) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = q := by
      rw [orderedToBaseCechZeroExtensionF_comp_baseCechToOrderedF,
        Category.id_comp]

/-- Alternating extension from increasing tuples to all tuples. -/
noncomputable def orderedToBaseCechAlternatingF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechObject π M U n ⟶ (baseCechComplex π M U).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
    (orderedToBaseCechZeroExtensionF π M U n ≫
      baseCechPermutationF π M U n σ)

private theorem orderedToBaseCechAlternatingF_comp_permutation
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    orderedToBaseCechAlternatingF π M U n ≫
        baseCechPermutationF π M U n τ =
      (Equiv.Perm.sign τ : ℤ) •
        orderedToBaseCechAlternatingF π M U n := by
  rw [orderedToBaseCechAlternatingF, sum_comp, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [zsmul_comp, Category.assoc, baseCechPermutationF_comp,
    Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]
  rw [show σ.trans τ = τ * σ by rfl]
  rw [Units.val_mul, ← mul_assoc, Int.units_coe_mul_self, one_mul]

private theorem baseCechProjection_comp_map_eq_of_eq
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (j k : Fin (n + 1) → ι) (hjk : j = k) {V : X.Opens}
    (a : V ⟶ ∏ᶜ fun x : Fin (n + 1) => U (j x))
    (b : V ⟶ ∏ᶜ fun x : Fin (n + 1) => U (k x)) :
    Pi.π (fun q : Fin (n + 1) → ι =>
        baseCechFactor π M U n q) j ≫
        (baseModulePresheaf π M).map a.op =
      Pi.π (fun q : Fin (n + 1) → ι =>
        baseCechFactor π M U n q) k ≫
        (baseModulePresheaf π M).map b.op := by
  subst k
  rw [Subsingleton.elim a b]

private theorem orderedToBaseCechAlternatingF_comp_coface_π_pair
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) :
    orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π M U n j) (i ∘ k.succAbove) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op =
      (Equiv.Perm.sign (cechDeleteSwapPerm k l) : ℤ) •
        (orderedToBaseCechAlternatingF π M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            baseCechFactor π M U n j) (i ∘ l.succAbove) ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op) := by
  let ρ := cechDeleteSwapPerm k l
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n (i ∘ l.succAbove) :=
    Pi.π (fun j : Fin (n + 1) → ι =>
      baseCechFactor π M U n j) (i ∘ l.succAbove)
  let r : baseCechFactor π M U n (i ∘ l.succAbove) ⟶
      baseCechFactor π M U (n + 1) i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op
  let pk : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n (i ∘ k.succAbove) :=
    Pi.π (fun j : Fin (n + 1) → ι =>
      baseCechFactor π M U n j) (i ∘ k.succAbove)
  let rk : baseCechFactor π M U n (i ∘ k.succAbove) ⟶
      baseCechFactor π M U (n + 1) i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op
  have htuple : (i ∘ l.succAbove) ∘ ρ = i ∘ k.succAbove :=
    comp_succAbove_cechDeleteSwapPerm_of_eq i k l hki
  let pρ : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n ((i ∘ l.succAbove) ∘ ρ) :=
    Pi.π (fun j : Fin (n + 1) → ι =>
      baseCechFactor π M U n j) ((i ∘ l.succAbove) ∘ ρ)
  let rρ : baseCechFactor π M U n ((i ∘ l.succAbove) ∘ ρ) ⟶
      baseCechFactor π M U n (i ∘ l.succAbove) :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower ρ).φ (i ∘ l.succAbove)).op
  have hρp : baseCechPermutationF π M U n ρ ≫ p = pρ ≫ rρ := by
    dsimp only [p, pρ, rρ]
    exact baseCechPermutationF_comp_π
      π M U n ρ (i ∘ l.succAbove)
  let a : (∏ᶜ fun x : Fin (n + 2) => U (i x)) ⟶
      ∏ᶜ fun x : Fin (n + 1) => U (((i ∘ l.succAbove) ∘ ρ) x) :=
    ((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i ≫
      ((FormalCoproduct.mk _ U).mapPower ρ).φ (i ∘ l.succAbove)
  let b : (∏ᶜ fun x : Fin (n + 2) => U (i x)) ⟶
      ∏ᶜ fun x : Fin (n + 1) => U ((i ∘ k.succAbove) x) :=
    ((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i
  have hrmaps : rρ ≫ r = (baseModulePresheaf π M).map a.op := by
    let f := ((FormalCoproduct.mk _ U).mapPower ρ).φ (i ∘ l.succAbove)
    let g := ((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i
    change (baseModulePresheaf π M).map f.op ≫
      (baseModulePresheaf π M).map g.op =
        (baseModulePresheaf π M).map (g ≫ f).op
    calc
      (baseModulePresheaf π M).map f.op ≫
          (baseModulePresheaf π M).map g.op =
        (baseModulePresheaf π M).map (f.op ≫ g.op) :=
          ((baseModulePresheaf π M).map_comp f.op g.op).symm
      _ = (baseModulePresheaf π M).map (g ≫ f).op := by
        exact congrArg (baseModulePresheaf π M).map
          (Subsingleton.elim _ _)
  have hproj : pρ ≫ (baseModulePresheaf π M).map a.op =
      pk ≫ (baseModulePresheaf π M).map b.op := by
    dsimp only [pρ, pk]
    exact baseCechProjection_comp_map_eq_of_eq
      π M U n ((i ∘ l.succAbove) ∘ ρ) (i ∘ k.succAbove)
        htuple a b
  have hrest : (pρ ≫ rρ) ≫ r = pk ≫ rk := by
    calc
      (pρ ≫ rρ) ≫ r = pρ ≫ (rρ ≫ r) := Category.assoc _ _ _
      _ = pρ ≫ (baseModulePresheaf π M).map a.op := by rw [hrmaps]
      _ = pk ≫ (baseModulePresheaf π M).map b.op := hproj
      _ = pk ≫ rk := by rfl
  have hface : baseCechPermutationF π M U n ρ ≫ p ≫ r = pk ≫ rk := by
    calc
      baseCechPermutationF π M U n ρ ≫ p ≫ r = (pρ ≫ rρ) ≫ r := by
        exact congrArg (fun f => f ≫ r) hρp
      _ = pk ≫ rk := hrest
  have hperm := orderedToBaseCechAlternatingF_comp_permutation
    π M U n ρ
  change orderedToBaseCechAlternatingF π M U n ≫ pk ≫ rk =
    (Equiv.Perm.sign ρ : ℤ) •
      (orderedToBaseCechAlternatingF π M U n ≫ p ≫ r)
  calc
    orderedToBaseCechAlternatingF π M U n ≫ pk ≫ rk =
        orderedToBaseCechAlternatingF π M U n ≫
          ((baseCechPermutationF π M U n ρ ≫ p) ≫ r) := by
      simp only [Category.assoc]
      rw [hface]
    _ = (orderedToBaseCechAlternatingF π M U n ≫
        baseCechPermutationF π M U n ρ) ≫ (p ≫ r) := by
      simp only [Category.assoc]
    _ = ((Equiv.Perm.sign ρ : ℤ) •
        orderedToBaseCechAlternatingF π M U n) ≫ (p ≫ r) := by
      rw [hperm]
    _ = (Equiv.Perm.sign ρ : ℤ) •
        (orderedToBaseCechAlternatingF π M U n ≫ p ≫ r) := by
      rw [zsmul_comp]

private theorem orderedToBaseCechAlternatingF_comp_coface_π_pair_cancel
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) (hkl : k ≠ l) :
    (-1 : ℤ) ^ (k : ℕ) •
        (orderedToBaseCechAlternatingF π M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            baseCechFactor π M U n j) (i ∘ k.succAbove) ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op) +
      (-1 : ℤ) ^ (l : ℕ) •
        (orderedToBaseCechAlternatingF π M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            baseCechFactor π M U n j) (i ∘ l.succAbove) ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op) = 0 := by
  let t := orderedToBaseCechAlternatingF π M U n ≫
    Pi.π (fun j : Fin (n + 1) → ι =>
      baseCechFactor π M U n j) (i ∘ l.succAbove) ≫
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op
  have hpair := orderedToBaseCechAlternatingF_comp_coface_π_pair
    π M U n i k l hki
  change (-1 : ℤ) ^ (k : ℕ) • _ + (-1 : ℤ) ^ (l : ℕ) • t = 0
  rw [hpair, smul_smul, cechDeleteSwapPerm_sign k l hkl]
  have hcoef :
      (-1 : ℤ) ^ (k : ℕ) *
          -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) =
        -((-1 : ℤ) ^ (l : ℕ)) := by
    rw [mul_neg, ← mul_assoc, ← pow_add,
      (Even.add_self (k : ℕ)).neg_one_pow, one_mul]
  rw [hcoef, neg_smul, neg_add_cancel]

theorem orderedToBaseCechAlternatingF_comp_π_of_not_injective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : ¬ Function.Injective i) :
    orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i = 0 := by
  let e : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  change orderedToBaseCechAlternatingF π M U n ≫ e = 0
  rw [orderedToBaseCechAlternatingF, sum_comp]
  apply Finset.sum_eq_zero
  intro σ _
  rw [zsmul_comp, Category.assoc, baseCechPermutationF_comp_π]
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n (i ∘ σ) :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) (i ∘ σ)
  let r : baseCechFactor π M U n (i ∘ σ) ⟶
      baseCechFactor π M U n i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
  change (Equiv.Perm.sign σ : ℤ) •
    (orderedToBaseCechZeroExtensionF π M U n ≫ p ≫ r) = 0
  have hmono : ¬ StrictMono (i ∘ σ) := by
    intro h
    apply hi
    intro a b hab
    apply σ.symm.injective
    apply h.injective
    simpa using hab
  have hz :
      orderedToBaseCechZeroExtensionF π M U n ≫ p = 0 := by
    dsimp only [p]
    exact orderedToBaseCechZeroExtensionF_comp_π_of_not_strictMono
      π M U n (i ∘ σ) hmono
  have hpost :
      orderedToBaseCechZeroExtensionF π M U n ≫ (p ≫ r) = 0 := by
    calc
      orderedToBaseCechZeroExtensionF π M U n ≫ (p ≫ r) =
          (orderedToBaseCechZeroExtensionF π M U n ≫ p) ≫ r :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hz, zero_comp]
  rw [hpost, smul_zero]

private theorem baseCechPermutationF_one
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    baseCechPermutationF π M U n 1 = 𝟙 _ := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
      (baseModulePresheaf π M))
  change F.map
        ((FormalCoproduct.mk _ U).mapPower (id : Fin (n + 1) → Fin (n + 1))).op = _
  rw [FormalCoproduct.mapPower_id]
  exact F.map_id _

private theorem orderedToBaseCechAlternatingF_comp_baseCechToOrderedF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedToBaseCechAlternatingF π M U n ≫
      baseCechToOrderedF π M U n = 𝟙 _ := by
  rw [orderedToBaseCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single 1]
  · simp [baseCechPermutationF_one,
      orderedToBaseCechZeroExtensionF_comp_baseCechToOrderedF]
  · intro σ hσ hne
    rw [zsmul_comp]
    simp [orderedToBaseCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
      π M U n σ hne]
  · simp

theorem orderedToBaseCechAlternatingF_comp_π_of_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      Pi.π (fun j : OrderedCechIndex ι n =>
        baseCechFactor π M U n j.1) ⟨i, hi⟩ := by
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  let q : orderedBaseCechObject π M U n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1) ⟨i, hi⟩
  have hp : baseCechToOrderedF π M U n ≫ q = p := by
    dsimp only [p, q]
    exact baseCechToOrderedF_comp_π π M U n ⟨i, hi⟩
  change orderedToBaseCechAlternatingF π M U n ≫ p = q
  calc
    orderedToBaseCechAlternatingF π M U n ≫ p =
        orderedToBaseCechAlternatingF π M U n ≫
          (baseCechToOrderedF π M U n ≫ q) :=
      congrArg (orderedToBaseCechAlternatingF π M U n ≫ ·) hp.symm
    _ = (orderedToBaseCechAlternatingF π M U n ≫
          baseCechToOrderedF π M U n) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = q := by
      rw [orderedToBaseCechAlternatingF_comp_baseCechToOrderedF,
        Category.id_comp]

theorem orderedToBaseCechAlternatingF_comp_π_of_injective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : Function.Injective i) :
    orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i =
      (Equiv.Perm.sign (Tuple.sort i) : ℤ) •
        (Pi.π (fun j : OrderedCechIndex ι n =>
          baseCechFactor π M U n j.1)
            ⟨i ∘ Tuple.sort i,
              (Tuple.monotone_sort i).strictMono_of_injective
                (hi.comp (Tuple.sort i).injective)⟩ ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower (Tuple.sort i)).φ i).op) := by
  let s := Tuple.sort i
  have hs : StrictMono (i ∘ s) :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp s.injective)
  let p : (baseCechComplex π M U).X n ⟶ baseCechFactor π M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor π M U n j) i
  let q : orderedBaseCechObject π M U n ⟶
      baseCechFactor π M U n (i ∘ s) :=
    Pi.π (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1) ⟨i ∘ s, hs⟩
  let r : baseCechFactor π M U n (i ∘ s) ⟶
      baseCechFactor π M U n i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower s).φ i).op
  change orderedToBaseCechAlternatingF π M U n ≫ p =
    (Equiv.Perm.sign s : ℤ) • (q ≫ r)
  rw [orderedToBaseCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single s]
  · rw [zsmul_comp, Category.assoc, baseCechPermutationF_comp_π]
    let ps : (baseCechComplex π M U).X n ⟶
        baseCechFactor π M U n (i ∘ s) :=
      Pi.π (fun j : Fin (n + 1) → ι =>
        baseCechFactor π M U n j) (i ∘ s)
    have hz :
        orderedToBaseCechZeroExtensionF π M U n ≫ ps = q := by
      dsimp only [ps, q]
      exact orderedToBaseCechZeroExtensionF_comp_π_of_strictMono
        π M U n (i ∘ s) hs
    change (Equiv.Perm.sign s : ℤ) •
      (orderedToBaseCechZeroExtensionF π M U n ≫ (ps ≫ r)) =
        (Equiv.Perm.sign s : ℤ) • (q ≫ r)
    have hpost :
        orderedToBaseCechZeroExtensionF π M U n ≫ (ps ≫ r) = q ≫ r := by
      calc
        orderedToBaseCechZeroExtensionF π M U n ≫ (ps ≫ r) =
            (orderedToBaseCechZeroExtensionF π M U n ≫ ps) ≫ r :=
          (Category.assoc _ _ _).symm
        _ = q ≫ r := congrArg (· ≫ r) hz
    exact congrArg ((Equiv.Perm.sign s : ℤ) • ·) hpost
  · intro σ _ hne
    rw [zsmul_comp, Category.assoc, baseCechPermutationF_comp_π]
    have hmono : ¬ StrictMono (i ∘ σ) := by
      intro h
      apply hne
      apply Equiv.ext
      intro x
      apply hi
      exact congrFun
        (Tuple.comp_sort_eq_comp_iff_monotone.mpr h.monotone) x
    have hz := orderedToBaseCechZeroExtensionF_comp_π_of_not_strictMono
      π M U n (i ∘ σ) hmono
    let rσ : baseCechFactor π M U n (i ∘ σ) ⟶
        baseCechFactor π M U n i :=
      (baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
    let pσ : (baseCechComplex π M U).X n ⟶
        baseCechFactor π M U n (i ∘ σ) :=
      Pi.π (fun j : Fin (n + 1) → ι =>
        baseCechFactor π M U n j) (i ∘ σ)
    change (Equiv.Perm.sign σ : ℤ) •
      (orderedToBaseCechZeroExtensionF π M U n ≫ (pσ ≫ rσ)) = 0
    have hpost :
        orderedToBaseCechZeroExtensionF π M U n ≫ (pσ ≫ rσ) = 0 := by
      calc
        orderedToBaseCechZeroExtensionF π M U n ≫ (pσ ≫ rσ) =
            (orderedToBaseCechZeroExtensionF π M U n ≫ pσ) ≫ rσ :=
          (Category.assoc _ _ _).symm
        _ = 0 := by
          dsimp only [pσ]
          rw [hz, zero_comp]
    rw [hpost, smul_zero]
  · simp

private theorem orderedToBaseCechAlternatingF_comp_d_comp_permutation
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) ≫
          baseCechPermutationF π M U (n + 1) σ =
      (Equiv.Perm.sign σ : ℤ) •
        (orderedToBaseCechAlternatingF π M U n ≫
          (baseCechComplex π M U).d n (n + 1)) := by
  rw [baseCechComplex_d_eq_sum_cofaces]
  simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp,
    Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv σ _ _ fun r => ?_
  rw [baseCechCoface_comp_permutation]
  rw [← Category.assoc,
    orderedToBaseCechAlternatingF_comp_permutation]
  simp only [zsmul_comp, smul_smul]
  rw [cechPermDelete_signed_coefficient]

private theorem orderedToBaseCechAlternatingF_comp_d_comp_π_of_not_injective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : ¬ Function.Injective i) :
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            baseCechFactor π M U (n + 1) j) i = 0 := by
  let p : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) j) i
  change orderedToBaseCechAlternatingF π M U n ≫
    ((baseCechComplex π M U).d n (n + 1) ≫ p) = 0
  let G : Fin (n + 2) →
      ((baseCechComplex π M U).X n ⟶ baseCechFactor π M U (n + 1) i) :=
    fun k => (-1 : ℤ) ^ (k : ℕ) •
      (Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π M U n j) (i ∘ k.succAbove) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op)
  let F : Fin (n + 2) →
      (orderedBaseCechObject π M U n ⟶ baseCechFactor π M U (n + 1) i) :=
    fun k => (-1 : ℤ) ^ (k : ℕ) •
      (orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π M U n j) (i ∘ k.succAbove) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op)
  have hd : (baseCechComplex π M U).d n (n + 1) ≫ p = ∑ k, G k := by
    dsimp only [p, G]
    exact baseCechComplex_d_comp_π π M U n i
  have hcomp : orderedToBaseCechAlternatingF π M U n ≫ (∑ k, G k) =
      ∑ k, orderedToBaseCechAlternatingF π M U n ≫ G k := by
    simpa using comp_sum (Finset.univ : Finset (Fin (n + 2)))
      (orderedToBaseCechAlternatingF π M U n) G
  have hterms : (∑ k, orderedToBaseCechAlternatingF π M U n ≫ G k) =
      ∑ k, F k := by
    apply Finset.sum_congr rfl
    intro k _
    let q : (baseCechComplex π M U).X n ⟶
        baseCechFactor π M U (n + 1) i :=
      Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π M U n j) (i ∘ k.succAbove) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op
    change orderedToBaseCechAlternatingF π M U n ≫
      ((-1 : ℤ) ^ (k : ℕ) • q) =
        (-1 : ℤ) ^ (k : ℕ) •
          (orderedToBaseCechAlternatingF π M U n ≫ q)
    exact comp_zsmul _ _ ((-1 : ℤ) ^ (k : ℕ))
  rw [hd, hcomp, hterms]
  by_cases hall : ∀ k : Fin (n + 2),
      ¬ Function.Injective (i ∘ k.succAbove)
  · apply Finset.sum_eq_zero
    intro k _
    let q : orderedBaseCechObject π M U n ⟶
        baseCechFactor π M U n (i ∘ k.succAbove) :=
      orderedToBaseCechAlternatingF π M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π M U n j) (i ∘ k.succAbove)
    let r : baseCechFactor π M U n (i ∘ k.succAbove) ⟶
        baseCechFactor π M U (n + 1) i :=
      (baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op
    have hk := orderedToBaseCechAlternatingF_comp_π_of_not_injective
      π M U n (i ∘ k.succAbove) (hall k)
    change (-1 : ℤ) ^ (k : ℕ) • (q ≫ r) = 0
    change q = 0 at hk
    rw [hk, zero_comp, smul_zero]
  · have hex : ∃ k : Fin (n + 2),
        Function.Injective (i ∘ k.succAbove) := by
      by_contra h
      apply hall
      intro k hk
      exact h ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    obtain ⟨l, hlk, hil⟩ := exists_partner_of_delete_injective i hi k hk
    have hkl : k ≠ l := hlk.symm
    have hother (m : Fin (n + 2)) (hmk : m ≠ k) (hml : m ≠ l) :
        F m = 0 := by
      let q : orderedBaseCechObject π M U n ⟶
          baseCechFactor π M U n (i ∘ m.succAbove) :=
        orderedToBaseCechAlternatingF π M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            baseCechFactor π M U n j) (i ∘ m.succAbove)
      let r : baseCechFactor π M U n (i ∘ m.succAbove) ⟶
          baseCechFactor π M U (n + 1) i :=
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower m.succAbove).φ i).op
      have hm := delete_not_injective_of_ne i k l m hkl hmk.symm hml.symm hil
      have hz := orderedToBaseCechAlternatingF_comp_π_of_not_injective
        π M U n (i ∘ m.succAbove) hm
      change (-1 : ℤ) ^ (m : ℕ) • (q ≫ r) = 0
      change q = 0 at hz
      rw [hz, zero_comp, smul_zero]
    have hrem : ((Finset.univ.erase l).erase k).sum F = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      have hml : m ≠ l :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      exact hother m hmk hml
    have hk_mem : k ∈ Finset.univ.erase l :=
      Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ k⟩
    calc
      ∑ m, F m = (Finset.univ.erase l).sum F + F l :=
        (Finset.sum_erase_add Finset.univ F (Finset.mem_univ l)).symm
      _ = (((Finset.univ.erase l).erase k).sum F + F k) + F l := by
        rw [Finset.sum_erase_add (Finset.univ.erase l) F hk_mem]
      _ = F k + F l := by rw [hrem, zero_add]
      _ = 0 := by
        dsimp only [F]
        exact orderedToBaseCechAlternatingF_comp_coface_π_pair_cancel
          π M U n i k l hil.symm hkl

private theorem orderedToBaseCechAlternatingF_comp_d_comp_π_of_strictMono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : StrictMono i) :
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            baseCechFactor π M U (n + 1) j) i =
      orderedBaseCechDifferential π M U n ≫
        orderedToBaseCechAlternatingF π M U (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            baseCechFactor π M U (n + 1) j) i := by
  let p : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) j) i
  let q : orderedBaseCechObject π M U (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun j : OrderedCechIndex ι (n + 1) =>
      baseCechFactor π M U (n + 1) j.1) ⟨i, hi⟩
  have hp : baseCechToOrderedF π M U (n + 1) ≫ q = p := by
    dsimp only [p, q]
    exact baseCechToOrderedF_comp_π π M U (n + 1) ⟨i, hi⟩
  have ha : orderedToBaseCechAlternatingF π M U (n + 1) ≫ p = q := by
    dsimp only [p, q]
    exact orderedToBaseCechAlternatingF_comp_π_of_strictMono
      π M U (n + 1) i hi
  change orderedToBaseCechAlternatingF π M U n ≫
      (baseCechComplex π M U).d n (n + 1) ≫ p =
    orderedBaseCechDifferential π M U n ≫
      orderedToBaseCechAlternatingF π M U (n + 1) ≫ p
  calc
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) ≫ p =
      orderedToBaseCechAlternatingF π M U n ≫
        ((baseCechComplex π M U).d n (n + 1) ≫
          baseCechToOrderedF π M U (n + 1)) ≫ q := by
        rw [Category.assoc, hp]
    _ = orderedToBaseCechAlternatingF π M U n ≫
        (baseCechToOrderedF π M U n ≫
          orderedBaseCechDifferential π M U n) ≫ q := by
      rw [baseCechComplex_d_comp_baseCechToOrderedF]
    _ = (orderedToBaseCechAlternatingF π M U n ≫
          baseCechToOrderedF π M U n) ≫
        orderedBaseCechDifferential π M U n ≫ q := by
      simp only [Category.assoc]
    _ = orderedBaseCechDifferential π M U n ≫ q := by
      rw [orderedToBaseCechAlternatingF_comp_baseCechToOrderedF,
        Category.id_comp]
    _ = orderedBaseCechDifferential π M U n ≫
        orderedToBaseCechAlternatingF π M U (n + 1) ≫ p := by
      rw [ha]

private theorem orderedToBaseCechAlternatingF_comp_d_comp_π_of_injective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : Function.Injective i) :
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            baseCechFactor π M U (n + 1) j) i =
      orderedBaseCechDifferential π M U n ≫
        orderedToBaseCechAlternatingF π M U (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            baseCechFactor π M U (n + 1) j) i := by
  let σ := Tuple.sort i
  let j := i ∘ σ
  have hj : StrictMono j :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp σ.injective)
  let A : orderedBaseCechObject π M U n ⟶
      (baseCechComplex π M U).X (n + 1) :=
    orderedToBaseCechAlternatingF π M U n ≫
      (baseCechComplex π M U).d n (n + 1)
  let B := orderedToBaseCechAlternatingF π M U (n + 1)
  let D := orderedBaseCechDifferential π M U n
  let P := baseCechPermutationF π M U (n + 1) σ
  let p : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun q : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) q) i
  let pj : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) j :=
    Pi.π (fun q : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) q) j
  let q : orderedBaseCechObject π M U (n + 1) ⟶
      baseCechFactor π M U (n + 1) j :=
    Pi.π (fun t : OrderedCechIndex ι (n + 1) =>
      baseCechFactor π M U (n + 1) t.1) ⟨j, hj⟩
  let r : baseCechFactor π M U (n + 1) j ⟶
      baseCechFactor π M U (n + 1) i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
  let s : ℤ := Equiv.Perm.sign σ
  have hPp : P ≫ p = pj ≫ r := by
    dsimp only [P, p, pj, r, j]
    exact baseCechPermutationF_comp_π π M U (n + 1) σ i
  have hAperm := orderedToBaseCechAlternatingF_comp_d_comp_permutation
    π M U n σ
  change A ≫ P = s • A at hAperm
  have hrel : A ≫ pj ≫ r = s • (A ≫ p) := by
    calc
      A ≫ pj ≫ r = A ≫ (P ≫ p) := by rw [hPp]
      _ = (A ≫ P) ≫ p := by simp only [Category.assoc]
      _ = (s • A) ≫ p := by rw [hAperm]
      _ = s • (A ≫ p) := by rw [zsmul_comp]
  have hs : s * s = 1 := by
    dsimp only [s]
    exact Int.units_coe_mul_self (Equiv.Perm.sign σ)
  have hrel' : A ≫ p = s • (A ≫ pj ≫ r) := by
    calc
      A ≫ p = s • (s • (A ≫ p)) := by
        rw [smul_smul, hs, one_smul]
      _ = s • (A ≫ pj ≫ r) := congrArg (s • ·) hrel.symm
  have hstrict :=
    orderedToBaseCechAlternatingF_comp_d_comp_π_of_strictMono
      π M U n j hj
  change A ≫ pj = D ≫ B ≫ pj at hstrict
  have hBj := orderedToBaseCechAlternatingF_comp_π_of_strictMono
    π M U (n + 1) j hj
  change B ≫ pj = q at hBj
  have hBi := orderedToBaseCechAlternatingF_comp_π_of_injective
    π M U (n + 1) i hi
  change B ≫ p = s • (q ≫ r) at hBi
  have hstrict_r : (A ≫ pj) ≫ r = (D ≫ B ≫ pj) ≫ r :=
    congrArg (fun f => f ≫ r) hstrict
  have hDj : D ≫ B ≫ pj = D ≫ q :=
    congrArg (D ≫ ·) hBj
  have hDj_r : (D ≫ B ≫ pj) ≫ r = (D ≫ q) ≫ r :=
    congrArg (fun f => f ≫ r) hDj
  change A ≫ p = D ≫ B ≫ p
  calc
    A ≫ p = s • (A ≫ pj ≫ r) := hrel'
    _ = s • ((D ≫ B ≫ pj) ≫ r) := congrArg (s • ·) hstrict_r
    _ = s • ((D ≫ q) ≫ r) := congrArg (s • ·) hDj_r
    _ = D ≫ (s • (q ≫ r)) := by
      calc
        s • ((D ≫ q) ≫ r) = s • (D ≫ (q ≫ r)) :=
          congrArg (s • ·) (Category.assoc D q r)
        _ = D ≫ (s • (q ≫ r)) :=
          (comp_zsmul D (q ≫ r) s).symm
    _ = D ≫ (B ≫ p) := by rw [hBi]
    _ = D ≫ B ≫ p := by rfl

theorem orderedToBaseCechAlternatingF_comp_d
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedToBaseCechAlternatingF π M U n ≫
        (baseCechComplex π M U).d n (n + 1) =
      orderedBaseCechDifferential π M U n ≫
        orderedToBaseCechAlternatingF π M U (n + 1) := by
  apply Pi.hom_ext
  intro i
  let p : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) j) i
  change (orderedToBaseCechAlternatingF π M U n ≫
      (baseCechComplex π M U).d n (n + 1)) ≫ p =
    (orderedBaseCechDifferential π M U n ≫
      orderedToBaseCechAlternatingF π M U (n + 1)) ≫ p
  by_cases hi : Function.Injective i
  · exact orderedToBaseCechAlternatingF_comp_d_comp_π_of_injective
      π M U n i hi
  · have hleft :=
      orderedToBaseCechAlternatingF_comp_d_comp_π_of_not_injective
        π M U n i hi
    change (orderedToBaseCechAlternatingF π M U n ≫
      (baseCechComplex π M U).d n (n + 1)) ≫ p = 0 at hleft
    have hright := orderedToBaseCechAlternatingF_comp_π_of_not_injective
      π M U (n + 1) i hi
    change orderedToBaseCechAlternatingF π M U (n + 1) ≫ p = 0 at hright
    rw [hleft, Category.assoc, hright, comp_zero]

/-- The alternating extension from ordered Cech cochains to native Cech cochains. -/
noncomputable def orderedToBaseCechAlternating
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedBaseCechComplex π M U ⟶ baseCechComplex π M U :=
  CochainComplex.ofHom (orderedToBaseCechAlternatingF π M U) fun n => by
    rw [orderedBaseCechComplex_d]
    exact orderedToBaseCechAlternatingF_comp_d π M U n

@[simp]
private theorem orderedToBaseCechAlternating_f
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedToBaseCechAlternating π M U).f n =
      orderedToBaseCechAlternatingF π M U n :=
  rfl

/-- Alternating extension is a left inverse to projection onto strictly
increasing Cech indices. -/
theorem orderedToBaseCechAlternating_comp_baseCechToOrdered
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedToBaseCechAlternating π M U ≫ baseCechToOrdered π M U =
      𝟙 (orderedBaseCechComplex π M U) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact orderedToBaseCechAlternatingF_comp_baseCechToOrderedF
    π M U n

end

end AlgebraicGeometry.Scheme.Modules
