/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# Degree-one comparison for ordered and native Cech complexes

A native degree-one Cech cocycle vanishes on repeated pairs and changes sign when its two
indices are exchanged. Consequently, projecting it to strictly increasing pairs and extending
alternatingly recovers the original cocycle. This transfers degree-one exactness from the bounded
ordered Cech complex to the native all-tuples Cech complex.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private noncomputable def mapPowerComponentIsoOfCoverage
    {X : Scheme.{u}} {ι : Type u} {α β : Type v} (U : ι → X.Opens)
    (f : α → β) (i : β → ι)
    (h : ∀ b, ∃ a, i b = i (f a)) :
    (∏ᶜ fun b : β => U (i b)) ≅
      (∏ᶜ fun a : α => U (i (f a))) where
  hom := ((FormalCoproduct.mk _ U).mapPower f).φ i
  inv := Pi.lift fun b =>
    Pi.π (fun a : α => U (i (f a))) (Classical.choose (h b)) ≫
      eqToHom (congrArg U (Classical.choose_spec (h b))).symm
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

private theorem baseCechProjection_comp_eqToHom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    {j k : Fin (n + 1) → ι} (h : j = k) :
    Pi.π (fun l : Fin (n + 1) → ι => baseCechFactor π M U n l) k ≫
        eqToHom (congrArg (baseCechFactor π M U n) h).symm =
      Pi.π (fun l : Fin (n + 1) → ι => baseCechFactor π M U n l) j := by
  subst k
  simp

private theorem baseCechFactor_eqToHom_symm_eq_map
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    {j k : Fin (n + 1) → ι} (h : j = k) :
    eqToHom (congrArg (baseCechFactor π M U n) h).symm =
      (baseModulePresheaf π M).map
        (eqToHom (congrArg (fun l : Fin (n + 1) → ι =>
          ∏ᶜ fun q => U (l q)) h)).op := by
  subst k
  simp

private theorem baseCechDegreeOneCocycle_diagonal
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (x : (baseCechComplex π M U).X 1)
    (hx : ((baseCechComplex π M U).d 1 2).hom x = 0)
    (i : Fin 2 → ι) (hi : ¬ Function.Injective i) :
    (Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) i).hom x = 0 := by
  have h01 : i 0 = i 1 := by
    by_contra hne
    apply hi
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  let c := i 0
  have hi_const : i = fun _ => c := by
    funext k
    fin_cases k
    · rfl
    · exact h01.symm
  let a : Fin 3 → ι := fun _ => c
  let p : (baseCechComplex π M U).X 1 ⟶
      baseCechFactor π M U 1 (fun _ => c) :=
    Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) (fun _ => c)
  let r (k : Fin 3) : baseCechFactor π M U 1 (fun _ => c) ⟶
      baseCechFactor π M U 2 a :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a).op
  have hr (k l : Fin 3) : r k = r l := by
    dsimp only [r]
    apply congrArg (baseModulePresheaf π M).map
    exact congrArg op (Subsingleton.elim _ _)
  have hsum :
      (∑ k : Fin 3, (-1 : ℤ) ^ (k : ℕ) • (r k).hom (p.hom x)) = 0 := by
    have hdx := ConcreteCategory.congr_hom
      (baseCechComplex_d_comp_π π M U 1 a) x
    change
      (Pi.π (fun j : Fin 3 → ι => baseCechFactor π M U 2 j) a).hom
          (((baseCechComplex π M U).d 1 2).hom x) =
        ∑ k : Fin 3, (-1 : ℤ) ^ (k : ℕ) • (r k).hom (p.hom x) at hdx
    have hleft :
        (Pi.π (fun j : Fin 3 → ι => baseCechFactor π M U 2 j) a).hom
            (((baseCechComplex π M U).d 1 2).hom x) = 0 := by
      rw [hx]
      exact map_zero _
    exact hdx.symm.trans hleft
  have hrzero : (r (2 : Fin 3)).hom (p.hom x) = 0 := by
    rw [Fin.sum_univ_three, hr 0 2, hr 1 2] at hsum
    norm_num at hsum
    simpa only [add_neg_cancel, zero_add] using hsum
  let e := mapPowerComponentIsoOfCoverage (X := X) (ι := ι)
    (α := Fin 2) (β := Fin 3) U
    (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun a (by
      intro b
      exact ⟨0, rfl⟩)
  letI : IsIso (r (2 : Fin 3)) := by
    change IsIso ((baseModulePresheaf π M).map e.hom.op)
    infer_instance
  have hpzero : p.hom x = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (r (2 : Fin 3))).1
    rw [map_zero]
    exact hrzero
  rw [hi_const]
  exact hpzero

private theorem baseCechDegreeOneCocycle_swap
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (x : (baseCechComplex π M U).X 1)
    (hx : ((baseCechComplex π M U).d 1 2).hom x = 0)
    (i : Fin 2 → ι) :
    ((baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower
        (Equiv.swap (0 : Fin 2) 1)).φ i).op).hom
        ((Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j)
          (i ∘ Equiv.swap (0 : Fin 2) 1)).hom x) =
      -((Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) i).hom x) := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let a : Fin 3 → ι := ![i 0, i 1, i 0]
  let p (k : Fin 3) : (baseCechComplex π M U).X 1 ⟶
      baseCechFactor π M U 1
        (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) :=
    Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j)
      (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  let r (k : Fin 3) :
      baseCechFactor π M U 1
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) ⟶
        baseCechFactor π M U 2 a :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a).op
  have hface0 :
      a ∘ (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun = i ∘ τ := by
    funext l
    fin_cases l <;> rfl
  have hface1 :
      a ∘ (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFun = fun _ => i 0 := by
    funext l
    fin_cases l <;> rfl
  have hface2 :
      a ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun = i := by
    funext l
    fin_cases l <;> rfl
  have hsum :
      (∑ k : Fin 3, (-1 : ℤ) ^ (k : ℕ) •
        (r k).hom ((p k).hom x)) = 0 := by
    have hdx := ConcreteCategory.congr_hom
      (baseCechComplex_d_comp_π π M U 1 a) x
    change
      (Pi.π (fun j : Fin 3 → ι => baseCechFactor π M U 2 j) a).hom
          (((baseCechComplex π M U).d 1 2).hom x) =
        ∑ k : Fin 3, (-1 : ℤ) ^ (k : ℕ) •
          (r k).hom ((p k).hom x) at hdx
    have hleft :
        (Pi.π (fun j : Fin 3 → ι => baseCechFactor π M U 2 j) a).hom
            (((baseCechComplex π M U).d 1 2).hom x) = 0 := by
      rw [hx]
      exact map_zero _
    exact hdx.symm.trans hleft
  have hmiddle : (p (1 : Fin 3)).hom x = 0 := by
    apply baseCechDegreeOneCocycle_diagonal π M U x hx
    rw [hface1]
    intro hinj
    exact (show (0 : Fin 2) ≠ 1 by decide) (hinj rfl)
  have houter :
      (r (0 : Fin 3)).hom ((p (0 : Fin 3)).hom x) +
        (r (2 : Fin 3)).hom ((p (2 : Fin 3)).hom x) = 0 := by
    rw [Fin.sum_univ_three] at hsum
    norm_num [hmiddle] at hsum
    exact hsum
  let t0 : baseCechFactor π M U 1 (i ∘ τ) ⟶
      baseCechFactor π M U 1
        (a ∘ (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun) :=
    eqToHom (congrArg (baseCechFactor π M U 1) hface0).symm
  let t2 : baseCechFactor π M U 1 i ⟶
      baseCechFactor π M U 1
        (a ∘ (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun) :=
    eqToHom (congrArg (baseCechFactor π M U 1) hface2).symm
  let r0 := t0 ≫ r (0 : Fin 3)
  let r2 := t2 ≫ r (2 : Fin 3)
  let p0 : (baseCechComplex π M U).X 1 ⟶
      baseCechFactor π M U 1 (i ∘ τ) :=
    Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) (i ∘ τ)
  let p2 : (baseCechComplex π M U).X 1 ⟶
      baseCechFactor π M U 1 i :=
    Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) i
  have hp0 : p0 ≫ t0 = p (0 : Fin 3) := by
    dsimp only [p0, t0]
    exact baseCechProjection_comp_eqToHom π M U 1 hface0
  have hp2 : p2 ≫ t2 = p (2 : Fin 3) := by
    dsimp only [p2, t2]
    exact baseCechProjection_comp_eqToHom π M U 1 hface2
  have hterm0 : r0.hom (p0.hom x) =
      (r (0 : Fin 3)).hom ((p (0 : Fin 3)).hom x) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    dsimp only [r0]
    rw [← Category.assoc, hp0]
  have hterm2 : r2.hom (p2.hom x) =
      (r (2 : Fin 3)).hom ((p (2 : Fin 3)).hom x) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    dsimp only [r2]
    rw [← Category.assoc, hp2]
  have houterNamed : r0.hom (p0.hom x) + r2.hom (p2.hom x) = 0 := by
    rw [hterm0, hterm2]
    exact houter
  let perm : baseCechFactor π M U 1 (i ∘ τ) ⟶
      baseCechFactor π M U 1 i :=
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower τ).φ i).op
  have hperm : perm ≫ r2 = r0 := by
    dsimp only [perm, r2, r0, t0, t2, r]
    rw [baseCechFactor_eqToHom_symm_eq_map π M U 1 hface0,
      baseCechFactor_eqToHom_symm_eq_map π M U 1 hface2]
    let F := baseModulePresheaf π M
    let qperm := (((FormalCoproduct.mk _ U).mapPower τ).φ i).op
    let qt2 := (eqToHom (congrArg (fun l : Fin 2 → ι =>
      ∏ᶜ fun q => U (l q)) hface2)).op
    let qd2 := (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun).φ a).op
    let qt0 := (eqToHom (congrArg (fun l : Fin 2 → ι =>
      ∏ᶜ fun q => U (l q)) hface0)).op
    let qd0 := (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFun).φ a).op
    change F.map qperm ≫ F.map qt2 ≫ F.map qd2 =
      F.map qt0 ≫ F.map qd0
    have hleft : F.map qperm ≫ F.map qt2 ≫ F.map qd2 =
        F.map ((qperm ≫ qt2) ≫ qd2) := by
      have h12 : F.map qperm ≫ F.map qt2 = F.map (qperm ≫ qt2) :=
        (F.map_comp qperm qt2).symm
      have h123 : F.map (qperm ≫ qt2) ≫ F.map qd2 =
          F.map ((qperm ≫ qt2) ≫ qd2) :=
        (F.map_comp (qperm ≫ qt2) qd2).symm
      exact (congrArg (· ≫ F.map qd2) h12).trans h123
    have hq' : (qperm ≫ qt2) ≫ qd2 = qt0 ≫ qd0 :=
      Subsingleton.elim _ _
    have hmap : F.map ((qperm ≫ qt2) ≫ qd2) =
        F.map (qt0 ≫ qd0) := by
      rw [hq']
      rfl
    have hright : F.map (qt0 ≫ qd0) = F.map qt0 ≫ F.map qd0 :=
      F.map_comp qt0 qd0
    exact hleft.trans (hmap.trans hright)
  let e := mapPowerComponentIsoOfCoverage (X := X) (ι := ι)
    (α := Fin 2) (β := Fin 3) U
    (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFun a (by
      intro b
      fin_cases b
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩)
  letI : IsIso (r (2 : Fin 3)) := by
    change IsIso ((baseModulePresheaf π M).map e.hom.op)
    infer_instance
  letI : IsIso t2 := by
    dsimp only [t2]
    infer_instance
  letI : IsIso r2 := by
    dsimp only [r2]
    infer_instance
  have hzero : perm.hom (p0.hom x) + p2.hom x = 0 := by
    apply (ConcreteCategory.bijective_of_isIso r2).1
    rw [map_zero, map_add]
    rw [← ConcreteCategory.comp_apply, hperm, ConcreteCategory.comp_apply]
    exact houterNamed
  change perm.hom (p0.hom x) = -p2.hom x
  exact eq_neg_of_add_eq_zero_left hzero

private theorem baseCechDegreeOneCocycle_alternating_component
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (x : (baseCechComplex π M U).X 1)
    (hx : ((baseCechComplex π M U).d 1 2).hom x = 0)
    (i : Fin 2 → ι) :
    (((baseCechToOrderedF π M U 1 ≫
        orderedToBaseCechAlternatingF π M U 1) ≫
      Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) i).hom x) =
      (Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) i).hom x := by
  let A := baseCechToOrderedF π M U 1 ≫
    orderedToBaseCechAlternatingF π M U 1
  let p : (baseCechComplex π M U).X 1 ⟶ baseCechFactor π M U 1 i :=
    Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) i
  change (A ≫ p).hom x = p.hom x
  by_cases hi : Function.Injective i
  · by_cases hmono : StrictMono i
    · have halt := orderedToBaseCechAlternatingF_comp_π_of_strictMono
        π M U 1 i hmono
      have hproj := baseCechToOrderedF_comp_π π M U 1 ⟨i, hmono⟩
      have hA : A ≫ p = p := by
        dsimp only [A]
        calc
          (baseCechToOrderedF π M U 1 ≫
              orderedToBaseCechAlternatingF π M U 1) ≫ p =
              baseCechToOrderedF π M U 1 ≫
                (orderedToBaseCechAlternatingF π M U 1 ≫ p) :=
            Category.assoc _ _ _
          _ = baseCechToOrderedF π M U 1 ≫
              Pi.π (fun j : OrderedCechIndex ι 1 =>
                baseCechFactor π M U 1 j.1) ⟨i, hmono⟩ :=
            congrArg (baseCechToOrderedF π M U 1 ≫ ·) halt
          _ = p := hproj
      exact ConcreteCategory.congr_hom hA x
    · let τ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
      have hnotlt : ¬ i 0 < i 1 := by
        intro hlt
        apply hmono
        rw [Fin.strictMono_iff_lt_succ]
        intro k
        fin_cases k
        exact hlt
      have hne : i 1 ≠ i 0 := by
        intro h
        exact (show (1 : Fin 2) ≠ 0 by decide) (hi h)
      have hlt : i 1 < i 0 :=
        lt_of_le_of_ne (le_of_not_gt hnotlt) hne
      have hτmono : StrictMono (i ∘ τ) := by
        rw [Fin.strictMono_iff_lt_succ]
        intro k
        fin_cases k
        simpa [τ] using hlt
      let s := Tuple.sort i
      have hisorted : i ∘ s = i ∘ τ :=
        Tuple.unique_monotone (Tuple.monotone_sort i) hτmono.monotone
      have hs : s = τ := by
        apply Equiv.ext
        intro k
        apply hi
        exact congrFun hisorted k
      have hsign : (Equiv.Perm.sign s : ℤ) = -1 := by
        rw [hs]
        simp [τ, Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide)]
      have hsmono : StrictMono (i ∘ s) :=
        (Tuple.monotone_sort i).strictMono_of_injective
          (hi.comp s.injective)
      let q : orderedBaseCechObject π M U 1 ⟶
          baseCechFactor π M U 1 (i ∘ s) :=
        Pi.π (fun j : OrderedCechIndex ι 1 =>
          baseCechFactor π M U 1 j.1) ⟨i ∘ s, hsmono⟩
      let ps : (baseCechComplex π M U).X 1 ⟶
          baseCechFactor π M U 1 (i ∘ s) :=
        Pi.π (fun j : Fin 2 → ι => baseCechFactor π M U 1 j) (i ∘ s)
      let r : baseCechFactor π M U 1 (i ∘ s) ⟶
          baseCechFactor π M U 1 i :=
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower s).φ i).op
      have halt := orderedToBaseCechAlternatingF_comp_π_of_injective
        π M U 1 i hi
      change orderedToBaseCechAlternatingF π M U 1 ≫ p =
        (Equiv.Perm.sign s : ℤ) • (q ≫ r) at halt
      have hproj : baseCechToOrderedF π M U 1 ≫ q = ps := by
        dsimp only [q, ps]
        exact baseCechToOrderedF_comp_π π M U 1 ⟨i ∘ s, hsmono⟩
      have hA : A ≫ p = (Equiv.Perm.sign s : ℤ) • (ps ≫ r) := by
        dsimp only [A]
        have h₁ : (baseCechToOrderedF π M U 1 ≫
              orderedToBaseCechAlternatingF π M U 1) ≫ p =
            baseCechToOrderedF π M U 1 ≫
              (orderedToBaseCechAlternatingF π M U 1 ≫ p) :=
          Category.assoc _ _ _
        have h₂ : baseCechToOrderedF π M U 1 ≫
              (orderedToBaseCechAlternatingF π M U 1 ≫ p) =
            baseCechToOrderedF π M U 1 ≫
              ((Equiv.Perm.sign s : ℤ) • (q ≫ r)) :=
          congrArg (baseCechToOrderedF π M U 1 ≫ ·) halt
        have h₃ : baseCechToOrderedF π M U 1 ≫
              ((Equiv.Perm.sign s : ℤ) • (q ≫ r)) =
            (Equiv.Perm.sign s : ℤ) •
              (baseCechToOrderedF π M U 1 ≫ (q ≫ r)) :=
          comp_zsmul _ _ _
        have h₄ : baseCechToOrderedF π M U 1 ≫ (q ≫ r) =
            (baseCechToOrderedF π M U 1 ≫ q) ≫ r :=
          (Category.assoc _ _ _).symm
        have h₅ : (baseCechToOrderedF π M U 1 ≫ q) ≫ r = ps ≫ r :=
          congrArg (· ≫ r) hproj
        exact h₁.trans (h₂.trans (h₃.trans
          (congrArg ((Equiv.Perm.sign s : ℤ) • ·) (h₄.trans h₅))))
      have hswap := baseCechDegreeOneCocycle_swap π M U x hx i
      have hr : r.hom (ps.hom x) = -p.hom x := by
        dsimp only [r, ps, p]
        rw [hs]
        exact hswap
      rw [hA, hsign, neg_one_smul]
      change (- (ps ≫ r)).hom x = p.hom x
      change -r.hom (ps.hom x) = p.hom x
      rw [hr, neg_neg]
  · have hleft := orderedToBaseCechAlternatingF_comp_π_of_not_injective
      π M U 1 i hi
    have hA : A ≫ p = 0 := by
      dsimp only [A]
      calc
        (baseCechToOrderedF π M U 1 ≫
            orderedToBaseCechAlternatingF π M U 1) ≫ p =
            baseCechToOrderedF π M U 1 ≫
              (orderedToBaseCechAlternatingF π M U 1 ≫ p) :=
          Category.assoc _ _ _
        _ = baseCechToOrderedF π M U 1 ≫ 0 :=
          congrArg (baseCechToOrderedF π M U 1 ≫ ·) hleft
        _ = 0 := comp_zero
    have hpzero := baseCechDegreeOneCocycle_diagonal π M U x hx i hi
    rw [hA]
    change 0 = p.hom x
    exact hpzero.symm

/-- Projecting a native degree-one Cech cocycle to increasing pairs and extending it
alternatingly recovers the original cocycle. -/
theorem baseCechDegreeOneCocycle_alternating
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (x : (baseCechComplex π M U).X 1)
    (hx : ((baseCechComplex π M U).d 1 2).hom x = 0) :
    (baseCechToOrderedF π M U 1 ≫
        orderedToBaseCechAlternatingF π M U 1).hom x = x := by
  apply (ConcreteCategory.bijective_of_isIso
    (baseCechXIsoPi π M U 1).hom).1
  funext i
  have hcomponent := baseCechDegreeOneCocycle_alternating_component
    π M U x hx i
  let p : ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ j : Fin 2 → ι, baseCechFactor π M U 1 j) ⟶
      ModuleCat.of Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U 1 i) :=
    ModuleCat.ofHom (LinearMap.proj i)
  have happ : ((((baseCechToOrderedF π M U 1 ≫
      orderedToBaseCechAlternatingF π M U 1) ≫
        (baseCechXIsoPi π M U 1).hom) ≫ p).hom x) =
      (((baseCechXIsoPi π M U 1).hom ≫ p).hom x) := by
    rw [Category.assoc, baseCechXIsoPi_hom_comp_proj]
    exact hcomponent
  exact happ

/-- Degree-one exactness of the bounded ordered Cech complex implies degree-one exactness of the
native all-tuples Cech complex. -/
private theorem baseCechComplex_exactAt_one_of_orderedBaseCechComplex_exactAt_one
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (h : (orderedBaseCechComplex π M U).ExactAt 1) :
    (baseCechComplex π M U).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)] at h ⊢
  rw [ShortComplex.moduleCat_exact_iff] at h ⊢
  change (∀ x₂ : (orderedBaseCechComplex π M U).X 1,
    ((orderedBaseCechComplex π M U).d 1 2).hom x₂ = 0 →
      ∃ x₁ : (orderedBaseCechComplex π M U).X 0,
        ((orderedBaseCechComplex π M U).d 0 1).hom x₁ = x₂) at h
  change ∀ x₂ : (baseCechComplex π M U).X 1,
    ((baseCechComplex π M U).d 1 2).hom x₂ = 0 →
      ∃ x₁ : (baseCechComplex π M U).X 0,
        ((baseCechComplex π M U).d 0 1).hom x₁ = x₂
  intro x hx
  let px := (baseCechToOrderedF π M U 1).hom x
  have hpx : ((orderedBaseCechComplex π M U).d 1 2).hom px = 0 := by
    rw [orderedBaseCechComplex_d]
    change ((baseCechToOrderedF π M U 1 ≫
      orderedBaseCechDifferential π M U 1).hom x) = 0
    rw [← baseCechComplex_d_comp_baseCechToOrderedF π M U 1]
    change (baseCechToOrderedF π M U 2).hom
      (((baseCechComplex π M U).d 1 2).hom x) = 0
    rw [hx, map_zero]
  obtain ⟨y, hy⟩ := h px hpx
  refine ⟨(orderedToBaseCechAlternatingF π M U 0).hom y, ?_⟩
  change ((orderedToBaseCechAlternatingF π M U 0 ≫
    (baseCechComplex π M U).d 0 1).hom y) = x
  rw [orderedToBaseCechAlternatingF_comp_d π M U 0]
  change (orderedToBaseCechAlternatingF π M U 1).hom
    (((orderedBaseCechComplex π M U).d 0 1).hom y) = x
  rw [hy]
  exact baseCechDegreeOneCocycle_alternating π M U x hx

end

end AlgebraicGeometry.Scheme.Modules
