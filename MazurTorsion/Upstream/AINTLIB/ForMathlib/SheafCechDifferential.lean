/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechCochains

/-!
# The Cech differential on local sections

This file computes the coface maps and the alternating differential of mathlib's Cech
complex under `TopologicalSpace.cechCochainAddEquiv`. Each coface restricts the section
indexed by the tuple obtained by deleting one entry.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopologicalSpace

variable {T : Type u} [TopologicalSpace T]
variable (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type u}
variable (U : ι → Opens T) (n : ℕ)

private theorem cechCoface_eq (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj F).δ k =
      Pi.lift (fun i : Fin (n + 2) → ι =>
        Pi.π (fun j : Fin (n + 1) → ι =>
          F.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          F.map (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) := by
  rw [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    FormalCoproduct.cech_map]
  rfl

private theorem cechDifferential_eq :
    ((cechComplexFunctor U).obj F).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj F).δ k := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj F).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ n).trans rfl

private theorem addCommGrp_sum_apply_finset {A B : AddCommGrpCat} {κ : Type*}
    (s : Finset κ) (f : κ → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        AddCommGrpCat.hom_add_apply, ih]

private theorem addCommGrp_sum_apply {A B : AddCommGrpCat} {κ : Type*}
    [Fintype κ] (f : κ → (A ⟶ B)) (x : A) :
    (∑ i, f i) x = ∑ i, f i x :=
  addCommGrp_sum_apply_finset Finset.univ f x

/-- A Cech coface restricts the component indexed by the tuple with its `k`th entry
deleted to the full tuple intersection. -/
theorem cechCoface_apply (x : ((cechComplexFunctor U).obj F).X n)
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    cechCochainAddEquiv F U (n + 1)
        (((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj F).δ k x) i =
      F.map (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
        (cechCochainAddEquiv F U n x
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  have hout := cechCochainAddEquiv_apply F U (n + 1)
    (((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj F).δ k x) i
  have hin := cechCochainAddEquiv_apply F U n x
    (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  rw [hout, hin, cechCoface_eq]
  exact ConcreteCategory.congr_hom
    (Pi.lift_π (fun i : Fin (n + 2) → ι =>
      Pi.π (fun j : Fin (n + 1) → ι =>
        F.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        F.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) i) x

/-- Under the concrete cochain equivalence, the Cech differential is the alternating
sum of restrictions along all tuple deletions. -/
theorem cechDifferential_apply (x : ((cechComplexFunctor U).obj F).X n)
    (i : Fin (n + 2) → ι) :
    cechCochainAddEquiv F U (n + 1)
        (((cechComplexFunctor U).obj F).d n (n + 1) x) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (cechCochainAddEquiv F U n x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [cechDifferential_eq]
  have hmapSum :
      cechCochainAddEquiv F U (n + 1)
          (∑ k : Fin (n + 2),
            (((-1 : ℤ) ^ (k : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k) x)) =
        ∑ k : Fin (n + 2), cechCochainAddEquiv F U (n + 1)
          (((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x) := by
    exact map_sum (cechCochainAddEquiv F U (n + 1)) _ Finset.univ
  calc
    _ = cechCochainAddEquiv F U (n + 1)
        (∑ k : Fin (n + 2),
          ((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x) i :=
      congrArg (fun y => cechCochainAddEquiv F U (n + 1) y i)
        (addCommGrp_sum_apply _ x)
    _ = (∑ k : Fin (n + 2),
        cechCochainAddEquiv F U (n + 1)
          (((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x)) i := by
      exact congrFun hmapSum i
    _ = ∑ k : Fin (n + 2),
        cechCochainAddEquiv F U (n + 1)
          (((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x) i :=
      Finset.sum_apply i Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        cechCochainAddEquiv F U (n + 1)
            (((-1 : ℤ) ^ (k : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k) x) i =
          cechCochainAddEquiv F U (n + 1)
            ((-1 : ℤ) ^ (k : ℕ) •
              (((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k x)) i :=
            congrArg (fun y => cechCochainAddEquiv F U (n + 1) y i)
              (show
                ((-1 : ℤ) ^ (k : ℕ) •
                  ((FormalCoproduct.cosimplicialObjectFunctor
                    (FormalCoproduct.mk _ U).cech).obj F).δ k) x =
                  (-1 : ℤ) ^ (k : ℕ) •
                    (((FormalCoproduct.cosimplicialObjectFunctor
                      (FormalCoproduct.mk _ U).cech).obj F).δ k x) from rfl)
        _ = (-1 : ℤ) ^ (k : ℕ) •
            cechCochainAddEquiv F U (n + 1)
              (((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k x) i :=
          congrFun (map_zsmul (cechCochainAddEquiv F U (n + 1))
            ((-1 : ℤ) ^ (k : ℕ))
            (((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k x)) i
        _ = _ := congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
          (cechCoface_apply F U n x k i)

end TopologicalSpace
