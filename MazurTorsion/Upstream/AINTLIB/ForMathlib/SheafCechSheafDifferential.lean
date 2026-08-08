/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechDifferential
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafTerms

/-!
# The differential in the sheaf-level Cech resolution

This file defines restriction between the intersection factors in a sheaf-level Cech term,
the cofaces induced by deleting tuple entries, and their alternating sum. The component
formulas identify these maps with the same restrictions that occur in the ordinary Cech
complex of sections.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)

private theorem cechTermFactorRestrictionLE {A B : Opens X} (h : A ≤ B)
    (V : Opens X) :
    A.isOpenEmbedding.functor.obj ((Opens.map A.inclusion').obj V) ≤
      B.isOpenEmbedding.functor.obj ((Opens.map B.inclusion').obj V) := by
  simpa only [Opens.functor_map_eq_inf] using inf_le_inf_left V h

/-- Restriction from the restriction-pushforward factor for `B` to the factor for a
smaller open `A`. -/
noncomputable def cechTermFactorRestriction {A B : Opens X} (h : A ≤ B) :
    (restrict AddCommGrpCat B.isOpenEmbedding ⋙
        pushforward AddCommGrpCat B.inclusion').obj F ⟶
      (restrict AddCommGrpCat A.isOpenEmbedding ⋙
        pushforward AddCommGrpCat A.inclusion').obj F :=
  ObjectProperty.homMk
    { app := fun V =>
        F.obj.map (homOfLE (cechTermFactorRestrictionLE h V.unop)).op
      naturality := by
        intro V W f
        change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        rfl }

private noncomputable def cechTermFactorSectionsIso (A V : Opens X) :
    ((restrict AddCommGrpCat A.isOpenEmbedding ⋙
        pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
      F.obj.obj (op (V ⊓ A)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf A V)))

private theorem cechTermFactorSectionsIso_hom (A V : Opens X) :
    (cechTermFactorSectionsIso F A V).hom =
      ((eqToIso (by rw [toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
        ((restrict AddCommGrpCat A.isOpenEmbedding ⋙
          pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
            F.obj.obj (op (V ⊓ A))).hom := by
  rw [cechTermFactorSectionsIso, Functor.mapIso_hom, eqToIso.hom, eqToIso.hom,
    eqToHom_map]
  cat_disch

private theorem cechTermFactorRestriction_sections_mapIso {A B : Opens X}
    (h : A ≤ B) (V : Opens X)
    (x : ((restrict AddCommGrpCat B.isOpenEmbedding ⋙
      pushforward AddCommGrpCat B.inclusion').obj F).obj.obj (op V)) :
    (cechTermFactorSectionsIso F A V).hom
        ((cechTermFactorRestriction F h).hom.app (op V) x) =
      F.obj.map (homOfLE (inf_le_inf_left V h)).op
        ((cechTermFactorSectionsIso F B V).hom x) := by
  have hmorph :
      F.obj.map (homOfLE (cechTermFactorRestrictionLE h V)).op ≫
          F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf A V))) =
        F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf B V))) ≫
          F.obj.map (homOfLE (inf_le_inf_left V h)).op := by
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  change (F.obj.map (homOfLE (cechTermFactorRestrictionLE h V)).op ≫
      F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf A V)))) x =
    (F.obj.map (eqToHom (congrArg op (Opens.functor_map_eq_inf B V))) ≫
      F.obj.map (homOfLE (inf_le_inf_left V h)).op) x
  exact ConcreteCategory.congr_hom hmorph x

/-- On sections over `V`, `cechTermFactorRestriction` is the usual restriction
`F(V ∩ B) → F(V ∩ A)`. -/
theorem cechTermFactorRestriction_apply {A B : Opens X} (h : A ≤ B) (V : Opens X)
    (x : ((restrict AddCommGrpCat B.isOpenEmbedding ⋙
      pushforward AddCommGrpCat B.inclusion').obj F).obj.obj (op V)) :
    ((eqToIso (by rw [toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
      ((restrict AddCommGrpCat A.isOpenEmbedding ⋙
        pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
          F.obj.obj (op (V ⊓ A))).hom
        ((cechTermFactorRestriction F h).hom.app (op V) x) =
      F.obj.map (homOfLE (inf_le_inf_left V h)).op
        (((eqToIso (by rw [toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
          ((restrict AddCommGrpCat B.isOpenEmbedding ⋙
            pushforward AddCommGrpCat B.inclusion').obj F).obj.obj (op V) ≅
              F.obj.obj (op (V ⊓ B))).hom x) := by
  rw [← cechTermFactorSectionsIso_hom, ← cechTermFactorSectionsIso_hom]
  exact cechTermFactorRestriction_sections_mapIso F h V x

variable {ι : Type u} (U : ι → Opens X) (n : ℕ)

private theorem cechTupleLE (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (n + 1) =>
        U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i)

/-- The sheaf-level Cech coface obtained by deleting the `k`th entry of every tuple. -/
noncomputable def cechCoface (k : Fin (n + 2)) :
    cechTerm F U n ⟶ cechTerm F U (n + 1) :=
  Pi.lift (fun i : Fin (n + 2) → ι =>
    Pi.π (cechTermFactor F U n)
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      cechTermFactorRestriction F (cechTupleLE U n k i))

/-- Under the concrete section equivalence, a sheaf-level Cech coface restricts the
component indexed by the tuple with its `k`th entry deleted. -/
theorem cechCoface_apply (V : Opens X) (x : (cechTerm F U n).obj.obj (op V))
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    cechTermSectionsAddEquiv F U (n + 1) V
        ((cechCoface F U n k).hom.app (op V) x) i =
      F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
        (cechTermSectionsAddEquiv F U n V x
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [cechTermSectionsAddEquiv_apply]
  have hcoface :
      cechCoface F U n k ≫ Pi.π (cechTermFactor F U (n + 1)) i =
        Pi.π (cechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          cechTermFactorRestriction F (cechTupleLE U n k i) := by
    change
      Pi.lift (fun i : Fin (n + 2) → ι =>
          Pi.π (cechTermFactor F U n)
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
            cechTermFactorRestriction F (cechTupleLE U n k i)) ≫
          Pi.π (cechTermFactor F U (n + 1)) i =
        Pi.π (cechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          cechTermFactorRestriction F (cechTupleLE U n k i)
    exact Pi.lift_π _ i
  have hcomponent :
      (Pi.π (cechTermFactor F U (n + 1)) i).hom.app (op V)
          ((cechCoface F U n k).hom.app (op V) x) =
        (cechTermFactorRestriction F (cechTupleLE U n k i)).hom.app (op V)
          ((Pi.π (cechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app (op V) x) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op V)) hcoface) x
  rw [hcomponent, cechTermFactorRestriction_apply,
    ← cechTermSectionsAddEquiv_apply]
  exact ConcreteCategory.congr_hom
    (congrArg F.obj.map (Subsingleton.elim _ _))
    (cechTermSectionsAddEquiv F U n V x
      (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))

/-- The differential in the sheaf-level Cech resolution. -/
noncomputable def cechDifferential :
    cechTerm F U n ⟶ cechTerm F U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • cechCoface F U n k

private theorem sheaf_sum_apply_finset {A B : Sheaf AddCommGrpCat.{u} X}
    {κ : Type*} (s : Finset κ) (f : κ → (A ⟶ B)) (V : (Opens X)ᵒᵖ)
    (x : A.obj.obj V) :
    (∑ i ∈ s, f i).hom.app V x = ∑ i ∈ s, (f i).hom.app V x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (f a).hom.app V x + (∑ i ∈ s, f i).hom.app V x = _
      rw [ih]

private theorem sheaf_sum_apply {A B : Sheaf AddCommGrpCat.{u} X}
    {κ : Type*} [Fintype κ] (f : κ → (A ⟶ B)) (V : (Opens X)ᵒᵖ)
    (x : A.obj.obj V) :
    (∑ i, f i).hom.app V x = ∑ i, (f i).hom.app V x :=
  sheaf_sum_apply_finset Finset.univ f V x

/-- Under the concrete section equivalence, the sheaf-level Cech differential is the
alternating sum of tuple-deletion restrictions. -/
theorem cechDifferential_apply (V : Opens X)
    (x : (cechTerm F U n).obj.obj (op V)) (i : Fin (n + 2) → ι) :
    cechTermSectionsAddEquiv F U (n + 1) V
        ((cechDifferential F U n).hom.app (op V) x) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
          (cechTermSectionsAddEquiv F U n V x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [cechDifferential]
  calc
    _ = cechTermSectionsAddEquiv F U (n + 1) V
        (∑ k : Fin (n + 2),
          ((-1 : ℤ) ^ (k : ℕ) • cechCoface F U n k).hom.app (op V) x) i :=
      congrArg (fun y => cechTermSectionsAddEquiv F U (n + 1) V y i)
        (sheaf_sum_apply _ (op V) x)
    _ = (∑ k : Fin (n + 2),
        cechTermSectionsAddEquiv F U (n + 1) V
          (((-1 : ℤ) ^ (k : ℕ) • cechCoface F U n k).hom.app (op V) x)) i := by
      rw [map_sum]
    _ = ∑ k : Fin (n + 2),
        cechTermSectionsAddEquiv F U (n + 1) V
          (((-1 : ℤ) ^ (k : ℕ) • cechCoface F U n k).hom.app (op V) x) i :=
      Finset.sum_apply i Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      change cechTermSectionsAddEquiv F U (n + 1) V
          ((-1 : ℤ) ^ (k : ℕ) • ((cechCoface F U n k).hom.app (op V) x)) i = _
      rw [map_zsmul, Pi.smul_apply, cechCoface_apply]
      exact congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
        (ConcreteCategory.congr_hom
          (congrArg F.obj.map (Subsingleton.elim _ _))
          (cechTermSectionsAddEquiv F U n V x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)))

end TopCat.Sheaf
