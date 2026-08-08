/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafComplex

/-!
# Local contraction of the sheaf-level Cech complex

This file contracts every positive-degree Cech cycle over an open contained in one member
of the cover. The contraction prepends the distinguished cover index to each tuple. The
cycle equation on that larger tuple then identifies the preceding differential with the
original cycle.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X)
variable (F : Sheaf AddCommGrpCat.{u} X)

private def cechPrependIndex {n : ℕ} (i₀ : ι) (i : Fin (n + 1) → ι) :
    Fin (n + 2) → ι :=
  Fin.cases i₀ i

private theorem cechPrependDeleteZero {n : ℕ} (i₀ : ι) (i : Fin (n + 1) → ι) :
    cechPrependIndex i₀ i ∘
        (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom = i := by
  funext k
  rfl

private theorem cechPrependDeleteSucc {n : ℕ} (i₀ : ι) (i : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    cechPrependIndex i₀ i ∘
        (SimplexCategory.δ k.succ).toOrderHom =
      cechPrependIndex i₀
        (i ∘ (SimplexCategory.δ k).toOrderHom) := by
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · simp [cechPrependIndex, SimplexCategory.δ, Function.comp_apply]

private theorem cechPrependIntersection_eq {n : ℕ} {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (i : Fin (n + 1) → ι) :
    V ⊓ (∏ᶜ fun k : Fin (n + 2) => U (cechPrependIndex i₀ i k)) =
      V ⊓ (∏ᶜ fun k : Fin (n + 1) => U (i k)) := by
  apply le_antisymm
  · refine le_inf inf_le_left (leOfHom (Pi.lift fun k => ?_))
    exact homOfLE (inf_le_right.trans
      (leOfHom (Pi.π (fun k : Fin (n + 2) => U (cechPrependIndex i₀ i k)) k.succ)))
  · refine le_inf inf_le_left (leOfHom (Pi.lift fun k => ?_))
    refine Fin.cases ?_ (fun j => ?_) k
    · exact homOfLE (inf_le_left.trans hV)
    · exact homOfLE (inf_le_right.trans
        (leOfHom (Pi.π (fun j : Fin (n + 1) => U (i j)) j)))

private noncomputable def cechLocalContraction {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ) (s : (cechTerm F U (n + 1)).obj.obj (op V)) :
    (cechTerm F U n).obj.obj (op V) :=
  (cechTermSectionsAddEquiv F U n V).symm fun i =>
    F.obj.map (eqToHom (congrArg op (cechPrependIntersection_eq U i₀ hV i)))
      (cechTermSectionsAddEquiv F U (n + 1) V s (cechPrependIndex i₀ i))

private theorem cechLocalContraction_apply {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ) (s : (cechTerm F U (n + 1)).obj.obj (op V))
    (i : Fin (n + 1) → ι) :
    cechTermSectionsAddEquiv F U n V (cechLocalContraction U F i₀ hV n s) i =
      F.obj.map (eqToHom (congrArg op (cechPrependIntersection_eq U i₀ hV i)))
        (cechTermSectionsAddEquiv F U (n + 1) V s (cechPrependIndex i₀ i)) := by
  rw [cechLocalContraction, AddEquiv.apply_symm_apply]

private theorem cechTermSectionsAddEquiv_transport (n : ℕ) (V : Opens X)
    (s : (cechTerm F U n).obj.obj (op V))
    {i j : Fin (n + 1) → ι} (h : i = j) :
    F.obj.map (eqToHom (congrArg
        (fun q : Fin (n + 1) → ι =>
          op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (q k))) h))
        (cechTermSectionsAddEquiv F U n V s i) =
      cechTermSectionsAddEquiv F U n V s j := by
  subst h
  simp

private noncomputable def cechFaceSection (n : ℕ) (V : Opens X)
    (s : (cechTerm F U n).obj.obj (op V)) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) :
    F.obj.obj (op (V ⊓ ∏ᶜ fun a : Fin (n + 2) => U (i a))) :=
  F.obj.map (homOfLE (inf_le_inf_left V
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
    (cechTermSectionsAddEquiv F U n V s
      (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))

private theorem cechFaceSection_zero_transport {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (cechTerm F U (n + 1)).obj.obj (op V)) (i : Fin (n + 2) → ι) :
    F.obj.map (eqToHom (congrArg op
        (cechPrependIntersection_eq U i₀ hV i)))
        (cechFaceSection U F (n + 1) V s 0 (cechPrependIndex i₀ i)) =
      cechTermSectionsAddEquiv F U (n + 1) V s i := by
  rw [cechFaceSection]
  rw [← cechTermSectionsAddEquiv_transport U F (n + 1) V s
    (cechPrependDeleteZero i₀ i)]
  change (F.obj.map _ ≫ F.obj.map _) _ = F.obj.map _ _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      (congrArg F.obj.map (Subsingleton.elim _ _))) _

private theorem cechFaceSection_succ_transport {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (cechTerm F U (n + 1)).obj.obj (op V)) (i : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    F.obj.map (eqToHom (congrArg op
        (cechPrependIntersection_eq U i₀ hV i)))
        (cechFaceSection U F (n + 1) V s k.succ (cechPrependIndex i₀ i)) =
      cechFaceSection U F n V (cechLocalContraction U F i₀ hV n s) k i := by
  rw [cechFaceSection, cechFaceSection, cechLocalContraction_apply]
  erw [← cechTermSectionsAddEquiv_transport U F (n + 1) V s
    (cechPrependDeleteSucc i₀ i k)]
  change (F.obj.map _ ≫ F.obj.map _) _ =
    (F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _) _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        ((F.obj.map_comp _ _).trans
          (congrArg (fun f ↦ F.obj.map _ ≫ f) (F.obj.map_comp _ _))))) _

private theorem cechLocalContraction_differential_component {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (cechTerm F U (n + 1)).obj.obj (op V))
    (hs : (cechDifferential F U (n + 1)).hom.app (op V) s = 0)
    (i : Fin (n + 2) → ι) :
    cechTermSectionsAddEquiv F U (n + 1) V
        ((cechDifferential F U n).hom.app (op V)
          (cechLocalContraction U F i₀ hV n s)) i =
      cechTermSectionsAddEquiv F U (n + 1) V s i := by
  rw [cechDifferential_apply]
  change (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    cechFaceSection U F n V (cechLocalContraction U F i₀ hV n s) k i) = _
  have hd := congrArg (fun y =>
    cechTermSectionsAddEquiv F U (n + 2) V y (cechPrependIndex i₀ i)) hs
  rw [cechDifferential_apply] at hd
  simp only [map_zero, Pi.zero_apply] at hd
  change (∑ k : Fin (n + 3), (-1 : ℤ) ^ (k : ℕ) •
    cechFaceSection U F (n + 1) V s k (cechPrependIndex i₀ i)) = 0 at hd
  have hd' := congrArg (fun y => F.obj.map (eqToHom (congrArg op
    (cechPrependIntersection_eq U i₀ hV i))) y) hd
  simp only [map_zero] at hd'
  rw [map_sum, Fin.sum_univ_succ] at hd'
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
    mul_neg, mul_one, neg_smul, map_neg, map_zsmul,
    cechFaceSection_zero_transport U F i₀ hV n s i,
    cechFaceSection_succ_transport U F i₀ hV n s i] at hd'
  rw [Finset.sum_neg_distrib] at hd'
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hd')).symm

/-- A positive-degree Cech cycle on an open contained in one cover member has a
preimage under the preceding Cech differential. -/
theorem exists_preimage_cechDifferential_of_le {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (cechTerm F U (n + 1)).obj.obj (op V))
    (hs : (cechDifferential F U (n + 1)).hom.app (op V) s = 0) :
    ∃ t : (cechTerm F U n).obj.obj (op V),
      (cechDifferential F U n).hom.app (op V) t = s := by
  refine ⟨cechLocalContraction U F i₀ hV n s,
    (cechTermSectionsAddEquiv F U (n + 1) V).injective ?_⟩
  funext i
  exact cechLocalContraction_differential_component U F i₀ hV n s hs i

end TopCat.Sheaf
