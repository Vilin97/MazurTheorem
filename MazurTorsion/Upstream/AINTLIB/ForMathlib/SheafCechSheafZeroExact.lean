/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafAugmentation

/-!
# Degree-zero exactness of the sheaf-level Cech complex

This file proves that the augmentation into the sheaf-level Cech complex is exact at
degree zero when the chosen opens cover the whole space. The proof first contracts cycles
over any open contained in one cover member, then applies this local result to stalk
representatives.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private def cechConstIndex (i₀ : ι) : Fin 1 → ι := fun _ => i₀

private def cechPairIndex (i₀ : ι) (i : Fin 1 → ι) : Fin 2 → ι := Fin.cases i₀ i

private theorem cechSingletonIntersection_eq (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 => U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun k : Fin 1 => U (i k)) 0)
  · exact leOfHom (Pi.lift fun k : Fin 1 => homOfLE (by
      rw [Subsingleton.elim k 0]))

private theorem cechConstIntersection_eq {V : Opens X} (i₀ : ι) (hV : V ≤ U i₀) :
    V ⊓ (∏ᶜ fun k : Fin 1 => U (cechConstIndex i₀ k)) = V := by
  rw [cechSingletonIntersection_eq U (cechConstIndex i₀), inf_eq_left]
  exact hV

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

private theorem cechPairDeleteZero (i₀ : ι) (i : Fin 1 → ι) :
    cechPairIndex i₀ i ∘
        (SimplexCategory.δ (0 : Fin 2)).toOrderHom = i := by
  funext k
  fin_cases k
  rfl

private theorem cechPairDeleteOne (i₀ : ι) (i : Fin 1 → ι) :
    cechPairIndex i₀ i ∘
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom = cechConstIndex i₀ := by
  funext k
  fin_cases k
  rfl

private theorem cechPairLEZero (i₀ : ι) (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 2 => U (cechPairIndex i₀ i k)) ≤
      ∏ᶜ fun k : Fin 1 => U (i k) := by
  rw [← congrArg (fun q : Fin 1 → ι =>
    ∏ᶜ fun k : Fin 1 => U (q k)) (cechPairDeleteZero i₀ i)]
  exact leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ (cechPairIndex i₀ i))

private theorem cechPairLEOne (i₀ : ι) (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 2 => U (cechPairIndex i₀ i k)) ≤
      ∏ᶜ fun k : Fin 1 => U (cechConstIndex i₀ k) := by
  rw [← congrArg (fun q : Fin 1 → ι =>
    ∏ᶜ fun k : Fin 1 => U (q k)) (cechPairDeleteOne i₀ i)]
  exact leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ (cechPairIndex i₀ i))

private theorem cechZeroCycle_pair_restrictions_eq {V : Opens X} (i₀ : ι)
    (s : (cechTerm F U 0).obj.obj (op V))
    (hs : (cechDifferential F U 0).hom.app (op V) s = 0)
    (i : Fin 1 → ι) :
    F.obj.map (homOfLE (inf_le_inf_left V (cechPairLEZero U i₀ i))).op
        (cechTermSectionsAddEquiv F U 0 V s i) =
      F.obj.map (homOfLE (inf_le_inf_left V (cechPairLEOne U i₀ i))).op
        (cechTermSectionsAddEquiv F U 0 V s (cechConstIndex i₀)) := by
  let iZero := cechPairIndex i₀ i ∘
    (SimplexCategory.δ (0 : Fin 2)).toOrderHom
  let iOne := cechPairIndex i₀ i ∘
    (SimplexCategory.δ (1 : Fin 2)).toOrderHom
  have hd := congrArg (fun y => cechTermSectionsAddEquiv F U 1 V y
    (cechPairIndex i₀ i)) hs
  rw [cechDifferential_apply] at hd
  simp only [Nat.reduceAdd, Int.reduceNeg, OrderHom.toFun_eq_coe,
    homOfLE_leOfHom, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, pow_zero, one_smul, Nat.mod_succ, pow_one, neg_smul,
    map_zero, Pi.zero_apply] at hd
  have htermZero :
      F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ
              (cechPairIndex i₀ i))))).op
          (cechTermSectionsAddEquiv F U 0 V s iZero) =
        F.obj.map (homOfLE (inf_le_inf_left V (cechPairLEZero U i₀ i))).op
          (cechTermSectionsAddEquiv F U 0 V s i) := by
    rw [← cechTermSectionsAddEquiv_transport F U 0 V s (cechPairDeleteZero i₀ i)]
    change F.obj.map _ _ = (F.obj.map _ ≫ F.obj.map _) _
    exact ConcreteCategory.congr_hom
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        (F.obj.map_comp _ _)) _
  have htermOne :
      F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ
              (cechPairIndex i₀ i))))).op
          (cechTermSectionsAddEquiv F U 0 V s iOne) =
        F.obj.map (homOfLE (inf_le_inf_left V (cechPairLEOne U i₀ i))).op
          (cechTermSectionsAddEquiv F U 0 V s (cechConstIndex i₀)) := by
    rw [← cechTermSectionsAddEquiv_transport F U 0 V s (cechPairDeleteOne i₀ i)]
    change F.obj.map _ _ = (F.obj.map _ ≫ F.obj.map _) _
    exact ConcreteCategory.congr_hom
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        (F.obj.map_comp _ _)) _
  let a := F.obj.map
    (homOfLE (inf_le_inf_left V (cechPairLEZero U i₀ i))).op
      (cechTermSectionsAddEquiv F U 0 V s i)
  let b := F.obj.map
    (homOfLE (inf_le_inf_left V (cechPairLEOne U i₀ i))).op
      (cechTermSectionsAddEquiv F U 0 V s (cechConstIndex i₀))
  rw [htermZero, htermOne] at hd
  change a + -b = 0 at hd
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg] using hd

private theorem cechZeroCycle_component_eq {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (s : (cechTerm F U 0).obj.obj (op V))
    (hs : (cechDifferential F U 0).hom.app (op V) s = 0)
    (i : Fin 1 → ι) :
    F.obj.map (homOfLE (inf_le_left :
        (V ⊓ (∏ᶜ fun k : Fin 1 => U (i k))) ≤ V)).op
        (F.obj.map (eqToHom (congrArg op (cechConstIntersection_eq U i₀ hV)))
          (cechTermSectionsAddEquiv F U 0 V s (cechConstIndex i₀))) =
      cechTermSectionsAddEquiv F U 0 V s i := by
  let j := cechPairIndex i₀ i
  have hToPair :
      V ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤
        ∏ᶜ fun k : Fin 2 => U (j k) := by
    exact leOfHom (Pi.lift fun k : Fin 2 => homOfLE (by
      fin_cases k
      · exact inf_le_left.trans hV
      · exact inf_le_right.trans
          (leOfHom (Pi.π (fun k : Fin 1 => U (i k)) 0))))
  have hBack :
      V ⊓ (∏ᶜ fun k : Fin 1 => U (i k)) ≤
        V ⊓ (∏ᶜ fun k : Fin 2 => U (j k)) :=
    le_inf inf_le_left hToPair
  calc
    _ = F.obj.map (homOfLE hBack).op
          (F.obj.map (homOfLE (inf_le_inf_left V (cechPairLEOne U i₀ i))).op
            (cechTermSectionsAddEquiv F U 0 V s (cechConstIndex i₀))) := by
      change (F.obj.map _ ≫ F.obj.map _) _ =
        (F.obj.map _ ≫ F.obj.map _) _
      exact ConcreteCategory.congr_hom
        ((F.obj.map_comp _ _).symm.trans
          ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
            (F.obj.map_comp _ _))) _
    _ = F.obj.map (homOfLE hBack).op
        (F.obj.map (homOfLE (inf_le_inf_left V (cechPairLEZero U i₀ i))).op
          (cechTermSectionsAddEquiv F U 0 V s i)) :=
      congrArg (fun y => F.obj.map (homOfLE hBack).op y)
        (cechZeroCycle_pair_restrictions_eq F U i₀ s hs i).symm
    _ = _ := by
      change (F.obj.map _ ≫ F.obj.map _) _ = _
      exact ConcreteCategory.congr_hom
        ((F.obj.map_comp _ _).symm.trans
          ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
            (F.obj.map_id _))) _

/-- A degree-zero Cech cycle on an open contained in one cover member is the
augmentation of a section on that open. -/
private theorem exists_preimage_cechAugmentation_of_le {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (s : (cechTerm F U 0).obj.obj (op V))
    (hs : (cechDifferential F U 0).hom.app (op V) s = 0) :
    ∃ t : F.obj.obj (op V),
      (cechAugmentation F U).hom.app (op V) t = s := by
  let t := F.obj.map (eqToHom (congrArg op (cechConstIntersection_eq U i₀ hV)))
    (cechTermSectionsAddEquiv F U 0 V s (cechConstIndex i₀))
  refine ⟨t, (cechTermSectionsAddEquiv F U 0 V).injective ?_⟩
  funext i
  rw [cechAugmentation_apply]
  exact cechZeroCycle_component_eq F U i₀ hV s hs i

private theorem exists_cechZeroCycle_restriction (hU : ⨆ i, U i = ⊤) (x : X)
    {V : Opens X} (hxV : x ∈ V) (s : (cechTerm F U 0).obj.obj (op V))
    (hy : (cechTerm F U 1).presheaf.germ V x hxV
      ((cechDifferential F U 0).hom.app (op V) s) = 0) :
    ∃ (i₀ : ι) (W : Opens X) (hxW : x ∈ W), W ≤ U i₀ ∧ W ≤ V ∧
      ∃ sW : (cechTerm F U 0).obj.obj (op W),
        (cechDifferential F U 0).hom.app (op W) sW = 0 ∧
          (cechTerm F U 0).presheaf.germ W x hxW sW =
            (cechTerm F U 0).presheaf.germ V x hxV s := by
  have hzeroGerm :
      (cechTerm F U 1).presheaf.germ V x hxV
          (0 : (cechTerm F U 1).obj.obj (op V)) = 0 :=
    map_zero _
  obtain ⟨W, hxW, iWV, _, hEq⟩ :=
    (cechTerm F U 1).presheaf.germ_eq x hxV hxV
      ((cechDifferential F U 0).hom.app (op V) s) 0
      (hy.trans hzeroGerm.symm)
  have hEqZero :
      (cechTerm F U 1).obj.map iWV.op
          ((cechDifferential F U 0).hom.app (op V) s) = 0 := by
    rw [hEq, map_zero]
  have hxCover : x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  rw [Opens.mem_iSup] at hxCover
  obtain ⟨i₀, hxi₀⟩ := hxCover
  let W' : Opens X := W ⊓ U i₀
  have hxW' : x ∈ W' := ⟨hxW, hxi₀⟩
  have hW'W : W' ≤ W := inf_le_left
  have hW'V : W' ≤ V := hW'W.trans iWV.le
  let s' : (cechTerm F U 0).obj.obj (op W') :=
    (cechTerm F U 0).obj.map (homOfLE hW'V).op s
  have hDiffRestrict :
      (cechTerm F U 1).obj.map (homOfLE hW'V).op
          ((cechDifferential F U 0).hom.app (op V) s) = 0 := by
    calc
      _ = (cechTerm F U 1).obj.map (homOfLE hW'W).op
          ((cechTerm F U 1).obj.map iWV.op
            ((cechDifferential F U 0).hom.app (op V) s)) := by
        change (cechTerm F U 1).obj.map _ _ =
          ((cechTerm F U 1).obj.map _ ≫
            (cechTerm F U 1).obj.map _) _
        exact ConcreteCategory.congr_hom
          ((congrArg (cechTerm F U 1).obj.map (Subsingleton.elim _ _)).trans
            ((cechTerm F U 1).obj.map_comp _ _)) _
      _ = 0 := by rw [hEqZero, map_zero]
  have hs' : (cechDifferential F U 0).hom.app (op W') s' = 0 := by
    calc
      _ = (cechTerm F U 1).obj.map (homOfLE hW'V).op
          ((cechDifferential F U 0).hom.app (op V) s) := by
        exact ConcreteCategory.congr_hom
          ((cechDifferential F U 0).hom.naturality (homOfLE hW'V).op) s
      _ = 0 := hDiffRestrict
  exact ⟨i₀, W', hxW', inf_le_right, hW'V, s', hs',
    (cechTerm F U 0).presheaf.germ_res_apply (homOfLE hW'V) x hxW' s⟩

private theorem exists_stalk_preimage_cechAugmentation (hU : ⨆ i, U i = ⊤)
    (x : X) (y : (cechTerm F U 0).presheaf.stalk x)
    (hy : (Presheaf.stalkFunctor AddCommGrpCat x).map
      (cechDifferential F U 0).hom y = 0) :
    ∃ t : F.presheaf.stalk x,
      (Presheaf.stalkFunctor AddCommGrpCat x).map
        (cechAugmentation F U).hom t = y := by
  obtain ⟨V, hxV, s, rfl⟩ :=
    (cechTerm F U 0).presheaf.exists_germ_eq y
  rw [Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨i₀, W, hxW, hWi₀, _, sW, hsW, hGerm⟩ :=
    exists_cechZeroCycle_restriction F U hU x hxV s hy
  obtain ⟨t, ht⟩ := exists_preimage_cechAugmentation_of_le F U i₀ hWi₀ sW hsW
  refine ⟨F.presheaf.germ W x hxW t, ?_⟩
  change (Presheaf.stalkFunctor AddCommGrpCat x).map
      (cechAugmentation F U).hom (F.presheaf.germ W x hxW t) =
    (cechTerm F U 0).presheaf.germ V x hxV s
  rw [Presheaf.stalkFunctor_map_germ_apply, ht]
  exact hGerm

/-- If the opens `U i` cover the whole space, the augmented sheaf-level Cech complex is
exact at degree zero. -/
theorem cechAugmentedShortComplex_exact (hU : ⨆ i, U i = ⊤) :
    (cechAugmentedShortComplex F U).Exact := by
  rw [exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  exact exists_stalk_preimage_cechAugmentation F U hU x

end TopCat.Sheaf
