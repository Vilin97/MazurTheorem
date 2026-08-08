/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafLocalContraction
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafZeroExact

/-!
# Positive-degree exactness of the sheaf-level Cech complex

This file applies the local Cech contraction to stalk representatives. When the chosen
opens cover the whole space, every positive-degree stalk cycle can be represented by a
cycle on a neighborhood contained in one cover member, where the local contraction gives
a preimage.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private theorem exists_cechCycle_restriction (hU : ⨆ i, U i = ⊤) (n : ℕ) (x : X)
    {V : Opens X} (hxV : x ∈ V)
    (s : (cechTerm F U (n + 1)).obj.obj (op V))
    (hy : (cechTerm F U (n + 2)).presheaf.germ V x hxV
      ((cechDifferential F U (n + 1)).hom.app (op V) s) = 0) :
    ∃ (i₀ : ι) (W : Opens X) (hxW : x ∈ W), W ≤ U i₀ ∧ W ≤ V ∧
      ∃ sW : (cechTerm F U (n + 1)).obj.obj (op W),
        (cechDifferential F U (n + 1)).hom.app (op W) sW = 0 ∧
          (cechTerm F U (n + 1)).presheaf.germ W x hxW sW =
            (cechTerm F U (n + 1)).presheaf.germ V x hxV s := by
  have hzeroGerm :
      (cechTerm F U (n + 2)).presheaf.germ V x hxV
          (0 : (cechTerm F U (n + 2)).obj.obj (op V)) = 0 :=
    map_zero _
  obtain ⟨W, hxW, iWV, _, hEq⟩ :=
    (cechTerm F U (n + 2)).presheaf.germ_eq x hxV hxV
      ((cechDifferential F U (n + 1)).hom.app (op V) s) 0
      (hy.trans hzeroGerm.symm)
  have hEqZero :
      (cechTerm F U (n + 2)).obj.map iWV.op
          ((cechDifferential F U (n + 1)).hom.app (op V) s) = 0 := by
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
  let s' : (cechTerm F U (n + 1)).obj.obj (op W') :=
    (cechTerm F U (n + 1)).obj.map (homOfLE hW'V).op s
  have hDiffRestrict :
      (cechTerm F U (n + 2)).obj.map (homOfLE hW'V).op
          ((cechDifferential F U (n + 1)).hom.app (op V) s) = 0 := by
    calc
      _ = (cechTerm F U (n + 2)).obj.map (homOfLE hW'W).op
          ((cechTerm F U (n + 2)).obj.map iWV.op
            ((cechDifferential F U (n + 1)).hom.app (op V) s)) := by
        change (cechTerm F U (n + 2)).obj.map _ _ =
          ((cechTerm F U (n + 2)).obj.map _ ≫
            (cechTerm F U (n + 2)).obj.map _) _
        rw [← (cechTerm F U (n + 2)).obj.map_comp]
        exact ConcreteCategory.congr_hom
          (congrArg (cechTerm F U (n + 2)).obj.map (Subsingleton.elim _ _)) _
      _ = 0 := by rw [hEqZero, map_zero]
  have hs' : (cechDifferential F U (n + 1)).hom.app (op W') s' = 0 := by
    calc
      _ = (cechTerm F U (n + 2)).obj.map (homOfLE hW'V).op
          ((cechDifferential F U (n + 1)).hom.app (op V) s) := by
        exact ConcreteCategory.congr_hom
          ((cechDifferential F U (n + 1)).hom.naturality (homOfLE hW'V).op) s
      _ = 0 := hDiffRestrict
  exact ⟨i₀, W', hxW', inf_le_right, hW'V, s', hs',
    (cechTerm F U (n + 1)).presheaf.germ_res_apply (homOfLE hW'V) x hxW' s⟩

private theorem exists_stalk_preimage_cechDifferential (hU : ⨆ i, U i = ⊤)
    (n : ℕ) (x : X) (y : (cechTerm F U (n + 1)).presheaf.stalk x)
    (hy : (Presheaf.stalkFunctor AddCommGrpCat x).map
      (cechDifferential F U (n + 1)).hom y = 0) :
    ∃ t : (cechTerm F U n).presheaf.stalk x,
      (Presheaf.stalkFunctor AddCommGrpCat x).map
        (cechDifferential F U n).hom t = y := by
  obtain ⟨V, hxV, s, rfl⟩ :=
    (cechTerm F U (n + 1)).presheaf.exists_germ_eq y
  rw [Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨i₀, W, hxW, hWi₀, _, sW, hsW, hGerm⟩ :=
    exists_cechCycle_restriction F U hU n x hxV s hy
  obtain ⟨t, ht⟩ :=
    exists_preimage_cechDifferential_of_le U F i₀ hWi₀ n sW hsW
  refine ⟨(cechTerm F U n).presheaf.germ W x hxW t, ?_⟩
  change (Presheaf.stalkFunctor AddCommGrpCat x).map
      (cechDifferential F U n).hom
        ((cechTerm F U n).presheaf.germ W x hxW t) =
    (cechTerm F U (n + 1)).presheaf.germ V x hxV s
  rw [Presheaf.stalkFunctor_map_germ_apply, ht]
  exact hGerm

/-- If the opens `U i` cover the whole space, the sheaf-level Cech complex is exact in
every positive degree. -/
theorem cechShortComplex_exact (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (ShortComplex.mk (cechDifferential F U n) (cechDifferential F U (n + 1))
      (cechDifferential_comp F U n)).Exact := by
  rw [exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  exact exists_stalk_preimage_cechDifferential F U hU n x

end TopCat.Sheaf
