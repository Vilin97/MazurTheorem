/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.TotalComplexUpNatHorizontalEdge
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Degree-one homology of the horizontal edge map

An explicit cycle-and-boundary chase shows that the horizontal edge map into a
first-quadrant total complex is a quasi-isomorphism in degree one under the
minimal low-row exactness hypotheses.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u

namespace HomologicalComplex₂

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

private theorem total_d_one_π_zero_two :
    (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 0 2 2 =
      K.πTotalUpNat 0 1 1 ≫ (K.X 0).d 1 2 := by
  calc
    _ = (𝟙 _ : (K.total (.up ℕ)).X 1 ⟶ _) ≫
        (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 0 2 2 := by simp
    _ = (K.πTotalUpNat 0 1 1 ≫ K.ιTotal (.up ℕ) 0 1 1 rfl +
          K.πTotalUpNat 1 0 1 ≫ K.ιTotal (.up ℕ) 1 0 1 rfl) ≫
        (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 0 2 2 := by
      rw [K.totalUpNat_one_decomposition]
    _ = _ := by
      simp only [Preadditive.add_comp, Category.assoc]
      rw [K.ιTotal_d_upNat_assoc 0 1, K.ιTotal_d_upNat_assoc 1 0]
      simp

private theorem total_d_one_π_one_one :
    (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 1 1 2 =
      K.πTotalUpNat 0 1 1 ≫ (K.d 0 1).f 1 -
        K.πTotalUpNat 1 0 1 ≫ (K.X 1).d 0 1 := by
  calc
    _ = (𝟙 _ : (K.total (.up ℕ)).X 1 ⟶ _) ≫
        (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 1 1 2 := by simp
    _ = (K.πTotalUpNat 0 1 1 ≫ K.ιTotal (.up ℕ) 0 1 1 rfl +
          K.πTotalUpNat 1 0 1 ≫ K.ιTotal (.up ℕ) 1 0 1 rfl) ≫
        (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 1 1 2 := by
      rw [K.totalUpNat_one_decomposition]
    _ = _ := by
      simp only [Preadditive.add_comp, Category.assoc]
      rw [K.ιTotal_d_upNat_assoc 0 1, K.ιTotal_d_upNat_assoc 1 0]
      simp [sub_eq_add_neg]

private theorem total_d_one_π_two_zero :
    (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 2 0 2 =
      K.πTotalUpNat 1 0 1 ≫ (K.d 1 2).f 0 := by
  calc
    _ = (𝟙 _ : (K.total (.up ℕ)).X 1 ⟶ _) ≫
        (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 2 0 2 := by simp
    _ = (K.πTotalUpNat 0 1 1 ≫ K.ιTotal (.up ℕ) 0 1 1 rfl +
          K.πTotalUpNat 1 0 1 ≫ K.ιTotal (.up ℕ) 1 0 1 rfl) ≫
        (K.total (.up ℕ)).d 1 2 ≫ K.πTotalUpNat 2 0 2 := by
      rw [K.totalUpNat_one_decomposition]
    _ = _ := by
      simp only [Preadditive.add_comp, Category.assoc]
      rw [K.ιTotal_d_upNat_assoc 0 1, K.ιTotal_d_upNat_assoc 1 0]
      simp

private theorem total_d_zero_π_zero_one :
    (K.total (.up ℕ)).d 0 1 ≫ K.πTotalUpNat 0 1 1 =
      K.πTotalUpNat 0 0 0 ≫ (K.X 0).d 0 1 := by
  calc
    _ = (𝟙 _ : (K.total (.up ℕ)).X 0 ⟶ _) ≫
        (K.total (.up ℕ)).d 0 1 ≫ K.πTotalUpNat 0 1 1 := by simp
    _ = (K.πTotalUpNat 0 0 0 ≫ K.ιTotal (.up ℕ) 0 0 0 rfl) ≫
        (K.total (.up ℕ)).d 0 1 ≫ K.πTotalUpNat 0 1 1 := by
      rw [K.totalUpNat_zero_decomposition]
    _ = _ := by
      simp only [Category.assoc]
      rw [K.ιTotal_d_upNat_assoc 0 0]
      simp

private theorem total_d_zero_π_one_zero :
    (K.total (.up ℕ)).d 0 1 ≫ K.πTotalUpNat 1 0 1 =
      K.πTotalUpNat 0 0 0 ≫ (K.d 0 1).f 0 := by
  calc
    _ = (𝟙 _ : (K.total (.up ℕ)).X 0 ⟶ _) ≫
        (K.total (.up ℕ)).d 0 1 ≫ K.πTotalUpNat 1 0 1 := by simp
    _ = (K.πTotalUpNat 0 0 0 ≫ K.ιTotal (.up ℕ) 0 0 0 rfl) ≫
        (K.total (.up ℕ)).d 0 1 ≫ K.πTotalUpNat 1 0 1 := by
      rw [K.totalUpNat_zero_decomposition]
    _ = _ := by
      simp only [Category.assoc]
      rw [K.ιTotal_d_upNat_assoc 0 0]
      simp

private theorem cycle_zero_two
    (x : (K.total (.up ℕ)).X 1)
    (hx : (K.total (.up ℕ)).d 1 2 x = 0) :
    (K.X 0).d 1 2 (K.πTotalUpNat 0 1 1 x) = 0 := by
  have h := congrArg (fun f ↦ f x) (K.total_d_one_π_zero_two)
  simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h.symm

private theorem cycle_one_one
    (x : (K.total (.up ℕ)).X 1)
    (hx : (K.total (.up ℕ)).d 1 2 x = 0) :
    (K.d 0 1).f 1 (K.πTotalUpNat 0 1 1 x) =
      (K.X 1).d 0 1 (K.πTotalUpNat 1 0 1 x) := by
  have h := congrArg (fun f ↦ f x) (K.total_d_one_π_one_one)
  simp only [ConcreteCategory.comp_apply, hx, map_zero] at h
  exact sub_eq_zero.mp h.symm

private theorem cycle_two_zero
    (x : (K.total (.up ℕ)).X 1)
    (hx : (K.total (.up ℕ)).d 1 2 x = 0) :
    (K.d 1 2).f 0 (K.πTotalUpNat 1 0 1 x) = 0 := by
  have h := congrArg (fun f ↦ f x) (K.total_d_one_π_two_zero)
  simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h.symm

private theorem boundary_zero_one (b : (K.total (.up ℕ)).X 0) :
    K.πTotalUpNat 0 1 1 ((K.total (.up ℕ)).d 0 1 b) =
      (K.X 0).d 0 1 (K.πTotalUpNat 0 0 0 b) := by
  have h := congrArg (fun f ↦ f b) (K.total_d_zero_π_zero_one)
  simpa only [ConcreteCategory.comp_apply] using h

private theorem boundary_one_zero (b : (K.total (.up ℕ)).X 0) :
    K.πTotalUpNat 1 0 1 ((K.total (.up ℕ)).d 0 1 b) =
      (K.d 0 1).f 0 (K.πTotalUpNat 0 0 0 b) := by
  have h := congrArg (fun f ↦ f b) (K.total_d_zero_π_one_zero)
  simpa only [ConcreteCategory.comp_apply] using h

private theorem total_one_eq_components (x : (K.total (.up ℕ)).X 1) :
    K.ιTotal (.up ℕ) 0 1 1 rfl (K.πTotalUpNat 0 1 1 x) +
      K.ιTotal (.up ℕ) 1 0 1 rfl (K.πTotalUpNat 1 0 1 x) = x := by
  have h := congrArg (fun f ↦ f x) K.totalUpNat_one_decomposition
  simpa only [AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply,
    CategoryTheory.id_apply] using h

private theorem total_zero_eq_component (x : (K.total (.up ℕ)).X 0) :
    K.ιTotal (.up ℕ) 0 0 0 rfl (K.πTotalUpNat 0 0 0 x) = x := by
  have h := congrArg (fun f ↦ f x) K.totalUpNat_zero_decomposition
  simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using h

private theorem up_prev_one : (ComplexShape.up ℕ).prev 1 = 0 :=
  (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 0 1 by rfl)

private theorem up_next_one : (ComplexShape.up ℕ).next 1 = 2 :=
  (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 1 2 by rfl)

private noncomputable def abCyclesMk
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (x : L.X 1)
    (hx : L.d 1 2 x = 0) : L.cycles 1 :=
  (L.cyclesIsoSc' 0 1 2 up_prev_one up_next_one).inv
    ((L.sc' 0 1 2).abCyclesIso.inv ⟨x, hx⟩)

@[simp]
private theorem i_abCyclesMk
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (x : L.X 1)
    (hx : L.d 1 2 x = 0) :
    L.iCycles 1 (abCyclesMk L x hx) = x := by
  have h₁ := congrArg
    (fun g ↦ g ((L.sc' 0 1 2).abCyclesIso.inv ⟨x, hx⟩))
    (L.cyclesIsoSc'_inv_iCycles 0 1 2 up_prev_one up_next_one)
  simp only [ConcreteCategory.comp_apply] at h₁
  have h₂ := (L.sc' 0 1 2).abCyclesIso_inv_apply_iCycles ⟨x, hx⟩
  exact h₁.trans h₂

private theorem cyclesMap_cyclesMk
    {L M : CochainComplex AddCommGrpCat.{u} ℕ} (f : L ⟶ M)
    (x : L.X 1) (hx : L.d 1 2 x = 0)
    (hfx : M.d 1 2 (f.f 1 x) = 0) :
    HomologicalComplex.cyclesMap f 1 (abCyclesMk L x hx) =
      abCyclesMk M (f.f 1 x) hfx := by
  apply (AddCommGrpCat.mono_iff_injective (M.iCycles 1)).mp inferInstance
  have h := congrArg (fun g ↦ g (abCyclesMk L x hx))
    (HomologicalComplex.cyclesMap_i f 1)
  simpa only [ConcreteCategory.comp_apply, i_abCyclesMk] using h

private theorem homologyπ_cyclesMk_eq_of_sub_eq_boundary
    (L : CochainComplex AddCommGrpCat.{u} ℕ)
    (x y : L.X 1) (hx : L.d 1 2 x = 0) (hy : L.d 1 2 y = 0)
    (b : L.X 0) (hxy : x - y = L.d 0 1 b) :
    L.homologyπ 1 (abCyclesMk L x hx) =
      L.homologyπ 1 (abCyclesMk L y hy) := by
  let S := L.sc' 0 1 2
  let cIso := L.cyclesIsoSc' 0 1 2 up_prev_one up_next_one
  let hIso := L.homologyIsoSc' 0 1 2 up_prev_one up_next_one
  let qIso := hIso ≪≫ S.abHomologyIso
  apply (AddCommGrpCat.mono_iff_injective qIso.hom).mp inferInstance
  have class_eq (z : L.X 1) (hz : L.d 1 2 z = 0) :
      qIso.hom (L.homologyπ 1 (abCyclesMk L z hz)) =
        QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨z, hz⟩ : AddMonoidHom.ker S.g.hom) := by
    have h₁ := congrArg (fun g ↦ g (abCyclesMk L z hz))
      (L.π_homologyIsoSc'_hom 0 1 2 up_prev_one up_next_one)
    have h₂ := congrArg
      (fun g ↦ g (cIso.hom (abCyclesMk L z hz)))
      S.abLeftHomologyData.homologyπ_comp_homologyIso_hom
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    calc
      _ = S.abHomologyIso.hom
          (hIso.hom (L.homologyπ 1 (abCyclesMk L z hz))) := rfl
      _ = S.abHomologyIso.hom
          (S.homologyπ (cIso.hom (abCyclesMk L z hz))) := by
        rw [h₁]
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (S.abCyclesIso.hom (cIso.hom (abCyclesMk L z hz))) := by
        change S.abLeftHomologyData.homologyIso.hom
            (S.homologyπ (cIso.hom (abCyclesMk L z hz))) =
          S.abLeftHomologyData.π
            (S.abLeftHomologyData.cyclesIso.hom
              (cIso.hom (abCyclesMk L z hz)))
        exact h₂
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨z, hz⟩ : AddMonoidHom.ker S.g.hom) := by
        change QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
            (S.abCyclesIso.hom
              (cIso.hom (cIso.inv (S.abCyclesIso.inv ⟨z, hz⟩)))) = _
        rw [cIso.inv_hom_id_apply, S.abCyclesIso.inv_hom_id_apply]
  rw [class_eq x hx, class_eq y hy]
  dsimp only [S]
  refine (QuotientAddGroup.eq_iff_sub_mem).2 ?_
  rw [AddMonoidHom.mem_range]
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change L.d 0 1 b = x - y
  exact hxy.symm

private theorem exists_boundary_of_homologyπ_abCyclesMk_eq_zero
    (L : CochainComplex AddCommGrpCat.{u} ℕ)
    (x : L.X 1) (hx : L.d 1 2 x = 0)
    (hzero : L.homologyπ 1 (abCyclesMk L x hx) = 0) :
    ∃ b : L.X 0, L.d 0 1 b = x := by
  let S := L.sc' 0 1 2
  let cIso := L.cyclesIsoSc' 0 1 2 up_prev_one up_next_one
  let hIso := L.homologyIsoSc' 0 1 2 up_prev_one up_next_one
  let qIso := hIso ≪≫ S.abHomologyIso
  have class_eq :
      qIso.hom (L.homologyπ 1 (abCyclesMk L x hx)) =
        QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom) := by
    have h₁ := congrArg (fun g ↦ g (abCyclesMk L x hx))
      (L.π_homologyIsoSc'_hom 0 1 2 up_prev_one up_next_one)
    have h₂ := congrArg
      (fun g ↦ g (cIso.hom (abCyclesMk L x hx)))
      S.abLeftHomologyData.homologyπ_comp_homologyIso_hom
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    calc
      _ = S.abHomologyIso.hom
          (hIso.hom (L.homologyπ 1 (abCyclesMk L x hx))) := rfl
      _ = S.abHomologyIso.hom
          (S.homologyπ (cIso.hom (abCyclesMk L x hx))) := by rw [h₁]
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (S.abCyclesIso.hom (cIso.hom (abCyclesMk L x hx))) := by
        change S.abLeftHomologyData.homologyIso.hom
            (S.homologyπ (cIso.hom (abCyclesMk L x hx))) =
          S.abLeftHomologyData.π
            (S.abLeftHomologyData.cyclesIso.hom
              (cIso.hom (abCyclesMk L x hx)))
        exact h₂
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom) := by
        change QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
            (S.abCyclesIso.hom
              (cIso.hom (cIso.inv (S.abCyclesIso.inv ⟨x, hx⟩)))) = _
        rw [cIso.inv_hom_id_apply, S.abCyclesIso.inv_hom_id_apply]
  have hclass :
      QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
        (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom) = 0 := by
    rw [← class_eq, hzero, map_zero]
  have hmem := (QuotientAddGroup.eq_zero_iff
    (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom)).mp hclass
  rw [AddMonoidHom.mem_range] at hmem
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, ?_⟩
  have hb' := congrArg Subtype.val hb
  exact hb'

private theorem homologyMap_abCyclesMk
    {L M : CochainComplex AddCommGrpCat.{u} ℕ} (f : L ⟶ M)
    (x : L.X 1) (hx : L.d 1 2 x = 0)
    (hfx : M.d 1 2 (f.f 1 x) = 0) :
    HomologicalComplex.homologyMap f 1
        (L.homologyπ 1 (abCyclesMk L x hx)) =
      M.homologyπ 1 (abCyclesMk M (f.f 1 x) hfx) := by
  have h := congrArg (fun g ↦ g (abCyclesMk L x hx))
    (HomologicalComplex.homologyπ_naturality (φ := f) (i := 1))
  simp only [ConcreteCategory.comp_apply, cyclesMap_cyclesMk f x hx hfx] at h
  exact h

private theorem totalUpNatHorizontalEdge_homologyMap_surjective
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (hrow10 : (ShortComplex.mk (e 1) ((K.X 1).d 0 1) (w 1)).Exact)
    (hrow01 : (ShortComplex.mk ((K.X 0).d 0 1) ((K.X 0).d 1 2)
      ((K.X 0).d_comp_d 0 1 2)).Exact)
    [Mono (e 2)] :
    Function.Surjective (HomologicalComplex.homologyMap
      (K.totalUpNatHorizontalEdge A e he w) 1) := by
  let T := K.total (.up ℕ)
  let edge := K.totalUpNatHorizontalEdge A e he w
  intro ξ
  have hπ : Function.Surjective (T.homologyπ 1) :=
    (AddCommGrpCat.epi_iff_surjective (T.homologyπ 1)).mp inferInstance
  obtain ⟨xc, rfl⟩ := hπ ξ
  let x : T.X 1 := T.iCycles 1 xc
  have hx : T.d 1 2 x = 0 := by
    have h := congrArg (fun g ↦ g xc) (T.iCycles_d 1 2)
    simpa only [x, ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  obtain ⟨b, hb⟩ :=
    ((ShortComplex.mk ((K.X 0).d 0 1) ((K.X 0).d 1 2)
      ((K.X 0).d_comp_d 0 1 2)).ab_exact_iff.mp hrow01)
    (K.πTotalUpNat 0 1 1 x) (K.cycle_zero_two x hx)
  let x10 : (K.X 1).X 0 :=
    K.πTotalUpNat 1 0 1 x - (K.d 0 1).f 0 b
  have hcomm :
      (K.X 1).d 0 1 ((K.d 0 1).f 0 b) =
        (K.d 0 1).f 1 ((K.X 0).d 0 1 b) := by
    have h := congrArg (fun g ↦ g b) (K.d_comm 0 1 0 1)
    simpa only [ConcreteCategory.comp_apply] using h
  have hx10h : (K.X 1).d 0 1 x10 = 0 := by
    simp only [x10, map_sub]
    rw [← K.cycle_one_one x hx, hcomm, hb, sub_self]
  obtain ⟨a, ha⟩ :=
    ((ShortComplex.mk (e 1) ((K.X 1).d 0 1) (w 1)).ab_exact_iff.mp hrow10)
      x10 hx10h
  have hvv : (K.d 1 2).f 0 ((K.d 0 1).f 0 b) = 0 := by
    have h := congrArg (fun g ↦ g b) (K.d_f_comp_d_f 0 1 2 0)
    simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  have hx10v : (K.d 1 2).f 0 x10 = 0 := by
    simp only [x10, map_sub, K.cycle_two_zero x hx, hvv, sub_self]
  have hnat :
      (K.d 1 2).f 0 (e 1 a) = e 2 (A.d 1 2 a) := by
    have h := congrArg (fun g ↦ g a) (he 1 2 rfl)
    simpa only [ConcreteCategory.comp_apply] using h
  have haCycle : A.d 1 2 a = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (e 2)).mp inferInstance
    rw [map_zero, ← hnat, ha, hx10v]
  have hedge : edge.f 1 a = K.ιTotal (.up ℕ) 1 0 1 rfl x10 := by
    have h := congrArg (fun g ↦ g a)
      (K.totalUpNatHorizontalEdge_f A e he w 1)
    simpa only [edge, ConcreteCategory.comp_apply, ha] using h
  let bt : T.X 0 := K.ιTotal (.up ℕ) 0 0 0 rfl b
  have hboundary :
      T.d 0 1 bt =
        K.ιTotal (.up ℕ) 1 0 1 rfl ((K.d 0 1).f 0 b) +
          K.ιTotal (.up ℕ) 0 1 1 rfl ((K.X 0).d 0 1 b) := by
    have h := congrArg (fun g ↦ g b) (K.ιTotal_d_upNat 0 0)
    simpa [T, bt, ConcreteCategory.comp_apply] using h
  have hdiff : x - edge.f 1 a = T.d 0 1 bt := by
    rw [← K.total_one_eq_components x, hedge, hboundary, hb]
    simp only [x10, map_sub]
    abel
  have hedgeCycle : T.d 1 2 (edge.f 1 a) = 0 := by
    have h := congrArg (fun g ↦ g a) (edge.comm 1 2)
    simpa only [ConcreteCategory.comp_apply, haCycle, map_zero] using h
  have hxc : abCyclesMk T x hx = xc := by
    apply (AddCommGrpCat.mono_iff_injective (T.iCycles 1)).mp inferInstance
    simp only [i_abCyclesMk, x]
  refine ⟨A.homologyπ 1 (abCyclesMk A a haCycle), ?_⟩
  calc
    HomologicalComplex.homologyMap edge 1
        (A.homologyπ 1 (abCyclesMk A a haCycle)) =
        T.homologyπ 1 (abCyclesMk T (edge.f 1 a) hedgeCycle) :=
      homologyMap_abCyclesMk edge a haCycle hedgeCycle
    _ = T.homologyπ 1 (abCyclesMk T x hx) :=
      (homologyπ_cyclesMk_eq_of_sub_eq_boundary T x (edge.f 1 a) hx
        hedgeCycle bt hdiff).symm
    _ = T.homologyπ 1 xc := by rw [hxc]

private theorem totalUpNatHorizontalEdge_f_one_π_zero_one
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0) :
    (K.totalUpNatHorizontalEdge A e he w).f 1 ≫ K.πTotalUpNat 0 1 1 = 0 := by
  rw [K.totalUpNatHorizontalEdge_f]
  simp

private theorem totalUpNatHorizontalEdge_f_one_π_one_zero
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0) :
    (K.totalUpNatHorizontalEdge A e he w).f 1 ≫ K.πTotalUpNat 1 0 1 = e 1 := by
  rw [K.totalUpNatHorizontalEdge_f]
  simp

private theorem totalUpNatHorizontalEdge_homologyMap_injective
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (hrow00 : (ShortComplex.mk (e 0) ((K.X 0).d 0 1) (w 0)).Exact)
    [Mono (e 1)] :
    Function.Injective (HomologicalComplex.homologyMap
      (K.totalUpNatHorizontalEdge A e he w) 1) := by
  let T := K.total (.up ℕ)
  let edge := K.totalUpNatHorizontalEdge A e he w
  intro ξ η hξη
  rw [← sub_eq_zero]
  have hmapzero :
      HomologicalComplex.homologyMap edge 1 (ξ - η) = 0 := by
    rw [map_sub, hξη, sub_self]
  have hπ : Function.Surjective (A.homologyπ 1) :=
    (AddCommGrpCat.epi_iff_surjective (A.homologyπ 1)).mp inferInstance
  obtain ⟨ac, hac⟩ := hπ (ξ - η)
  let a : A.X 1 := A.iCycles 1 ac
  have haCycle : A.d 1 2 a = 0 := by
    have h := congrArg (fun g ↦ g ac) (A.iCycles_d 1 2)
    simpa only [a, ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  have hedgeCycle : T.d 1 2 (edge.f 1 a) = 0 := by
    have h := congrArg (fun g ↦ g a) (edge.comm 1 2)
    simpa only [ConcreteCategory.comp_apply, haCycle, map_zero] using h
  have hac' : abCyclesMk A a haCycle = ac := by
    apply (AddCommGrpCat.mono_iff_injective (A.iCycles 1)).mp inferInstance
    simp only [i_abCyclesMk, a]
  have hedgeClassZero :
      T.homologyπ 1 (abCyclesMk T (edge.f 1 a) hedgeCycle) = 0 := by
    calc
      _ = HomologicalComplex.homologyMap edge 1
          (A.homologyπ 1 (abCyclesMk A a haCycle)) :=
        (homologyMap_abCyclesMk edge a haCycle hedgeCycle).symm
      _ = HomologicalComplex.homologyMap edge 1 (ξ - η) := by
        rw [hac', hac]
      _ = 0 := hmapzero
  obtain ⟨bt, hbt⟩ :=
    exists_boundary_of_homologyπ_abCyclesMk_eq_zero T (edge.f 1 a)
      hedgeCycle hedgeClassZero
  let b : (K.X 0).X 0 := K.πTotalUpNat 0 0 0 bt
  have hedge01 : K.πTotalUpNat 0 1 1 (edge.f 1 a) = 0 := by
    have h := congrArg (fun g ↦ g a)
      (K.totalUpNatHorizontalEdge_f_one_π_zero_one A e he w)
    simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  have hbHorizontal : (K.X 0).d 0 1 b = 0 := by
    rw [← K.boundary_zero_one bt, hbt]
    exact hedge01
  obtain ⟨c, hc⟩ :=
    ((ShortComplex.mk (e 0) ((K.X 0).d 0 1) (w 0)).ab_exact_iff.mp hrow00)
      b hbHorizontal
  have hedge10 : K.πTotalUpNat 1 0 1 (edge.f 1 a) = e 1 a := by
    have h := congrArg (fun g ↦ g a)
      (K.totalUpNatHorizontalEdge_f_one_π_one_zero A e he w)
    simpa only [ConcreteCategory.comp_apply] using h
  have hea : e 1 a = (K.d 0 1).f 0 b := by
    calc
      _ = K.πTotalUpNat 1 0 1 (edge.f 1 a) := hedge10.symm
      _ = K.πTotalUpNat 1 0 1 (T.d 0 1 bt) := by rw [hbt]
      _ = (K.d 0 1).f 0 b := K.boundary_one_zero bt
  have hnat : (K.d 0 1).f 0 (e 0 c) = e 1 (A.d 0 1 c) := by
    have h := congrArg (fun g ↦ g c) (he 0 1 rfl)
    simpa only [ConcreteCategory.comp_apply] using h
  have haBoundary : a = A.d 0 1 c := by
    apply (AddCommGrpCat.mono_iff_injective (e 1)).mp inferInstance
    calc
      e 1 a = (K.d 0 1).f 0 b := hea
      _ = (K.d 0 1).f 0 (e 0 c) := by rw [hc]
      _ = e 1 (A.d 0 1 c) := hnat
  have hzeroCycle : A.d 1 2 (0 : A.X 1) = 0 := by simp
  have habZero : abCyclesMk A 0 hzeroCycle = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (A.iCycles 1)).mp inferInstance
    simp only [i_abCyclesMk, map_zero]
  have haClassZero : A.homologyπ 1 (abCyclesMk A a haCycle) = 0 := by
    calc
      _ = A.homologyπ 1 (abCyclesMk A 0 hzeroCycle) :=
        homologyπ_cyclesMk_eq_of_sub_eq_boundary A a 0 haCycle hzeroCycle c
          (by simpa only [sub_zero] using haBoundary)
      _ = 0 := by rw [habZero, map_zero]
  calc
    ξ - η = A.homologyπ 1 ac := hac.symm
    _ = A.homologyπ 1 (abCyclesMk A a haCycle) := by rw [hac']
    _ = 0 := haClassZero

/-- The horizontal edge map is a quasi-isomorphism in degree one when the three
low horizontal short complexes used by the cycle chase are exact. -/
theorem totalUpNatHorizontalEdge_quasiIsoAt_one
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (hrow00 : (ShortComplex.mk (e 0) ((K.X 0).d 0 1) (w 0)).Exact)
    (hrow10 : (ShortComplex.mk (e 1) ((K.X 1).d 0 1) (w 1)).Exact)
    (hrow01 : (ShortComplex.mk ((K.X 0).d 0 1) ((K.X 0).d 1 2)
      ((K.X 0).d_comp_d 0 1 2)).Exact)
    [Mono (e 1)] [Mono (e 2)] :
    QuasiIsoAt (K.totalUpNatHorizontalEdge A e he w) 1 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let f := HomologicalComplex.homologyMap
    (K.totalUpNatHorizontalEdge A e he w) 1
  haveI : Mono f := (AddCommGrpCat.mono_iff_injective f).mpr
    (K.totalUpNatHorizontalEdge_homologyMap_injective A e he w hrow00)
  haveI : Epi f := (AddCommGrpCat.epi_iff_surjective f).mpr
    (K.totalUpNatHorizontalEdge_homologyMap_surjective A e he w hrow10 hrow01)
  exact isIso_of_mono_of_epi f

end HomologicalComplex₂
