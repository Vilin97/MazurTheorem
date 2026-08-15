/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFlasqueCohomology
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Cohomology on an open subspace

Mathlib's Mayer--Vietoris sequence uses `F.H' n U`, the `Ext` group out of
the sheafified free abelian presheaf represented by `U`.  Local vanishing
results are naturally stated as global cohomology of the restriction of `F`
to the open subspace `U`.

This file proves the vanishing comparison needed to pass between the two
forms.  The proof is a dimension-shifting argument.  In degree zero both
theories compute sections on `U`; in positive degrees an injective
presentation is used.  Restriction of its injective middle term is flasque,
so its positive global cohomology vanishes.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

namespace OpenCohomology

noncomputable section

noncomputable local instance sheafOpenCohomologyAddCommGroup
    {Z : TopCat.{u}}
    (G : Sheaf AddCommGrpCat.{u} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

noncomputable local instance extAddCommGroup
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt C]
    {A B : C} {n : ℕ} :
    AddCommGroup (Abelian.Ext A B n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

noncomputable local instance sheafHomAddCommGroup
    {Z : TopCat.{u}}
    (A B : Sheaf AddCommGrpCat.{u} Z) :
    AddCommGroup (A ⟶ B) :=
  @Preadditive.homGroup _ _
    (inferInstance : Preadditive (Sheaf AddCommGrpCat.{u} Z)) A B

/-- The source object occurring in `F.H' n U`. -/
abbrev freeAbSheaf (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X :=
  ((yoneda ⋙
      (Functor.whiskeringRight _ _ _).obj
        AddCommGrpCat.free ⋙
      presheafToSheaf _ _).op.obj (op U)).unop

noncomputable local instance freeAbSheafHomAddCommGroup
    {Z : TopCat.{u}} (U : Opens Z)
    (F : Sheaf AddCommGrpCat.{u} Z) :
    AddCommGroup
      (((yoneda ⋙
          (Functor.whiskeringRight _ _ _).obj
            AddCommGrpCat.free ⋙
          presheafToSheaf _ _).op.obj (op U)).unop ⟶ F) :=
  @Preadditive.homGroup _ _
    (inferInstance : Preadditive (Sheaf AddCommGrpCat.{u} Z))
    (((yoneda ⋙
      (Functor.whiskeringRight _ _ _).obj
        AddCommGrpCat.free ⋙
      presheafToSheaf _ _).op.obj (op U)).unop) F

noncomputable local instance freeAbSheafExtAddCommGroup
    {Z : TopCat.{u}} (U : Opens Z)
    (F : Sheaf AddCommGrpCat.{u} Z) (n : ℕ) :
    AddCommGroup
      (Abelian.Ext
        (((yoneda ⋙
          (Functor.whiskeringRight _ _ _).obj
            AddCommGrpCat.free ⋙
          presheafToSheaf _ _).op.obj (op U)).unop)
        F n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Morphisms out of the free abelian sheaf represented by `U` are sections on `U`. -/
abbrev freeAbSheafHomEquiv (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (freeAbSheaf U ⟶ F) ≃ F.obj.obj (op U) :=
  IsFlasque.freeAbSheafHomEquiv U F

lemma freeAbSheafHomEquiv_comp (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X}
    (φ : freeAbSheaf U ⟶ F) (f : F ⟶ G) :
    freeAbSheafHomEquiv U G (φ ≫ f) =
      f.hom.app (op U) (freeAbSheafHomEquiv U F φ) := by
  rfl

/-- Degree-zero objectwise cohomology is the group of sections on the open. -/
noncomputable def H'_zero_addEquiv_sections
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    CategoryTheory.Sheaf.H' F 0 U ≃+ F.obj.obj (op U) :=
  Abelian.Ext.addEquiv₀.trans
    { toEquiv := freeAbSheafHomEquiv U F
      map_add' := by
        intro φ ψ
        rfl }

/-- Sections of the restricted sheaf on its whole space are sections on `U`. -/
noncomputable def restrictTopSectionsIso
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F).obj.obj
        (op (⊤ : Opens U)) ≅ F.obj.obj (op U) :=
  (F.obj.mapIso
    (eqToIso (Opens.isOpenEmbedding_obj_top U)).op).symm

/-- Degree-zero global cohomology of the restriction is the group of sections on `U`. -/
noncomputable def restrict_H_zero_addEquiv_sections
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) 0 ≃+
      F.obj.obj (op U) :=
  (CategoryTheory.Sheaf.H.equiv₀
    ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F)
    Limits.isTerminalTop).trans
      (restrictTopSectionsIso F U).addCommGroupIsoToAddEquiv

/-- In degree zero, `H'` and global cohomology after restriction are additively equivalent. -/
noncomputable def H'_zero_addEquiv_restrict_H
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    CategoryTheory.Sheaf.H' F 0 U ≃+
      CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) 0 :=
  (H'_zero_addEquiv_sections F U).trans
    (restrict_H_zero_addEquiv_sections F U).symm

/--
If a morphism of sheaves is surjective on sections over `U`, then the
induced map on degree-zero `H'` over `U` is surjective.
-/
lemma ext_zero_postcomp_surjective_of_app_surjective
    (U : Opens X) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G)
    (hf : Function.Surjective (f.hom.app (op U))) :
    Function.Surjective
      ((Abelian.Ext.mk₀ f).postcomp (freeAbSheaf U) (add_zero 0)) := by
  intro x
  obtain ⟨s, hs⟩ :=
    hf (freeAbSheafHomEquiv U G (Abelian.Ext.addEquiv₀ x))
  let φ : freeAbSheaf U ⟶ F :=
    (freeAbSheafHomEquiv U F).symm s
  refine ⟨Abelian.Ext.mk₀ φ, ?_⟩
  change
    (Abelian.Ext.mk₀ φ).comp (Abelian.Ext.mk₀ f) (zero_add 0) = x
  rw [Abelian.Ext.mk₀_comp_mk₀,
    ← Abelian.Ext.mk₀_addEquiv₀_apply x]
  congr 1
  apply (freeAbSheafHomEquiv U G).injective
  rw [freeAbSheafHomEquiv_comp, Equiv.apply_symm_apply, hs]

/--
Surjectivity on degree-zero `H'` over `U` detects surjectivity on sections
over `U`.
-/
lemma app_surjective_of_ext_zero_postcomp_surjective
    (U : Opens X) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G)
    (hf : Function.Surjective
      ((Abelian.Ext.mk₀ f).postcomp (freeAbSheaf U) (add_zero 0))) :
    Function.Surjective (f.hom.app (op U)) := by
  intro s
  let φ : freeAbSheaf U ⟶ G :=
    (freeAbSheafHomEquiv U G).symm s
  obtain ⟨x, hx⟩ := hf (Abelian.Ext.mk₀ φ)
  let ψ : freeAbSheaf U ⟶ F := Abelian.Ext.addEquiv₀ x
  refine ⟨freeAbSheafHomEquiv U F ψ, ?_⟩
  rw [← freeAbSheafHomEquiv_comp]
  rw [← (freeAbSheafHomEquiv U G).apply_symm_apply s]
  congr 1
  change ψ ≫ f = φ
  apply Abelian.Ext.mk₀_bijective _ _ |>.injective
  calc
    Abelian.Ext.mk₀ (ψ ≫ f) =
        (Abelian.Ext.mk₀ ψ).comp
          (Abelian.Ext.mk₀ f) (zero_add 0) :=
      (Abelian.Ext.mk₀_comp_mk₀ ψ f).symm
    _ = ((Abelian.Ext.mk₀ f).postcomp
          (freeAbSheaf U) (add_zero 0)) x := by
      rw [show Abelian.Ext.mk₀ ψ = x from
        Abelian.Ext.mk₀_addEquiv₀_apply x]
      rfl
    _ = Abelian.Ext.mk₀ φ := hx

/-- Restriction of an injective abelian sheaf to an open subspace is flasque. -/
lemma restrict_isFlasque_of_injective
    (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X) [Injective I] :
    ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj I).IsFlasque where
  epi i := by
    change Epi (I.obj.map (U.isOpenEmbedding.functor.op.map i))
    letI : I.IsFlasque :=
      @TopCat.Sheaf.IsFlasque.of_injective _ I
        (inferInstance : Injective I)
    exact TopCat.Presheaf.IsFlasque.epi
      (F := I.obj) (U.isOpenEmbedding.functor.op.map i)

/--
Vanishing of global cohomology after restriction to `U` implies vanishing
of Mathlib's objectwise cohomology `H'` on `U`.

This is the direction consumed by the Mayer--Vietoris sequence.
-/
theorem subsingleton_H'_of_subsingleton_restrict_H
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (n : ℕ)
    (hF : Subsingleton
      (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H' F (n + 1) U) := by
  induction n generalizing F with
  | zero =>
      refine subsingleton_of_forall_eq 0 fun x => ?_
      let pres := (EnoughInjectives.presentation F).some.shortComplex
      have presEx : pres.ShortExact :=
        (EnoughInjectives.presentation F).some.shortExact_shortComplex
      let presU := pres.map (restrict AddCommGrpCat.{u} U.isOpenEmbedding)
      have presUEx : presU.ShortExact :=
        presEx.map_of_exact _
      haveI : Subsingleton (presU.X₁.H 1) := hF
      have hsections : Function.Surjective (pres.g.hom.app (op U)) := by
        erw [← Opens.isOpenEmbedding_obj_top U]
        exact CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
          presUEx Limits.isTerminalTop
      obtain ⟨y, hy⟩ :=
        Abelian.Ext.covariant_sequence_exact₁
          (freeAbSheaf U) presEx x
          (Abelian.Ext.eq_zero_of_injective _) rfl
      obtain ⟨z, hz⟩ :=
        ext_zero_postcomp_surjective_of_app_surjective U pres.g hsections y
      rw [← hy, ← hz]
      change
        (z.comp (Abelian.Ext.mk₀ pres.g) (add_zero 0)).comp
          presEx.extClass rfl = 0
      rw [Abelian.Ext.comp_assoc_of_second_deg_zero,
        ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero]
  | succ n hn =>
      refine subsingleton_of_forall_eq 0 fun x => ?_
      let pres := (EnoughInjectives.presentation F).some.shortComplex
      have presEx : pres.ShortExact :=
        (EnoughInjectives.presentation F).some.shortExact_shortComplex
      let presU := pres.map (restrict AddCommGrpCat.{u} U.isOpenEmbedding)
      have presUEx : presU.ShortExact :=
        presEx.map_of_exact _
      letI : presU.X₂.IsFlasque :=
        restrict_isFlasque_of_injective U pres.X₂
      have hC : Subsingleton (presU.X₃.H (n + 1)) := by
        refine subsingleton_of_forall_eq 0 fun y => ?_
        obtain ⟨z, hz⟩ :=
          CategoryTheory.Sheaf.H.longSequence_exact₃
            presUEx (n + 1) (n + 2) rfl y
            (hF.elim _ _)
        rw [← hz, Subsingleton.elim z 0]
        exact map_zero _
      have hC' : Subsingleton (pres.X₃.H' (n + 1) U) :=
        hn pres.X₃ hC
      obtain ⟨y, hy⟩ :=
        Abelian.Ext.covariant_sequence_exact₁
          (freeAbSheaf U) presEx x
          (Abelian.Ext.eq_zero_of_injective _) rfl
      rw [← hy, hC'.elim y 0]
      exact Abelian.Ext.zero_comp
        (freeAbSheaf U) (n + 1) presEx.extClass (n + 2) rfl

/--
Vanishing of Mathlib's objectwise cohomology `H'` on `U` implies vanishing
of global cohomology after restriction to the open subspace `U`.
-/
theorem subsingleton_restrict_H_of_subsingleton_H'
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (n : ℕ)
    (hF : Subsingleton (CategoryTheory.Sheaf.H' F (n + 1) U)) :
    Subsingleton
      (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) (n + 1)) := by
  induction n generalizing F with
  | zero =>
      refine subsingleton_of_forall_eq 0 fun x => ?_
      let pres := (EnoughInjectives.presentation F).some.shortComplex
      have presEx : pres.ShortExact :=
        (EnoughInjectives.presentation F).some.shortExact_shortComplex
      let presU := pres.map (restrict AddCommGrpCat.{u} U.isOpenEmbedding)
      have presUEx : presU.ShortExact :=
        presEx.map_of_exact _
      letI : presU.X₂.IsFlasque :=
        restrict_isFlasque_of_injective U pres.X₂
      have hext : Function.Surjective
          ((Abelian.Ext.mk₀ pres.g).postcomp
            (freeAbSheaf U) (add_zero 0)) := by
        intro y
        exact Abelian.Ext.covariant_sequence_exact₃
          (freeAbSheaf U) presEx y rfl (hF.elim _ _)
      have hsections : Function.Surjective
          (pres.g.hom.app (op U)) :=
        app_surjective_of_ext_zero_postcomp_surjective
          U pres.g hext
      have hsectionsU : Function.Surjective
          (presU.g.hom.app (op (⊤ : Opens U))) := by
        change Function.Surjective
          (pres.g.hom.app
            (op (U.isOpenEmbedding.functor.obj (⊤ : Opens U))))
        erw [Opens.isOpenEmbedding_obj_top U]
        exact hsections
      obtain ⟨y, hy⟩ :=
        CategoryTheory.Sheaf.H.longSequence_exact₁
          presUEx 0 1 rfl x (Subsingleton.elim _ _)
      obtain ⟨s, hs⟩ :=
        hsectionsU
          (CategoryTheory.Sheaf.H.equiv₀
            presU.X₃ Limits.isTerminalTop y)
      let z : presU.X₂.H 0 :=
        (CategoryTheory.Sheaf.H.equiv₀
          presU.X₂ Limits.isTerminalTop).symm s
      have hz :
          CategoryTheory.Sheaf.H.map presU.g 0 z = y := by
        apply (CategoryTheory.Sheaf.H.equiv₀
          presU.X₃ Limits.isTerminalTop).injective
        have hzsection :
            CategoryTheory.Sheaf.H.equiv₀
                presU.X₂ Limits.isTerminalTop z = s := by
          exact AddEquiv.apply_symm_apply _ s
        exact
          (CategoryTheory.Sheaf.H.equiv₀_naturality
              Limits.isTerminalTop presU.g z).symm.trans
            ((congrArg
              (fun q => presU.g.hom.app
                (op (⊤ : Opens U)) q) hzsection).trans hs)
      rw [← hy, ← hz]
      exact CategoryTheory.Sheaf.H.longSequence_comp_zero₃
        presUEx 0 1 rfl z
  | succ n hn =>
      refine subsingleton_of_forall_eq 0 fun x => ?_
      let pres := (EnoughInjectives.presentation F).some.shortComplex
      have presEx : pres.ShortExact :=
        (EnoughInjectives.presentation F).some.shortExact_shortComplex
      let presU := pres.map (restrict AddCommGrpCat.{u} U.isOpenEmbedding)
      have presUEx : presU.ShortExact :=
        presEx.map_of_exact _
      letI : presU.X₂.IsFlasque :=
        restrict_isFlasque_of_injective U pres.X₂
      have hC' : Subsingleton (pres.X₃.H' (n + 1) U) := by
        refine subsingleton_of_forall_eq 0 fun y => ?_
        obtain ⟨z, hz⟩ :=
          Abelian.Ext.covariant_sequence_exact₃
            (freeAbSheaf U) presEx y rfl (hF.elim _ _)
        rw [← hz, Abelian.Ext.eq_zero_of_injective z]
        exact Abelian.Ext.zero_comp
          (freeAbSheaf U) (n + 1)
          (Abelian.Ext.mk₀ pres.g) (n + 1) (add_zero _)
      have hC : Subsingleton (presU.X₃.H (n + 1)) :=
        hn pres.X₃ hC'
      obtain ⟨y, hy⟩ :=
        CategoryTheory.Sheaf.H.longSequence_exact₁
          presUEx (n + 1) (n + 2) rfl x
          (Subsingleton.elim _ _)
      rw [← hy, hC.elim y 0]
      exact map_zero _

/--
For positive degrees, objectwise site cohomology on an open and global
cohomology of the restricted sheaf vanish simultaneously.
-/
theorem subsingleton_H'_iff_subsingleton_restrict_H
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H' F (n + 1) U) ↔
      Subsingleton
        (CategoryTheory.Sheaf.H
          ((restrict AddCommGrpCat.{u} U.isOpenEmbedding).obj F) (n + 1)) :=
  ⟨subsingleton_restrict_H_of_subsingleton_H' F U n,
    subsingleton_H'_of_subsingleton_restrict_H F U n⟩

end

end OpenCohomology

end TopCat.Sheaf
