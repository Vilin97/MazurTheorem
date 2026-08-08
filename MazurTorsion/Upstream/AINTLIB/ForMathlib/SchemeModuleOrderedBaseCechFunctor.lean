/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechBasic

/-!
# Functoriality of ordered base-linear Cech complexes

This file makes the ordered base-linear Cech complex functorial in the scheme module.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The degree-`n` term of the ordered base-linear Cech complex, functorially in the
scheme module. -/
noncomputable def orderedBaseCechObjectFunctor
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) :
    X.Modules ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
  baseModulePresheafFunctor π ⋙
    FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ⋙
    (CategoryTheory.evaluation ((FormalCoproduct.{u} X.Opens)ᵒᵖ)
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
        (op (orderedCechFormalObject U n))

@[simp]
theorem orderedBaseCechObjectFunctor_obj
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) (M : X.Modules) :
    (orderedBaseCechObjectFunctor π U n).obj M =
      orderedBaseCechObject π M U n :=
  rfl

instance orderedBaseCechObjectFunctor_additive
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) :
    (orderedBaseCechObjectFunctor π U n).Additive := by
  dsimp only [orderedBaseCechObjectFunctor]
  infer_instance

private theorem orderedBaseCechCoface_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    orderedBaseCechCoface π M U n k ≫
        (orderedBaseCechObjectFunctor π U (n + 1)).map f =
      (orderedBaseCechObjectFunctor π U n).map f ≫
        orderedBaseCechCoface π N U n k := by
  let E : (X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ⥤
      ((FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
        ModuleCat.{u} Γ(S, (⊤ : S.Opens))) :=
    FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))
  let α := E.map ((baseModulePresheafFunctor π).map f)
  exact α.naturality (orderedCechFace U n k).op

private theorem orderedBaseCechDifferential_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechDifferential π M U n ≫
        (orderedBaseCechObjectFunctor π U (n + 1)).map f =
      (orderedBaseCechObjectFunctor π U n).map f ≫
        orderedBaseCechDifferential π N U n := by
  let fn : orderedBaseCechObject π M U n ⟶
      orderedBaseCechObject π N U n :=
    (orderedBaseCechObjectFunctor π U n).map f
  let fn1 : orderedBaseCechObject π M U (n + 1) ⟶
      orderedBaseCechObject π N U (n + 1) :=
    (orderedBaseCechObjectFunctor π U (n + 1)).map f
  change orderedBaseCechDifferential π M U n ≫ fn1 =
    fn ≫ orderedBaseCechDifferential π N U n
  have hface (k : Fin (n + 2)) :
      orderedBaseCechCoface π M U n k ≫ fn1 =
        fn ≫ orderedBaseCechCoface π N U n k :=
    orderedBaseCechCoface_naturality π f U n k
  have hterm (k : Fin (n + 2)) :
      ((-1 : ℤ) ^ (k : ℕ) • orderedBaseCechCoface π M U n k) ≫ fn1 =
        fn ≫ ((-1 : ℤ) ^ (k : ℕ) •
          orderedBaseCechCoface π N U n k) := by
    calc
      _ = (-1 : ℤ) ^ (k : ℕ) •
          (orderedBaseCechCoface π M U n k ≫ fn1) :=
        Preadditive.zsmul_comp _ _ _
      _ = (-1 : ℤ) ^ (k : ℕ) •
          (fn ≫ orderedBaseCechCoface π N U n k) :=
        congrArg (fun q ↦ (-1 : ℤ) ^ (k : ℕ) • q) (hface k)
      _ = _ := (Preadditive.comp_zsmul _ _ _).symm
  change
    (∑ k : Fin (n + 2),
        (-1 : ℤ) ^ (k : ℕ) • orderedBaseCechCoface π M U n k) ≫ fn1 =
      fn ≫ ∑ k : Fin (n + 2),
        (-1 : ℤ) ^ (k : ℕ) • orderedBaseCechCoface π N U n k
  calc
    _ = ∑ k : Fin (n + 2),
        ((-1 : ℤ) ^ (k : ℕ) • orderedBaseCechCoface π M U n k) ≫ fn1 :=
      Preadditive.sum_comp Finset.univ _ _
    _ = ∑ k : Fin (n + 2),
        fn ≫ ((-1 : ℤ) ^ (k : ℕ) • orderedBaseCechCoface π N U n k) :=
      Finset.sum_congr rfl fun k _ ↦ hterm k
    _ = _ := (Preadditive.comp_sum Finset.univ _ _).symm

private noncomputable def orderedBaseCechComplexMap
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedBaseCechComplex π M U ⟶ orderedBaseCechComplex π N U :=
  CochainComplex.ofHom
    (fun n ↦ (orderedBaseCechObjectFunctor π U n).map f)
    (fun n ↦ by
      rw [orderedBaseCechComplex_d, orderedBaseCechComplex_d]
      exact (orderedBaseCechDifferential_naturality π f U n).symm)

/-- The ordered base-linear Cech complex, functorially in the scheme module. -/
noncomputable def orderedBaseCechComplexFunctor
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) ℕ where
  obj M := orderedBaseCechComplex π M U
  map f := orderedBaseCechComplexMap π f U
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (orderedBaseCechObjectFunctor π U n).map (𝟙 M) = 𝟙 _
    exact (orderedBaseCechObjectFunctor π U n).map_id M
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (orderedBaseCechObjectFunctor π U n).map (f ≫ g) =
      (orderedBaseCechObjectFunctor π U n).map f ≫
        (orderedBaseCechObjectFunctor π U n).map g
    exact (orderedBaseCechObjectFunctor π U n).map_comp f g

@[simp]
theorem orderedBaseCechComplexFunctor_obj
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (M : X.Modules) :
    (orderedBaseCechComplexFunctor π U).obj M =
      orderedBaseCechComplex π M U :=
  rfl

instance orderedBaseCechComplexFunctor_additive
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) :
    (orderedBaseCechComplexFunctor π U).Additive where
  map_add := by
    intro M N f g
    apply HomologicalComplex.Hom.ext
    funext n
    change (orderedBaseCechObjectFunctor π U n).map (f + g) =
      (orderedBaseCechObjectFunctor π U n).map f +
        (orderedBaseCechObjectFunctor π U n).map g
    exact Functor.map_add _

instance orderedBaseCechComplexFunctor_preservesZeroMorphisms
    {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) :
    (orderedBaseCechComplexFunctor π U).PreservesZeroMorphisms where
  map_zero M N := by
    apply HomologicalComplex.Hom.ext
    funext n
    change Limits.Pi.map (fun _ ↦ 0) = 0
    refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Pi.map_π, comp_zero]
    exact CategoryTheory.Limits.zero_comp.symm

end

end AlgebraicGeometry.Scheme.Modules
