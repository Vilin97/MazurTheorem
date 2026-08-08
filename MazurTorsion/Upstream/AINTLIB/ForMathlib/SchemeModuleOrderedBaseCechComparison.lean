/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCech
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechBasic

/-!
# Comparison with the native Cech complex

This file defines the canonical projection from the native all-tuples Cech complex to the
bounded complex indexed by strictly increasing tuples. Degreewise, this projection is a split
epimorphism: its section extends an ordered tuple family by zero on non-increasing tuples.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The ordered intersection family includes in the all-tuples intersection family. -/
private noncomputable def orderedCechFormalInclusion {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedCechFormalObject U n ⟶
      (FormalCoproduct.mk _ U).power (Fin (n + 1)) where
  f i := i.1
  φ _ := 𝟙 _

private theorem orderedCechFace_comp_formalInclusion {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    orderedCechFace U n k ≫ orderedCechFormalInclusion U n =
      orderedCechFormalInclusion U (n + 1) ≫
        (FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun := by
  apply FormalCoproduct.hom_ext rfl
  intro i
  exact Subsingleton.elim _ _

/-- A native Cech coface before taking the alternating sum. -/
noncomputable def baseCechCoface {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    (baseCechComplex π M U).X n ⟶ (baseCechComplex π M U).X (n + 1) :=
  ((FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ U).cech).obj (baseModulePresheaf π M)).δ k

theorem baseCechCoface_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    baseCechCoface π M U n k ≫
        Pi.π (fun j : Fin (n + 2) → ι =>
          baseCechFactor π M U (n + 1) j) i =
      Pi.π (fun j : Fin (n + 1) → ι =>
        baseCechFactor π M U n j)
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op := by
  change (Pi.lift fun j : Fin (n + 2) → ι =>
      Pi.π (fun l : Fin (n + 1) → ι =>
        baseCechFactor π M U n l)
          (j ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ j).op) ≫ _ = _
  exact Pi.lift_π _ i

/-- Projection from all tuple components to strictly increasing components. -/
noncomputable def baseCechToOrderedF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex π M U).X n ⟶ orderedBaseCechObject π M U n :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
      (baseModulePresheaf π M)).map (orderedCechFormalInclusion U n).op

private theorem baseCechCoface_comp_baseCechToOrderedF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    baseCechCoface π M U n k ≫ baseCechToOrderedF π M U (n + 1) =
      baseCechToOrderedF π M U n ≫ orderedBaseCechCoface π M U n k := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} Γ(S, (⊤ : S.Opens)) :=
    ((FormalCoproduct.evalOp.{u} X.Opens
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj
        (baseModulePresheaf π M))
  change F.map ((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).op ≫
      F.map (orderedCechFormalInclusion U (n + 1)).op =
    F.map (orderedCechFormalInclusion U n).op ≫
      F.map (orderedCechFace U n k).op
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
    orderedCechFace_comp_formalInclusion U n k]

theorem baseCechComplex_d_eq_sum_cofaces
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex π M U).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        baseCechCoface π M U n k := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj
      (baseModulePresheaf π M)).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ n).trans rfl

theorem baseCechComplex_d_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) :
    (baseCechComplex π M U).d n (n + 1) ≫
        Pi.π (fun j : Fin (n + 2) → ι =>
          baseCechFactor π M U (n + 1) j) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π M U n j)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) := by
  let p : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) j) i
  change (baseCechComplex π M U).d n (n + 1) ≫ p = _
  rw [baseCechComplex_d_eq_sum_cofaces, sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsmul_comp, baseCechCoface_comp_π]
  rfl

theorem baseCechComplex_d_comp_baseCechToOrderedF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex π M U).d n (n + 1) ≫
        baseCechToOrderedF π M U (n + 1) =
      baseCechToOrderedF π M U n ≫
        orderedBaseCechDifferential π M U n := by
  rw [baseCechComplex_d_eq_sum_cofaces,
    orderedBaseCechDifferential, sum_comp, comp_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zsmul_comp, comp_zsmul,
    baseCechCoface_comp_baseCechToOrderedF]

/-- The canonical projection from native Cech cochains to ordered Cech cochains. -/
noncomputable def baseCechToOrdered
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    baseCechComplex π M U ⟶ orderedBaseCechComplex π M U :=
  CochainComplex.ofHom (baseCechToOrderedF π M U) fun n => by
    rw [orderedBaseCechComplex_d]
    exact (baseCechComplex_d_comp_baseCechToOrderedF π M U n).symm

@[simp]
private theorem baseCechToOrdered_f
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (baseCechToOrdered π M U).f n = baseCechToOrderedF π M U n :=
  rfl

/-- Restriction of an all-tuples family to strictly increasing tuples. -/
private noncomputable def baseCechPiToOrderedLinearMap
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (∀ i : Fin (n + 1) → ι, baseCechFactor π M U n i) →ₗ[Γ(S, (⊤ : S.Opens))]
      orderedBaseCechTerm π M U n :=
  LinearMap.pi fun i => LinearMap.proj i.1

/-- Extend a dependent family on a subtype by zero. -/
private noncomputable def piSubtypeZeroExtend
    {R I : Type u} [Semiring R] (p : I → Prop) [DecidablePred p]
    (Z : I → Type u) [∀ i, AddCommMonoid (Z i)] [∀ i, Module R (Z i)] :
    (∀ i : Subtype p, Z i.1) →ₗ[R] ∀ i, Z i where
  toFun x i := if h : p i then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    by_cases h : p i <;> simp [h]
  map_smul' r x := by
    funext i
    by_cases h : p i <;> simp [h]

private theorem piSubtypeRestriction_comp_zeroExtend
    {R I : Type u} [Semiring R] (p : I → Prop) [DecidablePred p]
    (Z : I → Type u) [∀ i, AddCommMonoid (Z i)] [∀ i, Module R (Z i)] :
    (LinearMap.pi fun i : Subtype p =>
      (LinearMap.proj i.1 : (∀ i, Z i) →ₗ[R] Z i.1)).comp
        (piSubtypeZeroExtend p Z) = LinearMap.id := by
  ext x i
  simp [piSubtypeZeroExtend, i.2]

/-- Extend an ordered family by zero on tuples that are not strictly increasing. -/
noncomputable def orderedBaseCechZeroExtendLinearMap
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechTerm π M U n →ₗ[Γ(S, (⊤ : S.Opens))]
      (∀ i : Fin (n + 1) → ι, baseCechFactor π M U n i) :=
  piSubtypeZeroExtend (fun i => StrictMono i)
    (fun i => baseCechFactor π M U n i)

private theorem baseCechPiToOrderedLinearMap_comp_zeroExtend
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (baseCechPiToOrderedLinearMap π M U n).comp
      (orderedBaseCechZeroExtendLinearMap π M U n) = LinearMap.id := by
  exact piSubtypeRestriction_comp_zeroExtend (fun i => StrictMono i)
    (fun i => baseCechFactor π M U n i)

theorem baseCechToOrderedF_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : OrderedCechIndex ι n) :
    baseCechToOrderedF π M U n ≫
        Pi.π (fun j : OrderedCechIndex ι n =>
          baseCechFactor π M U n j.1) i =
      Pi.π (fun j : Fin (n + 1) → ι =>
        baseCechFactor π M U n j) i.1 := by
  change (Pi.lift fun j : OrderedCechIndex ι n =>
      Pi.π (fun k : Fin (n + 1) → ι =>
        baseCechFactor π M U n k) j.1 ≫
          (baseModulePresheaf π M).map (𝟙 _).op) ≫ _ = _
  simp

theorem orderedBaseCechObjectIsoPi_hom_comp_proj
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : OrderedCechIndex ι n) :
    (orderedBaseCechObjectIsoPi π M U n).hom ≫
        ModuleCat.ofHom
          (LinearMap.proj i : orderedBaseCechTerm π M U n →ₗ[
            Γ(S, (⊤ : S.Opens))] baseCechFactor π M U n i.1) =
      Pi.π (fun j : OrderedCechIndex ι n =>
        baseCechFactor π M U n j.1) i := by
  change (ModuleCat.piIsoPi (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1)).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = _
  exact ModuleCat.piIsoPi_hom_ker_subtype _ i

theorem baseCechXIsoPi_inv_comp_proj
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechXIsoPi π M U n).inv ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π M U n j) i =
      ModuleCat.ofHom
        (LinearMap.proj i :
          (∀ j : Fin (n + 1) → ι, baseCechFactor π M U n j) →ₗ[
            Γ(S, (⊤ : S.Opens))] baseCechFactor π M U n i) := by
  exact ModuleCat.piIsoPi_inv_kernel_ι _ i

private theorem baseCechToOrderedF_concrete
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (baseCechXIsoPi π M U n).inv ≫ baseCechToOrderedF π M U n ≫
        (orderedBaseCechObjectIsoPi π M U n).hom =
      ModuleCat.ofHom (baseCechPiToOrderedLinearMap π M U n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hcomp :
      ((baseCechXIsoPi π M U n).inv ≫ baseCechToOrderedF π M U n ≫
          (orderedBaseCechObjectIsoPi π M U n).hom) ≫
          ModuleCat.ofHom (LinearMap.proj i) =
        ModuleCat.ofHom (baseCechPiToOrderedLinearMap π M U n) ≫
          ModuleCat.ofHom (LinearMap.proj i) := by
    simp only [Category.assoc]
    rw [orderedBaseCechObjectIsoPi_hom_comp_proj]
    rw [baseCechToOrderedF_comp_π]
    rw [baseCechXIsoPi_inv_comp_proj]
    ext y
    rfl
  exact ConcreteCategory.congr_hom hcomp x

/-- A degreewise section of the projection, obtained by zero extension. -/
noncomputable def orderedToBaseCechZeroExtensionF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedBaseCechObject π M U n ⟶ (baseCechComplex π M U).X n :=
  (orderedBaseCechObjectIsoPi π M U n).hom ≫
    ModuleCat.ofHom (orderedBaseCechZeroExtendLinearMap π M U n) ≫
      (baseCechXIsoPi π M U n).inv

theorem orderedToBaseCechZeroExtensionF_comp_baseCechToOrderedF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedToBaseCechZeroExtensionF π M U n ≫
      baseCechToOrderedF π M U n = 𝟙 _ := by
  apply (cancel_mono (orderedBaseCechObjectIsoPi π M U n).hom).1
  simp only [orderedToBaseCechZeroExtensionF, Category.id_comp,
    Category.assoc]
  rw [baseCechToOrderedF_concrete]
  change (orderedBaseCechObjectIsoPi π M U n).hom ≫
      ModuleCat.ofHom ((baseCechPiToOrderedLinearMap π M U n).comp
        (orderedBaseCechZeroExtendLinearMap π M U n)) =
    (orderedBaseCechObjectIsoPi π M U n).hom
  rw [baseCechPiToOrderedLinearMap_comp_zeroExtend]
  simp

private instance baseCechToOrderedF_epi
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    Epi (baseCechToOrderedF π M U n) :=
  (SplitEpi.mk
    (orderedToBaseCechZeroExtensionF π M U n)
    (orderedToBaseCechZeroExtensionF_comp_baseCechToOrderedF π M U n)).epi

end

end AlgebraicGeometry.Scheme.Modules
