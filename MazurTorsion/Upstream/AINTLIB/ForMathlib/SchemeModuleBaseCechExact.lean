/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechBasic
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechCochains
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineExact

/-!
# Exact sequences of base-linear Cech complexes

This file proves that a short exact sequence of quasicoherent scheme modules remains short exact
after taking base-linear sections over an affine open. The finite affine Cech-complex consequence
is assembled degreewise below.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private theorem affineGlobalSections_surjective_of_epi
    {Y : Scheme.{u}} [IsAffine Y]
    {M N : Y.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom := by
  rw [← (isoSpec Y).inv.opensRange_of_isIso,
    ← (isoSpec Y).inv.image_top_eq_opensRange]
  change Function.Surjective
    ((((restrictFunctor (isoSpec Y).inv).map f).val.app (op ⊤)).hom)
  exact moduleSpecGlobalSections_surjective_of_epi
    ((restrictFunctor (isoSpec Y).inv).map f)

private theorem affineOpenSections_surjective_of_epi
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op U)).hom := by
  letI : IsAffine U.toScheme := hU
  have h := affineGlobalSections_surjective_of_epi
    ((restrictFunctor U.ι).map f)
  change Function.Surjective
    (f.val.app (op (U.ι ''ᵁ (⊤ : U.toScheme.Opens)))).hom at h
  rw [U.ι_image_top] at h
  exact h

/-- A short exact sequence of quasicoherent scheme modules remains short exact after taking
base-linear sections over an affine open. -/
theorem shortExact_map_baseModulePresheaf_eval_of_isAffineOpen
    {X S : Scheme.{u}} (π : X ⟶ S)
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (T.map (baseModulePresheafFunctor π ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ
        (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))).ShortExact := by
  let A := T.map (baseModulePresheafFunctor π ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))
  let K := T.map (toSheaf X)
  have hK : K.ShortExact := hT.map_of_exact (toSheaf X)
  haveI : Mono T.f := hT.mono_f
  haveI : Epi T.g := hT.epi_g
  haveI : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (K.f.hom.app (op U)).hom
    haveI : Mono K.f := hK.mono_f
    haveI : Mono K.f.hom := by
      change Mono ((TopCat.Sheaf.forget AddCommGrpCat X).map K.f)
      infer_instance
    haveI : Mono (K.f.hom.app (op U)) := by infer_instance
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  haveI : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    exact affineOpenSections_surjective_of_epi U hU T.g
  refine ShortComplex.ShortExact.mk ?_
  change A.Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  have hy' : K.g.hom.app (op U) y = 0 := hy
  obtain ⟨x, hx⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (U := U) hK.exact hK.mono_f y hy'
  exact ⟨x, hx⟩

private noncomputable def baseCechFunctorXIsoPi
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    ((baseCechComplexFunctor π U).obj M).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : Fin (n + 1) → ι,
          ((baseModulePresheafFunctor π).obj M).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)))) :=
  ModuleCat.piIsoPi _

@[simp]
private theorem baseCechFunctorXIsoPi_hom_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : ((baseCechComplexFunctor π U).obj M).X n)
    (i : Fin (n + 1) → ι) :
    (baseCechFunctorXIsoPi π M U n).hom x i =
      Pi.π (fun j : Fin (n + 1) → ι ↦
        ((baseModulePresheafFunctor π).obj M).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k)))) i x :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply _ i x

private theorem baseCechFunctorXIsoPi_hom_map_apply
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : ((baseCechComplexFunctor π U).obj M).X n)
    (i : Fin (n + 1) → ι) :
    (baseCechFunctorXIsoPi π N U n).hom
        (((baseCechComplexFunctor π U).map f).f n x) i =
      (((baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))))
        ((baseCechFunctorXIsoPi π M U n).hom x i) := by
  rw [baseCechFunctorXIsoPi_hom_apply,
    baseCechFunctorXIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : Fin (n + 1) → ι ↦
      ((baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k)))) i) x

/-- A short exact sequence of quasicoherent scheme modules remains short exact after taking its
base-linear Cech complexes on a finite affine family. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.map_baseCechComplexFunctor_of_affine_openCover
    {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (T.map (baseCechComplexFunctor π U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (T.map (baseCechComplexFunctor π U)).map
    (HomologicalComplex.eval _ _ n)
  change A.ShortExact
  have hlocal (i : Fin (n + 1) → ι) :=
    shortExact_map_baseModulePresheaf_eval_of_isAffineOpen
      π hT (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))
      (IsAffineOpen.cechIntersection U hU n i)
  haveI : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (((baseCechComplexFunctor π U).map T.f).f n)
    intro x y hxy
    apply (ModuleCat.mono_iff_injective
      (baseCechFunctorXIsoPi π T.X₁ U n).hom).mp inferInstance
    funext i
    have hi := congrArg
      (fun z ↦ (baseCechFunctorXIsoPi π T.X₂ U n).hom z i) hxy
    rw [baseCechFunctorXIsoPi_hom_map_apply,
      baseCechFunctorXIsoPi_hom_map_apply] at hi
    exact (hlocal i).moduleCat_injective_f hi
  haveI : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (((baseCechComplexFunctor π U).map T.g).f n)
    intro y
    have preimage (i : Fin (n + 1) → ι) :
        ∃ x : ((baseModulePresheafFunctor π).obj T.X₂).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))),
          ((baseModulePresheafFunctor π).map T.g).app
              (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) x =
            (baseCechFunctorXIsoPi π T.X₃ U n).hom y i :=
      (hlocal i).moduleCat_surjective_g _
    choose x hx using preimage
    let x' := (baseCechFunctorXIsoPi π T.X₂ U n).inv x
    refine ⟨x', ?_⟩
    apply (ModuleCat.mono_iff_injective
      (baseCechFunctorXIsoPi π T.X₃ U n).hom).mp inferInstance
    funext i
    rw [baseCechFunctorXIsoPi_hom_map_apply]
    have hx'i : (baseCechFunctorXIsoPi π T.X₂ U n).hom x' i = x i :=
      congrFun (Iso.inv_hom_id_apply
        (baseCechFunctorXIsoPi π T.X₂ U n) x) i
    rw [hx'i]
    exact hx i
  refine ShortComplex.ShortExact.mk ?_
  change ((T.map (baseCechComplexFunctor π U)).map
    (HomologicalComplex.eval _ _ n)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  change ((baseCechComplexFunctor π U).obj T.X₂).X n at y
  change (((baseCechComplexFunctor π U).map T.g).f n) y = 0 at hy
  have preimage (i : Fin (n + 1) → ι) :
      ∃ x : ((baseModulePresheafFunctor π).obj T.X₁).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))),
        ((baseModulePresheafFunctor π).map T.f).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) x =
          (baseCechFunctorXIsoPi π T.X₂ U n).hom y i := by
    have hyi :
        ((baseModulePresheafFunctor π).map T.g).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)))
              ((baseCechFunctorXIsoPi π T.X₂ U n).hom y i) = 0 := by
      calc
        _ = (baseCechFunctorXIsoPi π T.X₃ U n).hom
            (((baseCechComplexFunctor π U).map T.g).f n y) i :=
          (baseCechFunctorXIsoPi_hom_map_apply π T.g U n y i).symm
        _ = 0 := by rw [hy, map_zero]; rfl
    exact ((ShortComplex.moduleCat_exact_iff _).mp (hlocal i).exact) _ hyi
  choose x hx using preimage
  let x' := (baseCechFunctorXIsoPi π T.X₁ U n).inv x
  refine ⟨x', ?_⟩
  change (((baseCechComplexFunctor π U).map T.f).f n) x' = y
  apply (ModuleCat.mono_iff_injective
    (baseCechFunctorXIsoPi π T.X₂ U n).hom).mp inferInstance
  funext i
  rw [baseCechFunctorXIsoPi_hom_map_apply]
  have hx'i : (baseCechFunctorXIsoPi π T.X₁ U n).hom x' i = x i :=
    congrFun (Iso.inv_hom_id_apply
      (baseCechFunctorXIsoPi π T.X₁ U n) x) i
  rw [hx'i]
  exact hx i

end

end AlgebraicGeometry.Scheme.Modules
