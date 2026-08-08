/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechExact
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechFunctor

/-!
# Exact sequences of ordered base-linear Cech complexes

This file proves that the ordered base-linear Cech complex on an affine family sends short exact
sequences of quasicoherent scheme modules to degreewise short exact sequences.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private noncomputable def orderedBaseCechFunctorXIsoPi
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    ((orderedBaseCechComplexFunctor π U).obj M).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : OrderedCechIndex ι n,
          ((baseModulePresheafFunctor π).obj M).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k)))) :=
  orderedBaseCechObjectIsoPi π M U n

@[simp]
private theorem orderedBaseCechFunctorXIsoPi_hom_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : ((orderedBaseCechComplexFunctor π U).obj M).X n)
    (i : OrderedCechIndex ι n) :
    (orderedBaseCechFunctorXIsoPi π M U n).hom x i =
      Pi.π (fun j : OrderedCechIndex ι n ↦
        ((baseModulePresheafFunctor π).obj M).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j.1 k)))) i x :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply _ i x

private theorem orderedBaseCechFunctorXIsoPi_hom_map_apply
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : ((orderedBaseCechComplexFunctor π U).obj M).X n)
    (i : OrderedCechIndex ι n) :
    (orderedBaseCechFunctorXIsoPi π N U n).hom
        (((orderedBaseCechComplexFunctor π U).map f).f n x) i =
      (((baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))))
        ((orderedBaseCechFunctorXIsoPi π M U n).hom x i) := by
  rw [orderedBaseCechFunctorXIsoPi_hom_apply,
    orderedBaseCechFunctorXIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : OrderedCechIndex ι n ↦
      ((baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j.1 k)))) i) x

/-- A short exact sequence of quasicoherent scheme modules remains short exact after taking its
ordered base-linear Cech complexes on an affine family. -/
theorem shortExact_map_orderedBaseCechComplex_of_affineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (T.map (orderedBaseCechComplexFunctor π U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (T.map (orderedBaseCechComplexFunctor π U)).map
    (HomologicalComplex.eval _ _ n)
  change A.ShortExact
  have hlocal (i : OrderedCechIndex ι n) :=
    shortExact_map_baseModulePresheaf_eval_of_isAffineOpen
      π hT (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))
      (IsAffineOpen.cechIntersection U hU n i.1)
  haveI : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (((orderedBaseCechComplexFunctor π U).map T.f).f n)
    intro x y hxy
    apply (ModuleCat.mono_iff_injective
      (orderedBaseCechFunctorXIsoPi π T.X₁ U n).hom).mp inferInstance
    funext i
    have hi := congrArg
      (fun z ↦ (orderedBaseCechFunctorXIsoPi π T.X₂ U n).hom z i) hxy
    rw [orderedBaseCechFunctorXIsoPi_hom_map_apply,
      orderedBaseCechFunctorXIsoPi_hom_map_apply] at hi
    exact (hlocal i).moduleCat_injective_f hi
  haveI : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (((orderedBaseCechComplexFunctor π U).map T.g).f n)
    intro y
    have preimage (i : OrderedCechIndex ι n) :
        ∃ x : ((baseModulePresheafFunctor π).obj T.X₂).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))),
          ((baseModulePresheafFunctor π).map T.g).app
              (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))) x =
            (orderedBaseCechFunctorXIsoPi π T.X₃ U n).hom y i :=
      (hlocal i).moduleCat_surjective_g _
    choose x hx using preimage
    let x' := (orderedBaseCechFunctorXIsoPi π T.X₂ U n).inv x
    refine ⟨x', ?_⟩
    apply (ModuleCat.mono_iff_injective
      (orderedBaseCechFunctorXIsoPi π T.X₃ U n).hom).mp inferInstance
    funext i
    rw [orderedBaseCechFunctorXIsoPi_hom_map_apply]
    have hx'i : (orderedBaseCechFunctorXIsoPi π T.X₂ U n).hom x' i = x i :=
      congrFun (Iso.inv_hom_id_apply
        (orderedBaseCechFunctorXIsoPi π T.X₂ U n) x) i
    rw [hx'i]
    exact hx i
  refine ShortComplex.ShortExact.mk ?_
  change ((T.map (orderedBaseCechComplexFunctor π U)).map
    (HomologicalComplex.eval _ _ n)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  change ((orderedBaseCechComplexFunctor π U).obj T.X₂).X n at y
  change (((orderedBaseCechComplexFunctor π U).map T.g).f n) y = 0 at hy
  have preimage (i : OrderedCechIndex ι n) :
      ∃ x : ((baseModulePresheafFunctor π).obj T.X₁).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))),
        ((baseModulePresheafFunctor π).map T.f).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))) x =
          (orderedBaseCechFunctorXIsoPi π T.X₂ U n).hom y i := by
    have hyi :
        ((baseModulePresheafFunctor π).map T.g).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k)))
              ((orderedBaseCechFunctorXIsoPi π T.X₂ U n).hom y i) = 0 := by
      calc
        _ = (orderedBaseCechFunctorXIsoPi π T.X₃ U n).hom
            (((orderedBaseCechComplexFunctor π U).map T.g).f n y) i :=
          (orderedBaseCechFunctorXIsoPi_hom_map_apply π T.g U n y i).symm
        _ = 0 := by rw [hy, map_zero]; rfl
    exact ((ShortComplex.moduleCat_exact_iff _).mp (hlocal i).exact) _ hyi
  choose x hx using preimage
  let x' := (orderedBaseCechFunctorXIsoPi π T.X₁ U n).inv x
  refine ⟨x', ?_⟩
  change (((orderedBaseCechComplexFunctor π U).map T.f).f n) x' = y
  apply (ModuleCat.mono_iff_injective
    (orderedBaseCechFunctorXIsoPi π T.X₂ U n).hom).mp inferInstance
  funext i
  rw [orderedBaseCechFunctorXIsoPi_hom_map_apply]
  have hx'i : (orderedBaseCechFunctorXIsoPi π T.X₁ U n).hom x' i = x i :=
    congrFun (Iso.inv_hom_id_apply
      (orderedBaseCechFunctorXIsoPi π T.X₁ U n) x) i
  rw [hx'i]
  exact hx i

end

end AlgebraicGeometry.Scheme.Modules
