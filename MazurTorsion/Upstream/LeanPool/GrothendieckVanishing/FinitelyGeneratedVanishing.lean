/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import MazurTorsion.Upstream.LeanPool.GrothendieckVanishing.PresheafFilteredColimit
import MazurTorsion.Upstream.LeanPool.GrothendieckVanishing.ClosedImmersionCohomology
import MazurTorsion.Upstream.LeanPool.GrothendieckVanishing.GeneratedSubsheaf

/-!
# Finitely generated vanishing reduction

On a Noetherian space, every sheaf is the filtered colimit of its finitely generated
subsheaves, and sheaf cohomology commutes with filtered colimits. Combining the two
reduces vanishing of `Hⁿ` for arbitrary sheaves to vanishing for finitely generated ones.
This file packages that reduction; together with the Noetherian-shrinking step, it
underlies the irreducible positive-dimensional case of Grothendieck vanishing.

## Main definitions

* `finsetGenFunctor` — the filtered diagram of finitely generated subsheaves.
* `finsetGenCocone`, `finsetGenCoconeIsColimit` — exhibits `K` as the colimit.

## Main results

* `cohomology_vanishing_of_finitelyGenerated_vanishing` — vanishing for f.g. subsheaves
  propagates to the whole sheaf via the filtered-colimit comparison.
* `finsetGeneratedSheaf_vanishing` — `Finset.induction` reducing vanishing for finitely
  generated subsheaves to vanishing for the epi-images of `zeroOutsideInt V`.
* `directLimit_cohomology_vanishing` — composes both above into the headline reduction.

The `isFlasque_filtered_colimit` and `sheafHPreservesFilteredColimits` building blocks
live in the `PresheafFilteredColimit` modules.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram

variable {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

omit [NoetherianSpace X] in
/-- The canonical inclusion of an abelian image in the opaque topological-sheaf
category is monic.  This typed bridge keeps downstream functoriality proofs from
having to unfold `TopCat.Sheaf` during typeclass search. -/
private theorem sheafAbelianImage_ι_mono
    {A B : TopCat.Sheaf AddCommGrpCat.{u} X} (f : A ⟶ B) :
    Mono (Abelian.image.ι f) := by
  change Mono (kernel.ι (cokernel.π f))
  infer_instance

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
noncomputable def finsetGenFunctor :
    Finset
        (TopCat.Presheaf.SectionIndex K) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := TopCat.Presheaf.finsetGeneratedSheaf hK S
  map h := TopCat.Presheaf.finsetImageInclGen hK h.le
  map_id S := by
    letI := sheafAbelianImage_ι_mono
      (TopCat.Presheaf.finsetGeneratorMap hK S)
    apply (cancel_mono (Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S))).1
    exact (TopCat.Presheaf.finsetImageInclGen_comp_ι hK (le_refl S)).trans
      (Category.id_comp _).symm
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    letI := sheafAbelianImage_ι_mono
      (TopCat.Presheaf.finsetGeneratorMap hK S₃)
    apply (cancel_mono (Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₃))).1
    calc
      TopCat.Presheaf.finsetImageInclGen hK (h₁ ≫ h₂).le ≫
            Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₃) =
          Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₁) :=
        TopCat.Presheaf.finsetImageInclGen_comp_ι hK (h₁ ≫ h₂).le
      _ = TopCat.Presheaf.finsetImageInclGen hK h₁.le ≫
            Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₂) :=
        (TopCat.Presheaf.finsetImageInclGen_comp_ι hK h₁.le).symm
      _ = TopCat.Presheaf.finsetImageInclGen hK h₁.le ≫
            (TopCat.Presheaf.finsetImageInclGen hK h₂.le ≫
              Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₃)) :=
        congrArg (fun e ↦ TopCat.Presheaf.finsetImageInclGen hK h₁.le ≫ e)
          (TopCat.Presheaf.finsetImageInclGen_comp_ι hK h₂.le).symm
      _ = (TopCat.Presheaf.finsetImageInclGen hK h₁.le ≫
              TopCat.Presheaf.finsetImageInclGen hK h₂.le) ≫
            Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₃) :=
        (Category.assoc _ _ _).symm

/-- Cocone with vertex `K`: the cocone maps are `image.ι : finsetGeneratedSheaf S ⟶ K`. -/
noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor hK) :=
  Cocone.mk (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    { app := fun S ↦ Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S)
      naturality := fun S S' h ↦ by
        change TopCat.Presheaf.finsetImageInclGen hK h.le ≫
            Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S') =
          Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S) ≫
            𝟙 (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
        rw [TopCat.Presheaf.finsetImageInclGen_comp_ι]
        exact (Category.comp_id _).symm }

omit [NoetherianSpace X] in
private theorem finsetGenCocone_ι_app (S : Finset
    (TopCat.Presheaf.SectionIndex K)) :
    (finsetGenCocone hK).ι.app S =
      Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S) := rfl

omit [NoetherianSpace X] in
private theorem allSectionMap_ι (σ : TopCat.Presheaf.SectionIndex K) :
    Sigma.ι (fun τ : TopCat.Presheaf.SectionIndex K ↦
        TopCat.Sheaf.zeroOutsideInt τ.1) σ ≫
      TopCat.Presheaf.allSectionMap hK =
        TopCat.Sheaf.zeroOutsideInt.sHom
          (F := (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) σ.2 := by
  exact Sigma.ι_desc _ _

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
noncomputable def finsetGenCoconeIsColimit :
    IsColimit (finsetGenCocone hK) := by
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d : colimit (finsetGenFunctor hK) ⟶
      (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) :=
    colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  haveI hd_mono : Mono d := by
    haveI : IsConnected
        (Finset (TopCat.Presheaf.SectionIndex K)) := IsFiltered.isConnected _
    haveI : ∀ j, Mono ((finsetGenCocone hK).ι.app j) := fun j ↦
      sheafAbelianImage_ι_mono (TopCat.Presheaf.finsetGeneratorMap hK j)
    haveI := NatTrans.mono_of_mono_app (finsetGenCocone hK).ι
    exact colim.map_mono' (finsetGenCocone hK).ι (colimit.isColimit _)
      (isColimitConstCocone _ _) d (fun j ↦ by
        change colimit.ι (finsetGenFunctor hK) j ≫
            colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK) =
          (finsetGenCocone hK).ι.app j
        exact colimit.ι_desc (finsetGenCocone hK) j)
  -- desc is epi: allSectionMap K factors through desc
  haveI hd_epi : Epi d := by
    let g : (∐ fun σ : TopCat.Presheaf.SectionIndex K ↦ TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor hK) :=
      Sigma.desc fun σ ↦
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          Abelian.factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
          colimit.ι (finsetGenFunctor hK) {σ}
    have hfac : g ≫ d = TopCat.Presheaf.allSectionMap hK := by
      ext σ
      have hgσ :
          Sigma.ι (fun τ : TopCat.Presheaf.SectionIndex K ↦
              TopCat.Sheaf.zeroOutsideInt τ.1) σ ≫ g =
            Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
                TopCat.Sheaf.zeroOutsideInt τ.1.1)
                ⟨σ, Finset.mem_singleton_self σ⟩ ≫
              Abelian.factorThruImage
                (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
              colimit.ι (finsetGenFunctor hK) {σ} := by
        dsimp only [g]
        exact Sigma.ι_desc _ _
      have hdσ :
          colimit.ι (finsetGenFunctor hK) {σ} ≫ d =
            Abelian.image.ι
              (TopCat.Presheaf.finsetGeneratorMap hK {σ}) := by
        exact (show colimit.ι (finsetGenFunctor hK) {σ} ≫ d =
            (finsetGenCocone hK).ι.app {σ} by
          dsimp only [d]
          exact colimit.ι_desc (finsetGenCocone hK) {σ}).trans
            (finsetGenCocone_ι_app hK {σ})
      calc
        Sigma.ι (fun τ : TopCat.Presheaf.SectionIndex K ↦
              TopCat.Sheaf.zeroOutsideInt τ.1) σ ≫ (g ≫ d) =
            (Sigma.ι (fun τ : TopCat.Presheaf.SectionIndex K ↦
                TopCat.Sheaf.zeroOutsideInt τ.1) σ ≫ g) ≫ d :=
          (Category.assoc _ _ _).symm
        _ = (Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
                TopCat.Sheaf.zeroOutsideInt τ.1.1)
                ⟨σ, Finset.mem_singleton_self σ⟩ ≫
              Abelian.factorThruImage
                (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
              colimit.ι (finsetGenFunctor hK) {σ}) ≫ d :=
          congrArg (fun e ↦ e ≫ d) hgσ
        _ = Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
                TopCat.Sheaf.zeroOutsideInt τ.1.1)
                ⟨σ, Finset.mem_singleton_self σ⟩ ≫
              Abelian.factorThruImage
                (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
              (colimit.ι (finsetGenFunctor hK) {σ} ≫ d) := by
          exact (Category.assoc _ _ _).trans
            (congrArg (fun e ↦ Sigma.ι
              (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
                TopCat.Sheaf.zeroOutsideInt τ.1.1)
                ⟨σ, Finset.mem_singleton_self σ⟩ ≫ e)
              (Category.assoc _ _ _))
        _ = Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
                TopCat.Sheaf.zeroOutsideInt τ.1.1)
                ⟨σ, Finset.mem_singleton_self σ⟩ ≫
              Abelian.factorThruImage
                (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
              Abelian.image.ι
                (TopCat.Presheaf.finsetGeneratorMap hK {σ}) :=
          congrArg (fun e ↦ Sigma.ι
            (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
              TopCat.Sheaf.zeroOutsideInt τ.1.1)
              ⟨σ, Finset.mem_singleton_self σ⟩ ≫
            Abelian.factorThruImage
              (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫ e)
            hdσ
        _ = Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
                TopCat.Sheaf.zeroOutsideInt τ.1.1)
                ⟨σ, Finset.mem_singleton_self σ⟩ ≫
              TopCat.Presheaf.finsetGeneratorMap hK {σ} :=
          congrArg (fun e ↦ Sigma.ι
            (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
              TopCat.Sheaf.zeroOutsideInt τ.1.1)
              ⟨σ, Finset.mem_singleton_self σ⟩ ≫ e)
            (Abelian.image.fac (TopCat.Presheaf.finsetGeneratorMap hK {σ}))
        _ = TopCat.Sheaf.zeroOutsideInt.sHom
              (F := (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) σ.2 :=
          TopCat.Presheaf.finsetGeneratorMap_ι hK {σ}
            ⟨σ, Finset.mem_singleton_self σ⟩
        _ = Sigma.ι (fun τ : TopCat.Presheaf.SectionIndex K ↦
                TopCat.Sheaf.zeroOutsideInt τ.1) σ ≫
              TopCat.Presheaf.allSectionMap hK :=
          (allSectionMap_ι hK σ).symm
    exact @epi_of_epi_fac _ _ _ _ _ g d (TopCat.Presheaf.allSectionMap hK)
      (TopCat.Presheaf.allSectionMap_epi (F := K) hK) hfac
  -- mono + epi → iso in abelian category
  haveI : IsIso ((colimit.isColimit (finsetGenFunctor hK)).desc (finsetGenCocone hK)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor hK)).ofPointIso

end FilteredDiagram

/-- **Hartshorne III, Ex. 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. Uses the filtered-colimit comparison isomorphism
    for the diagram of finitely generated subsheaves and transports zero across it. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hfg : ∀ (S : Finset
        (TopCat.Presheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  have hZeroDiagram : IsZero (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m) := by
    refine Functor.isZero _ ?_
    intro S
    haveI : Subsingleton ↑((sheafCohomologyFunctor X m).obj
        (TopCat.Presheaf.finsetGeneratedSheaf hK S)) := by
      change Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m)
      exact hfg S
    change IsZero ((sheafCohomologyFunctor X m).obj
      (TopCat.Presheaf.finsetGeneratedSheaf hK S))
    exact AddCommGrpCat.isZero_of_subsingleton
      ((sheafCohomologyFunctor X m).obj
        (TopCat.Presheaf.finsetGeneratedSheaf hK S))
  have hZeroColim :
      IsZero (colimit (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m)) :=
    (colimit.isColimit _).isZero_pt hZeroDiagram
  have hZeroTarget :
      IsZero ((sheafCohomologyFunctor X m).obj
        (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
    change IsZero ((sheafCohomologyFunctor X m).obj (finsetGenCocone hK).pt)
    exact IsZero.of_iso hZeroColim
      (sheafHPreservesFilteredColimits
        (Y' := finsetGenFunctor hK)
        (c' := finsetGenCocone hK)
        (hc' := finsetGenCoconeIsColimit hK)
        m).symm
  have h := AddCommGrpCat.subsingleton_of_isZero hZeroTarget
  change Subsingleton (Sheaf.H
    (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) at h
  exact h

section FinsetGenerated

variable {X : TopCat.{u}} {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}}
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m))
    (S : Finset
      (TopCat.Presheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := by
  classical
  suffices h : ∀ (T : Finset (TopCat.Presheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK T) m) from h S
  intro T; induction T using Finset.induction with
  | empty =>
    let G := fun σ : {σ // σ ∈ (∅ : Finset (TopCat.Presheaf.SectionIndex K))} ↦
      TopCat.Sheaf.zeroOutsideInt σ.1.1
    have hG : IsZero (Discrete.functor G) := by
      refine Functor.isZero _ ?_
      intro j
      exact (by cases j.as.2)
    have hcoprod : IsZero (∐ G) := (coproductIsCoproduct G).isZero_pt hG
    haveI : Epi (Abelian.factorThruImage
        (TopCat.Presheaf.finsetGeneratorMap hK ∅)) :=
      Abelian.instEpiFactorThruImage
        (C := TopCat.Sheaf AddCommGrpCat.{u} X)
        (TopCat.Presheaf.finsetGeneratorMap hK ∅)
    exact sheafH_subsingleton_of_isZero
      (IsZero.of_epi
        (Abelian.factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK ∅)) hcoprod) m
  | @insert σ₀ S' _ ih =>
    let h_sub := Finset.subset_insert σ₀ S'
    let f := TopCat.Presheaf.finsetImageInclGen hK h_sub
    let qIns := Abelian.factorThruImage
      (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))
    let qS := Abelian.factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK S')
    let g : TopCat.Sheaf.zeroOutsideInt σ₀.1 ⟶ cokernel f :=
      Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫ qIns ≫ cokernel.π f
    haveI : Epi qIns := by
      dsimp only [qIns]
      exact Abelian.instEpiFactorThruImage
        (C := TopCat.Sheaf AddCommGrpCat.{u} X)
        (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))
    haveI : Epi (qIns ≫ cokernel.π f) := epi_comp _ _
    haveI : Epi g := by
      refine epi_of_epi_fac
        (f := Sigma.desc fun σ ↦ if h : σ.1 = σ₀ then eqToHom (by rw [h]) else 0)
        (h := qIns ≫ cokernel.π f) ?_
      ext ⟨σ, hσ⟩
      by_cases h : σ = σ₀
      · subst h
        rw [← Category.assoc, Sigma.ι_desc]
        simp [g]
      · rw [← Category.assoc, Sigma.ι_desc, dif_neg h, zero_comp]
        have hfacBase :
            TopCat.Presheaf.finsetCoproductInclGen h_sub ≫ qIns = qS ≫ f := by
          letI := sheafAbelianImage_ι_mono
            (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))
          apply (cancel_mono (Abelian.image.ι
            (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')))).1
          dsimp only [qIns, qS, f]
          calc
            (TopCat.Presheaf.finsetCoproductInclGen h_sub ≫
                Abelian.factorThruImage
                  (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))) ≫
                Abelian.image.ι
                  (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')) =
              TopCat.Presheaf.finsetCoproductInclGen h_sub ≫
                (Abelian.factorThruImage
                    (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')) ≫
                  Abelian.image.ι
                    (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))) :=
              Category.assoc _ _ _
            _ = TopCat.Presheaf.finsetCoproductInclGen h_sub ≫
                  TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S') :=
              congrArg (fun e ↦ TopCat.Presheaf.finsetCoproductInclGen h_sub ≫ e)
                (Abelian.image.fac
                  (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')))
            _ = TopCat.Presheaf.finsetGeneratorMap hK S' :=
              TopCat.Presheaf.finsetCoproductInclGen_comp_generatorMap hK h_sub
            _ = Abelian.factorThruImage
                  (TopCat.Presheaf.finsetGeneratorMap hK S') ≫
                Abelian.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S') :=
              (Abelian.image.fac (TopCat.Presheaf.finsetGeneratorMap hK S')).symm
            _ = Abelian.factorThruImage
                  (TopCat.Presheaf.finsetGeneratorMap hK S') ≫
                (TopCat.Presheaf.finsetImageInclGen hK h_sub ≫
                  Abelian.image.ι
                    (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))) :=
              congrArg (fun e ↦ Abelian.factorThruImage
                (TopCat.Presheaf.finsetGeneratorMap hK S') ≫ e)
                (TopCat.Presheaf.finsetImageInclGen_comp_ι hK h_sub).symm
            _ = (Abelian.factorThruImage
                    (TopCat.Presheaf.finsetGeneratorMap hK S') ≫
                  TopCat.Presheaf.finsetImageInclGen hK h_sub) ≫
                Abelian.image.ι
                  (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')) :=
              (Category.assoc _ _ _).symm
        have hfac' :=
          congrArg (fun e ↦ Sigma.ι
            (fun τ : {τ // τ ∈ S'} ↦ TopCat.Sheaf.zeroOutsideInt τ.1.1)
            ⟨σ, Finset.mem_of_mem_insert_of_ne hσ h⟩ ≫ e ≫ cokernel.π f) hfacBase
        have hzero_rhs :
            Sigma.ι
                (fun σ : {σ // σ ∈ insert σ₀ S'} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1)
                ⟨σ, hσ⟩ ≫ qIns ≫ cokernel.π f = 0 := by
          simpa [TopCat.Presheaf.finsetCoproductInclGen, Category.assoc, h,
            cokernel.condition, Sigma.ι_desc_assoc, Sigma.ι_desc] using hfac'
        exact hzero_rhs.symm
    exact subsingleton_sheafH_of_shortExact_middle f m ih <|
      hzero (cokernel f).property g.hom
        ((TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr inferInstance)

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) :=
  cohomology_vanishing_of_finitelyGenerated_vanishing hK m
    (fun S _ ↦ finsetGeneratedSheaf_vanishing hK m hzero S)
