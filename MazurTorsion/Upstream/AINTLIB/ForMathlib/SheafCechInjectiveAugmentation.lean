/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechInjectiveBicomplex
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCohomologyExact
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafDerivedGlobalSections
import MazurTorsion.Upstream.AINTLIB.ForMathlib.TopCatSheafRestrict
import MazurTorsion.Upstream.AINTLIB.ForMathlib.TotalComplexUpNatVerticalEdge

/-!
# The Cech augmentation into an injective resolution

Apply the native Cech functor to the augmentation of the chosen injective
resolution and record the low-column exactness used by the vertical total edge.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

private abbrev sectionsAt (V : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  (CategoryTheory.sheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (Opposite.op V)

private noncomputable instance sectionsAt_preservesFiniteLimits (V : Opens X) :
    PreservesFiniteLimits (sectionsAt V) := by
  letI : PreservesFiniteLimits
      (CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  change PreservesFiniteLimits
    (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V))
  exact comp_preservesFiniteLimits _ _

private theorem cechCochainAddEquiv_map_apply
    {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) (p : ℕ)
    (x : ((cechComplexFunctor U).obj P).X p)
    (i : Fin (p + 1) → ι) :
    cechCochainAddEquiv Q U p (((cechComplexFunctor U).map f).f p x) i =
      f.app (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
        (cechCochainAddEquiv P U p x i) := by
  rw [cechCochainAddEquiv_apply, cechCochainAddEquiv_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : Fin (p + 1) → ι ↦
      f.app (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i) x

private theorem injectiveResolution_augmentation_app_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app (Opposite.op V) ≫
      ((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V) = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  have h : (I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom = 0 :=
    congrArg (fun f ↦ f.hom) I.ι_f_zero_comp_complex_d
  change ((I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom).app _ = 0
  exact (congr_app h _).trans rfl

private theorem injectiveResolution_augmentation_app_exact
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    (ShortComplex.mk
      (((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app (Opposite.op V))
      (((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V))
      (injectiveResolution_augmentation_app_comp_d F V)).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit
    (I.kernelFork.mapIsLimit I.isLimitKernelFork (sectionsAt V)) ?_
  apply Fork.ext (Iso.refl _)

/-- The native Cech map induced by the augmentation into the chosen injective
resolution. -/
private noncomputable def cechInjectiveResolutionAugmentation
    (F : Sheaf AddCommGrpCat.{u} X) :
    (cechComplexFunctor U).obj F.obj ⟶
      (cechInjectiveResolutionBicomplex U F).X 0 :=
  (cechComplexFunctor U).map
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom

@[simp]
private theorem cechInjectiveResolutionAugmentation_f
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p =
      ((cechComplexFunctor U).map
        ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom).f p :=
  rfl

@[reassoc]
private theorem cechInjectiveResolutionAugmentation_f_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p ≫
      ((cechInjectiveResolutionBicomplex U F).d 0 1).f p = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  have h :
      (I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom = 0 := by
    exact congrArg (fun f ↦ f.hom)
      (InjectiveResolution.ι_f_zero_comp_complex_d I)
  change Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.ι.f 0).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) ≫
    Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.cocomplex.d 0 1).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) = 0
  rw [Limits.Pi.map_comp_map]
  refine Limits.Pi.hom_ext _ _ fun i ↦ ?_
  rw [Limits.Pi.map_π]
  have hi := congr_app h
    (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
  have hi' :
      (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) ≫
        (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) = 0 := by
    change ((I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom).app _ = 0
    exact hi.trans rfl
  rw [hi', comp_zero, zero_comp]

private noncomputable instance cechInjectiveResolutionAugmentation_f_mono
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    Mono ((cechInjectiveResolutionAugmentation U F).f p) := by
  change Mono (Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app
      (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))))
  infer_instance

/-- The augmented resolution column in every Cech degree is exact at resolution
degree zero. -/
private theorem cechInjectiveResolutionAugmentation_exact
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (ShortComplex.mk
      ((cechInjectiveResolutionAugmentation U F).f p)
      (((cechInjectiveResolutionBicomplex U F).d 0 1).f p)
      (cechInjectiveResolutionAugmentation_f_comp_d U F p)).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  have hy' :
      Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
        (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) y = 0 :=
    hy
  have preimage (i : Fin (p + 1) → ι) :
      ∃ x : F.obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))),
        (I.ι.f 0).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) x =
          Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 0).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y := by
    let V := ∏ᶜ fun k : Fin (p + 1) ↦ U (i k)
    have hyi :
        (I.cocomplex.d 0 1).hom.app (Opposite.op V)
          (Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 0).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y) = 0 := by
      have hmap := ConcreteCategory.congr_hom
        (Limits.Pi.map_π (fun j : Fin (p + 1) → ι ↦
          (I.cocomplex.d 0 1).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i) y
      calc
        _ = Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
              (I.cocomplex.X 1).obj.obj
                (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i
              (Limits.Pi.map (fun j : Fin (p + 1) → ι ↦
                (I.cocomplex.d 0 1).hom.app
                  (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) y) :=
          hmap.symm
        _ = 0 := by rw [hy', map_zero]
    exact ((ShortComplex.mk
      (((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app (Opposite.op V))
      (((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V))
      (injectiveResolution_augmentation_app_comp_d F V)).ab_exact_iff.mp
        (injectiveResolution_augmentation_app_exact F V)) _ hyi
  choose x hx using preimage
  let x' := (cechCochainAddEquiv F.obj U p).symm x
  refine ⟨x', ?_⟩
  apply (cechCochainAddEquiv (I.cocomplex.X 0).obj U p).injective
  funext i
  have hx'i : cechCochainAddEquiv F.obj U p x' i = x i := by
    simp [x']
  calc
    _ = (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
          (cechCochainAddEquiv F.obj U p x' i) := by
      change cechCochainAddEquiv (I.cocomplex.X 0).obj U p
          (((cechComplexFunctor U).map (I.ι.f 0).hom).f p x') i = _
      exact cechCochainAddEquiv_map_apply U (I.ι.f 0).hom p x' i
    _ = (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) (x i) := by
      rw [hx'i]
    _ = Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
        (I.cocomplex.X 0).obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y := hx i
    _ = _ := (cechCochainAddEquiv_apply (I.cocomplex.X 0).obj U p y i).symm

private theorem injectiveResolution_d_app_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    ((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V) ≫
      ((injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2).hom.app
        (Opposite.op V) = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  have h : (I.cocomplex.d 0 1).hom ≫ (I.cocomplex.d 1 2).hom = 0 :=
    congrArg (fun f ↦ f.hom) (I.complex_d_comp 0)
  change ((I.cocomplex.d 0 1).hom ≫ (I.cocomplex.d 1 2).hom).app _ = 0
  exact (congr_app h _).trans rfl

/-- If degree-one cohomology vanishes after restriction to an open, sections of
the cokernel of the injective-resolution augmentation lift on that open. -/
private theorem injectiveResolution_cokernel_app_surjective_of_subsingleton_H
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X)
    [Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat V.isOpenEmbedding).obj F) 1)] :
    Function.Surjective
      ((cokernel.π
        ((injectiveResolution (toSiteSheaf F)).ι.f 0)).hom.app
          (Opposite.op V)) := by
  let I := injectiveResolution (toSiteSheaf F)
  change Function.Surjective
    ((cokernel.π (I.ι.f 0)).hom.app (Opposite.op V))
  let S := ShortComplex.mk (I.ι.f 0) (cokernel.π (I.ι.f 0))
    (cokernel.condition (I.ι.f 0))
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (I.ι.f 0))
  let R := restrict AddCommGrpCat.{u} V.isOpenEmbedding
  haveI : R.Additive :=
    restrict_additive V.isOpenEmbedding
  have hR : R.PreservesZeroMorphisms :=
    { map_zero := fun _ _ ↦
        R.mapAddHom.map_zero }
  have hRlim : PreservesFiniteLimits R := by
    dsimp [R]
    exact restrict_preservesFiniteLimits V.isOpenEmbedding
  have hRcolim : PreservesFiniteColimits R := by
    dsimp [R]
    infer_instance
  change Function.Surjective (S.g.hom.app (Opposite.op V))
  let SV := @ShortComplex.map _ _ _ _ _ _ S R hR
  have hSV : SV.ShortExact := by
    exact @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ S hS R hR
      hRlim hRcolim
  have hH0 : Subsingleton (CategoryTheory.Sheaf.H (R.obj F) 1) := by
    dsimp [R]
    infer_instance
  have hH : Subsingleton (SV.X₁.H 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H (R.obj F) 1)
    exact hH0
  have htop := CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
    hSV isTerminalTop
  change Function.Surjective
    (S.g.hom.app (Opposite.op (V.isOpenEmbedding.functor.obj ⊤))) at htop
  rw [Opens.isOpenEmbedding_obj_top V] at htop
  exact htop

private noncomputable def injectiveResolutionAugmentationHom
    (F : Sheaf AddCommGrpCat.{u} X) :
    toSiteSheaf F ⟶
      (injectiveResolution (toSiteSheaf F)).cocomplex.X 0 :=
  (injectiveResolution (toSiteSheaf F)).ι.f 0

private theorem injectiveResolutionAugmentationHom_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) :
    injectiveResolutionAugmentationHom F ≫
      (injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1 = 0 := by
  exact (injectiveResolution (toSiteSheaf F)).ι_f_zero_comp_complex_d

private noncomputable def injectiveResolutionAugmentationShortComplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (injectiveResolutionAugmentationHom F)
    ((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1)
    (injectiveResolutionAugmentationHom_comp_d F)

private theorem injectiveResolutionAugmentationShortComplex_exact
    (F : Sheaf AddCommGrpCat.{u} X) :
    (injectiveResolutionAugmentationShortComplex F).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit I.isLimitKernelFork ?_
  apply Fork.ext (Iso.refl _)

private noncomputable def injectiveResolutionCokernelToOne
    (F : Sheaf AddCommGrpCat.{u} X) :
    cokernel (injectiveResolutionAugmentationShortComplex F).f ⟶
      (injectiveResolution (toSiteSheaf F)).cocomplex.X 1 :=
  cokernel.desc
    (injectiveResolutionAugmentationShortComplex F).f
    (injectiveResolutionAugmentationShortComplex F).g
    (injectiveResolutionAugmentationShortComplex F).zero

@[reassoc]
private theorem injectiveResolution_cokernel_π_comp_toOne
    (F : Sheaf AddCommGrpCat.{u} X) :
    cokernel.π (injectiveResolutionAugmentationShortComplex F).f ≫
      injectiveResolutionCokernelToOne F =
        (injectiveResolutionAugmentationShortComplex F).g := by
  exact cokernel.π_desc
    (injectiveResolutionAugmentationShortComplex F).f
    (injectiveResolutionAugmentationShortComplex F).g
    (injectiveResolutionAugmentationShortComplex F).zero

private noncomputable instance injectiveResolutionCokernelToOne_mono
    (F : Sheaf AddCommGrpCat.{u} X) :
    Mono (injectiveResolutionCokernelToOne F) := by
  exact ShortComplex.Exact.mono_cokernelDesc
    (injectiveResolutionAugmentationShortComplex_exact F)

private theorem injectiveResolutionCokernelToOne_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) :
    injectiveResolutionCokernelToOne F ≫
      (injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2 = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  let πc := cokernel.π (injectiveResolutionAugmentationShortComplex F).f
  apply (cancel_epi πc).1
  calc
    πc ≫ (injectiveResolutionCokernelToOne F ≫ I.cocomplex.d 1 2) =
        (πc ≫ injectiveResolutionCokernelToOne F) ≫ I.cocomplex.d 1 2 :=
      (Category.assoc _ _ _).symm
    _ = (injectiveResolutionAugmentationShortComplex F).g ≫
        I.cocomplex.d 1 2 := by
      exact congrArg (fun k ↦ k ≫ I.cocomplex.d 1 2)
        (injectiveResolution_cokernel_π_comp_toOne F)
    _ = 0 := by
      change I.cocomplex.d 0 1 ≫ I.cocomplex.d 1 2 = 0
      exact I.complex_d_comp 0
    _ = πc ≫ 0 := by
      symm
      exact comp_zero

private noncomputable def injectiveResolutionCokernelTail
    (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (injectiveResolutionCokernelToOne F)
    ((injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2)
    (injectiveResolutionCokernelToOne_comp_d F)

private theorem injectiveResolutionCokernelTail_exact
    (F : Sheaf AddCommGrpCat.{u} X) :
    (injectiveResolutionCokernelTail F).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  let S := ShortComplex.mk (I.cocomplex.d 0 1) (I.cocomplex.d 1 2)
    (I.complex_d_comp 0)
  let e : S ⟶ injectiveResolutionCokernelTail F :=
    { τ₁ := cokernel.π (injectiveResolutionAugmentationShortComplex F).f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        simpa [S, I, injectiveResolutionCokernelTail,
          injectiveResolutionAugmentationShortComplex] using
          (injectiveResolution_cokernel_π_comp_toOne F)
      comm₂₃ := by
        change (𝟙 _) ≫ I.cocomplex.d 1 2 =
          I.cocomplex.d 1 2 ≫ 𝟙 _
        simp }
  letI : Epi e.τ₁ := by
    dsimp [e]
    exact epi_of_isColimit_cofork (colimit.isColimit _)
  letI : IsIso e.τ₂ := by
    dsimp [e]
    exact CategoryTheory.IsIso.id _
  letI : IsIso e.τ₃ := by
    dsimp [e]
    exact CategoryTheory.IsIso.id _
  letI : Mono e.τ₃ := by
    infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono e).mp (I.exact_succ 0)

private theorem injectiveResolutionCokernelToOne_app_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    (injectiveResolutionCokernelToOne F).hom.app (Opposite.op V) ≫
      ((injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2).hom.app
        (Opposite.op V) = 0 := by
  have h := congrArg (fun f ↦ f.hom)
    (injectiveResolutionCokernelToOne_comp_d F)
  change ((injectiveResolutionCokernelToOne F).hom ≫
    ((injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2).hom).app _ = 0
  exact (congr_app h _).trans rfl

private theorem injectiveResolutionCokernelTail_app_exact
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    (ShortComplex.mk
      ((injectiveResolutionCokernelToOne F).hom.app (Opposite.op V))
      (((injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2).hom.app
        (Opposite.op V))
      (injectiveResolutionCokernelToOne_app_comp_d F V)).Exact := by
  letI : Mono (injectiveResolutionCokernelTail F).f := by
    change Mono (injectiveResolutionCokernelToOne F)
    exact injectiveResolutionCokernelToOne_mono F
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit
    (KernelFork.mapIsLimit _
      (injectiveResolutionCokernelTail_exact F).fIsKernel (sectionsAt V)) ?_
  apply Fork.ext (Iso.refl _)

/-- If degree-one cohomology vanishes after restriction to an open, evaluating an
injective resolution on that open is exact in resolution degree one. -/
private theorem injectiveResolution_app_exactAt_one_of_subsingleton_H
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X)
    [Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat V.isOpenEmbedding).obj F) 1)] :
    (ShortComplex.mk
      (((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V))
      (((injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2).hom.app
        (Opposite.op V))
      (injectiveResolution_d_app_comp_d F V)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨q, hq⟩ := (ShortComplex.mk
    ((injectiveResolutionCokernelToOne F).hom.app (Opposite.op V))
    (((injectiveResolution (toSiteSheaf F)).cocomplex.d 1 2).hom.app
      (Opposite.op V))
    (injectiveResolutionCokernelToOne_app_comp_d F V)).ab_exact_iff.mp
      (injectiveResolutionCokernelTail_app_exact F V) y hy
  have hq' :
      (injectiveResolutionCokernelToOne F).hom.app (Opposite.op V) q = y := hq
  obtain ⟨x, hx⟩ :=
    injectiveResolution_cokernel_app_surjective_of_subsingleton_H F V q
  refine ⟨x, ?_⟩
  have hπφ := congrArg (fun f ↦ f.hom)
    (injectiveResolution_cokernel_π_comp_toOne F)
  have hπφV := ConcreteCategory.congr_hom
    (congr_app hπφ (Opposite.op V)) x
  rw [← hq', ← hx]
  exact hπφV.symm

/-- If `H¹` vanishes on every intersection indexing a Cech degree, then the
injective-resolution column is exact in resolution degree one at that Cech
degree. -/
private theorem cechInjectiveResolutionBicomplex_column_exactAt_one
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ)
    (hH : ∀ i : Fin (p + 1) → ι,
      Subsingleton (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).isOpenEmbedding).obj F) 1)) :
    (ShortComplex.mk
      (((cechInjectiveResolutionBicomplex U F).d 0 1).f p)
      (((cechInjectiveResolutionBicomplex U F).d 1 2).f p)
      ((cechInjectiveResolutionBicomplex U F).d_f_comp_d_f 0 1 2 p)).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  have hy' :
      Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
        (I.cocomplex.d 1 2).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) y = 0 := hy
  have preimage (i : Fin (p + 1) → ι) :
      ∃ x : (I.cocomplex.X 0).obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))),
        (I.cocomplex.d 0 1).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) x =
          Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 1).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y := by
    let V := ∏ᶜ fun k : Fin (p + 1) ↦ U (i k)
    have hyi :
        (I.cocomplex.d 1 2).hom.app (Opposite.op V)
          (Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 1).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y) = 0 := by
      have hmap := ConcreteCategory.congr_hom
        (Limits.Pi.map_π (fun j : Fin (p + 1) → ι ↦
          (I.cocomplex.d 1 2).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i) y
      calc
        _ = Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
              (I.cocomplex.X 2).obj.obj
                (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i
              (Limits.Pi.map (fun j : Fin (p + 1) → ι ↦
                (I.cocomplex.d 1 2).hom.app
                  (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) y) :=
          hmap.symm
        _ = 0 := by rw [hy', map_zero]
    letI : Subsingleton (CategoryTheory.Sheaf.H
        ((restrict AddCommGrpCat V.isOpenEmbedding).obj F) 1) := hH i
    exact ((ShortComplex.mk
      ((I.cocomplex.d 0 1).hom.app (Opposite.op V))
      ((I.cocomplex.d 1 2).hom.app (Opposite.op V))
      (injectiveResolution_d_app_comp_d F V)).ab_exact_iff.mp
        (injectiveResolution_app_exactAt_one_of_subsingleton_H F V)) _ hyi
  choose x hx using preimage
  let x' := (cechCochainAddEquiv (I.cocomplex.X 0).obj U p).symm x
  refine ⟨x', ?_⟩
  apply (cechCochainAddEquiv (I.cocomplex.X 1).obj U p).injective
  funext i
  have hx'i : cechCochainAddEquiv (I.cocomplex.X 0).obj U p x' i = x i := by
    simp [x']
  calc
    _ = (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
          (cechCochainAddEquiv (I.cocomplex.X 0).obj U p x' i) := by
      change cechCochainAddEquiv (I.cocomplex.X 1).obj U p
          (((cechComplexFunctor U).map (I.cocomplex.d 0 1).hom).f p x') i = _
      exact cechCochainAddEquiv_map_apply U (I.cocomplex.d 0 1).hom p x' i
    _ = (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) (x i) := by
      rw [hx'i]
    _ = Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
        (I.cocomplex.X 1).obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y := hx i
    _ = _ := (cechCochainAddEquiv_apply (I.cocomplex.X 1).obj U p y i).symm

private theorem cechSingletonIntersection_eq (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 ↦ U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Limits.Pi.π (fun k : Fin 1 ↦ U (i k)) 0)
  · exact leOfHom (Limits.Pi.lift fun k : Fin 1 ↦ homOfLE (by
      rw [Subsingleton.elim k 0]))

/-- Vanishing of `H¹` on each member of the cover gives the resolution-degree-one
exactness required in Cech degree zero. -/
private theorem cechInjectiveResolutionBicomplex_column_zero_exactAt_one
    (F : Sheaf AddCommGrpCat.{u} X)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    (ShortComplex.mk
      (((cechInjectiveResolutionBicomplex U F).d 0 1).f 0)
      (((cechInjectiveResolutionBicomplex U F).d 1 2).f 0)
      ((cechInjectiveResolutionBicomplex U F).d_f_comp_d_f 0 1 2 0)).Exact := by
  apply cechInjectiveResolutionBicomplex_column_exactAt_one U F 0
  intro i
  rw [cechSingletonIntersection_eq U i]
  exact hH (i 0)

private theorem cechInjectiveResolutionAugmentation_comm
    (F : Sheaf AddCommGrpCat.{u} X) (p p' : ℕ)
    (_ : (ComplexShape.up ℕ).Rel p p') :
    (cechInjectiveResolutionAugmentation U F).f p ≫
        ((cechInjectiveResolutionBicomplex U F).X 0).d p p' =
      ((cechComplexFunctor U).obj F.obj).d p p' ≫
        (cechInjectiveResolutionAugmentation U F).f p' := by
  exact HomologicalComplex.Hom.comm
    (cechInjectiveResolutionAugmentation U F) p p'

/-- The Cech complex of a sheaf maps into the total Cech complex of its chosen
injective resolution by the vertical edge. -/
noncomputable def cechInjectiveResolutionVerticalEdge
    (F : Sheaf AddCommGrpCat.{u} X) :
    (cechComplexFunctor U).obj F.obj ⟶
      (cechInjectiveResolutionBicomplex U F).total (.up ℕ) :=
  (cechInjectiveResolutionBicomplex U F).totalUpNatVerticalEdge
    ((cechComplexFunctor U).obj F.obj)
    (fun p ↦ (cechInjectiveResolutionAugmentation U F).f p)
    (cechInjectiveResolutionAugmentation_comm U F)
    (cechInjectiveResolutionAugmentation_f_comp_d U F)

@[simp]
private theorem cechInjectiveResolutionVerticalEdge_f
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionVerticalEdge U F).f p =
      (cechInjectiveResolutionAugmentation U F).f p ≫
        (cechInjectiveResolutionBicomplex U F).ιTotal
          (.up ℕ) 0 p p (zero_add p) := by
  apply HomologicalComplex₂.totalUpNatVerticalEdge_f

/-- The total-complex map induced by a cochain map between the chosen
injective resolutions. -/
noncomputable def cechInjectiveResolutionTotalMap
    {F G : Sheaf AddCommGrpCat.{u} X}
    (phi : (injectiveResolution (toSiteSheaf F)).cocomplex ⟶
      (injectiveResolution (toSiteSheaf G)).cocomplex) :
    (cechInjectiveResolutionBicomplex U F).total (.up ℕ) ⟶
      (cechInjectiveResolutionBicomplex U G).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    (cechInjectiveResolutionBicomplexMap U phi) (.up ℕ)

/-- The vertical Cech edge commutes with a morphism between chosen injective
resolutions that lifts a morphism of sheaves. -/
theorem cechInjectiveResolutionVerticalEdge_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (phi : InjectiveResolution.Hom
      (injectiveResolution (toSiteSheaf F))
      (injectiveResolution (toSiteSheaf G)) f) :
    cechInjectiveResolutionVerticalEdge U F ≫
        cechInjectiveResolutionTotalMap U phi.hom =
      (cechComplexFunctor U).map f.hom ≫
        cechInjectiveResolutionVerticalEdge U G := by
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    cechInjectiveResolutionVerticalEdge_f,
    cechInjectiveResolutionVerticalEdge_f]
  rw [Category.assoc, cechInjectiveResolutionTotalMap,
    HomologicalComplex₂.ιTotal_map]
  simp only [← Category.assoc]
  congr 1
  change
    (((cechComplexFunctor U).map
          ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom) ≫
        (cechComplexFunctor U).map (phi.hom.f 0).hom).f p =
      (((cechComplexFunctor U).map f.hom ≫
          (cechComplexFunctor U).map
            ((injectiveResolution (toSiteSheaf G)).ι.f 0).hom).f p)
  let a := ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom
  let b := (phi.hom.f 0).hom
  let c := f.hom
  let d := ((injectiveResolution (toSiteSheaf G)).ι.f 0).hom
  have hphi : a ≫ b = c ≫ d :=
    congrArg (fun g ↦ g.hom) phi.ι_f_zero_comp_hom_f_zero
  have hmap :
      (cechComplexFunctor U).map a ≫ (cechComplexFunctor U).map b =
        (cechComplexFunctor U).map c ≫ (cechComplexFunctor U).map d :=
    ((cechComplexFunctor U).map_comp a b).symm.trans
      ((congrArg (cechComplexFunctor U).map hphi).trans
        ((cechComplexFunctor U).map_comp c d))
  exact congrArg (fun g ↦ g.f p) hmap

/-- If `H¹` vanishes on each cover member, the vertical Cech-to-injective-total
edge is a quasi-isomorphism in degree one. -/
theorem cechInjectiveResolutionVerticalEdge_quasiIsoAt_one
    (F : Sheaf AddCommGrpCat.{u} X)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    QuasiIsoAt (cechInjectiveResolutionVerticalEdge U F) 1 := by
  apply HomologicalComplex₂.totalUpNatVerticalEdge_quasiIsoAt_one
  · exact cechInjectiveResolutionAugmentation_exact U F 0
  · exact cechInjectiveResolutionAugmentation_exact U F 1
  · exact cechInjectiveResolutionBicomplex_column_zero_exactAt_one U F hH

end

end TopCat.Sheaf
