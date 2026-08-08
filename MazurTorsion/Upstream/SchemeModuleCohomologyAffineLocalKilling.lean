/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Abelian
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineCoverMono

/-!
# Degree-one local killing on an affine spectrum

This file proves the local-killing step in Kempf's dimension-shifting
argument.  A degree-one Ext class of a scheme module on `Spec R` vanishes
after restriction to every member of a suitable finite affine open cover.
The same cover kills the class under the actual `toAffineCoverModule` map.

The proof first works with additive sheaves on a topological space.  An
injective presentation represents the class by a global section of its
cokernel.  Local surjectivity gives a lift on a basis neighbourhood, and
naturality of the short-exact Ext class makes the restricted class zero.
For scheme modules, an explicit isomorphism compares the underlying sheaf of
the module restriction-pushforward with topological restriction-pushforward;
this avoids relying on an expensive definitional-equality reduction.  Finite
compactness then supplies the cover, and additivity proves vanishing after
mapping to its product.

The argument was cross-checked against AINTLIB's
`ForMathlib/KempfLocalKilling.lean` and `ForMathlib/AffineVanishing.lean` at
commit `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.  The implementation here is
an independent derivation against this repository's exact Mathlib pin.

This file does not assert affine acyclicity: it proves the finite local
killing input that the subsequent dimension-shifting argument consumes.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Abelian
open _root_.AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.LocalKilling

open Topology

/-- The constant additive sheaf used as the first argument of Zariski Ext. -/
noncomputable def topologicalConstant (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u} :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))

/-- The underlying group of topological Ext cohomology. -/
abbrev TopologicalH {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (n : ℕ) : Type u :=
  Ext (topologicalConstant X) F n

/-- The map on topological Ext cohomology. -/
noncomputable abbrev topologicalHMap {X : TopCat.{u}}
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) :
    TopologicalH F n →+ TopologicalH G n :=
  (Ext.mk₀ f).postcomp (topologicalConstant X) (add_zero n)

private lemma topologicalHMap_comp_apply {X : TopCat.{u}}
    {F G K : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}} (f : F ⟶ G) (g : G ⟶ K) (n : ℕ)
    (x : TopologicalH F n) :
    topologicalHMap (f ≫ g) n x =
      topologicalHMap g n (topologicalHMap f n x) := by
  change x.comp (Ext.mk₀ (f ≫ g)) (add_zero n) =
    (x.comp (Ext.mk₀ f) (add_zero n)).comp
      (Ext.mk₀ g) (add_zero n)
  simp

private lemma topologicalHMap_id_apply {X : TopCat.{u}}
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}} (n : ℕ) (x : TopologicalH F n) :
    topologicalHMap (𝟙 F) n x = x := by
  change x.comp (Ext.mk₀ (𝟙 F)) (add_zero n) = x
  exact Ext.comp_mk₀_id x

/-- Degree-zero topological Ext cohomology is global sections. -/
noncomputable def topologicalHZeroEquiv {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    TopologicalH F 0 ≃+ F.obj.obj (op ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop

private lemma longSequence_equiv_zero_exact_one
    {X : TopCat.{u}}
    {S : ShortComplex (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (x : TopologicalH S.X₁ 1)
    (hx : topologicalHMap S.f 1 x = 0) :
    ∃ y : S.X₃.obj.obj (op ⊤),
      hS.extClass.postcomp _ rfl
          ((topologicalHZeroEquiv S.X₃).symm y) = x := by
  have hx' : x.comp (Ext.mk₀ S.f) rfl = 0 := hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (topologicalConstant X) hS x hx' rfl
  refine ⟨topologicalHZeroEquiv S.X₃ y, ?_⟩
  rw [AddEquiv.symm_apply_apply]
  exact hy

/-- Restriction of topological sheaves along an open embedding. -/
abbrev topologicalRestrict {C : Type*} [Category* C]
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    Functor
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) C) :=
  haveI := hf.functor_isContinuous
  hf.functor.sheafPushforwardContinuous C ..

/-- Pushforward of topological sheaves, with the site-sheaf source and target
types made explicit. -/
abbrev topologicalPushforward {C : Type*} [Category* C]
    {X Y : TopCat.{u}} (f : Y ⟶ X) :
    Functor
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) C)
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C) :=
  TopCat.Sheaf.pushforward C f

/-- Restriction along an open embedding is left adjoint to pushforward. -/
abbrev topologicalRestrictPushforwardAdjunction
    {C : Type*} [Category* C] {X Y : TopCat.{u}}
    {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    topologicalRestrict hf ⊣ topologicalPushforward (C := C) f :=
  haveI := hf.functor_isContinuous
  Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction ..

private lemma topologicalRestrict_comp_forget_preservesFiniteLimits
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    PreservesFiniteLimits
      (topologicalRestrict (C := AddCommGrpCat.{u}) hf ⋙
        sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) := by
  letI := hf.functor_isContinuous
  letI : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    inferInstance
  letI : PreservesFiniteLimits
      ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ
        AddCommGrpCat.{u}).obj hf.functor.op) := inferInstance
  change PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (Functor.whiskeringLeft _ _ _).obj hf.functor.op)
  exact comp_preservesFiniteLimits _ _

private lemma sheafToPresheaf_reflectsFiniteShape
    {Y : TopCat.{u}} (J : Type) [SmallCategory J] [FinCategory J] :
    ReflectsLimitsOfShape J
      (sheafToPresheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}) := by
  infer_instance

/-- Restriction of additive sheaves along an open embedding preserves finite
limits. -/
local instance topologicalRestrict_preservesFiniteLimits
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    PreservesFiniteLimits
      (topologicalRestrict (C := AddCommGrpCat.{u}) hf) := by
  letI := topologicalRestrict_comp_forget_preservesFiniteLimits hf
  constructor
  intro J _ _
  have hPreserve : PreservesLimitsOfShape J
      (topologicalRestrict (C := AddCommGrpCat.{u}) hf ⋙
        sheafToPresheaf (Opens.grothendieckTopology Y)
          AddCommGrpCat.{u}) := inferInstance
  have hReflect := sheafToPresheaf_reflectsFiniteShape (Y := Y) J
  exact @preservesLimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _
    (topologicalRestrict (C := AddCommGrpCat.{u}) hf)
    (sheafToPresheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}) hPreserve hReflect

/-- Restriction of additive sheaves along an open embedding is additive. -/
local instance topologicalRestrict_additive
    {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) :
    (topologicalRestrict (C := AddCommGrpCat.{u}) hf).Additive where
  map_add := by
    intros
    apply CategoryTheory.Sheaf.hom_ext
    rfl

/-- Pushforward of additive topological sheaves is additive. -/
local instance topologicalPushforward_additive {X Y : TopCat.{u}}
    (f : Y ⟶ X) :
    (topologicalPushforward (C := AddCommGrpCat.{u}) f).Additive where
  map_add := by
    intros
    apply CategoryTheory.Sheaf.hom_ext
    rfl

/-- The unit from a sheaf to the pushforward of its restriction to an open. -/
abbrev topologicalToRestrict {C : Type*} [Category* C]
    {X : TopCat.{u}} (U : Opens X) :=
  (topologicalRestrictPushforwardAdjunction (C := C) U.isOpenEmbedding).unit

private theorem topologicalToRestrict_app
    {X : TopCat.{u}} (F : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (U V : Opens X) :
    ((topologicalToRestrict
      (C := AddCommGrpCat.{u}) U).app F).hom.app (op V) =
      F.obj.map
        (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op := by
  simp
  rfl

private lemma topologicalToRestrict_naturality
    {X : TopCat.{u}} (U : Opens X)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}} (f : F ⟶ G) :
    f ≫ (topologicalToRestrict (C := AddCommGrpCat.{u}) U).app G =
      (topologicalToRestrict (C := AddCommGrpCat.{u}) U).app F ≫
        (topologicalRestrict U.isOpenEmbedding ⋙
          topologicalPushforward
            (C := AddCommGrpCat.{u}) U.inclusion').map f := by
  exact (topologicalToRestrict
    (C := AddCommGrpCat.{u}) U).naturality f

private lemma comp_app_apply
    {X : TopCat.{u}}
    {F G H : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}}
    {f : F ⟶ G} {g : G ⟶ H} {h : F ⟶ H} (e : f ≫ g = h)
    (V : (Opens X)ᵒᵖ) (x : F.obj.obj V) :
    g.hom.app V (f.hom.app V x) = h.hom.app V x := by
  change (f ≫ g).hom.app V x = h.hom.app V x
  exact congr($(e).hom.app V x)

private lemma restrict_restrict_apply
    {X : TopCat.{u}}
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}}
    {U V W : (Opens X)ᵒᵖ} (s : F.obj.obj U)
    (hUW : U ⟶ W) (hUV : U ⟶ V) (hVW : V ⟶ W) :
    F.obj.map hVW (F.obj.map hUV s) = F.obj.map hUW s := by
  have h : hUV ≫ hVW = hUW := Subsingleton.elim _ _
  simpa using congr(F.obj.map $(h) s)

private lemma hom_naturality_apply
    {X : TopCat.{u}}
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}}
    (f : F ⟶ G) {U V : (Opens X)ᵒᵖ} (hUV : U ⟶ V)
    (s : F.obj.obj U) :
    f.hom.app V (F.obj.map hUV s) =
      G.obj.map hUV (f.hom.app U s) := by
  simp

private lemma hZeroEquiv_symm_naturality
    {X : TopCat.{u}}
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}}
    (f : F ⟶ G) (x : F.obj.obj (op ⊤)) :
    topologicalHMap f 0
        ((topologicalHZeroEquiv F).symm x) =
      (topologicalHZeroEquiv G).symm
        (f.hom.app (op ⊤) x) :=
  CategoryTheory.Sheaf.H.equiv₀_symm_naturality isTerminalTop f x

private lemma hOne_map_toRestrict_eq_zero_of_lift
    {X : TopCat.{u}}
    (S : ShortComplex (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (V : Opens X)
    (b : S.X₃.obj.obj (op ⊤)) (s : S.X₂.obj.obj (op V))
    (hs : S.g.hom.app (op V) s = S.X₃.obj.map V.leTop.op b) :
    topologicalHMap
        ((topologicalToRestrict (C := AddCommGrpCat.{u}) V).app S.X₁) 1
        (hS.extClass.postcomp _ rfl
          ((topologicalHZeroEquiv S.X₃).symm b)) = 0 := by
  letI : Mono S.f := hS.2
  letI : Epi S.g := hS.3
  let pushforwardAdjunction :
      TopCat.Sheaf.pullback AddCommGrpCat.{u} V.inclusion' ⊣
        topologicalPushforward
          (C := AddCommGrpCat.{u}) V.inclusion' :=
    TopCat.Sheaf.pullbackPushforwardAdjunction _ V.inclusion'
  letI : (topologicalPushforward
      (C := AddCommGrpCat.{u}) V.inclusion').IsRightAdjoint :=
    pushforwardAdjunction.isRightAdjoint
  letI : PreservesFiniteLimits
      (topologicalPushforward
        (C := AddCommGrpCat.{u}) V.inclusion') := inferInstance
  let RV := topologicalRestrict V.isOpenEmbedding ⋙
    topologicalPushforward (C := AddCommGrpCat.{u}) V.inclusion'
  letI : PreservesFiniteLimits RV := by
    dsimp only [RV]
    exact comp_preservesFiniteLimits _ _
  let SV := ShortComplex.mk
    (RV.map S.f)
    (cokernel.π (RV.map S.f))
    (cokernel.condition _)
  have hSV : SV.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)
  let SV' := S.map RV
  have hSV' : SV'.Exact :=
    ((_ ⋙ topologicalPushforward (C := AddCommGrpCat.{u}) _).preservesFiniteLimits_tfae.out
      3 1 rfl rfl).mp inferInstance S ⟨hS.1, hS.2⟩ |>.1
  let φ : SV.X₃ ⟶ SV'.X₃ := cokernel.desc SV'.f SV'.g SV'.zero
  have hφMono : Mono φ := ShortComplex.Exact.mono_cokernelDesc hSV'
  let res : S ⟶ SV := ShortComplex.Hom.mk
    ((topologicalToRestrict (C := AddCommGrpCat.{u}) V).app S.X₁)
    ((topologicalToRestrict (C := AddCommGrpCat.{u}) V).app S.X₂)
    (ShortComplex.Exact.desc hS.exact
      ((topologicalToRestrict (C := AddCommGrpCat.{u}) V).app S.X₂ ≫ SV.g)
      (by
        have hcomm :
            S.f ≫ (topologicalToRestrict
                (C := AddCommGrpCat.{u}) V).app S.X₂ =
              (topologicalToRestrict
                (C := AddCommGrpCat.{u}) V).app S.X₁ ≫ SV.f := by
          change S.f ≫
              (topologicalToRestrict
                (C := AddCommGrpCat.{u}) V).app S.X₂ =
            (topologicalToRestrict
              (C := AddCommGrpCat.{u}) V).app S.X₁ ≫ RV.map S.f
          exact topologicalToRestrict_naturality V S.f
        calc
          S.f ≫ ((topologicalToRestrict
                (C := AddCommGrpCat.{u}) V).app S.X₂ ≫ SV.g) =
              (S.f ≫ (topologicalToRestrict
                (C := AddCommGrpCat.{u}) V).app S.X₂) ≫ SV.g :=
            (Category.assoc _ _ _).symm
          _ = ((topologicalToRestrict
                (C := AddCommGrpCat.{u}) V).app S.X₁ ≫ SV.f) ≫ SV.g :=
            congrArg (fun k ↦ k ≫ SV.g) hcomm
          _ = (topologicalToRestrict
                (C := AddCommGrpCat.{u}) V).app S.X₁ ≫ (SV.f ≫ SV.g) :=
            Category.assoc _ _ _
          _ = 0 := by rw [SV.zero, comp_zero]))
    (by
      change (topologicalToRestrict
          (C := AddCommGrpCat.{u}) V).app S.X₁ ≫ RV.map S.f =
        S.f ≫ (topologicalToRestrict
          (C := AddCommGrpCat.{u}) V).app S.X₂
      exact (topologicalToRestrict_naturality V S.f).symm)
    (by simp)
  have hφ₁ : SV.g ≫ φ = RV.map S.g :=
    cokernel.π_desc SV'.f SV'.g SV'.zero
  let toRes₃ := (topologicalToRestrict
    (C := AddCommGrpCat.{u}) V).app S.X₃
  have htoRes₃ : S.g ≫ toRes₃ = res.τ₂ ≫ RV.map S.g := by
    change S.g ≫ (topologicalToRestrict
        (C := AddCommGrpCat.{u}) V).app S.X₃ =
      (topologicalToRestrict
        (C := AddCommGrpCat.{u}) V).app S.X₂ ≫ RV.map S.g
    exact topologicalToRestrict_naturality V S.g
  have hφ₂ : res.τ₃ ≫ φ = toRes₃ := by
    apply (cancel_epi S.g).1
    have hcomm : S.g ≫ res.τ₃ = res.τ₂ ≫ SV.g := res.comm₂₃.symm
    rw [← Category.assoc, hcomm, Category.assoc, hφ₁]
    exact htoRes₃.symm
  let t := S.X₂.obj.map
    (homOfLE (Opens.isOpenEmbedding_obj_top V).le).op s
  have hres : res.τ₃.hom.app (op ⊤) b = SV.g.hom.app (op ⊤) t := by
    haveI : Mono φ.hom := @Functor.map_mono _ _ _ _
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat) _ _ _ φ hφMono
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (φ.hom.app (op ⊤))
    have hφ₂App : φ.hom.app (op ⊤) (res.τ₃.hom.app (op ⊤) b) =
        toRes₃.hom.app (op ⊤) b :=
      comp_app_apply hφ₂ (op ⊤) b
    have hφ₁App : φ.hom.app (op ⊤) (SV.g.hom.app (op ⊤) t) =
        (RV.map S.g).hom.app (op ⊤) t :=
      comp_app_apply hφ₁ (op ⊤) t
    have hrestriction : toRes₃.hom.app (op ⊤) b =
        (RV.map S.g).hom.app (op ⊤) t := by
      dsimp only [toRes₃, t]
      erw [hom_naturality_apply S.g]
      rw [hs]
      change S.X₃.obj.map _ b = S.X₃.obj.map _ (S.X₃.obj.map _ b)
      exact (restrict_restrict_apply b ..).symm
    exact hφ₂App.trans (hrestriction.trans hφ₁App.symm)
  let bH : TopologicalH S.X₃ 0 :=
    (topologicalHZeroEquiv S.X₃).symm b
  let δS : TopologicalH S.X₃ 0 →+ TopologicalH S.X₁ 1 :=
    hS.extClass.postcomp _ rfl
  let δSV : TopologicalH SV.X₃ 0 →+ TopologicalH SV.X₁ 1 :=
    hSV.extClass.postcomp _ rfl
  have hδNat : δSV (topologicalHMap res.τ₃ 0 bH) =
      topologicalHMap res.τ₁ 1 (δS bH) := by
    dsimp only [δSV, δS]
    simp [ShortComplex.ShortExact.extClass_naturality hS hSV res]
  have hresMap : topologicalHMap res.τ₃ 0 bH =
      (topologicalHZeroEquiv SV.X₃).symm
        (res.τ₃.hom.app (op ⊤) b) :=
    hZeroEquiv_symm_naturality res.τ₃ b
  have hSVMap : topologicalHMap SV.g 0
        ((topologicalHZeroEquiv SV.X₂).symm t) =
      (topologicalHZeroEquiv SV.X₃).symm
        (SV.g.hom.app (op ⊤) t) :=
    hZeroEquiv_symm_naturality SV.g t
  have hzero : δSV (topologicalHMap SV.g 0
      ((topologicalHZeroEquiv SV.X₂).symm t)) = 0 := by
    change (((topologicalHZeroEquiv SV.X₂).symm t).comp
      (Ext.mk₀ SV.g) rfl).comp hSV.extClass rfl = 0
    simp only [Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
  change topologicalHMap res.τ₁ 1 (δS bH) = 0
  calc
    topologicalHMap res.τ₁ 1 (δS bH) =
        δSV (topologicalHMap res.τ₃ 0 bH) := hδNat.symm
    _ = δSV ((topologicalHZeroEquiv SV.X₃).symm
        (res.τ₃.hom.app (op ⊤) b)) := congrArg δSV hresMap
    _ = δSV ((topologicalHZeroEquiv SV.X₃).symm
        (SV.g.hom.app (op ⊤) t)) :=
      congrArg (fun y ↦ δSV ((topologicalHZeroEquiv SV.X₃).symm y)) hres
    _ = δSV (topologicalHMap SV.g 0
        ((topologicalHZeroEquiv SV.X₂).symm t)) :=
      congrArg δSV hSVMap.symm
    _ = 0 := hzero

/-- Every degree-one Ext cohomology class is killed on a basis neighborhood
of any chosen point. -/
theorem degreeOneClass_locally_zero
    {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u})
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (c : TopologicalH F 1) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ U ∈ B ∧
      topologicalHMap
        ((topologicalToRestrict (C := AddCommGrpCat.{u}) U).app F) 1 c = 0 := by
  let S := (EnoughInjectives.presentation F).some.shortComplex
  have hS : S.ShortExact :=
    (EnoughInjectives.presentation F).some.shortExact_shortComplex
  obtain ⟨b, hb⟩ := longSequence_equiv_zero_exact_one hS c
    (by
      change c.comp (Ext.mk₀ S.f) rfl = 0
      exact Ext.eq_zero_of_injective _)
  have hloc : CategoryTheory.Sheaf.IsLocallySurjective S.g :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      AddCommGrpCat.{u} S.g).2 hS.3
  have hEpi : TopCat.Presheaf.IsLocallySurjective S.g.hom := hloc
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hEpi
  obtain ⟨V', hV'₁, ⟨⟨s', hs'⟩, hV'₃⟩⟩ :=
    hEpi ⊤ b x (Opens.mem_top x)
  obtain ⟨V, hV₁, hV₂, hV₃⟩ :=
    Opens.isBasis_iff_nbhd.mp hB hV'₃
  refine ⟨V, hV₂, hV₁, ?_⟩
  let s := S.X₂.obj.map (homOfLE hV₃).op s'
  have hs : S.g.hom.app (op V) s = S.X₃.obj.map V.leTop.op b := by
    dsimp [s]
    rw [hom_naturality_apply, hs']
    exact restrict_restrict_apply b ..
  rw [← hb]
  exact hOne_map_toRestrict_eq_zero_of_lift S hS V b s hs

/-- The underlying additive sheaf of a scheme module, with its site written
explicitly for use in Ext constructions. -/
noncomputable abbrev schemeModuleUnderlyingSheaf {X : Scheme.{u}}
    (M : X.Modules) : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

/-- The underlying additive-sheaf morphism of a scheme-module morphism. -/
noncomputable abbrev schemeModuleUnderlyingHom {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) :
    schemeModuleUnderlyingSheaf M ⟶ schemeModuleUnderlyingSheaf N :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map f

/-- Forgetting the module structure identifies scheme-module
restriction-pushforward with additive-sheaf restriction-pushforward. -/
noncomputable def restrictionPushforwardUnderlyingIso {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) :
    schemeModuleUnderlyingSheaf
        ((Scheme.Modules.restrictFunctor U.ι ⋙
          Scheme.Modules.pushforward U.ι).obj M) ≅
      (topologicalRestrict (C := AddCommGrpCat.{u})
          (TopologicalSpace.Opens.isOpenEmbedding (U : Opens X)) ⋙
        topologicalPushforward (C := AddCommGrpCat.{u})
          (TopologicalSpace.Opens.inclusion' (U : Opens X))).obj
          (schemeModuleUnderlyingSheaf M) := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦ Iso.refl _) ?_)
  intro V W f
  rfl

/-- If every restriction-unit component kills a cohomology class, then the
map to their finite product kills it. -/
theorem zariskiMap_toAffineCoverModule_eq_zero
    {R : CommRingCat.{u}} {I : Type u} [Finite I]
    (M : (Spec R).Modules) (U : I → (Spec R).Opens)
    (n : ℕ) (c : H M n)
    (h : ∀ i, (zariskiFunctor (Spec R) n).map
      ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) :
    (zariskiFunctor (Spec R) n).map (toAffineCoverModule M U) c = 0 := by
  let Z := zariskiFunctor (Spec R) n
  letI : Z.Additive := by
    change (SheafOfModules.toSheaf (Spec R).ringCatSheaf ⋙
      CategoryTheory.Sheaf.functorH
        (_root_.Opens.grothendieckTopology (Spec R)) n).Additive
    infer_instance
  let p (i : I) : affineCoverModule M U ⟶
      (Scheme.Modules.restrictFunctor (U i).ι ⋙
        Scheme.Modules.pushforward (U i).ι).obj M := by
    change (∏ᶜ fun i ↦
      (Scheme.Modules.restrictFunctor (U i).ι ⋙
        Scheme.Modules.pushforward (U i).ι).obj M) ⟶ _
    exact Pi.π _ i
  change Z.map (toAffineCoverModule M U) c = 0
  apply Limits.Concrete.Pi.map_ext
  intro i
  change Z.map (p i) (Z.map (toAffineCoverModule M U) c) =
    Z.map (p i) 0
  rw [map_zero]
  have hp : toAffineCoverModule M U ≫ p i =
      (Scheme.Modules.restrictAdjunction (U i).ι).unit.app M := by
    change toAffineCoverModule M U ≫
      Pi.π (fun i ↦
        (Scheme.Modules.restrictFunctor (U i).ι ⋙
          Scheme.Modules.pushforward (U i).ι).obj M) i = _
    exact toAffineCoverModule_comp_pi M U i
  calc
    Z.map (p i) (Z.map (toAffineCoverModule M U) c) =
        Z.map (toAffineCoverModule M U ≫ p i) c := by
      exact (Z.map_comp_apply (toAffineCoverModule M U) (p i) c).symm
    _ = Z.map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c := by
      rw [hp]
    _ = 0 := by
      exact h i

/-- A degree-one class of a scheme module on an affine spectrum is killed on
an actual finite affine open cover. -/
theorem schemeHOne_finiteAffineKillingCover
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (c : H M 1) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧ IsOpenCover U ∧ (∀ i, IsAffine (U i)) ∧
        (∀ i, (zariskiFunctor (Spec R) 1).map
          ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
        (zariskiFunctor (Spec R) 1).map
          (toAffineCoverModule M U) c = 0 := by
  let F := schemeModuleUnderlyingSheaf M
  let cF : TopologicalH F 1 := c
  have hlocal (x : Spec R) :=
    degreeOneClass_locally_zero F (Spec R).isBasis_affineOpens cF x
  choose U hxU hUaff hzero using hlocal
  have hcover : IsOpenCover U := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    exact (le_iSup U x) (hxU x)
  obtain ⟨s, hs⟩ := hcover.exists_finite_of_compactSpace
  let Us : s → (Spec R).Opens := fun i ↦ U i.1
  have hcomponent (i : s) : (zariskiFunctor (Spec R) 1).map
      ((Scheme.Modules.restrictAdjunction (Us i).ι).unit.app M) c = 0 := by
    have hz := hzero i.1
    let V : (Spec R).Opens := Us i
    let e := restrictionPushforwardUnderlyingIso M V
    let unitHom := schemeModuleUnderlyingHom
      ((Scheme.Modules.restrictAdjunction V.ι).unit.app M)
    have hunit : unitHom ≫ e.hom =
        (topologicalToRestrict (C := AddCommGrpCat.{u}) V).app F := by
      apply CategoryTheory.Sheaf.hom_ext
      ext W y
      rfl
    change topologicalHMap unitHom 1 cF = 0
    have hinj : Function.Injective (topologicalHMap e.hom 1) := by
      intro x y hxy
      have h := congrArg (topologicalHMap e.inv 1) hxy
      rw [← topologicalHMap_comp_apply,
        ← topologicalHMap_comp_apply, e.hom_inv_id,
        topologicalHMap_id_apply, topologicalHMap_id_apply] at h
      exact h
    apply hinj
    rw [map_zero]
    rw [← topologicalHMap_comp_apply unitHom e.hom 1 cF, hunit]
    exact hz
  refine ⟨s, Us, inferInstance, hs, ?_, hcomponent, ?_⟩
  · intro i
    exact hUaff i.1
  · exact zariskiMap_toAffineCoverModule_eq_zero M Us 1 c hcomponent

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.LocalKilling
