/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineCover

/-!
# Local killing of degree-one scheme-module cohomology

This file proves that a degree-one Zariski cohomology class on an affine
spectrum dies after restriction to each member of a suitable finite affine
open cover.  The proof uses an injective embedding of the underlying
abelian sheaf, local surjectivity of its cokernel map, and compactness of an
affine spectrum.

This is a clean-room derivation against this repository's pinned Mathlib.
The unlicensed AINTLIB files `KempfLocalKilling.lean` and
`AffineVanishing.lean`, the prior implementation branch, and commit
`77901d2` were not consulted.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.LocalKilling

private abbrev AbSheaf (X : Scheme.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

private abbrev ExtH {X : Scheme.{u}}
    (F : AbSheaf X) (n : ℕ) : Type u :=
  Abelian.Ext
    ((CategoryTheory.constantSheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))) F n

private noncomputable def openSheafPullback
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf U :=
  U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}

private noncomputable def openSheafPushforward
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf U ⥤ AbSheaf X :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} U.ι.base

private noncomputable def openRestrictionPushforward
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf X :=
  openSheafPullback U ⋙ openSheafPushforward U

private noncomputable def openRestrictionPushforwardUnit
    {X : Scheme.{u}} (U : X.Opens) :
    𝟭 (AbSheaf X) ⟶
      openRestrictionPushforward U where
  app F :=
    { hom :=
        { app V := F.1.map
            (homOfLE (U.ι.image_preimage_le V.unop)).op
          naturality := by
            intro V W i
            change F.1.map i ≫ F.1.map _ =
              F.1.map _ ≫ F.1.map _
            calc
              _ = F.1.map (i ≫ _) := (F.1.map_comp _ _).symm
              _ = F.1.map (_ ≫ _) := congrArg F.1.map (Subsingleton.elim _ _)
              _ = _ := F.1.map_comp _ _ } }
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext
    ext V x
    change (f.hom.app V ≫ G.1.map _).hom x =
      (F.1.map _ ≫ f.hom.app _).hom x
    exact congrArg (fun k ↦ k.hom x)
      (f.hom.naturality
        (homOfLE (U.ι.image_preimage_le V.unop)).op).symm

private noncomputable def openRestrictionPushforwardSection
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (t : F.1.obj (op U)) :
    ((openRestrictionPushforward U).obj F).1.obj
      (op (⊤ : Opens X)) := by
  let W := U.ι.isOpenEmbedding.functor.obj
    ((Opens.map U.ι.base).obj (⊤ : Opens X))
  change F.1.obj (op W)
  have hW : W = U := by
    ext x
    simp [W]
  exact F.1.map (eqToHom hW).op t

private theorem openRestrictionPushforwardSection_map
    {X : Scheme.{u}} (U : X.Opens) {F G : AbSheaf X}
    (f : F ⟶ G) (t : F.1.obj (op U)) :
    (((openRestrictionPushforward U).map f).hom.app (op (⊤ : Opens X)))
        (openRestrictionPushforwardSection U F t) =
      openRestrictionPushforwardSection U G (f.hom.app (op U) t) := by
  let W := U.ι.isOpenEmbedding.functor.obj
    ((Opens.map U.ι.base).obj (⊤ : Opens X))
  have hW : W = U := by
    ext x
    simp [W]
  change f.hom.app (op W) (F.1.map (eqToHom hW).op t) =
    G.1.map (eqToHom hW).op (f.hom.app (op U) t)
  exact congrArg (fun k ↦ k.hom t)
    (f.hom.naturality (eqToHom hW).op)

private theorem openRestrictionPushforwardUnit_section
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (s : F.1.obj (op (⊤ : Opens X))) :
    ((openRestrictionPushforwardUnit U).app F).hom.app
        (op (⊤ : Opens X)) s =
      openRestrictionPushforwardSection U F
        (F.1.map (homOfLE le_top).op s) := by
  have hW : U.ι ''ᵁ (U.ι ⁻¹ᵁ (⊤ : Opens X)) = U := by
    ext x
    simp
  change F.1.map (homOfLE (U.ι.image_preimage_le (⊤ : Opens X))).op s =
    F.1.map (eqToHom hW).op (F.1.map (homOfLE le_top).op s)
  have hk : (homOfLE (U.ι.image_preimage_le (⊤ : Opens X))).op =
      (homOfLE le_top).op ≫ (eqToHom hW).op :=
    Subsingleton.elim _ _
  rw [hk, F.1.map_comp, ConcreteCategory.comp_apply]

private noncomputable def openRestrictionPushforwardHZeroOfSection
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (t : F.1.obj (op U)) :
    ExtH ((openRestrictionPushforward U).obj F) 0 :=
  (CategoryTheory.Sheaf.H.equiv₀
    ((openRestrictionPushforward U).obj F)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).symm
      (openRestrictionPushforwardSection U F t)

private theorem openRestrictionPushforwardHZeroOfSection_map
    {X : Scheme.{u}} (U : X.Opens) {F G : AbSheaf X}
    (f : F ⟶ G) (t : F.1.obj (op U)) :
    (openRestrictionPushforwardHZeroOfSection U F t).comp
        (Abelian.Ext.mk₀ ((openRestrictionPushforward U).map f)) rfl =
      openRestrictionPushforwardHZeroOfSection U G
        (f.hom.app (op U) t) := by
  change CategoryTheory.Sheaf.H.map
      ((openRestrictionPushforward U).map f) 0
        (openRestrictionPushforwardHZeroOfSection U F t) = _
  apply (CategoryTheory.Sheaf.H.equiv₀
    ((openRestrictionPushforward U).obj G)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  dsimp [openRestrictionPushforwardHZeroOfSection]
  simp only [AddEquiv.apply_symm_apply]
  exact openRestrictionPushforwardSection_map U f t

private theorem openRestrictionPushforwardUnit_HZero
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (q : ExtH F 0) :
    q.comp (Abelian.Ext.mk₀
        ((openRestrictionPushforwardUnit U).app F)) rfl =
      openRestrictionPushforwardHZeroOfSection U F
        (F.1.map (homOfLE le_top).op
          (CategoryTheory.Sheaf.H.equiv₀ F
            (isTerminalTop : IsTerminal (⊤ : Opens X)) q)) := by
  change CategoryTheory.Sheaf.H.map
      ((openRestrictionPushforwardUnit U).app F) 0 q = _
  apply (CategoryTheory.Sheaf.H.equiv₀
    ((openRestrictionPushforward U).obj F)
    (isTerminalTop : IsTerminal (⊤ : Opens X))).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  dsimp [openRestrictionPushforwardHZeroOfSection]
  rw [AddEquiv.apply_symm_apply]
  exact openRestrictionPushforwardUnit_section U F _

private noncomputable instance openSheafPullback_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openSheafPullback U) := by
  letI := U.ι.isOpenEmbedding.functor_isContinuous
  let E₁ := openSheafPullback U ⋙
    sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}
  let E₂ := sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      U.ι.isOpenEmbedding.functor.op
  let e : E₁ ≅ E₂ :=
    U.ι.isOpenEmbedding.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{u} (Opens.grothendieckTopology U)
        (Opens.grothendieckTopology X)
  haveI : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}) := by infer_instance
  haveI : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
        U.ι.isOpenEmbedding.functor.op) := by infer_instance
  haveI : PreservesFiniteLimits E₂ := by infer_instance
  haveI : PreservesFiniteLimits E₁ :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})

private noncomputable instance openSheafPushforward_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openSheafPushforward U) := by
  let E₁ := openSheafPushforward U ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let E₂ := sheafToPresheaf
      (Opens.grothendieckTopology U) AddCommGrpCat.{u} ⋙
    TopCat.Presheaf.pushforward AddCommGrpCat.{u} U.ι.base
  let e : E₁ ≅ E₂ :=
    TopCat.Sheaf.pushforwardForgetIso AddCommGrpCat.{u} U.ι.base
  haveI : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology U)
        AddCommGrpCat.{u}) := by infer_instance
  haveI : PreservesFiniteLimits
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} U.ι.base) := by
    dsimp [TopCat.Presheaf.pushforward]
    exact ⟨fun J _ _ ↦ whiskeringLeft_preservesLimitsOfShape J _⟩
  haveI : PreservesFiniteLimits E₂ := by infer_instance
  haveI : PreservesFiniteLimits E₁ :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

private noncomputable instance openRestrictionPushforward_preservesFiniteLimits
    {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (openRestrictionPushforward U) := by
  letI : PreservesFiniteLimits
      (openSheafPullback U) :=
    openSheafPullback_preservesFiniteLimits U
  letI : PreservesFiniteLimits
      (openSheafPushforward U) := by
    exact openSheafPushforward_preservesFiniteLimits U
  exact comp_preservesFiniteLimits _ _

private theorem toSheaf_restrictAdjunction_unit
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) =
      (openRestrictionPushforwardUnit U).app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := rfl

private theorem zariskiFunctor_map_restrictAdjunction_unit_eq_zero
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (c : H M 1)
    (hc : (c.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) rfl :
          ExtH ((openRestrictionPushforward U).obj
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) 1) = 0) :
    (zariskiFunctor X 1).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) c = 0 := by
  exact hc

private theorem openRestrictionPushforward_map_mono {X : Scheme.{u}}
    (U : X.Opens)
    {F G : AbSheaf X} (f : F ⟶ G) [Mono f] :
    Mono ((openRestrictionPushforward U).map f) := by
  haveI : Mono f.hom := by
    change Mono ((sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map f)
    infer_instance
  haveI hmono : Mono ((openRestrictionPushforward U).map f).hom := by
    exact (NatTrans.mono_iff_mono_app _).mpr fun V ↦ by
      change Mono (f.hom.app _)
      infer_instance
  exact Functor.mono_of_mono_map
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hmono

private theorem openRestrictionPushforward_cokernelComparison_mono
    {X : Scheme.{u}} (U : X.Opens)
    {F G : AbSheaf X} (f : F ⟶ G) [Mono f] :
    Mono (cokernelComparison f (openRestrictionPushforward U)) := by
  let E := openRestrictionPushforward U
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := ShortComplex.exact_cokernel f
  have hT : (S.map E).Exact :=
    hS.map_of_mono_of_preservesKernel E (by infer_instance) (by infer_instance)
  dsimp [S] at hT
  change (ShortComplex.mk (E.map f) (E.map (cokernel.π f)) _).Exact at hT
  let e : cokernel (E.map f) ≅ image (E.map (cokernel.π f)) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (E.map f))
      hT.isColimitImage
  have he_fac : cokernel.π (E.map f) ≫ e.hom =
      factorThruImage (E.map (cokernel.π f)) := by
    simpa [e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (E.map f)) hT.isColimitImage
          WalkingParallelPair.one)
  have he : cokernelComparison f E =
      e.hom ≫ image.ι (E.map (cokernel.π f)) := by
    rw [← cancel_epi (cokernel.π (E.map f))]
    rw [π_comp_cokernelComparison]
    symm
    rw [← Category.assoc, he_fac, image.fac]
  rw [he]
  infer_instance

private noncomputable abbrev injectiveCokernelSequence
    {X : Scheme.{u}} (F : AbSheaf X) :
    ShortComplex (AbSheaf X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

private theorem injectiveCokernelSequence_shortExact
    {X : Scheme.{u}} (F : AbSheaf X) :
    (injectiveCokernelSequence F).ShortExact := by
  letI : Mono (injectiveCokernelSequence F).f := by
    change Mono (Injective.ι F)
    infer_instance
  letI : Epi (injectiveCokernelSequence F).g := by
    change Epi (cokernel.π (Injective.ι F))
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.exact_cokernel (Injective.ι F))

private noncomputable abbrev openInjectiveCokernelSequence
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    ShortComplex (AbSheaf X) :=
  let E := openRestrictionPushforward U
  ShortComplex.mk (E.map (Injective.ι F))
    (cokernel.π (E.map (Injective.ι F)))
    (cokernel.condition (E.map (Injective.ι F)))

private theorem openInjectiveCokernelSequence_shortExact
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    (openInjectiveCokernelSequence U F).ShortExact := by
  letI : Mono ((openRestrictionPushforward U).map (Injective.ι F)) :=
    openRestrictionPushforward_map_mono U (Injective.ι F)
  letI : Mono (openInjectiveCokernelSequence U F).f := by
    change Mono ((openRestrictionPushforward U).map (Injective.ι F))
    infer_instance
  letI : Epi (openInjectiveCokernelSequence U F).g := by
    change Epi (cokernel.π
      ((openRestrictionPushforward U).map (Injective.ι F)))
    infer_instance
  exact ShortComplex.ShortExact.mk
    (ShortComplex.exact_cokernel
      ((openRestrictionPushforward U).map (Injective.ι F)))

private noncomputable def openInjectiveCokernelMap
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    cokernel (Injective.ι F) ⟶
      cokernel ((openRestrictionPushforward U).map (Injective.ι F)) :=
  cokernel.map (Injective.ι F)
    ((openRestrictionPushforward U).map (Injective.ι F))
    ((openRestrictionPushforwardUnit U).app F)
    ((openRestrictionPushforwardUnit U).app (Injective.under F))
    ((openRestrictionPushforwardUnit U).naturality (Injective.ι F))

private noncomputable def injectiveCokernelSequenceToOpen
    {X : Scheme.{u}} (U : X.Opens)
    (F : AbSheaf X) :
    injectiveCokernelSequence F ⟶ openInjectiveCokernelSequence U F where
  τ₁ := (openRestrictionPushforwardUnit U).app F
  τ₂ := (openRestrictionPushforwardUnit U).app (Injective.under F)
  τ₃ := openInjectiveCokernelMap U F
  comm₁₂ := by
    simpa [injectiveCokernelSequence, openInjectiveCokernelSequence] using
      ((openRestrictionPushforwardUnit U).naturality (Injective.ι F)).symm
  comm₂₃ := by
    simp [injectiveCokernelSequence, openInjectiveCokernelSequence,
      openInjectiveCokernelMap]

private theorem openRestrictionPushforwardUnit_HOne_eq_zero_of_lift
    {X : Scheme.{u}} {F : AbSheaf X}
    (c : ExtH F 1)
    (q : ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (t : ExtH
      ((openRestrictionPushforward U).obj (Injective.under F)) 0)
    (ht : t.comp
        (Abelian.Ext.mk₀ ((openRestrictionPushforward U).map
          (cokernel.π (Injective.ι F)))) rfl =
      q.comp (Abelian.Ext.mk₀
        ((openRestrictionPushforwardUnit U).app
          (cokernel (Injective.ι F)))) rfl) :
    (c.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app F)) rfl :
        ExtH ((openRestrictionPushforward U).obj F) 1) =
      (0 : ExtH ((openRestrictionPushforward U).obj F) 1) := by
  let E := openRestrictionPushforward U
  let η := openRestrictionPushforwardUnit U
  let i := Injective.ι F
  let π := cokernel.π i
  let ζ := openInjectiveCokernelMap U F
  let μ := cokernelComparison i E
  have hT := openInjectiveCokernelSequence_shortExact U F
  change (ShortComplex.mk (E.map i) (cokernel.π (E.map i)) _).ShortExact at hT
  letI : Mono μ := by
    dsimp [μ, E, i]
    exact openRestrictionPushforward_cokernelComparison_mono U (Injective.ι F)
  have hπζ : cokernel.π i ≫ ζ =
      η.app (Injective.under F) ≫ cokernel.π (E.map i) := by
    dsimp [ζ, η, E, i, openInjectiveCokernelMap]
    apply cokernel.π_desc
  have hζμ : ζ ≫ μ = η.app (cokernel i) := by
    rw [← cancel_epi (cokernel.π i)]
    calc
      cokernel.π i ≫ (ζ ≫ μ) =
          (cokernel.π i ≫ ζ) ≫ μ := Category.assoc _ _ _ |>.symm
      _ = (η.app (Injective.under F) ≫
          cokernel.π (E.map i)) ≫ μ := by rw [hπζ]
      _ = η.app (Injective.under F) ≫
          (cokernel.π (E.map i) ≫ μ) := Category.assoc _ _ _
      _ = η.app (Injective.under F) ≫ E.map π := by
        rw [π_comp_cokernelComparison]
      _ = cokernel.π i ≫ η.app (cokernel i) :=
        (η.naturality (cokernel.π i)).symm
  have hπμ : cokernel.π (E.map i) ≫ μ = E.map π := by
    exact π_comp_cokernelComparison i E
  have hqζ : q.comp (Abelian.Ext.mk₀ ζ) rfl =
      t.comp (Abelian.Ext.mk₀ (cokernel.π (E.map i))) rfl := by
    refine (Abelian.Ext.postcomp_mk₀_injective_of_mono
      ((CategoryTheory.constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))) μ) ?_
    change
      (q.comp (Abelian.Ext.mk₀ ζ) rfl).comp
          (Abelian.Ext.mk₀ μ) rfl =
        (t.comp (Abelian.Ext.mk₀ (cokernel.π (E.map i))) rfl).comp
          (Abelian.Ext.mk₀ μ) rfl
    simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, hζμ, hπμ] using ht.symm
  calc
    c.comp (Abelian.Ext.mk₀ (η.app F)) rfl =
        (q.comp (injectiveCokernelSequence_shortExact F).extClass rfl).comp
          (Abelian.Ext.mk₀ (η.app F)) rfl := by rw [hq]
    _ = q.comp
        ((injectiveCokernelSequence_shortExact F).extClass.comp
          (Abelian.Ext.mk₀ (η.app F)) rfl) rfl := by
      rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
    _ = q.comp ((Abelian.Ext.mk₀ ζ).comp hT.extClass rfl) rfl := by
      exact congrArg (fun x ↦ q.comp x rfl)
        ((injectiveCokernelSequence_shortExact F).extClass_naturality
          hT (injectiveCokernelSequenceToOpen U F))
    _ = (q.comp (Abelian.Ext.mk₀ ζ) rfl).comp hT.extClass rfl := by
      simpa only using (Abelian.Ext.comp_assoc q
        (Abelian.Ext.mk₀ ζ) hT.extClass rfl rfl rfl).symm
    _ = (t.comp (Abelian.Ext.mk₀ (cokernel.π (E.map i))) rfl).comp
        hT.extClass rfl := by rw [hqζ]
    _ = t.comp ((Abelian.Ext.mk₀ (cokernel.π (E.map i))).comp
        hT.extClass rfl) rfl := by
      simpa only using (Abelian.Ext.comp_assoc t
        (Abelian.Ext.mk₀ (cokernel.π (E.map i)))
          hT.extClass rfl rfl rfl)
    _ = 0 := by simp only [hT.comp_extClass, Abelian.Ext.comp_zero]

private theorem openRestrictionPushforwardUnit_HOne_eq_zero_of_section_lift
    {X : Scheme.{u}} {F : AbSheaf X}
    (c : ExtH F 1)
    (q : ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (U : X.Opens)
    (t : (Injective.under F).1.obj (op U))
    (ht : (cokernel.π (Injective.ι F)).hom.app (op U) t =
      (cokernel (Injective.ι F)).1.map (homOfLE le_top).op
        (CategoryTheory.Sheaf.H.equiv₀ (cokernel (Injective.ι F))
          (isTerminalTop : IsTerminal (⊤ : Opens X)) q)) :
    (c.comp (Abelian.Ext.mk₀
      ((openRestrictionPushforwardUnit U).app F)) rfl :
        ExtH ((openRestrictionPushforward U).obj F) 1) = 0 := by
  apply openRestrictionPushforwardUnit_HOne_eq_zero_of_lift c q hq U
    (openRestrictionPushforwardHZeroOfSection U (Injective.under F) t)
  rw [openRestrictionPushforwardHZeroOfSection_map,
    openRestrictionPushforwardUnit_HZero]
  exact congrArg
    (openRestrictionPushforwardHZeroOfSection U (cokernel (Injective.ι F))) ht

private theorem exists_injectiveCokernel_class
    {X : Scheme.{u}} {F : AbSheaf X} (c : ExtH F 1) :
    ∃ q : ExtH (cokernel (Injective.ι F)) 0,
      q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c := by
  let Z := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))
  have hc : c.comp (Abelian.Ext.mk₀ (Injective.ι F)) rfl = 0 :=
    Abelian.Ext.eq_zero_of_injective _
  exact Abelian.Ext.covariant_sequence_exact₁ Z
    (injectiveCokernelSequence_shortExact F) c hc rfl

private theorem exists_affineOpen_HOne_killing
    {X : Scheme.{u}} {F : AbSheaf X}
    (c : ExtH F 1)
    (q : ExtH (cokernel (Injective.ι F)) 0)
    (hq : q.comp (injectiveCokernelSequence_shortExact F).extClass rfl = c)
    (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      (c.comp (Abelian.Ext.mk₀
        ((openRestrictionPushforwardUnit U).app F)) rfl :
          ExtH ((openRestrictionPushforward U).obj F) 1) = 0 := by
  let π := cokernel.π (Injective.ι F)
  have hπepi : Epi π := by
    dsimp [π]
    infer_instance
  let s := CategoryTheory.Sheaf.H.equiv₀ (cokernel (Injective.ι F))
    (isTerminalTop : IsTerminal (⊤ : Opens X)) q
  have hlocal : TopCat.Presheaf.IsLocallySurjective π.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi π).2 hπepi
  have hex := (TopCat.Presheaf.isLocallySurjective_iff π.hom).1 hlocal
    (⊤ : Opens X) s x (by simp)
  rcases hex with ⟨V, hVtop, hpre, hxV⟩
  rcases hpre with ⟨t, ht⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ V := hUV
  let tU := (Injective.under F).1.map (homOfLE hUV').op t
  have htU : π.hom.app (op U) tU =
      (cokernel (Injective.ι F)).1.map (homOfLE le_top).op s := by
    have ht' := congrArg
      (fun y ↦ (cokernel (Injective.ι F)).1.map (homOfLE hUV').op y) ht
    dsimp [tU]
    rw [← ConcreteCategory.comp_apply, ← π.hom.naturality] at ht'
    have hk : (homOfLE hVtop).op ≫ (homOfLE hUV').op =
        (homOfLE le_top).op := Subsingleton.elim _ _
    simpa only [TopCat.Presheaf.restrict, ← ConcreteCategory.comp_apply,
      ← (cokernel (Injective.ι F)).1.map_comp, hk] using ht'
  refine ⟨U, hU, hxU, ?_⟩
  exact openRestrictionPushforwardUnit_HOne_eq_zero_of_section_lift
    c q hq U tU htU

private theorem zariskiFunctor_map_toAffineCoverModule_eq_zero
    {R : CommRingCat.{u}} {I : Type u} [Finite I]
    (M : (Spec R).Modules) (U : I → (Spec R).Opens) (c : H M 1)
    (hc : ∀ i, (zariskiFunctor (Spec R) 1).map
      ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) :
    (zariskiFunctor (Spec R) 1).map (toAffineCoverModule M U) c = 0 := by
  letI : PreservesFiniteProducts (zariskiFunctor (Spec R) 1) := by
    letI : (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (Spec R)) 1).Additive := by
      infer_instance
    change PreservesFiniteProducts
      (SheafOfModules.toSheaf (Spec R).ringCatSheaf ⋙
        CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology (Spec R)) 1)
    exact comp_preservesFiniteProducts _ _
  unfold toAffineCoverModule affineCoverModule
  apply Concrete.Pi.map_ext
    (fun i ↦ (Scheme.Modules.restrictFunctor (U i).ι ⋙
      Scheme.Modules.pushforward (U i).ι).obj M)
    (zariskiFunctor (Spec R) 1)
  intro i
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    limit.lift_π, Fan.mk_π_app, hc i]
  simp

/-- Every degree-one Zariski cohomology class on an affine spectrum is
killed by restriction to the members of a finite affine open cover.  The
last conclusion records the same vanishing for the induced map to the
finite product of restriction-pushforwards. -/
theorem schemeHOne_finiteAffineKillingCover
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (c : H M 1) :
    ∃ (I : Type u) (U : I → (Spec R).Opens),
      Finite I ∧
      IsOpenCover U ∧
      (∀ i, IsAffine (U i)) ∧
      (∀ i, (zariskiFunctor (Spec R) 1).map
        ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M) c = 0) ∧
      (zariskiFunctor (Spec R) 1).map (toAffineCoverModule M U) c = 0 := by
  let F := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M
  obtain ⟨q, hq⟩ := exists_injectiveCokernel_class (F := F) c
  choose U hUaffine hxU hUkills using fun x : Spec R ↦
    exists_affineOpen_HOne_killing c q hq x
  have hUcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply le_antisymm le_top
    rw [← SetLike.coe_subset_coe]
    intro x hx
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hUcover.exists_finite_of_compactSpace
  let V : s → (Spec R).Opens := fun i ↦ U i.1
  have hVkills (i : s) :
      (zariskiFunctor (Spec R) 1).map
        ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M) c = 0 := by
    exact zariskiFunctor_map_restrictAdjunction_unit_eq_zero
      (V i) M c (hUkills i.1)
  letI : Finite s := inferInstance
  refine ⟨s, V, inferInstance, hs, fun i ↦ hUaffine i.1,
    hVkills, ?_⟩
  exact zariskiFunctor_map_toAffineCoverModule_eq_zero M V c hVkills

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.LocalKilling
