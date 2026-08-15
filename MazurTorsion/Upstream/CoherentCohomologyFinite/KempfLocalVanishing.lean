/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFlasqueCohomology
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Topology.Sets.OpenCover

/-!
# Kempf's local-vanishing argument

The main theorem says that a higher cohomology class vanishes after
restriction to a cover drawn from a basis, provided lower cohomology
vanishes on members of that basis.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

open Topology

noncomputable local instance kempfCohomologyAddCommGroup
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

private theorem cohomology_subsingleton_of_injective
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [hF : Injective F]
    (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact @CategoryTheory.Abelian.Ext.subsingleton_of_injective
    _ _ _ _ _ _ hF n

/-- Restriction of a flasque sheaf to an open subspace is flasque. -/
theorem IsFlasque.of_restrict (C : Type*) [Category* C]
    {Y : TopCat.{u}} {f : Y ⟶ X}
    (F : TopCat.Sheaf C X) [F.IsFlasque]
    (hf : IsOpenEmbedding f) :
    ((restrict C hf).obj F).IsFlasque where
  epi i := by
    change Epi (F.obj.map (hf.functor.op.map i))
    infer_instance

section

attribute [local instance]
  Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
  Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

instance restrict_additive {Y : TopCat.{u}} {f : Y ⟶ X}
    (hf : IsOpenEmbedding f) :
    (restrict AddCommGrpCat.{u} hf).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

instance pushforward_additive {Y : TopCat.{u}} {f : Y ⟶ X} :
    (pushforward AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end

lemma _root_.TopologicalSpace.IsOpenCover.def
    {ι Y : Type*} [TopologicalSpace Y]
    (U : ι → Opens Y) :
    IsOpenCover U ↔ ∀ x, ∃ i, x ∈ U i := by
  refine ⟨fun hU x => hU.exists_mem x, fun hU => ?_⟩
  rw [IsOpenCover, ← SetLike.coe_set_eq, Opens.coe_iSup]
  ext
  simp [hU]

/-- Restriction along an equality of opens. -/
abbrev restrictOfEq {C : Type*} [Category* C]
    (F : Sheaf C X) {U V : Opens X} (h : U = V) :=
  F.obj.map (homOfLE (le_of_eq h)).op

lemma comp_app_apply {A : Type*} [Category.{u} A]
    {FC : A → A → Type*} {CC : A → Type u}
    [∀ A₁ A₂ : A, FunLike (FC A₁ A₂) (CC A₁) (CC A₂)]
    [ConcreteCategory.{u} A FC]
    {F G H : Sheaf A X} {f : F ⟶ G} {g : G ⟶ H}
    {φ : F ⟶ H} (h : f ≫ g = φ)
    (V : (Opens X)ᵒᵖ) (x : ToType (F.obj.obj V)) :
    g.hom.app V (f.hom.app V x) = φ.hom.app V x := by
  simpa [Sheaf.comp_app] using congr($(h).hom.app V x)

lemma restrict_restrict_apply {A : Type*} [Category.{u} A]
    {FC : A → A → Type*} {CC : A → Type u}
    [∀ A₁ A₂ : A, FunLike (FC A₁ A₂) (CC A₁) (CC A₂)]
    [ConcreteCategory.{u} A FC]
    {F : Sheaf A X} {U V W : (Opens X)ᵒᵖ}
    (s : ToType (F.obj.obj U)) (hUW : U ⟶ W)
    (hUV : U ⟶ V) (hVW : V ⟶ W) :
    F.obj.map hVW (F.obj.map hUV s) =
      F.obj.map hUW s := by
  have hcomp : hUV ≫ hVW = hUW := Subsingleton.elim _ _
  simpa using congr(F.obj.map $(hcomp) s)

lemma hom_naturality_apply {A : Type*} [Category.{u} A]
    {FC : A → A → Type*} {CC : A → Type u}
    [∀ A₁ A₂ : A, FunLike (FC A₁ A₂) (CC A₁) (CC A₂)]
    [ConcreteCategory.{u} A FC]
    {F G : Sheaf A X} (f : F ⟶ G)
    {U V : (Opens X)ᵒᵖ} (hUV : U ⟶ V)
    (s : ToType (F.obj.obj U)) :
    f.hom.app V (F.obj.map hUV s) =
      G.obj.map hUV (f.hom.app U s) := by
  simp

lemma one_ex_opens_toRestrict_app_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (c : CategoryTheory.Sheaf.H F 1) (x : X) :
    ∃ U : Opens X,
      x ∈ U ∧ U ∈ B ∧
        CategoryTheory.Sheaf.H.map
          ((toRestrict _ U).app F) 1 c = 0 := by
  let ip := (EnoughInjectives.presentation F).some
  let pres := ip.shortComplex
  letI : Injective pres.X₂ := ip.injective
  have presEx : pres.ShortExact :=
    (EnoughInjectives.presentation F).some.shortExact_shortComplex
  obtain ⟨b, hb⟩ :=
    CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₁
      presEx Limits.isTerminalTop c
        ((cohomology_subsingleton_of_injective pres.X₂ 0).elim _ _)
  have hlocal := presEx.3
  rw [← isLocallySurjective_iff_epi,
    Presheaf.isLocallySurjective_iff] at hlocal
  obtain ⟨V', ⟨hV'₁, ⟨⟨s', hs'⟩, hV'₃⟩⟩⟩ :=
    hlocal ⊤ b x (Opens.mem_top x)
  obtain ⟨V, ⟨hV₁, ⟨hV₂, hV₃⟩⟩⟩ :=
    Opens.isBasis_iff_nbhd.mp hB hV'₃
  refine ⟨V, hV₂, hV₁, ?_⟩
  let s := pres.X₂.obj.map (homOfLE hV₃).op s'
  have hs :
      pres.g.hom.app (op V) s =
        pres.X₃.obj.map V.leTop.op b := by
    dsimp [s]
    rw [hom_naturality_apply, hs']
    exact restrict_restrict_apply b ..
  clear_value s
  clear V' hV'₁ hV'₃ s' hs' hV₃ hV₁ hV₂ hlocal
  let presᵥ :=
    ShortComplex.mk
      ((restrict AddCommGrpCat V.isOpenEmbedding ⋙
        pushforward AddCommGrpCat V.inclusion').map pres.f)
      (cokernel.π
        ((restrict AddCommGrpCat V.isOpenEmbedding ⋙
          pushforward AddCommGrpCat V.inclusion').map pres.f))
      (by simp)
  have presᵥEx : presᵥ.ShortExact :=
    ShortComplex.ShortExact.mk
      (ShortComplex.exact_cokernel _)
  let presᵥ' :=
    pres.map
      (restrict AddCommGrpCat V.isOpenEmbedding ⋙
        pushforward AddCommGrpCat V.inclusion')
  have presᵥ'Ex : presᵥ'.Exact :=
    (((_ ⋙ pushforward _ _).preservesFiniteLimits_tfae.out
      3 1 rfl rfl).mp inferInstance pres
      ⟨presEx.1, presEx.2⟩).1
  let φ : presᵥ.X₃ ⟶ presᵥ'.X₃ :=
    cokernel.desc presᵥ'.f presᵥ'.g presᵥ'.zero
  have : Mono φ :=
    ShortComplex.Exact.mono_cokernelDesc presᵥ'Ex
  let res : pres ⟶ presᵥ :=
    ShortComplex.Hom.mk
      ((toRestrict _ V).app pres.X₁)
      ((toRestrict _ V).app pres.X₂)
      (ShortComplex.Exact.desc presEx.exact
        ((toRestrict _ V).app pres.X₂ ≫ presᵥ.g)
        (by
          have hcomm :
              pres.f ≫ (toRestrict AddCommGrpCat V).app pres.X₂ =
                (toRestrict AddCommGrpCat V).app pres.X₁ ≫
                  presᵥ.f := by
            simp [pres, presᵥ]
          rw [← Category.assoc, hcomm, Category.assoc]
          simp))
      (by simp [pres, presᵥ])
      (by simp)
  let τ₃ : pres.X₃ ⟶ presᵥ'.X₃ :=
    (toRestrict AddCommGrpCat V).app pres.X₃
  have φ₁ :
      presᵥ.g ≫ φ =
        (restrict AddCommGrpCat V.isOpenEmbedding ⋙
          pushforward AddCommGrpCat V.inclusion').map pres.g :=
    cokernel.π_desc presᵥ'.f presᵥ'.g presᵥ'.zero
  have φ₂ :
      res.τ₃ ≫ φ = τ₃ := by
    rw [← cancel_epi pres.g, ← res.comm₂₃_assoc, φ₁]
    exact ((toRestrict AddCommGrpCat V).naturality pres.g).symm
  change (CategoryTheory.Sheaf.H.map res.τ₁ 1) c = 0
  subst hb
  have hres :
      res.τ₃.hom.app (op ⊤) b =
        presᵥ.g.hom.app (op ⊤)
          (pres.X₂.restrictOfEq
            (Opens.isOpenEmbedding_obj_top V) s) := by
    have hmonoHom : Mono φ.hom := by
      exact
        (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} φ).mp this
    letI : Mono φ.hom := hmonoHom
    letI : Mono (φ.hom.app (op ⊤)) :=
      (NatTrans.mono_iff_mono_app φ.hom).mp
        hmonoHom (op ⊤)
    apply
      ConcreteCategory.injective_of_mono_of_preservesPullback
        (φ.hom.app (op ⊤))
    let y := pres.X₂.restrictOfEq
      (Opens.isOpenEmbedding_obj_top V) s
    have hleft := comp_app_apply φ₂ (op ⊤) b
    have hright := comp_app_apply φ₁ (op ⊤) y
    have hmiddle :
        τ₃.hom.app (op ⊤) b =
          ((restrict AddCommGrpCat V.isOpenEmbedding ⋙
            pushforward AddCommGrpCat V.inclusion').map pres.g).hom.app
              (op ⊤) y := by
      dsimp only [τ₃, y]
      erw [hom_naturality_apply pres.g]
      dsimp [presᵥ']
      simp only [hs]
      exact
        (restrict_restrict_apply b
          (V.isOpenEmbedding.isOpenMap.adjunction.counit.app ⊤).op
          V.leTop.op
          (homOfLE
            (le_of_eq (Opens.isOpenEmbedding_obj_top V))).op).symm
    exact hleft.trans (hmiddle.trans hright.symm)
  have hnatural :=
    CategoryTheory.Sheaf.H.connectingHom_naturality
      0 1 rfl presEx presᵥEx res
        ((CategoryTheory.Sheaf.H.equiv₀ pres.X₃
          Limits.isTerminalTop).symm b)
  let y := pres.X₂.restrictOfEq
    (Opens.isOpenEmbedding_obj_top V) s
  have hresZero :
      CategoryTheory.Sheaf.H.map res.τ₃ 0
          ((CategoryTheory.Sheaf.H.equiv₀ pres.X₃
            Limits.isTerminalTop).symm b) =
        (CategoryTheory.Sheaf.H.equiv₀ presᵥ.X₃
          Limits.isTerminalTop).symm
            (presᵥ.g.hom.app (op ⊤) y) := by
    exact
      (CategoryTheory.Sheaf.H.equiv₀_symm_naturality
        Limits.isTerminalTop res.τ₃ b).trans
        (congrArg
          (fun z =>
            (CategoryTheory.Sheaf.H.equiv₀ presᵥ.X₃
              Limits.isTerminalTop).symm z)
          hres)
  have hmapInput :
      CategoryTheory.Sheaf.H.map res.τ₃ 0
          ((CategoryTheory.Sheaf.H.equiv₀ pres.X₃
            Limits.isTerminalTop).symm b) =
        CategoryTheory.Sheaf.H.map presᵥ.g 0
          ((CategoryTheory.Sheaf.H.equiv₀ presᵥ.X₂
            Limits.isTerminalTop).symm y) :=
    hresZero.trans
      (CategoryTheory.Sheaf.H.equiv₀_symm_naturality
        Limits.isTerminalTop presᵥ.g y).symm
  have hzero :
      CategoryTheory.Sheaf.H.connectingHom
          presᵥEx 0 1 rfl
          (CategoryTheory.Sheaf.H.map res.τ₃ 0
            ((CategoryTheory.Sheaf.H.equiv₀ pres.X₃
              Limits.isTerminalTop).symm b)) = 0 :=
    (congrArg
      (CategoryTheory.Sheaf.H.connectingHom presᵥEx 0 1 rfl)
      hmapInput).trans
        (CategoryTheory.Sheaf.H.longSequence_comp_zero₃
          presᵥEx 0 1 rfl
            ((CategoryTheory.Sheaf.H.equiv₀ presᵥ.X₂
              Limits.isTerminalTop).symm y))
  exact hnatural.symm.trans hzero

/--
Every class in degree `n + 1` vanishes on a basis-valued open cover if
degrees `1, …, n` vanish on basis opens.
-/
theorem kempf_local_vanishing
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) {B : Set (Opens X)}
    (hB : Opens.IsBasis B)
    (hinter : ∀ U V : Opens X,
      U ∈ B → V ∈ B → U ⊓ V ∈ B)
    (vanish : ∀ (r : ℕ) (U : Opens X),
      1 ≤ r → r ≤ n → U ∈ B →
        Subsingleton
          (CategoryTheory.Sheaf.H
            ((restrict AddCommGrpCat.{u}
              U.isOpenEmbedding).obj F) r))
    (c : CategoryTheory.Sheaf.H F (n + 1)) :
    ∃ (I : Type u) (U : I → Opens X),
      IsOpenCover U ∧
        ∀ i, U i ∈ B ∧
          CategoryTheory.Sheaf.H.map
            ((toRestrict _ (U i)).app F) (n + 1) c = 0 := by
  induction n generalizing F with
  | zero =>
      use X,
        fun x =>
          (one_ex_opens_toRestrict_app_zero F hB c x).choose
      refine ⟨?_, fun x =>
        (one_ex_opens_toRestrict_app_zero
          F hB c x).choose_spec.2⟩
      rw [IsOpenCover.def]
      exact fun x =>
        ⟨x,
          (one_ex_opens_toRestrict_app_zero
            F hB c x).choose_spec.1⟩
  | succ n hn =>
      let ip := (EnoughInjectives.presentation F).some
      let pres := ip.shortComplex
      letI : Injective pres.X₂ := ip.injective
      have presEx : pres.ShortExact :=
        (EnoughInjectives.presentation F).some.shortExact_shortComplex
      obtain ⟨b, hb⟩ :=
        CategoryTheory.Sheaf.H.longSequence_exact₁
          presEx (n + 1) (n + 1 + 1) rfl c
          ((cohomology_subsingleton_of_injective
            pres.X₂ (n + 1)).elim _ _)
      obtain ⟨I, U, hU₁, hU₂⟩ :=
        hn pres.X₃
          (by
            intro r U hr₁ hr₂ hU
            refine subsingleton_of_forall_eq 0 (fun x => ?_)
            let presᵤ := pres.map
              (restrict _ U.isOpenEmbedding)
            have presᵤEx : presᵤ.ShortExact :=
              presEx.map_of_exact _
            have hnext :
                Subsingleton (presᵤ.X₁.H (r + 1)) :=
              vanish (r + 1) U (by omega) (by omega) hU
            obtain ⟨x₂, rfl⟩ :=
              CategoryTheory.Sheaf.H.longSequence_exact₃
                presᵤEx r (r + 1) rfl x
                (Subsingleton.elim _ _)
            have hflasque :
                Subsingleton (presᵤ.X₂.H r) := by
              letI : pres.X₂.IsFlasque :=
                @IsFlasque.of_injective _ pres.X₂ this
              letI : presᵤ.X₂.IsFlasque :=
                IsFlasque.of_restrict _ pres.X₂ U.isOpenEmbedding
              rw [(Nat.sub_eq_iff_eq_add hr₁).mp rfl]
              exact IsFlasque.subsingleton_H (r - 1)
            rw [Subsingleton.elim x₂ 0]
            exact map_zero _)
          b
      use I, U, hU₁
      refine fun i => ⟨(hU₂ i).1, ?_⟩
      have hrestricted :
          (pres.map
            (restrict AddCommGrpCat
              (U i).isOpenEmbedding ⋙
              pushforward AddCommGrpCat
                (U i).inclusion')).ShortExact := by
        have hexact :=
          ((restrict AddCommGrpCat
            (U i).isOpenEmbedding ⋙
            pushforward AddCommGrpCat
              (U i).inclusion').preservesFiniteLimits_tfae.out
              3 1 rfl rfl).mp inferInstance pres
            ⟨presEx.1, presEx.2⟩
        refine ShortComplex.ShortExact.mk'
          hexact.1 hexact.2 ?_
        dsimp
        rw [← isLocallySurjective_iff_epi,
          Presheaf.isLocallySurjective_iff]
        intro V s x hx
        obtain ⟨W, hW⟩ :=
          Opens.isBasis_iff_nbhd.mp hB hx
        use W, hW.2.2
        refine ⟨?_, hW.2.1⟩
        have fs {V : Opens X} (hV : V ∈ B) :
            Function.Surjective
              (pres.g.hom.app (op V)) := by
          erw [← Opens.isOpenEmbedding_obj_top V]
          let presᵥ :=
            pres.map (restrict _ V.isOpenEmbedding)
          have presᵥEx : presᵥ.ShortExact :=
            presEx.map_of_exact _
          have hdegreeOne :
              Subsingleton (presᵥ.X₁.H 1) :=
            vanish 1 V (le_refl 1) (by omega) hV
          exact
            CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
              presᵥEx Limits.isTerminalTop
        have hopen :
            (U i).isOpenEmbedding.functor.obj
              ((Opens.map (U i).inclusion').obj W) ∈ B := by
          rw [Opens.functor_map_eq_inf]
          exact hinter _ _ hW.1 (hU₂ i).1
        apply fs hopen
      have r₁ :=
        CategoryTheory.Sheaf.H.connectingHom_naturality
          (n + 1) (n + 1 + 1) rfl
          presEx hrestricted
          (pres.mapNatTrans
            (toRestrict AddCommGrpCat (U i))) b
      have r₂ := (hU₂ i).2
      have hstart :
          CategoryTheory.Sheaf.H.map
              ((toRestrict AddCommGrpCat (U i)).app F)
              (n + 1 + 1) c =
            CategoryTheory.Sheaf.H.map
              (pres.mapNatTrans
                (toRestrict AddCommGrpCat (U i))).τ₁
              (n + 1 + 1)
              (CategoryTheory.Sheaf.H.connectingHom
                presEx (n + 1) (n + 1 + 1) rfl b) := by
        rw [hb]
        rfl
      have hnatural :
          CategoryTheory.Sheaf.H.map
              (pres.mapNatTrans
                (toRestrict AddCommGrpCat (U i))).τ₁
              (n + 1 + 1)
              (CategoryTheory.Sheaf.H.connectingHom
                presEx (n + 1) (n + 1 + 1) rfl b) =
            CategoryTheory.Sheaf.H.connectingHom
              hrestricted (n + 1) (n + 1 + 1) rfl
              (CategoryTheory.Sheaf.H.map
                (pres.mapNatTrans
                  (toRestrict AddCommGrpCat (U i))).τ₃
                (n + 1) b) :=
        r₁.symm
      have hzero :
          CategoryTheory.Sheaf.H.connectingHom
              hrestricted (n + 1) (n + 1 + 1) rfl
              (CategoryTheory.Sheaf.H.map
                (pres.mapNatTrans
                  (toRestrict AddCommGrpCat (U i))).τ₃
                (n + 1) b) = 0 := by
        change
            CategoryTheory.Sheaf.H.connectingHom
              hrestricted (n + 1) (n + 1 + 1) rfl
              (CategoryTheory.Sheaf.H.map
                ((toRestrict AddCommGrpCat (U i)).app pres.X₃)
                (n + 1) b) = 0
        rw [r₂]
        exact map_zero _
      exact hstart.trans (hnatural.trans hzero)

end TopCat.Sheaf
