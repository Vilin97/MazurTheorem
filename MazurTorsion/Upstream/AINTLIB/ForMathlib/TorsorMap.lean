/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient
import MazurTorsion.Upstream.AINTLIB.ForMathlib.PullbackLocalAtTarget
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# G-maps of finite étale G-torsors ([B2a]/[B2b], KM pp. 115–116)

* `isIso_of_equivariant_of_torsor` — a `G`-equivariant `S`-morphism between `G`-torsors is an
  isomorphism ("being a G-map between G-torsors", KM p. 116): the base change along the fppf
  cover is identified componentwise with the torsor trivializations (`FinitaryExtensive Scheme`
  for the `∐`-pullback interchange), and descends by `isIso_of_isPullback_of_fppf`.
* `isPullback_of_equivariant_of_torsor` — a `G`-equivariant morphism of `G`-torsors over
  `f₀ : S ⟶ S'` is cartesian (KM p. 115): the comparison into the pulled-back torsor is a
  `G`-map of torsors, hence an iso.

* `existsUnique_descent_of_torsor` — a `G`-invariant morphism out of a `G`-torsor over an
  **arbitrary** base descends uniquely through it (the torsor realizes its base as the quotient):
  the `torsorCompare` presentation reduces the kernel-pair coequalizing condition to invariance,
  and a quasi-compact + surjective + flat morphism is an fpqc effective epimorphism.
* `isIso_torsorCompare_pullback`, `isIso_sigmaDesc_of_isPullback`, `isIso_sigmaDesc_section` —
  the base-change/trivialization helpers (also used by the KM 4.7.0 bijection's curve-level
  descent).

These are the torsor facts of the KM 4.7.0 representability argument.
-/
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace ModularCurves

/-- The `∐_G`-torsor presentation: `(γ, z) ↦ (γ·z, z)`. -/
noncomputable def torsorCompare {S Z : Scheme.{u}} {G : Type u} [Group G]
    (fZ : Z ⟶ S) (σZ : SchemeAction G Z) (hover : ∀ γ, σZ.hom γ ≫ fZ = fZ) :
    (∐ fun _ : G => Z) ⟶ Limits.pullback fZ fZ :=
  Limits.Sigma.desc fun γ : G => Limits.pullback.lift (σZ.hom γ) (𝟙 Z)
    (by rw [Category.id_comp]; exact hover γ)

@[simp]
theorem ι_torsorCompare {S Z : Scheme.{u}} {G : Type u} [Group G]
    (fZ : Z ⟶ S) (σZ : SchemeAction G Z) (hover : ∀ γ, σZ.hom γ ≫ fZ = fZ) (γ : G) :
    Sigma.ι (fun _ : G => Z) γ ≫ torsorCompare fZ σZ hover =
      pullback.lift (σZ.hom γ) (𝟙 Z) (by rw [Category.id_comp]; exact hover γ) := by
  simp [torsorCompare]

/-- The `G`-action on `pullback fW f₀` pulled back from an action on `fW : W ⟶ S'` over `S'`,
acting on the `W`-factor. -/
noncomputable def pullbackTorsorAction {S S' W : Scheme.{u}} {G : Type u} [Group G]
    {fW : W ⟶ S'} (σW : SchemeAction G W) (hWover : ∀ γ, σW.hom γ ≫ fW = fW) (f₀ : S ⟶ S') :
    SchemeAction G (pullback fW f₀) where
  hom γ := pullback.map fW f₀ fW f₀ (σW.hom γ) (𝟙 S) (𝟙 S')
    (by rw [Category.comp_id, hWover]) (by rw [Category.comp_id, Category.id_comp])
  hom_one := by apply pullback.hom_ext <;> simp [pullback.map, σW.hom_one]
  hom_mul γ δ := by
    apply pullback.hom_ext <;>
      simp [pullback.map, σW.hom_mul, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc]

@[simp]
theorem pullbackTorsorAction_hom {S S' W : Scheme.{u}} {G : Type u} [Group G]
    {fW : W ⟶ S'} (σW : SchemeAction G W) (hWover : ∀ γ, σW.hom γ ≫ fW = fW) (f₀ : S ⟶ S')
    (γ : G) :
    (pullbackTorsorAction σW hWover f₀).hom γ =
      pullback.map fW f₀ fW f₀ (σW.hom γ) (𝟙 S) (𝟙 S')
        (by rw [Category.comp_id, hWover]) (by rw [Category.comp_id, Category.id_comp]) := rfl

theorem pullbackTorsorAction_over {S S' W : Scheme.{u}} {G : Type u} [Group G]
    {fW : W ⟶ S'} (σW : SchemeAction G W) (hWover : ∀ γ, σW.hom γ ≫ fW = fW) (f₀ : S ⟶ S')
    (γ : G) :
    (pullbackTorsorAction σW hWover f₀).hom γ ≫ pullback.snd fW f₀ = pullback.snd fW f₀ := by
  simp [pullback.map, pullback.lift_snd]

/-- **Descent of coproduct decompositions** (schemes form a finitary extensive category): given a
trivialization `κ : ∐_G Y ≅ Q`, a morphism `q : Q' ⟶ Q`, and a family `ι' γ : X ⟶ Q'` fitting in
componentwise pullback squares over the components of `κ`, the induced comparison
`∐_G X ⟶ Q'` is an isomorphism. -/
theorem isIso_sigmaDesc_of_isPullback {G : Type u} [Finite G] {X Y Q Q' : Scheme.{u}}
    (κ : (∐ fun _ : G => Y) ⟶ Q) [IsIso κ] (q : Q' ⟶ Q) (v : X ⟶ Y) (ι' : G → (X ⟶ Q'))
    (h : ∀ γ : G, IsPullback (ι' γ) v q (Sigma.ι (fun _ : G => Y) γ ≫ κ)) :
    IsIso (Sigma.desc ι') := by
  have vK : IsVanKampenColimit (Cofan.mk (∐ fun _ : G => Y) (Sigma.ι fun _ : G => Y)) :=
    FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct fun _ : G => Y)
  have hnat : Discrete.natTrans (fun _ => v) ≫
        (Cofan.mk (∐ fun _ : G => Y) (Sigma.ι fun _ : G => Y)).ι =
      (Cofan.mk Q' ι').ι ≫ (Functor.const (Discrete G)).map (q ≫ inv κ) := by
    ext ⟨γ⟩
    change v ≫ Sigma.ι (fun _ : G => Y) γ = ι' γ ≫ (q ≫ inv κ)
    rw [← Category.assoc, (h γ).w]
    simp
  have hsq : ∀ j : Discrete G,
      IsPullback ((Cofan.mk Q' ι').ι.app j) ((Discrete.natTrans fun _ => v).app j) (q ≫ inv κ)
        ((Cofan.mk (∐ fun _ : G => Y) (Sigma.ι fun _ : G => Y)).ι.app j) := by
    rintro ⟨γ⟩
    have hb : IsPullback (Sigma.ι (fun _ : G => Y) γ ≫ κ) (𝟙 Y) (inv κ)
        (Sigma.ι (fun _ : G => Y) γ) :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have hp := (h γ).paste_vert hb
    rw [Category.comp_id] at hp
    exact hp
  obtain ⟨hc⟩ := (vK (Cofan.mk Q' ι') (Discrete.natTrans fun _ => v)
    ((q ≫ inv κ : Q' ⟶ ∐ fun _ : G => Y)) hnat
    (NatTrans.Equifibered.of_discrete _)).mpr hsq
  have hdesc : Sigma.desc ι' =
      ((coproductIsCoproduct fun _ : G => X).coconePointUniqueUpToIso hc).hom := by
    refine Sigma.hom_ext _ _ fun γ => ?_
    rw [Sigma.ι_desc]
    exact ((coproductIsCoproduct fun _ : G => X).comp_coconePointUniqueUpToIso_hom hc ⟨γ⟩).symm
  rw [hdesc]
  infer_instance

/-- **Base change of a torsor is a torsor**: if `torsorCompare fW σW hWover` is an isomorphism,
so is the torsor comparison of the pulled-back action on `pullback fW f₀ ⟶ S`. -/
theorem isIso_torsorCompare_pullback {S S' W : Scheme.{u}} {G : Type u} [Group G]
    [Finite G] {fW : W ⟶ S'} (σW : SchemeAction G W) (hWover : ∀ γ, σW.hom γ ≫ fW = fW)
    (hWtors : IsIso (torsorCompare fW σW hWover)) (f₀ : S ⟶ S') :
    IsIso (torsorCompare (pullback.snd fW f₀) (pullbackTorsorAction σW hWover f₀)
      (pullbackTorsorAction_over σW hWover f₀)) := by
  haveI := hWtors
  have hq : pullback.snd fW f₀ ≫ f₀ = pullback.fst fW f₀ ≫ fW := pullback.condition.symm
  -- the comparison `P ×_S P ⟶ W ×_{S'} W` on both `W`-factors
  have hsq : ∀ γ : G,
      IsPullback
        (pullback.lift ((pullbackTorsorAction σW hWover f₀).hom γ) (𝟙 (pullback fW f₀))
          (by rw [Category.id_comp]; exact pullbackTorsorAction_over σW hWover f₀ γ))
        (pullback.fst fW f₀)
        (pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
          (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ hq hq)
        (Sigma.ι (fun _ : G => W) γ ≫ torsorCompare fW σW hWover) := by
    intro γ
    rw [ι_torsorCompare]
    -- the right rectangle: `P ×_S P` is the pullback of `W ×_{S'} W ⟶ W` along `fst : P ⟶ W`
    have t : IsPullback (pullback.snd (pullback.snd fW f₀) (pullback.snd fW f₀))
        (pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
          (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ hq hq)
        (pullback.fst fW f₀) (pullback.snd fW fW) := by
      apply IsPullback.of_bot _ _ ((IsPullback.of_hasPullback fW fW).flip)
      · rw [show pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
              (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ hq hq ≫ pullback.fst fW fW =
            pullback.fst (pullback.snd fW f₀) (pullback.snd fW f₀) ≫ pullback.fst fW f₀ from
            pullback.lift_fst _ _ _,
          show pullback.fst fW f₀ ≫ fW = pullback.snd fW f₀ ≫ f₀ from pullback.condition]
        exact (IsPullback.of_hasPullback (pullback.snd fW f₀) (pullback.snd fW f₀)).flip.paste_vert
          (IsPullback.of_hasPullback fW f₀).flip
      · simp [pullback.map, pullback.lift_snd]
    apply IsPullback.of_right _ _ t
    · rw [pullback.lift_snd, pullback.lift_snd]
      exact IsPullback.of_id_fst
    · apply pullback.hom_ext <;>
        simp [pullback.map, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  exact isIso_sigmaDesc_of_isPullback (torsorCompare fW σW hWover)
    (pullback.map (pullback.snd fW f₀) (pullback.snd fW f₀) fW fW
      (pullback.fst fW f₀) (pullback.fst fW f₀) f₀ hq hq)
    (pullback.fst fW f₀) _ hsq

/-- **A torsor with a section is trivial**: if `fP : P ⟶ Z` is a `G`-torsor and `s : Z ⟶ P` a
section, then `(γ, z) ↦ γ·s(z)` is an isomorphism `∐_G Z ≅ P`. -/
theorem isIso_sigmaDesc_section {Z P : Scheme.{u}} {G : Type u} [Group G] [Finite G]
    {fP : P ⟶ Z} (σP : SchemeAction G P) (hPover : ∀ γ, σP.hom γ ≫ fP = fP)
    (hPtors : IsIso (torsorCompare fP σP hPover)) (s : Z ⟶ P) (hs : s ≫ fP = 𝟙 Z) :
    IsIso (Sigma.desc fun γ : G => s ≫ σP.hom γ) := by
  haveI := hPtors
  have hq : 𝟙 P ≫ fP = (fP ≫ s) ≫ fP := by
    rw [Category.id_comp, Category.assoc, hs, Category.comp_id]
  have hsq : ∀ γ : G, IsPullback (s ≫ σP.hom γ) s (pullback.lift (𝟙 P) (fP ≫ s) hq)
      (Sigma.ι (fun _ : G => P) γ ≫ torsorCompare fP σP hPover) := by
    intro γ
    rw [ι_torsorCompare]
    -- the right rectangle: `P` is the pullback of `P ×_Z P ⟶ P` along the section
    have t : IsPullback fP (pullback.lift (𝟙 P) (fP ≫ s) hq) s (pullback.snd fP fP) := by
      apply IsPullback.of_bot _ _ ((IsPullback.of_hasPullback fP fP).flip)
      · rw [pullback.lift_fst, hs]
        exact IsPullback.of_id_snd
      · rw [pullback.lift_snd]
    apply IsPullback.of_right _ _ t
    · have h1 : (s ≫ σP.hom γ) ≫ fP = 𝟙 Z := by rw [Category.assoc, hPover, hs]
      rw [h1, pullback.lift_snd]
      exact IsPullback.of_id_fst
    · apply pullback.hom_ext <;>
        simp [pullback.lift_fst, pullback.lift_snd, reassoc_of% (hPover γ), reassoc_of% hs]
  exact isIso_sigmaDesc_of_isPullback (torsorCompare fP σP hPover)
    (pullback.lift (𝟙 P) (fP ≫ s) hq) s _ hsq

/-- **([B2b], KM p. 116)** A `G`-equivariant `S`-morphism between finite étale `G`-torsors is an
isomorphism. -/
theorem isIso_of_equivariant_of_torsor {S Z W : Scheme.{u}} {G : Type u} [Group G] [Finite G]
    {fZ : Z ⟶ S} {fW : W ⟶ S} (σZ : SchemeAction G Z) (σW : SchemeAction G W)
    (hZover : ∀ γ, σZ.hom γ ≫ fZ = fZ) (hWover : ∀ γ, σW.hom γ ≫ fW = fW)
    (hZtors : IsIso (torsorCompare fZ σZ hZover))
    (hWtors : IsIso (torsorCompare fW σW hWover))
    [Surjective fZ] [Flat fZ] [QuasiCompact fZ]
    (u : Z ⟶ W) (hu : u ≫ fW = fZ)
    (hequiv : ∀ γ, σZ.hom γ ≫ u = u ≫ σW.hom γ) :
    IsIso u := by
  haveI := hZtors
  -- `u` gives a section of the pulled-back torsor `pullback fW fZ ⟶ Z`,
  -- so the latter is trivialized by `(γ, z) ↦ γ·(u z, z)`
  have hlift : u ≫ fW = 𝟙 Z ≫ fZ := by rw [Category.id_comp]; exact hu
  have hsec : pullback.lift u (𝟙 Z) hlift ≫ pullback.snd fW fZ = 𝟙 Z := pullback.lift_snd _ _ _
  have htU : IsIso (Sigma.desc fun γ : G =>
      pullback.lift u (𝟙 Z) hlift ≫ (pullbackTorsorAction σW hWover fZ).hom γ) :=
    isIso_sigmaDesc_section (pullbackTorsorAction σW hWover fZ)
      (pullbackTorsorAction_over σW hWover fZ)
      (isIso_torsorCompare_pullback σW hWover hWtors fZ)
      (pullback.lift u (𝟙 Z) hlift) hsec
  -- the trivialization factors as `torsorCompare fZ` followed by the base change of `u`
  have e₁ : fZ ≫ 𝟙 S = u ≫ fW := by rw [Category.comp_id, hu]
  have e₂ : fZ ≫ 𝟙 S = 𝟙 Z ≫ fZ := by rw [Category.comp_id, Category.id_comp]
  have hfac : torsorCompare fZ σZ hZover ≫ pullback.map fZ fZ fW fZ u (𝟙 Z) (𝟙 S) e₁ e₂ =
      Sigma.desc fun γ : G =>
        pullback.lift u (𝟙 Z) hlift ≫ (pullbackTorsorAction σW hWover fZ).hom γ := by
    refine Sigma.hom_ext _ _ fun γ => ?_
    rw [← Category.assoc, ι_torsorCompare, Sigma.ι_desc]
    apply pullback.hom_ext
    · simp [pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, hequiv γ]
    · simp [pullback.map, pullback.lift_snd]
  haveI hbc : IsIso (pullback.map fZ fZ fW fZ u (𝟙 Z) (𝟙 S) e₁ e₂) := by
    haveI : IsIso (torsorCompare fZ σZ hZover ≫
        pullback.map fZ fZ fW fZ u (𝟙 Z) (𝟙 S) e₁ e₂) := by
      rw [hfac]; exact htU
    exact IsIso.of_isIso_comp_left (torsorCompare fZ σZ hZover) _
  -- so `u` is an isomorphism after the fppf base change `fZ`; descend
  have hsq : IsPullback (pullback.map fZ fZ fW fZ u (𝟙 Z) (𝟙 S) e₁ e₂)
      (pullback.fst fZ fZ) (pullback.fst fW fZ) u := by
    apply IsPullback.of_right _ _ ((IsPullback.of_hasPullback fW fZ).flip)
    · rw [show pullback.map fZ fZ fW fZ u (𝟙 Z) (𝟙 S) e₁ e₂ ≫ pullback.snd fW fZ =
          pullback.snd fZ fZ from by simp [pullback.map, pullback.lift_snd], hu]
      exact (IsPullback.of_hasPullback fZ fZ).flip
    · simp [pullback.map, pullback.lift_fst]
  haveI : Surjective (pullback.fst fW fZ) := MorphismProperty.pullback_fst _ _ ‹Surjective fZ›
  haveI : Flat (pullback.fst fW fZ) := MorphismProperty.pullback_fst _ _ ‹Flat fZ›
  haveI : QuasiCompact (pullback.fst fW fZ) := MorphismProperty.pullback_fst _ _ ‹QuasiCompact fZ›
  exact isIso_of_isPullback_of_fppf hsq

/-- **([B2a], KM p. 115)** A `G`-equivariant morphism of finite étale `G`-torsors over a base
morphism `f₀ : S ⟶ S'` is cartesian. -/
theorem isPullback_of_equivariant_of_torsor {S S' Z W : Scheme.{u}} {G : Type u} [Group G]
    [Finite G]
    {fZ : Z ⟶ S} {fW : W ⟶ S'} (σZ : SchemeAction G Z) (σW : SchemeAction G W)
    (hZover : ∀ γ, σZ.hom γ ≫ fZ = fZ) (hWover : ∀ γ, σW.hom γ ≫ fW = fW)
    (hZtors : IsIso (torsorCompare fZ σZ hZover))
    (hWtors : IsIso (torsorCompare fW σW hWover))
    [Surjective fZ] [Flat fZ] [QuasiCompact fZ]
    [Surjective fW] [Flat fW] [QuasiCompact fW]
    (u : Z ⟶ W) (f₀ : S ⟶ S') (hu : u ≫ fW = fZ ≫ f₀)
    (hequiv : ∀ γ, σZ.hom γ ≫ u = u ≫ σW.hom γ) :
    IsPullback u fZ fW f₀ := by
  -- the comparison `c : Z ⟶ S ×_{S'} W` is a `G`-map of `G`-torsors over `S`
  have hc : pullback.lift u fZ hu ≫ pullback.snd fW f₀ = fZ := pullback.lift_snd _ _ _
  have hcequiv : ∀ γ, σZ.hom γ ≫ pullback.lift u fZ hu =
      pullback.lift u fZ hu ≫ (pullbackTorsorAction σW hWover f₀).hom γ := by
    intro γ
    apply pullback.hom_ext
    · simp [pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, hequiv γ]
    · simp [pullback.map, pullback.lift_snd, hZover γ]
  haveI : IsIso (pullback.lift u fZ hu) :=
    isIso_of_equivariant_of_torsor σZ (pullbackTorsorAction σW hWover f₀) hZover
      (pullbackTorsorAction_over σW hWover f₀) hZtors
      (isIso_torsorCompare_pullback σW hWover hWtors f₀) (pullback.lift u fZ hu) hc hcequiv
  exact IsPullback.of_iso_pullback ⟨hu⟩ (asIso (pullback.lift u fZ hu))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)


/-! ### [B2c′] Torsor morphism-descent (KM p. 114/115) -/

/-- The kernel pair of a `G`-torsor is coequalized by any `G`-invariant morphism: the
`torsorCompare` presentation `∐_G Z ≅ Z ×_S Z` reduces the check to `σ γ ≫ q = q`. -/
theorem kernelPair_coequalized_of_invariant {S Z Y : Scheme.{u}} {G : Type u} [Group G]
    {f : Z ⟶ S} (σ : SchemeAction G Z) (hover : ∀ γ, σ.hom γ ≫ f = f)
    (htors : IsIso (torsorCompare f σ hover))
    (q : Z ⟶ Y) (hq : ∀ γ, σ.hom γ ≫ q = q) :
    pullback.fst f f ≫ q = pullback.snd f f ≫ q := by
  haveI := htors
  rw [← cancel_epi (torsorCompare f σ hover)]
  refine Sigma.hom_ext _ _ fun γ => ?_
  simp only [← Category.assoc, ι_torsorCompare, pullback.lift_fst, pullback.lift_snd]
  rw [hq γ, Category.id_comp]

/-- **([B2c′], torsor morphism-descent — KM p. 114/115)** A `G`-invariant morphism out of a
finite étale `G`-torsor `f : Z ⟶ S` descends **uniquely** through `f` (the torsor realizes its
base `S` as the quotient `Z/G`) — over an **arbitrary** base. The `torsorCompare` presentation
`∐_G Z ≅ Z ×_S Z` reduces the kernel-pair coequalizing condition to invariance, and a
quasi-compact + surjective + flat morphism is an fpqc effective epimorphism
(`AlgebraicGeometry.Sites.Fpqc`); no affineness or finiteness of `G` is needed. -/
theorem existsUnique_descent_of_torsor {S Z Y : Scheme.{u}} {G : Type u} [Group G]
    {f : Z ⟶ S} (σ : SchemeAction G Z) (hover : ∀ γ, σ.hom γ ≫ f = f)
    (htors : IsIso (torsorCompare f σ hover))
    [Surjective f] [Flat f] [QuasiCompact f]
    (q : Z ⟶ Y) (hq : ∀ γ, σ.hom γ ≫ q = q) :
    ∃! u : S ⟶ Y, f ≫ u = q := by
  have hqcoeq : pullback.fst f f ≫ q = pullback.snd f f ≫ q :=
    kernelPair_coequalized_of_invariant σ hover htors q hq
  -- any pair coequalized by `f` is coequalized by `q`, via the kernel-pair lift
  have h : ∀ {Z' : Scheme.{u}} (g₁ g₂ : Z' ⟶ Z), g₁ ≫ f = g₂ ≫ f → g₁ ≫ q = g₂ ≫ q := by
    intro Z' g₁ g₂ heq
    calc g₁ ≫ q
        = pullback.lift g₁ g₂ heq ≫ pullback.fst f f ≫ q := by
          rw [← Category.assoc, pullback.lift_fst]
      _ = pullback.lift g₁ g₂ heq ≫ pullback.snd f f ≫ q := by rw [hqcoeq]
      _ = g₂ ≫ q := by rw [← Category.assoc, pullback.lift_snd]
  exact ⟨EffectiveEpi.desc f q h, EffectiveEpi.fac f q h,
    fun u hu => EffectiveEpi.uniq f q h u hu⟩


/-! ### fppf descent of a cartesian square (KM 4.7.0 bijection, curve-square) -/

/-- **fppf descent of a cartesian square**: a commuting square whose base change along an fppf
cover `c` of the bottom-right is a pullback is itself a pullback. (The comparison to the pullback
is iso after fppf base change, hence iso by `isIso_of_isPullback_of_fppf`.) -/
theorem isPullback_of_fppf_baseChange {E B XE XB W : Scheme.{u}}
    {πY : E ⟶ B} {vtop : E ⟶ XE} {πX : XE ⟶ XB} {f₀ : B ⟶ XB}
    (hw : vtop ≫ πX = πY ≫ f₀)
    (c : W ⟶ B) [Surjective c] [Flat c] [QuasiCompact c]
    -- the base change of the square along `c` is a pullback:
    (hbc : IsPullback (pullback.fst πY c ≫ vtop) (pullback.snd πY c)
      πX (c ≫ f₀)) :
    IsPullback vtop πY πX f₀ := by
  obtain ⟨κ, hκ_fst, hκ_snd⟩ :
      ∃ κ : E ⟶ pullback πX f₀,
        κ ≫ pullback.fst πX f₀ = vtop ∧ κ ≫ pullback.snd πX f₀ = πY :=
    ⟨pullback.lift vtop πY hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- It suffices to show the comparison morphism `κ : E ⟶ X ×_{XB} B` is an isomorphism.
  haveI : IsIso κ := by
    -- The comparison morphism between the fppf base changes.
    have hcomm : (pullback.fst πY c ≫ κ) ≫ pullback.snd πX f₀ = pullback.snd πY c ≫ c := by
      rw [Category.assoc, hκ_snd]
      exact pullback.condition
    set fst : pullback πY c ⟶ pullback (pullback.snd πX f₀) c :=
      pullback.lift (pullback.fst πY c ≫ κ) (pullback.snd πY c) hcomm with hfst_def
    have fst_fst : fst ≫ pullback.fst (pullback.snd πX f₀) c = pullback.fst πY c ≫ κ := by
      rw [hfst_def]; exact pullback.lift_fst _ _ _
    have fst_snd : fst ≫ pullback.snd (pullback.snd πX f₀) c = pullback.snd πY c := by
      rw [hfst_def]; exact pullback.lift_snd _ _ _
    -- `fst` agrees with `hbc.isoPullback` through `pullbackLeftPullbackSndIso`, hence is an iso.
    haveI : IsIso fst := by
      have key : fst ≫ (pullbackLeftPullbackSndIso πX f₀ c).hom = hbc.isoPullback.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst, hbc.isoPullback_hom_fst,
            ← Category.assoc, fst_fst, Category.assoc, hκ_fst]
        · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, hbc.isoPullback_hom_snd, fst_snd]
      have hfst_eq : fst = hbc.isoPullback.hom ≫ (pullbackLeftPullbackSndIso πX f₀ c).inv := by
        rw [← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [hfst_eq]; infer_instance
    -- The fppf leg inherits surjectivity, flatness and quasi-compactness by base change.
    haveI : Surjective (pullback.fst (pullback.snd πX f₀) c) :=
      MorphismProperty.pullback_fst (P := @Surjective) (pullback.snd πX f₀) c inferInstance
    haveI : Flat (pullback.fst (pullback.snd πX f₀) c) :=
      MorphismProperty.pullback_fst (P := @Flat) (pullback.snd πX f₀) c inferInstance
    haveI : QuasiCompact (pullback.fst (pullback.snd πX f₀) c) :=
      MorphismProperty.pullback_fst (P := @QuasiCompact) (pullback.snd πX f₀) c inferInstance
    -- The base change of the comparison square along `c` is a pullback (left-cancellation of the
    -- standard pasting square).
    have hsq : IsPullback fst (pullback.fst πY c) (pullback.fst (pullback.snd πX f₀) c) κ := by
      refine IsPullback.of_right ?_ fst_fst
        (IsPullback.of_hasPullback (pullback.snd πX f₀) c).flip
      rw [fst_snd, hκ_snd]
      exact (IsPullback.of_hasPullback πY c).flip
    exact isIso_of_isPullback_of_fppf hsq
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso κ) hκ_fst hκ_snd

end ModularCurves
