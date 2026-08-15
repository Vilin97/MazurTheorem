/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtalePointSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient

/-!
# Equivariant pointwise split charts for finite étale morphisms

An equivariant finite étale morphism has invariant fiber rank under the
target action.  At a fixed target point, refine the constant-rank locus to a
stable affine neighborhood.  Its inverse image is stable as well, and the
restricted finite étale morphism splits after an affine fpqc cover.

The named downstream consumer is the occurrence-wise selected-component
chart in `GeometricAssignedAffineChart`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteEtalePointSplitChart

open AffineFiniteEtaleSplitChart
open EtaleSplitChart
open FiniteFlatConstantRankNeighborhood

variable {G : Type*} [Group G]
variable {X Y : Scheme.{u}} (σ : SchemeAction G X) (τ : SchemeAction G Y)
variable (f : X ⟶ Y) [Etale f] [IsFinite f]

/-- Equivariance by automorphisms preserves the fiber rank of a finite
étale morphism. -/
theorem finrank_action
    (heq : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    (g : G) (y : Y) :
    f.finrank (τ.hom g y) = f.finrank y := by
  have hpb : IsPullback (σ.hom g) f f (τ.hom g) :=
    IsPullback.of_horiz_isIso ⟨heq g⟩
  exact (Scheme.Hom.finrank_of_isPullback
    (σ.hom g) f f (τ.hom g) hpb y).symm

/-- The constant-rank locus through a point is stable under every
equivariant target action. -/
theorem rankOpen_isStable
    (heq : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g) (y : Y) :
    τ.IsStableOpen (rankOpen f y) := by
  intro g
  ext z
  change f.finrank (τ.hom g z) = f.finrank y ↔
    f.finrank z = f.finrank y
  rw [finrank_action σ τ f heq]

omit [Etale f] [IsFinite f] in
/-- The inverse image of a stable open is stable for an equivariant
morphism. -/
theorem preimage_isStable
    (heq : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    {V : Y.Opens} (hV : τ.IsStableOpen V) :
    σ.IsStableOpen (f ⁻¹ᵁ V) := by
  intro g
  ext x
  change f (σ.hom g x) ∈ V ↔ f x ∈ V
  have hx := congrArg (fun q : X ⟶ Y => q x) (heq g)
  change f (σ.hom g x) = τ.hom g (f x) at hx
  rw [hx]
  exact SetLike.ext_iff.mp (hV g) (f x)

variable [Finite G]
variable [IsAffineHom (pullback.diagonal (terminal.from Y))]

/-- A fixed point has a stable affine neighborhood contained in the
constant-rank locus of a finite étale morphism. -/
theorem exists_stableAffineOpen_le_rankOpen
    (y : Y) (hfixed : ∀ g : G, τ.hom g y = y) :
    ∃ V : Y.Opens, τ.IsStableOpen V ∧ IsAffineOpen V ∧
      y ∈ V ∧ V ≤ rankOpen f y := by
  obtain ⟨_, ⟨U : Y.Opens, hUa, rfl⟩, hyU, hUrank⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (mem_rankOpen f y) (rankOpen f y).2
  let V : Y.Opens := ⨅ g : G, (τ.hom g) ⁻¹ᵁ U
  have hVs : τ.IsStableOpen V := by
    dsimp only [V]
    intro g
    have hcoe : ∀ (q : Y ⟶ Y) (W : Y.Opens),
        (↑(q ⁻¹ᵁ W) : Set Y) = q.base ⁻¹' ↑W := fun _ _ => rfl
    refine TopologicalSpace.Opens.ext ?_
    rw [hcoe, TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter]
    have htranslate : ∀ h : G,
        (τ.hom g).base ⁻¹' (↑((τ.hom h) ⁻¹ᵁ U) : Set Y) =
          ↑((τ.hom (g * h)) ⁻¹ᵁ U) := by
      intro h
      rw [hcoe, hcoe, ← Set.preimage_comp]
      congr 1
      rw [τ.hom_mul]
      rfl
    rw [Set.iInter_congr htranslate]
    exact (Equiv.mulLeft g).surjective.iInter_comp
      (fun k => (↑((τ.hom k) ⁻¹ᵁ U) : Set Y))
  have hVa : IsAffineOpen V := by
    dsimp only [V]
    exact IsAffineOpen.iInf
      (fun g => hUa.preimage_of_isIso (τ.hom g))
  have hyV : y ∈ V := by
    change y ∈ (↑(⨅ g : G, (τ.hom g) ⁻¹ᵁ U) : Set Y)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun g => by simpa [hfixed g] using hyU)
  have hVU : V ≤ U := by
    dsimp only [V]
    calc
      (⨅ g : G, (τ.hom g) ⁻¹ᵁ U) ≤ (τ.hom 1) ⁻¹ᵁ U := iInf_le _ 1
      _ = U := by rw [τ.hom_one]; rfl
  exact ⟨V, hVs, hVa, hyV, hVU.trans hUrank⟩

/-- At a fixed point, an equivariant finite étale morphism splits fpqc
locally over a stable affine constant-rank neighborhood.  Both the target
open and its source preimage retain their actions. -/
theorem exists_stableAffineOpen_fpqc_splitCover
    (heq : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    (y : Y) (hfixed : ∀ g : G, τ.hom g y = y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V),
      τ.IsStableOpen V ∧ σ.IsStableOpen (f ⁻¹ᵁ V) ∧ y ∈ V ∧
      let fV := f ∣_ V
      letI : IsAffine V.toScheme := hV
      letI : IsAffine (f ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom fV
      letI : Algebra Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤) := fV.appTop.hom.toAlgebra
      ∃ (T : Type u) (_ : CommRing T)
        (_ : Algebra Γ(V, ⊤) T)
        (_ : Module.FaithfullyFlat Γ(V, ⊤) T)
        (_ : Module.Finite Γ(V, ⊤) T)
        (_ : Algebra.Etale Γ(V, ⊤) T) (m : ℕ)
        (_e : T ⊗[Γ(V, ⊤)] Γ(f ⁻¹ᵁ V, ⊤) ≃ₐ[T] (Fin m → T))
        (q : Spec (.of T) ⟶ V.toScheme)
        (_E : pullback fV q ≅ Spec (.of (Fin m → T))),
        _E.hom ≫ splitProjection T m = pullback.snd fV q ∧
          m = f.finrank y ∧ Flat q ∧ Surjective q ∧ QuasiCompact q := by
  letI : Flat f := inferInstance
  letI : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨V, hVs, hVa, hyV, hVrank⟩ :=
    exists_stableAffineOpen_le_rankOpen τ f y hfixed
  refine ⟨V, hVa, hVs, preimage_isStable σ τ f heq hVs, hyV, ?_⟩
  let fV := f ∣_ V
  letI : IsAffine V.toScheme := hVa
  letI : Etale fV := inferInstance
  letI : IsFinite fV := inferInstance
  letI : IsAffine (f ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom fV
  have hRank : fV.finrank = fun _ ↦ f.finrank y := by
    funext z
    rw [Scheme.Hom.finrank_of_isPullback
      (f ⁻¹ᵁ V).ι fV f V.ι (isPullback_morphismRestrict f V).flip]
    exact hVrank z.2
  obtain ⟨T, _, _, _, _, _, m, e, q, E, hE, hflat, hsurjective, hqc⟩ :=
    exists_fpqc_splitCover fV (f.finrank y) hRank
  letI : Flat q := hflat
  letI : Surjective q := hsurjective
  obtain ⟨t, _⟩ := q.surjective (⟨y, hyV⟩ : V.toScheme)
  letI : Nontrivial T := PrimeSpectrum.nonempty_iff_nontrivial.mp
    ⟨⟨t.1, t.2⟩⟩
  have hSplitRank := congrFun
    (finrank_eq_of_iso_splitProjection T m (pullback.snd fV q) E hE) t
  have hm : m = f.finrank y := by
    calc
      m = (pullback.snd fV q).finrank t := hSplitRank.symm
      _ = fV.finrank (q t) :=
        Scheme.Hom.finrank_pullback_snd fV q t
      _ = f.finrank y := congrFun hRank (q t)
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, m, e, q, E, hE, hm, hflat, hsurjective, hqc⟩

end MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteEtalePointSplitChart
