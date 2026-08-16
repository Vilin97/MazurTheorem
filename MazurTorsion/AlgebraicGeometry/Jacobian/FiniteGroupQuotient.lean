/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Adjoin.Tower

/-!
# Finite-group quotients from affine orbit neighbourhoods

AINTLIB constructs the quotient of a scheme by a finite group action from a
stable affine atlas.  This file packages the geometric input normally used to
produce that atlas: every finite orbit is contained in an affine open.

The transfer theorem is the point needed by the symmetric-power construction.
An equivariant affine morphism pulls affine orbit neighbourhoods back to
affine orbit neighbourhoods.  In particular, after constructing the
permutation quotient of a power of `P¹`, a finite equivariant map from a power
of a curve supplies the atlas needed to construct its symmetric power.
-/

universe u

open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient

open _root_.AlgebraicGeometry

variable {G : Type*} [Group G] {X Y : Scheme.{u}}

/-- Every orbit of an action is contained in an affine open.  For finite `G`
and affine diagonal, AINTLIB refines such an open to a stable affine
neighbourhood by intersecting its translates. -/
def HasAffineOrbit (σ : SchemeAction G X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g : G, σ.hom g x ∈ U

/-- Every action on an affine scheme has affine orbit neighbourhoods: the
whole scheme is already one such neighbourhood. -/
theorem hasAffineOrbit_of_isAffine (σ : SchemeAction G X) [IsAffine X] :
    HasAffineOrbit σ := by
  intro x
  refine ⟨⊤, isAffineOpen_top X, ?_⟩
  intro g
  exact Set.mem_univ (σ.hom g x)

/-- Affine-orbit neighbourhoods pull back along an equivariant affine
morphism. -/
theorem hasAffineOrbit_of_equivariant_affine
    (σ : SchemeAction G X) (τ : SchemeAction G Y) (f : X ⟶ Y)
    [IsAffineHom f] (hτ : HasAffineOrbit τ)
    (heq : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g) :
    HasAffineOrbit σ := by
  intro x
  obtain ⟨U, hUa, hxU⟩ := hτ (f.base x)
  refine ⟨f ⁻¹ᵁ U, hUa.preimage f, ?_⟩
  intro g
  change f.base ((σ.hom g).base x) ∈ U
  rw [← Scheme.Hom.comp_apply, heq g, Scheme.Hom.comp_apply]
  exact hxU g

section Quotient

variable [Finite G] (σ : SchemeAction G X)
variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- The AINTLIB stable-affine refinement applied to an affine orbit
neighbourhood. -/
theorem exists_stableAffineOpen (hσ : HasAffineOrbit σ) (x : X) :
    ∃ V : X.Opens, σ.IsStableOpen V ∧ IsAffineOpen V ∧ x ∈ V := by
  obtain ⟨U, hUa, horbit⟩ := hσ x
  exact σ.exists_isStableOpen_isAffineOpen hUa x horbit

/-- The stable affine neighbourhood selected from an affine orbit
neighbourhood. -/
noncomputable def stableAffineOpen (hσ : HasAffineOrbit σ) (x : X) : X.Opens :=
  Classical.choose (exists_stableAffineOpen σ hσ x)

theorem stableAffineOpen_isStable (hσ : HasAffineOrbit σ) (x : X) :
    σ.IsStableOpen (stableAffineOpen σ hσ x) :=
  (Classical.choose_spec (exists_stableAffineOpen σ hσ x)).1

theorem stableAffineOpen_isAffine (hσ : HasAffineOrbit σ) (x : X) :
    IsAffineOpen (stableAffineOpen σ hσ x) :=
  (Classical.choose_spec (exists_stableAffineOpen σ hσ x)).2.1

theorem mem_stableAffineOpen (hσ : HasAffineOrbit σ) (x : X) :
    x ∈ stableAffineOpen σ hσ x :=
  (Classical.choose_spec (exists_stableAffineOpen σ hσ x)).2.2

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- On an affine chart of a scheme locally of finite type over a base, a
finite action over that base makes the chart ring module-finite over its
invariant subring.  The point is that the base sections land in the invariant
ring, so finite generation over the base implies finite generation over the
invariants; integrality of finite-group invariants then gives module
finiteness. -/
theorem chart_moduleFinite_of_locallyOfFiniteType {S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (hbase : ∀ g : G, σ.hom g ≫ f = f)
    {W : S.Opens} (hW : IsAffineOpen W) {U : X.Opens}
    (hUs : σ.IsStableOpen U) (hUa : IsAffineOpen U)
    (e : U ≤ f ⁻¹ᵁ W) :
    letI := σ.gammaMulSemiringAction hUs
    Module.Finite (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) := by
  letI := σ.gammaMulSemiringAction hUs
  let φ : Γ(S, W) →+* Γ(X, U) := (f.appLE W U e).hom
  have hφfixed (r : Γ(S, W)) (g : G) : g • φ r = φ r := by
    change ((σ.hom g).appLE U U (hUs.le_preimage g)).hom
        ((f.appLE W U e).hom r) = (f.appLE W U e).hom r
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hbase g]
  let φfixed : Γ(S, W) →+*
      FixedPoints.subalgebra ℤ (↑Γ(X, U)) G :=
    φ.codRestrict _ fun r ↦ hφfixed r
  have hcomp :
      (algebraMap (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U)).comp
          φfixed = φ := by
    ext r
    rfl
  have hftφ : φ.FiniteType := f.finiteType_appLE hW hUa e
  have hft :
      (algebraMap (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U)).FiniteType :=
    RingHom.FiniteType.of_comp_finiteType (hcomp ▸ hftφ)
  have hint :
      (algebraMap (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U)).IsIntegral :=
    Algebra.isIntegral_def.mp
      (Algebra.IsInvariant.isIntegral
        (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U) G)
  exact RingHom.finite_algebraMap.mp (hint.to_finite hft)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- Artin--Tate on a stable affine chart: if the affine base ring is
Noetherian, its map to the invariant ring is of finite type.  The returned
map is the unique factorization of the chart's structure map through the
invariant subring. -/
theorem exists_chartBaseToInvariants_finiteType {S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (hbase : ∀ g : G, σ.hom g ≫ f = f)
    {W : S.Opens} (hW : IsAffineOpen W) [IsNoetherianRing Γ(S, W)]
    {U : X.Opens} (hUs : σ.IsStableOpen U) (hUa : IsAffineOpen U)
    (e : U ≤ f ⁻¹ᵁ W) :
    letI := σ.gammaMulSemiringAction hUs
    ∃ φfixed : Γ(S, W) →+*
        FixedPoints.subalgebra ℤ (↑Γ(X, U)) G,
      (algebraMap (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U)).comp
          φfixed = (f.appLE W U e).hom ∧
        φfixed.FiniteType := by
  letI := σ.gammaMulSemiringAction hUs
  let φ : Γ(S, W) →+* Γ(X, U) := (f.appLE W U e).hom
  have hφfixed (r : Γ(S, W)) (g : G) : g • φ r = φ r := by
    change ((σ.hom g).appLE U U (hUs.le_preimage g)).hom
        ((f.appLE W U e).hom r) = (f.appLE W U e).hom r
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hbase g]
  let φfixed : Γ(S, W) →+*
      FixedPoints.subalgebra ℤ (↑Γ(X, U)) G :=
    φ.codRestrict _ fun r ↦ hφfixed r
  have hcomp :
      (algebraMap (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U)).comp
          φfixed = φ := by
    ext r
    rfl
  letI : Algebra Γ(S, W)
      (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) := φfixed.toAlgebra
  letI : Algebra Γ(S, W) Γ(X, U) := φ.toAlgebra
  letI : IsScalarTower Γ(S, W)
      (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hftφ : φ.FiniteType := f.finiteType_appLE hW hUa e
  have hfgBase : (⊤ : Subalgebra Γ(S, W) Γ(X, U)).FG := by
    have : Algebra.FiniteType Γ(S, W) Γ(X, U) := by
      rw [← RingHom.finiteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact hftφ
    exact this.out
  haveI : Module.Finite
      (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U) :=
    chart_moduleFinite_of_locallyOfFiniteType σ f hbase hW hUs hUa e
  have hfgInvariants :
      (⊤ : Subalgebra Γ(S, W)
        (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G)).FG :=
    fg_of_fg_of_fg Γ(S, W)
      (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U)
      hfgBase Module.Finite.fg_top
      (FaithfulSMul.algebraMap_injective
        (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) Γ(X, U))
  refine ⟨φfixed, hcomp, ?_⟩
  change Algebra.FiniteType Γ(S, W)
    (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G)
  exact ⟨hfgInvariants⟩

/-- The scheme quotient attached to affine orbit neighbourhoods. -/
noncomputable def quotient (hσ : HasAffineOrbit σ) : Scheme.{u} :=
  σ.quotient (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)

/-- The canonical projection to the finite-group quotient. -/
noncomputable def quotientπ (hσ : HasAffineOrbit σ) : X ⟶ quotient σ hσ :=
  σ.quotientπ (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ)

/-- The finite-group quotient projection is affine. -/
instance quotientπ_isAffineHom (hσ : HasAffineOrbit σ) :
    IsAffineHom (quotientπ σ hσ) := by
  exact SchemeAction.isAffineHom_quotientπ σ (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ)

/-- The finite-group quotient projection is surjective on points. -/
theorem quotientπ_surjective (hσ : HasAffineOrbit σ) :
    Function.Surjective ⇑(quotientπ σ hσ) :=
  σ.quotientπ_surjective (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ)

/-- The quotient projection packaged as Mathlib's surjective morphism
property. -/
instance quotientπ_surjectiveProperty (hσ : HasAffineOrbit σ) :
    Surjective (quotientπ σ hσ) :=
  ⟨quotientπ_surjective σ hσ⟩

/-- The quotient projection is finite whenever its invariant affine-chart
extensions are module-finite.  This is the local algebra criterion used below
for permutation quotients: on a stable affine chart `U`, the projection is
`Spec Γ(U) ⟶ Spec Γ(U)ᴳ`. -/
theorem quotientπ_isFinite_of_chart_moduleFinite (hσ : HasAffineOrbit σ)
    (hfinite : ∀ x,
      letI := σ.gammaMulSemiringAction (stableAffineOpen_isStable σ hσ x)
      Module.Finite
        (FixedPoints.subalgebra ℤ (↑Γ(X, stableAffineOpen σ hσ x)) G)
        ↑Γ(X, stableAffineOpen σ hσ x)) :
    IsFinite (quotientπ σ hσ) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (σ.quotientChart (stableAffineOpen σ hσ)
      (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ))
    (σ.iSup_quotientChart_eq_top (stableAffineOpen σ hσ)
      (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)) fun x ↦ ?_
  change IsFinite
    (σ.quotientπ (stableAffineOpen σ hσ)
      (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
      (mem_stableAffineOpen σ hσ) ∣_
        σ.quotientChart (stableAffineOpen σ hσ)
          (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ) x)
  rw [SchemeAction.morphismRestrict_quotientπ σ (stableAffineOpen σ hσ)
      (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
      (mem_stableAffineOpen σ hσ) x,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite),
    SchemeAction.localQuotientπ_eq σ (stableAffineOpen_isStable σ hσ x)
      (stableAffineOpen_isAffine σ hσ x),
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)]
  letI := σ.gammaMulSemiringAction (stableAffineOpen_isStable σ hσ x)
  haveI := hfinite x
  rw [invariantsπ, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem hom_quotientπ (hσ : HasAffineOrbit σ) (g : G) :
    σ.hom g ≫ quotientπ σ hσ = quotientπ σ hσ :=
  σ.hom_quotientπ (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ) g

/-- Two points have the same image in the quotient exactly when they lie in
the same finite-group orbit. -/
theorem quotientπ_apply_eq_iff (hσ : HasAffineOrbit σ) (x y : X) :
    quotientπ σ hσ x = quotientπ σ hσ y ↔
      ∃ g : G, σ.hom g x = y := by
  constructor
  · intro hxy
    change
      σ.quotientπ (stableAffineOpen σ hσ)
          (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
          (mem_stableAffineOpen σ hσ) x =
        σ.quotientπ (stableAffineOpen σ hσ)
          (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
          (mem_stableAffineOpen σ hσ) y at hxy
    have hxU : x ∈ stableAffineOpen σ hσ x := mem_stableAffineOpen σ hσ x
    have hyU : y ∈ stableAffineOpen σ hσ x := by
      have hxchart :
          σ.quotientπ (stableAffineOpen σ hσ)
              (stableAffineOpen_isStable σ hσ)
              (stableAffineOpen_isAffine σ hσ) (mem_stableAffineOpen σ hσ) x ∈
          σ.quotientChart (stableAffineOpen σ hσ)
            (stableAffineOpen_isStable σ hσ)
            (stableAffineOpen_isAffine σ hσ) x := by
        change x ∈
          σ.quotientπ (stableAffineOpen σ hσ)
              (stableAffineOpen_isStable σ hσ)
              (stableAffineOpen_isAffine σ hσ) (mem_stableAffineOpen σ hσ) ⁻¹ᵁ
          σ.quotientChart (stableAffineOpen σ hσ)
            (stableAffineOpen_isStable σ hσ)
            (stableAffineOpen_isAffine σ hσ) x
        rw [SchemeAction.quotientπ_preimage_quotientChart σ
          (stableAffineOpen σ hσ) (stableAffineOpen_isStable σ hσ)
          (stableAffineOpen_isAffine σ hσ) (mem_stableAffineOpen σ hσ) x]
        exact hxU
      have hychart :
          σ.quotientπ (stableAffineOpen σ hσ)
              (stableAffineOpen_isStable σ hσ)
              (stableAffineOpen_isAffine σ hσ) (mem_stableAffineOpen σ hσ) y ∈
            σ.quotientChart (stableAffineOpen σ hσ)
              (stableAffineOpen_isStable σ hσ)
              (stableAffineOpen_isAffine σ hσ) x := hxy ▸ hxchart
      have hyPre : y ∈
          σ.quotientπ (stableAffineOpen σ hσ)
            (stableAffineOpen_isStable σ hσ)
            (stableAffineOpen_isAffine σ hσ) (mem_stableAffineOpen σ hσ) ⁻¹ᵁ
          σ.quotientChart (stableAffineOpen σ hσ)
            (stableAffineOpen_isStable σ hσ)
            (stableAffineOpen_isAffine σ hσ) x := hychart
      rw [SchemeAction.quotientπ_preimage_quotientChart σ
        (stableAffineOpen σ hσ) (stableAffineOpen_isStable σ hσ)
        (stableAffineOpen_isAffine σ hσ) (mem_stableAffineOpen σ hσ) x] at hyPre
      exact hyPre
    let xU : (stableAffineOpen σ hσ x : Scheme.{u}) := ⟨x, hxU⟩
    let yU : (stableAffineOpen σ hσ x : Scheme.{u}) := ⟨y, hyU⟩
    have hlocal :
        σ.localQuotientπ (stableAffineOpen_isStable σ hσ x)
            (stableAffineOpen_isAffine σ hσ x) xU =
          σ.localQuotientπ (stableAffineOpen_isStable σ hσ x)
            (stableAffineOpen_isAffine σ hσ x) yU := by
      let j := (σ.quotientChartIso (stableAffineOpen σ hσ)
          (stableAffineOpen_isStable σ hσ)
          (stableAffineOpen_isAffine σ hσ) x).hom ≫
        (σ.quotientChart (stableAffineOpen σ hσ)
          (stableAffineOpen_isStable σ hσ)
          (stableAffineOpen_isAffine σ hσ) x).ι
      apply j.isOpenEmbedding.injective
      change
        (σ.localQuotientπ (stableAffineOpen_isStable σ hσ x)
            (stableAffineOpen_isAffine σ hσ x) ≫ j) xU =
          (σ.localQuotientπ (stableAffineOpen_isStable σ hσ x)
            (stableAffineOpen_isAffine σ hσ x) ≫ j) yU
      rw [show σ.localQuotientπ (stableAffineOpen_isStable σ hσ x)
            (stableAffineOpen_isAffine σ hσ x) ≫ j =
          (stableAffineOpen σ hσ x).ι ≫
            σ.quotientπ (stableAffineOpen σ hσ)
              (stableAffineOpen_isStable σ hσ)
              (stableAffineOpen_isAffine σ hσ)
              (mem_stableAffineOpen σ hσ) from
        SchemeAction.localQuotientπ_quotientChartIso σ
          (stableAffineOpen σ hσ) (stableAffineOpen_isStable σ hσ)
          (stableAffineOpen_isAffine σ hσ) (mem_stableAffineOpen σ hσ) x,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hxy
    letI := σ.gammaMulSemiringAction (stableAffineOpen_isStable σ hσ x)
    rw [SchemeAction.localQuotientπ_eq σ
      (stableAffineOpen_isStable σ hσ x)
      (stableAffineOpen_isAffine σ hσ x),
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hlocal
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G
      ↑Γ(X, stableAffineOpen σ hσ x) ℤ _ _).mp hlocal
    refine ⟨g, ?_⟩
    have hrestricted :
        (σ.hom g).resLE (stableAffineOpen σ hσ x) (stableAffineOpen σ hσ x)
            ((stableAffineOpen_isStable σ hσ x).le_preimage g) xU = yU := by
      apply (stableAffineOpen_isAffine σ hσ x).isoSpec.hom.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply,
        SchemeAction.resLE_isoSpec_hom σ
          (stableAffineOpen_isStable σ hσ x)
          (stableAffineOpen_isAffine σ hσ x) g,
        Scheme.Hom.comp_apply]
      exact hg
    calc
      σ.hom g x =
          ((stableAffineOpen σ hσ x).ι ≫ σ.hom g) xU := rfl
      _ = ((σ.hom g).resLE (stableAffineOpen σ hσ x)
          (stableAffineOpen σ hσ x)
          ((stableAffineOpen_isStable σ hσ x).le_preimage g) ≫
            (stableAffineOpen σ hσ x).ι) xU := by
        rw [Scheme.Hom.resLE_comp_ι]
      _ = (stableAffineOpen σ hσ x).ι yU := by
        simp only [Scheme.Hom.comp_apply, hrestricted]
      _ = y := rfl
  · rintro ⟨g, rfl⟩
    have h := congrArg (fun q : X ⟶ quotient σ hσ ↦ q x) (hom_quotientπ σ hσ g)
    simpa only [Scheme.Hom.comp_apply] using h.symm

/-- The packaged quotient has the expected categorical universal property. -/
theorem existsUnique_quotientπ_lift (hσ : HasAffineOrbit σ)
    {Z : Scheme.{u}} (f : X ⟶ Z) (hf : ∀ g : G, σ.hom g ≫ f = f) :
    ∃! q : quotient σ hσ ⟶ Z, quotientπ σ hσ ≫ q = f :=
  σ.existsUnique_quotientπ_lift (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ) f hf

/-- The projection to the quotient attached to affine orbit neighbourhoods
is an epimorphism.  The named downstream consumers include the degree-one
symmetric-power comparison and flat quotient base change. -/
theorem epi_quotientπ (hσ : HasAffineOrbit σ) : Epi (quotientπ σ hσ) := by
  constructor
  intro Y f₁ f₂ h
  exact σ.quotientπ_hom_ext (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ) f₁ f₂ h

/-- The morphism out of a quotient descended from an invariant morphism.
The named consumers are the symmetric-power structure map and the ordered
incidence quotient structure map. -/
noncomputable def descendedMap (hσ : HasAffineOrbit σ) {S : Scheme.{u}}
    (f : X ⟶ S) (hf : ∀ g : G, σ.hom g ≫ f = f) :
    quotient σ hσ ⟶ S :=
  Classical.choose (existsUnique_quotientπ_lift σ hσ f hf)

@[reassoc]
theorem quotientπ_comp_descendedMap (hσ : HasAffineOrbit σ)
    {S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ g : G, σ.hom g ≫ f = f) :
    quotientπ σ hσ ≫ descendedMap σ hσ f hf = f :=
  (Classical.choose_spec (existsUnique_quotientπ_lift σ hσ f hf)).1

/-- An invariant locally finite-type morphism to an affine Noetherian base
descends to a locally finite-type morphism on the finite-group quotient.
Chartwise this is Artin--Tate for the inclusion of the invariant ring. -/
theorem descendedMap_locallyOfFiniteType (hσ : HasAffineOrbit σ)
    {S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ g : G, σ.hom g ≫ f = f)
    [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [LocallyOfFiniteType f] :
    LocallyOfFiniteType (descendedMap σ hσ f hf) := by
  let V := stableAffineOpen σ hσ
  let hVs := stableAffineOpen_isStable σ hσ
  let hVa := stableAffineOpen_isAffine σ hσ
  let Q : X → (quotient σ hσ).Opens :=
    fun x ↦ σ.quotientChart V hVs hVa x
  let 𝒰 := (quotient σ hσ).openCoverOfIsOpenCover Q
    (σ.iSup_quotientChart_eq_top V hVs hVa)
  letI : ∀ x, IsAffine (𝒰.X x) := fun x ↦ by
    dsimp only [𝒰, Scheme.openCoverOfIsOpenCover_X, Q]
    exact σ.isAffineOpen_quotientChart V hVs hVa x
  apply HasRingHomProperty.of_source_openCover (P := @LocallyOfFiniteType) 𝒰
  intro x
  change X at x
  letI := σ.gammaMulSemiringAction (hVs x)
  let e : V x ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp
  obtain ⟨φ, hφ, hφft⟩ :=
    exists_chartBaseToInvariants_finiteType σ f hf
      (isAffineOpen_top S) (hVs x) (hVa x) e
  let f₀ : σ.quotient V hVs hVa ⟶ S := descendedMap σ hσ f hf
  have hf₀ : σ.quotientπ V hVs hVa (mem_stableAffineOpen σ hσ) ≫ f₀ = f := by
    exact quotientπ_comp_descendedMap σ hσ f hf
  let q : (σ.quotientChart V hVs hVa x : Scheme) ⟶ S :=
    (σ.quotientChartIso V hVs hVa x).inv ≫
      Spec.map (CommRingCat.ofHom φ) ≫
      (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι
  have hq : (σ.quotientChart V hVs hVa x).ι ≫ f₀ = q := by
    apply (cancel_epi (σ.quotientChartIso V hVs hVa x).hom).mp
    apply invariantsπ_hom_ext G ↑Γ(X, V x) ℤ
    apply (cancel_epi (hVa x).isoSpec.hom).mp
    dsimp only [q]
    simp only [Iso.hom_inv_id_assoc]
    change σ.localQuotientπ (hVs x) (hVa x) ≫
        (σ.quotientChartIso V hVs hVa x).hom ≫
          (σ.quotientChart V hVs hVa x).ι ≫ f₀ =
      σ.localQuotientπ (hVs x) (hVa x) ≫
        Spec.map (CommRingCat.ofHom φ) ≫
          (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι
    rw [← Category.assoc, ← Category.assoc,
      Category.assoc (σ.localQuotientπ (hVs x) (hVa x))
        (σ.quotientChartIso V hVs hVa x).hom
        (σ.quotientChart V hVs hVa x).ι,
      σ.localQuotientπ_quotientChartIso V hVs hVa
        (mem_stableAffineOpen σ hσ) x,
      Category.assoc, hf₀]
    rw [σ.localQuotientπ_eq (hVs x) (hVa x), invariantsπ, Category.assoc,
      ← Spec.map_comp_assoc]
    have hφ' : CommRingCat.ofHom φ ≫
        CommRingCat.ofHom
          (algebraMap (FixedPoints.subalgebra ℤ ↑Γ(X, V x) G) Γ(X, V x)) =
          f.appLE ⊤ (V x) e := by
      ext r
      exact DFunLike.congr_fun hφ r
    rw [hφ', IsAffineOpen.isoSpec_hom]
    dsimp only [V] at e ⊢
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
      IsAffineOpen.toSpecΓ_isoSpec_inv_assoc, Scheme.Hom.resLE_comp_ι]
  have hqft : LocallyOfFiniteType
      ((σ.quotientChart V hVs hVa x).ι ≫ f₀) := by
    rw [hq]
    dsimp only [q]
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hφft
    haveI : LocallyOfFiniteType (σ.quotientChartIso V hVs hVa x).inv := by
      infer_instance
    haveI : LocallyOfFiniteType (isAffineOpen_top S).isoSpec.inv := by
      infer_instance
    haveI : LocallyOfFiniteType (⊤ : S.Opens).ι := by infer_instance
    haveI : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom φ) ≫
          (isAffineOpen_top S).isoSpec.inv) := by infer_instance
    haveI : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom φ) ≫
          (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι) := by
      infer_instance
    haveI : LocallyOfFiniteType
        ((σ.quotientChartIso V hVs hVa x).inv ≫
          Spec.map (CommRingCat.ofHom φ)) := by infer_instance
    haveI : LocallyOfFiniteType
        ((σ.quotientChartIso V hVs hVa x).inv ≫
          Spec.map (CommRingCat.ofHom φ) ≫
            (isAffineOpen_top S).isoSpec.inv) := by infer_instance
    have hcomp := MorphismProperty.comp_mem @LocallyOfFiniteType
      (σ.quotientChartIso V hVs hVa x).inv
      (Spec.map (CommRingCat.ofHom φ) ≫
        (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι)
      (inferInstance : LocallyOfFiniteType
        (σ.quotientChartIso V hVs hVa x).inv)
      (inferInstance : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom φ) ≫
          (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι))
    simpa only [Category.assoc] using hcomp
  letI : IsAffine (σ.quotientChart V hVs hVa x : Scheme) :=
    σ.isAffineOpen_quotientChart V hVs hVa x
  have hqtop :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hqft
  change ((((σ.quotientChart V hVs hVa x).ι ≫
    descendedMap σ hσ f hf).appTop).hom.FiniteType)
  simpa only [f₀] using hqtop

end Quotient

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
