/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Finite

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

/-- The packaged quotient has the expected categorical universal property. -/
theorem existsUnique_quotientπ_lift (hσ : HasAffineOrbit σ)
    {Z : Scheme.{u}} (f : X ⟶ Z) (hf : ∀ g : G, σ.hom g ≫ f = f) :
    ∃! q : quotient σ hσ ⟶ Z, quotientπ σ hσ ≫ q = f :=
  σ.existsUnique_quotientπ_lift (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ) f hf

end Quotient

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
