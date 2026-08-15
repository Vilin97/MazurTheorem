/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient

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

/-- The scheme quotient attached to affine orbit neighbourhoods. -/
noncomputable def quotient (hσ : HasAffineOrbit σ) : Scheme.{u} :=
  σ.quotient (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)

/-- The canonical projection to the finite-group quotient. -/
noncomputable def quotientπ (hσ : HasAffineOrbit σ) : X ⟶ quotient σ hσ :=
  σ.quotientπ (stableAffineOpen σ hσ)
    (stableAffineOpen_isStable σ hσ) (stableAffineOpen_isAffine σ hσ)
    (mem_stableAffineOpen σ hσ)

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
