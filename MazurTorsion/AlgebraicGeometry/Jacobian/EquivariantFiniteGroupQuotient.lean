/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient

/-!
# Maps induced between finite-group quotients

An equivariant morphism for two actions of the same finite group induces a
canonical morphism between their quotients.  This file packages that map and
its defining commutative square using the categorical universal property from
`FiniteGroupQuotient`.

The named downstream consumer is the block-coordinate quotient map in
`GeometricAssignedAffineChart`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteGroupQuotient

open FiniteGroupQuotient

variable {G : Type*} [Group G] [Finite G]
variable {X Y : Scheme.{u}} (σ : SchemeAction G X) (τ : SchemeAction G Y)
variable [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
variable [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
variable (hσ : HasAffineOrbit σ) (hτ : HasAffineOrbit τ)
variable (f : X ⟶ Y)
variable (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)

include hf

omit [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] in
/-- The composite of an equivariant morphism with the target quotient
projection is invariant under the source action. -/
theorem comp_targetQuotientπ_invariant (g : G) :
    σ.hom g ≫ (f ≫ quotientπ τ hτ) = f ≫ quotientπ τ hτ := by
  rw [← Category.assoc, hf g, Category.assoc, hom_quotientπ τ hτ g]

/-- The canonical morphism induced between the two finite-group quotients. -/
noncomputable def descendedMap :
    quotient σ hσ ⟶ quotient τ hτ :=
  FiniteGroupQuotient.descendedMap σ hσ (f ≫ quotientπ τ hτ)
    (comp_targetQuotientπ_invariant σ τ hτ f hf)

/-- The quotient projections and the induced map form the expected
commutative square. -/
@[reassoc]
theorem quotientπ_comp_descendedMap :
    quotientπ σ hσ ≫ descendedMap σ τ hσ hτ f hf =
      f ≫ quotientπ τ hτ :=
  FiniteGroupQuotient.quotientπ_comp_descendedMap σ hσ
    (f ≫ quotientπ τ hτ)
    (comp_targetQuotientπ_invariant σ τ hτ f hf)

/-- A point and its image under an equivariant morphism have compatible
images in the two quotient spaces. -/
theorem descendedMap_apply_quotientPoint (x : X) :
    descendedMap σ τ hσ hτ f hf (quotientπ σ hσ x) =
      quotientπ τ hτ (f x) := by
  have h := congrArg (fun q : X ⟶ quotient τ hτ ↦ q x)
    (quotientπ_comp_descendedMap σ τ hσ hτ f hf)
  simpa only [Scheme.Hom.comp_apply] using h

end MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteGroupQuotient
