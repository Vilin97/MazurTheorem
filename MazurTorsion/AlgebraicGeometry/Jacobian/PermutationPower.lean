/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient

/-!
# Permutation actions on relative powers

This file constructs the canonical action of `Equiv.Perm ι` on the relative
power of a scheme over a base.  It also records functoriality of the power map
as the equivariance statement consumed by the symmetric-power quotient.
-/

universe u

open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) (ι : Type) [Finite ι]

/-- The `ι`-fold relative power of `X` over `S`. -/
noncomputable abbrev power (X : Over S) : Over S :=
  ∏ᶜ fun _ : ι => X

/-- Reindexing the relative power by a permutation. -/
noncomputable def permutationHom (X : Over S) (g : Equiv.Perm ι) :
    power S ι X ⟶ power S ι X :=
  Limits.Pi.lift (fun i => Pi.π (fun _ : ι => X) (g i))

@[reassoc]
theorem permutationHom_comp_π (X : Over S) (g : Equiv.Perm ι) (i : ι) :
    permutationHom S ι X g ≫ Pi.π (fun _ : ι => X) i =
      Pi.π (fun _ : ι => X) (g i) := by
  exact Limits.Pi.lift_π (fun i => Pi.π (fun _ : ι => X) (g i)) i

theorem permutationHom_one (X : Over S) :
    permutationHom S ι X 1 = 𝟙 (power S ι X) := by
  apply Limits.Pi.hom_ext
  intro i
  rw [permutationHom_comp_π, Category.id_comp]
  rfl

theorem permutationHom_mul (X : Over S) (g h : Equiv.Perm ι) :
    permutationHom S ι X (g * h) =
      permutationHom S ι X g ≫ permutationHom S ι X h := by
  apply Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, permutationHom_comp_π, permutationHom_comp_π,
    permutationHom_comp_π]
  rfl

/-- The permutation action on the underlying scheme of a relative power. -/
noncomputable def action (X : Over S) :
    SchemeAction (Equiv.Perm ι) (power S ι X).left where
  hom g := (permutationHom S ι X g).left
  hom_one := congrArg Over.Hom.left (permutationHom_one S ι X)
  hom_mul g h := congrArg Over.Hom.left (permutationHom_mul S ι X g h)

/-- Every permutation acts over the base. -/
theorem action_hom_comp_structureMap (X : Over S) (g : Equiv.Perm ι) :
    (action S ι X).hom g ≫ (power S ι X).hom = (power S ι X).hom := by
  exact (permutationHom S ι X g).w

/-- The map on relative powers induced componentwise by a morphism over the
base. -/
noncomputable def map {X Y : Over S} (f : X ⟶ Y) :
    power S ι X ⟶ power S ι Y :=
  Limits.Pi.map (fun _ : ι => f)

@[reassoc]
theorem map_comp_π {X Y : Over S} (f : X ⟶ Y) (i : ι) :
    map S ι f ≫ Pi.π (fun _ : ι => Y) i =
      Pi.π (fun _ : ι => X) i ≫ f := by
  change Limits.Pi.map (fun _ : ι => f) ≫ Pi.π (fun _ : ι => Y) i = _
  exact Limits.Pi.map_π (fun _ : ι => f) i

/-- Componentwise maps commute with permutation actions. -/
theorem action_equivariant {X Y : Over S} (f : X ⟶ Y) (g : Equiv.Perm ι) :
    (action S ι X).hom g ≫ (map S ι f).left =
      (map S ι f).left ≫ (action S ι Y).hom g := by
  have h : permutationHom S ι X g ≫ map S ι f =
      map S ι f ≫ permutationHom S ι Y g := by
    apply Limits.Pi.hom_ext
    intro i
    calc
      (permutationHom S ι X g ≫ map S ι f) ≫ Pi.π (fun _ : ι => Y) i =
          permutationHom S ι X g ≫ (Pi.π (fun _ : ι => X) i ≫ f) := by
            rw [Category.assoc, map_comp_π]
      _ = (permutationHom S ι X g ≫ Pi.π (fun _ : ι => X) i) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = Pi.π (fun _ : ι => X) (g i) ≫ f := by
        rw [permutationHom_comp_π]
      _ = map S ι f ≫ Pi.π (fun _ : ι => Y) (g i) :=
        (map_comp_π S ι f (g i)).symm
      _ = (map S ι f ≫ permutationHom S ι Y g) ≫
          Pi.π (fun _ : ι => Y) i := by
        rw [Category.assoc, permutationHom_comp_π]
  simpa [action] using congrArg Over.Hom.left h

end MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
