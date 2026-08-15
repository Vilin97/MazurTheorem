/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower

/-!
# Relative symmetric powers from finite permutation quotients

This module constructs the relative symmetric power once the permutation
orbits in the relative power have affine neighbourhoods.  The hypothesis is
exactly the geometric premise required by the checked AINTLIB finite-group
quotient construction; it is not a representability assumption.
-/

universe u

open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SymmetricPower

open _root_.AlgebraicGeometry
open FiniteGroupQuotient
open PermutationPower

variable (S : Scheme.{u}) (d : ℕ) (X : Over S)

noncomputable abbrev Action : SchemeAction (Equiv.Perm (Fin d)) (power S (Fin d) X).left :=
  action S (Fin d) X

/-- The affine-orbit premise needed to construct `Sym^d_S(X)`. -/
noncomputable abbrev HasAffineOrbits : Prop :=
  HasAffineOrbit (Action S d X)

/-- Affine permutation-orbit neighbourhoods transfer along an affine
componentwise map of relative powers. -/
theorem hasAffineOrbits_of_map {X Y : Over S} (f : X ⟶ Y)
    [IsAffineHom (PermutationPower.map S (Fin d) f).left]
    (hY : HasAffineOrbits S d Y) : HasAffineOrbits S d X :=
  FiniteGroupQuotient.hasAffineOrbit_of_equivariant_affine
    (Action S d X) (Action S d Y) (PermutationPower.map S (Fin d) f).left hY
    (PermutationPower.action_equivariant S (Fin d) f)

/-- Finite componentwise maps transfer affine permutation-orbit
neighbourhoods. -/
theorem hasAffineOrbits_of_finite_map {X Y : Over S} (f : X ⟶ Y)
    [IsFinite f.left] (hY : HasAffineOrbits S d Y) : HasAffineOrbits S d X := by
  letI : IsFinite (PermutationPower.map S (Fin d) f).left :=
    PermutationPower.map_isFinite S (Fin d) f
  exact hasAffineOrbits_of_map S d f hY

section

variable [IsAffineHom
  (pullback.diagonal (terminal.from (power S (Fin d) X).left))]
variable (hX : HasAffineOrbits S d X)

/-- The underlying scheme quotient of the relative power by permutations. -/
noncomputable def underlying : Scheme.{u} :=
  FiniteGroupQuotient.quotient (Action S d X) hX

/-- The quotient projection on underlying schemes. -/
noncomputable def underlyingProjection :
    (power S (Fin d) X).left ⟶ underlying S d X hX :=
  FiniteGroupQuotient.quotientπ (Action S d X) hX

/-- The structure map descended from the relative power. -/
noncomputable def structureMap : underlying S d X hX ⟶ S :=
  Classical.choose <|
    FiniteGroupQuotient.existsUnique_quotientπ_lift (Action S d X) hX
      (power S (Fin d) X).hom (action_hom_comp_structureMap S (Fin d) X)

/-- The quotient projection followed by the descended structure map is the
original structure map. -/
theorem underlyingProjection_comp_structureMap :
    underlyingProjection S d X hX ≫ structureMap S d X hX =
      (power S (Fin d) X).hom :=
  (Classical.choose_spec <|
    FiniteGroupQuotient.existsUnique_quotientπ_lift (Action S d X) hX
      (power S (Fin d) X).hom (action_hom_comp_structureMap S (Fin d) X)).1

/-- The relative symmetric power as a scheme over the base. -/
noncomputable def scheme : Over S :=
  Over.mk (structureMap S d X hX)

/-- The canonical projection `X^d_S ⟶ Sym^d_S(X)`. -/
noncomputable def projection : power S (Fin d) X ⟶ scheme S d X hX :=
  Over.homMk (underlyingProjection S d X hX)
    (underlyingProjection_comp_structureMap S d X hX)

/-- The symmetric-power projection is invariant under every permutation. -/
theorem action_comp_projection (g : Equiv.Perm (Fin d)) :
    (Action S d X).hom g ≫ (projection S d X hX).left =
      (projection S d X hX).left :=
  FiniteGroupQuotient.hom_quotientπ (Action S d X) hX g

end

end MazurTorsion.AlgebraicGeometry.Jacobian.SymmetricPower
