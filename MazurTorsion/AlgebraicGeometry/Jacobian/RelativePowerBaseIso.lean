/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleAssignedCoproductPower

/-!
# Relative powers transported along a base isomorphism

Postcomposition along an isomorphism of bases preserves finite products in
the corresponding slice categories.  This file records the canonical
relative-power comparison, its effect on projections and points, and its
compatibility with repeating coordinates according to a finite assignment.

The named downstream consumer is the exact geometric-support point in
`GeometricAssignedAffineChart`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.RelativePowerBaseIso

open FiniteEtaleAssignedCoproductPower

variable (S T : Scheme.{u}) (e : S ≅ T) (X : Over S)

/-- The canonical comparison between transporting a finite relative power
and taking the relative power after transport along the base isomorphism. -/
noncomputable def powerIso (n : ℕ) :
    (Over.map e.hom).obj (PermutationPower.power S (Fin n) X) ≅
      PermutationPower.power T (Fin n) ((Over.map e.hom).obj X) :=
  preservesLimitIso (Over.map e.hom)
    (Discrete.functor fun _ : Fin n ↦ X)

@[reassoc]
theorem powerIso_hom_comp_projection (n : ℕ) (i : Fin n) :
    (powerIso S T e X n).hom ≫
        Pi.π (fun _ : Fin n ↦ (Over.map e.hom).obj X) i =
      (Over.map e.hom).map (Pi.π (fun _ : Fin n ↦ X) i) := by
  exact preservesLimitIso_hom_π (Over.map e.hom)
    (Discrete.functor fun _ : Fin n ↦ X) (Discrete.mk i)

/-- The power comparison commutes with repeating or reordering coordinates
by an assignment. -/
theorem powerIso_natural_assignmentRepeatHom
    (m d : ℕ) (a : Fin d → Fin m) :
    (Over.map e.hom).map (assignmentRepeatHom S m d X a) ≫
          (powerIso S T e X d).hom =
      (powerIso S T e X m).hom ≫
        assignmentRepeatHom T m d ((Over.map e.hom).obj X) a := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, powerIso_hom_comp_projection]
  rw [Category.assoc, assignmentRepeatHom_comp_projection]
  rw [powerIso_hom_comp_projection]
  have h := congrArg (Over.map e.hom).map
    (assignmentRepeatHom_comp_projection S m d X a i)
  simpa only [(Over.map e.hom).map_comp] using h

/-- Transport a point of a relative power through the canonical base-
isomorphism comparison. -/
noncomputable def powerPoint (n : ℕ)
    (p : (PermutationPower.power S (Fin n) X).left) :
    (PermutationPower.power T (Fin n) ((Over.map e.hom).obj X)).left :=
  (powerIso S T e X n).hom.left p

@[simp]
theorem powerPoint_projection (n : ℕ)
    (p : (PermutationPower.power S (Fin n) X).left) (i : Fin n) :
    (Pi.π (fun _ : Fin n ↦ (Over.map e.hom).obj X) i).left
        (powerPoint S T e X n p) =
      (Pi.π (fun _ : Fin n ↦ X) i).left p := by
  have h := congrArg Over.Hom.left
    (powerIso_hom_comp_projection S T e X n i)
  exact congrArg (fun q ↦ q p) h

/-- Repetition of coordinates commutes exactly with transport of points,
including their residue-field correlation. -/
@[simp]
theorem assignmentRepeatHom_powerPoint
    (m d : ℕ) (a : Fin d → Fin m)
    (p : (PermutationPower.power S (Fin m) X).left) :
    (assignmentRepeatHom T m d ((Over.map e.hom).obj X) a).left
        (powerPoint S T e X m p) =
      powerPoint S T e X d
        ((assignmentRepeatHom S m d X a).left p) := by
  have h := congrArg Over.Hom.left
    (powerIso_natural_assignmentRepeatHom S T e X m d a)
  exact (congrArg (fun q ↦ q p) h).symm

end MazurTorsion.AlgebraicGeometry.Jacobian.RelativePowerBaseIso
