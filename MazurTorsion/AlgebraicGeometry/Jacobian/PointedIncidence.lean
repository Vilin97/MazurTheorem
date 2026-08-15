/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisor

/-!
# Inserting a distinguished point into the ordered incidence family

The expected total space of the degree-`n + 1` universal divisor is
`X × Symⁿ(X)`: a pair `(x, D)` maps to `(x, x + D)`.  Before quotienting,
this construction inserts the distinguished point as coordinate zero of an
ordered `(n + 1)`-tuple.  The resulting map lands scheme-theoretically in the
ordered incidence family because its defining product ideal is contained in
the zeroth coordinate-graph ideal.

The named downstream consumer is `UniversalEffectiveDivisorDescent`, which
will descend this map to `X × Symⁿ(X)` and compare it with the finite
incidence quotient.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidence

open PermutationPower
open UniversalEffectiveDivisor

variable (S : Scheme.{u}) (n : ℕ) (X : Over S)

/-- Insert the distinguished point as coordinate zero and retain the
remaining ordered coordinates. -/
noncomputable def prependPower :
    orderedAmbient S n X ⟶ power S (Fin (n + 1)) X :=
  Limits.Pi.lift fun i ↦ Fin.cases
    (pointProjection S n X)
    (fun j ↦ coordinateProjection S n X j) i

@[reassoc]
theorem prependPower_comp_π_zero :
    prependPower S n X ≫ Pi.π (fun _ : Fin (n + 1) ↦ X) 0 =
      pointProjection S n X := by
  exact Limits.Pi.lift_π _ 0

@[reassoc]
theorem prependPower_comp_π_succ (i : Fin n) :
    prependPower S n X ≫ Pi.π (fun _ : Fin (n + 1) ↦ X) i.succ =
      coordinateProjection S n X i := by
  exact Limits.Pi.lift_π _ i.succ

/-- Recover the distinguished point and the remaining coordinates after
forgetting coordinate zero.  The named downstream consumer is the finite-
fiber proof for pointed addition in `PointedIncidenceDescent`. -/
noncomputable def unprependPower :
    power S (Fin (n + 1)) X ⟶ orderedAmbient S n X :=
  Limits.prod.lift
    (Pi.π (fun _ : Fin (n + 1) ↦ X) 0)
    (Limits.Pi.lift fun i : Fin n ↦
      Pi.π (fun _ : Fin (n + 1) ↦ X) i.succ)

/-- Deleting the newly prepended coordinate is a left inverse to
prepending it. -/
@[reassoc]
theorem prependPower_comp_unprependPower :
    prependPower S n X ≫ unprependPower S n X =
      𝟙 (orderedAmbient S n X) := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, unprependPower, Limits.prod.lift_fst,
      prependPower_comp_π_zero, Category.id_comp]
  · apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, unprependPower, Limits.prod.lift_snd,
      Limits.Pi.lift_π, prependPower_comp_π_succ, Category.id_comp]
    rfl

/-- Prepending a coordinate is injective on underlying scheme points. -/
theorem prependPower_injective :
    Function.Injective (prependPower S n X).left := by
  intro x y hxy
  have h := congrArg (unprependPower S n X).left hxy
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply] at h
  have hcomp := congrArg Over.Hom.left
    (prependPower_comp_unprependPower S n X)
  change
    (prependPower S n X).left ≫ (unprependPower S n X).left =
      𝟙 (orderedAmbient S n X).left at hcomp
  rw [hcomp] at h
  simpa using h

/-- Forget one selected ordered coordinate while retaining the distinguished
point.  The remaining coordinates are indexed using `Fin.succAbove`. -/
noncomputable def removeCoordinate (i : Fin (n + 1)) :
    orderedAmbient S (n + 1) X ⟶ orderedAmbient S n X :=
  Limits.prod.lift
    (pointProjection S (n + 1) X)
    (Limits.Pi.lift fun j : Fin n ↦
      coordinateProjection S (n + 1) X (i.succAbove j))

@[reassoc]
theorem removeCoordinate_comp_pointProjection (i : Fin (n + 1)) :
    removeCoordinate S n X i ≫ pointProjection S n X =
      pointProjection S (n + 1) X := by
  exact Limits.prod.lift_fst _ _

@[reassoc]
theorem removeCoordinate_comp_coordinateProjection
    (i : Fin (n + 1)) (j : Fin n) :
    removeCoordinate S n X i ≫ coordinateProjection S n X j =
      coordinateProjection S (n + 1) X (i.succAbove j) := by
  rw [coordinateProjection, ← Category.assoc, removeCoordinate,
    Limits.prod.lift_snd, Limits.Pi.lift_π]

/-- Reindex a tuple inserted at coordinate zero so that its new coordinate
occupies the selected position `i`. -/
def moveZeroTo (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' 0).trans (finSuccEquiv' i).symm

@[simp]
theorem moveZeroTo_zero (i : Fin (n + 1)) :
    moveZeroTo n i 0 = i := by
  simp [moveZeroTo]

@[simp]
theorem moveZeroTo_succ (i : Fin (n + 1)) (j : Fin n) :
    moveZeroTo n i j.succ = i.succAbove j := by
  change (finSuccEquiv' i).symm (finSuccEquiv' 0 j.succ) = i.succAbove j
  rw [← Fin.succAbove_zero_apply j, finSuccEquiv'_succAbove]
  simp

@[simp]
theorem moveZeroTo_symm_index (i : Fin (n + 1)) :
    (moveZeroTo n i).symm i = 0 := by
  apply (moveZeroTo n i).injective
  simp

@[simp]
theorem moveZeroTo_symm_succAbove (i : Fin (n + 1)) (j : Fin n) :
    (moveZeroTo n i).symm (i.succAbove j) = j.succ := by
  apply (moveZeroTo n i).injective
  simp

/-- The ordered pointed-addition map
`X × Xⁿ ⟶ X × Xⁿ⁺¹`. -/
noncomputable def orderedAmbientInsertion :
    orderedAmbient S n X ⟶ orderedAmbient S (n + 1) X :=
  Limits.prod.lift (pointProjection S n X) (prependPower S n X)

@[reassoc]
theorem orderedAmbientInsertion_comp_pointProjection :
    orderedAmbientInsertion S n X ≫ pointProjection S (n + 1) X =
      pointProjection S n X := by
  exact Limits.prod.lift_fst _ _

@[reassoc]
theorem orderedAmbientInsertion_comp_coordinateProjection_zero :
    orderedAmbientInsertion S n X ≫
        coordinateProjection S (n + 1) X 0 =
      pointProjection S n X := by
  rw [coordinateProjection, ← Category.assoc,
    orderedAmbientInsertion, Limits.prod.lift_snd,
    prependPower_comp_π_zero]

@[reassoc]
theorem orderedAmbientInsertion_comp_coordinateProjection_succ (i : Fin n) :
    orderedAmbientInsertion S n X ≫
        coordinateProjection S (n + 1) X i.succ =
      coordinateProjection S n X i := by
  rw [coordinateProjection, ← Category.assoc,
    orderedAmbientInsertion, Limits.prod.lift_snd,
    prependPower_comp_π_succ]

/-- Extend a permutation of the remaining coordinates to one fixing the
new zeroth coordinate. -/
def fixZeroPermutation (g : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  g.extendDomain (finSuccAboveEquiv 0)

@[simp]
theorem fixZeroPermutation_zero (g : Equiv.Perm (Fin n)) :
    fixZeroPermutation n g 0 = 0 := by
  exact Equiv.Perm.extendDomain_apply_not_subtype g
    (finSuccAboveEquiv 0) (by simp)

@[simp]
theorem fixZeroPermutation_succ (g : Equiv.Perm (Fin n)) (i : Fin n) :
    fixZeroPermutation n g i.succ = (g i).succ := by
  change g.extendDomain (finSuccAboveEquiv 0)
      ((finSuccAboveEquiv 0 i).1) = _
  rw [Equiv.Perm.extendDomain_apply_image]
  rfl

/-- Insertion is equivariant for permutations of the old coordinates and
their extensions fixing coordinate zero. -/
theorem orderedAmbientPermutationHom_comp_orderedAmbientInsertion
    (g : Equiv.Perm (Fin n)) :
    orderedAmbientPermutationHom S n X g ≫ orderedAmbientInsertion S n X =
      orderedAmbientInsertion S n X ≫
        orderedAmbientPermutationHom S (n + 1) X
          (fixZeroPermutation n g) := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc,
      orderedAmbientInsertion_comp_pointProjection,
      orderedAmbientPermutationHom_comp_pointProjection]
  · apply Limits.Pi.hom_ext
    intro i
    change
      (orderedAmbientPermutationHom S n X g ≫
          orderedAmbientInsertion S n X) ≫
          coordinateProjection S (n + 1) X i =
        (orderedAmbientInsertion S n X ≫
          orderedAmbientPermutationHom S (n + 1) X
            (fixZeroPermutation n g)) ≫
          coordinateProjection S (n + 1) X i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Category.assoc,
        orderedAmbientInsertion_comp_coordinateProjection_zero,
        orderedAmbientPermutationHom_comp_pointProjection,
        orderedAmbientPermutationHom_comp_coordinateProjection,
        fixZeroPermutation_zero]
    · simp only [Category.assoc,
        orderedAmbientInsertion_comp_coordinateProjection_succ,
        orderedAmbientPermutationHom_comp_coordinateProjection,
        fixZeroPermutation_succ]

/-- The ordered pointed-addition map regarded as a map to the zeroth
coordinate graph. -/
noncomputable def orderedAmbientToZeroGraph :
    orderedAmbient S n X ⟶ coordinateGraph S (n + 1) X 0 :=
  equalizer.lift (orderedAmbientInsertion S n X) (by
    rw [orderedAmbientInsertion_comp_pointProjection,
      orderedAmbientInsertion_comp_coordinateProjection_zero])

@[reassoc (attr := simp)]
theorem orderedAmbientToZeroGraph_comp_ι :
    orderedAmbientToZeroGraph S n X ≫
        coordinateGraphι S (n + 1) X 0 =
      orderedAmbientInsertion S n X :=
  equalizer.lift_ι _ _

/-- On the `i`-th coordinate graph, deleting coordinate `i`, prepending the
distinguished point, and moving coordinate zero back to `i` recovers the
original ambient tuple.  The named downstream consumer is surjectivity of
the pointed incidence comparison in `PointedIncidenceDescent`. -/
theorem coordinateGraphι_comp_removeCoordinate_comp_insertion_comp_permutation
    (i : Fin (n + 1)) :
    coordinateGraphι S (n + 1) X i ≫
        removeCoordinate S n X i ≫
        orderedAmbientInsertion S n X ≫
        orderedAmbientPermutationHom S (n + 1) X
          (moveZeroTo n i).symm =
      coordinateGraphι S (n + 1) X i := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc,
      orderedAmbientPermutationHom_comp_pointProjection,
      orderedAmbientInsertion_comp_pointProjection,
      removeCoordinate_comp_pointProjection]
  · apply Limits.Pi.hom_ext
    intro j
    change
      (coordinateGraphι S (n + 1) X i ≫
        removeCoordinate S n X i ≫
        orderedAmbientInsertion S n X ≫
        orderedAmbientPermutationHom S (n + 1) X
          (moveZeroTo n i).symm) ≫
          coordinateProjection S (n + 1) X j =
        coordinateGraphι S (n + 1) X i ≫
          coordinateProjection S (n + 1) X j
    refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
    · simp only [Category.assoc,
        orderedAmbientPermutationHom_comp_coordinateProjection,
        moveZeroTo_symm_index,
        orderedAmbientInsertion_comp_coordinateProjection_zero,
        removeCoordinate_comp_pointProjection]
      exact equalizer.condition
        (pointProjection S (n + 1) X)
        (coordinateProjection S (n + 1) X i)
    · simp only [Category.assoc,
        orderedAmbientPermutationHom_comp_coordinateProjection,
        moveZeroTo_symm_succAbove,
        orderedAmbientInsertion_comp_coordinateProjection_succ,
        removeCoordinate_comp_coordinateProjection]

variable [IsSeparated X.hom]

/-- The ordered pointed-addition map annihilates the full incidence ideal. -/
theorem orderedIncidenceIdeal_le_ker_orderedAmbientInsertion :
    orderedIncidenceIdeal S (n + 1) X ≤
      (orderedAmbientInsertion S n X).left.ker := by
  refine (orderedIncidenceIdeal_le_coordinateGraphIdeal S (n + 1) X 0).trans ?_
  rw [coordinateGraphIdeal]
  have h := Scheme.Hom.le_ker_comp
    (orderedAmbientToZeroGraph S n X).left
    (coordinateGraphι S (n + 1) X 0).left
  simpa only [← Over.comp_left, orderedAmbientToZeroGraph_comp_ι] using h

/-- Scheme-theoretic insertion into the ordered incidence family. -/
noncomputable def orderedPointedIncidenceMap :
    (orderedAmbient S n X).left ⟶ orderedIncidence S (n + 1) X :=
  IsClosedImmersion.lift
    (orderedIncidenceι S (n + 1) X)
    (orderedAmbientInsertion S n X).left
    (by
      change (orderedIncidenceIdeal S (n + 1) X).subschemeι.ker ≤ _
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact orderedIncidenceIdeal_le_ker_orderedAmbientInsertion S n X)

@[reassoc]
theorem orderedPointedIncidenceMap_comp_ι :
    orderedPointedIncidenceMap S n X ≫
        orderedIncidenceι S (n + 1) X =
      (orderedAmbientInsertion S n X).left :=
  IsClosedImmersion.lift_fac _ _ _

/-- Scheme-theoretic insertion is equivariant for permutations of the old
coordinates and the corresponding permutations fixing coordinate zero. -/
theorem orderedAmbientAction_comp_orderedPointedIncidenceMap
    (g : Equiv.Perm (Fin n)) :
    (orderedAmbientAction S n X).hom g ≫
        orderedPointedIncidenceMap S n X =
      orderedPointedIncidenceMap S n X ≫
        (orderedIncidenceAction S (n + 1) X).hom
          (fixZeroPermutation n g) := by
  apply (cancel_mono (orderedIncidenceι S (n + 1) X)).mp
  rw [Category.assoc, orderedPointedIncidenceMap_comp_ι,
    Category.assoc, orderedIncidenceAction_comp_ι,
    ← Category.assoc, orderedPointedIncidenceMap_comp_ι]
  exact congrArg Over.Hom.left
    (orderedAmbientPermutationHom_comp_orderedAmbientInsertion S n X g)

end MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidence
