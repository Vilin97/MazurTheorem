/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFiberMonicCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitTupleStabilizer
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentUniversalRoot

/-!
# Coefficient charts for split symmetric-quotient components

On a component of a split ordered power, the residual tuple stabilizer is a
product of symmetric groups, one for every sheet fiber.  Enumerate every
finite fiber and transport this stabilizer action to the joint root variables
used by SplitComponentUniversalRoot.  The finite-family block invariant
theorem then identifies the stabilizer fixed ring, and hence its affine
quotient, with the joint monic-coefficient space.

The named downstream consumer is the local comparison for
PointedIncidenceDescent.pointedUniversalEffectiveDivisor.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitSymmetricQuotientChart

open SplitFiniteSymmetricQuotient
open SplitTupleStabilizer
open SplitComponentUniversalRoot
open BlockPermutationInvariants
open FiniteFiberPermutationInvariants
open FiniteFiberMonicCoordinates

variable (R : Type u) [CommRing R]
variable (d m : ℕ) (c : splitComponentIndex d m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- Independent permutations of the enumerated root variables on every
sheet of a split component. -/
abbrev componentRootPermutationGroup :=
  ∀ j : Fin m, Equiv.Perm (Fin (sheetMultiplicity d m c j))

/-- Enumerate a sheet fiber by Fin and conjugate its permutation group. -/
noncomputable def fiberPermutationEquivRootPermutation :
    (∀ j : Fin m, Equiv.Perm { i : Fin d // c.out i = j }) ≃*
      componentRootPermutationGroup d m c :=
  MulEquiv.piCongrRight fun j ↦
    (Fintype.equivFin { i : Fin d // c.out i = j }).permCongrHom

/-- The tuple stabilizer, expressed as permutations of the enumerated root
variables grouped by sheet. -/
noncomputable def stabilizerEquivRootPermutation :
    MulAction.stabilizer (Equiv.Perm (Fin d)) c.out ≃*
      componentRootPermutationGroup d m c :=
  (stabilizerEquivFiberPerm d m c.out).trans
    (fiberPermutationEquivRootPermutation d m c)

/-- The residual tuple stabilizer acts on the root-coordinate polynomial
ring through its independent sheet-fiber permutations. -/
@[instance_reducible]
noncomputable def componentStabilizerRootAction :
    MulSemiringAction
      (MulAction.stabilizer (Equiv.Perm (Fin d)) c.out)
      (coefficientRing R d m c) := by
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  exact MulSemiringAction.compHom (coefficientRing R d m c)
    (stabilizerEquivRootPermutation d m c).toMonoidHom

/-- The transported stabilizer action fixes the coefficient base ring. -/
theorem componentStabilizerRootSMulCommClass :
    letI := componentStabilizerRootAction R d m c
    SMulCommClass (MulAction.stabilizer (Equiv.Perm (Fin d)) c.out) R
      (coefficientRing R d m c) := by
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := fiberPermutationSMulCommClass R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := componentStabilizerRootAction R d m c
  constructor
  intro g r p
  change stabilizerEquivRootPermutation d m c g • (r • p) =
    r • stabilizerEquivRootPermutation d m c g • p
  exact smul_comm _ _ _

/-- Replacing the tuple stabilizer by the isomorphic product of root-fiber
permutation groups does not change the fixed ring. -/
noncomputable def stabilizerFixedEquivRootPermutationFixed :
    letI := componentStabilizerRootAction R d m c
    letI := componentStabilizerRootSMulCommClass R d m c
    letI := fiberPermutationAction R (Fin m)
      (fun j ↦ Fin (sheetMultiplicity d m c j))
    letI := fiberPermutationSMulCommClass R (Fin m)
      (fun j ↦ Fin (sheetMultiplicity d m c j))
    FixedPoints.subalgebra R (coefficientRing R d m c)
        (MulAction.stabilizer (Equiv.Perm (Fin d)) c.out) ≃ₐ[R]
      FixedPoints.subalgebra R (coefficientRing R d m c)
        (componentRootPermutationGroup d m c) := by
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := fiberPermutationSMulCommClass R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := componentStabilizerRootAction R d m c
  letI := componentStabilizerRootSMulCommClass R d m c
  let G := MulAction.stabilizer (Equiv.Perm (Fin d)) c.out
  let H := componentRootPermutationGroup d m c
  let A := FixedPoints.subalgebra R (coefficientRing R d m c) G
  let B := FixedPoints.subalgebra R (coefficientRing R d m c) H
  let forward : A →ₐ[R] B :=
    { toFun := fun p ↦ ⟨p.1, fun h ↦ by
          let g := (stabilizerEquivRootPermutation d m c).symm h
          have hg := p.2 g
          change stabilizerEquivRootPermutation d m c g • p.1 = p.1 at hg
          simpa [g] using hg⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  let backward : B →ₐ[R] A :=
    { toFun := fun p ↦ ⟨p.1, fun g ↦ by
          change stabilizerEquivRootPermutation d m c g • p.1 = p.1
          exact p.2 (stabilizerEquivRootPermutation d m c g)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  apply AlgEquiv.ofAlgHom forward backward
  · rfl
  · rfl

/-- The actual residual-stabilizer invariant ring on a split component is the
joint polynomial coefficient ring used by its universal monic root family. -/
noncomputable def componentStabilizerInvariantAlgEquiv :
    letI := componentStabilizerRootAction R d m c
    letI := componentStabilizerRootSMulCommClass R d m c
    coefficientRing R d m c ≃ₐ[R]
      FixedPoints.subalgebra R (coefficientRing R d m c)
        (MulAction.stabilizer (Equiv.Perm (Fin d)) c.out) := by
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := fiberPermutationSMulCommClass R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := componentStabilizerRootAction R d m c
  letI := componentStabilizerRootSMulCommClass R d m c
  exact (monicCoefficientInvariantAlgEquiv R m
      (sheetMultiplicity d m c)).trans
    (stabilizerFixedEquivRootPermutationFixed R d m c).symm

/-- The split-component quotient chart uses the same monic coefficient
coordinates as the universal root polynomial on every sheet. -/
theorem componentStabilizerInvariantAlgEquiv_X
    (x : componentRootIndex d m c) :
    letI := componentStabilizerRootAction R d m c
    letI := componentStabilizerRootSMulCommClass R d m c
    ((componentStabilizerInvariantAlgEquiv R d m c)
      (MvPolynomial.X x)).1 =
      MvPolynomial.C ((-1 : R) ^
        (sheetMultiplicity d m c x.1 - (x.2 : ℕ))) *
        blockElementarySymmetric R (Fin m)
          (fun j ↦ Fin (sheetMultiplicity d m c j)) x.1
          (sheetMultiplicity d m c x.1 - (x.2 : ℕ)) := by
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := fiberPermutationSMulCommClass R (Fin m)
    (fun j ↦ Fin (sheetMultiplicity d m c j))
  letI := componentStabilizerRootAction R d m c
  letI := componentStabilizerRootSMulCommClass R d m c
  change ((monicCoefficientInvariantAlgEquiv R m
    (sheetMultiplicity d m c)) (MvPolynomial.X x)).1 = _
  exact monicCoefficientInvariantAlgEquiv_X R m
    (sheetMultiplicity d m c) x

/-- Affine scheme form of the split component calculation: the quotient by
the residual tuple stabilizer is the coefficient base of the universal root
projection. -/
noncomputable def componentStabilizerInvariantSchemeIso :
    letI := componentStabilizerRootAction R d m c
    letI := componentStabilizerRootSMulCommClass R d m c
    _root_.AlgebraicGeometry.Spec (.of
      (FixedPoints.subalgebra R (coefficientRing R d m c)
        (MulAction.stabilizer (Equiv.Perm (Fin d)) c.out))) ≅
      _root_.AlgebraicGeometry.Spec (.of (coefficientRing R d m c)) := by
  letI := componentStabilizerRootAction R d m c
  letI := componentStabilizerRootSMulCommClass R d m c
  exact _root_.AlgebraicGeometry.Scheme.Spec.mapIso
    (componentStabilizerInvariantAlgEquiv R d m c).toRingEquiv.toCommRingCatIso.op

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitSymmetricQuotientChart
