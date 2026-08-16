/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFiberMonicCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitTupleStabilizer

/-!
# Monic coordinates for the stabilizer of an assigned tuple

Fix a finite tuple `a : Fin d → Fin m`.  Its stabilizer in the symmetric
group on `Fin d` is canonically the product of the symmetric groups on the
fibers of `a`.  After reindexing root variables by those fibers, the
fundamental theorem of symmetric polynomials therefore identifies the
stabilizer-fixed ring with a polynomial ring in blockwise monic
coefficients.

The construction applies to an arbitrary tuple, including empty fibers,
and records both the algebra equivalence and its contravariant scheme
isomorphism.  The named downstream consumer is `GeometricBlockMonicChart`,
where `a` is the support-assignment tuple of a geometric divisor.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AssignedTupleMonicCoordinates

open AffineLineSymmetricPower
open BlockPermutationInvariants
open FiniteFiberMonicCoordinates
open SplitFiniteSymmetricQuotient
open SplitTupleStabilizer

variable (R : Type u) [CommRing R]
variable (d m : ℕ) (a : Fin d → Fin m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- The subgroup of coordinate permutations preserving the assigned tuple. -/
abbrev stabilizer :=
  MulAction.stabilizer (Equiv.Perm (Fin d)) a

/-- The number of occurrences assigned to one support index. -/
abbrev fiberSize (j : Fin m) :=
  Fintype.card { i : Fin d // a i = j }

/-- The family of monic-coefficient variables, grouped by support index. -/
abbrev monicIndex :=
  Σ j : Fin m, Fin (fiberSize d m a j)

/-- Replace each subtype fiber by its canonical finite ordinal. -/
def fiberSigmaEquivMonicIndex :
    (Σ j : Fin m, { i : Fin d // a i = j }) ≃ monicIndex d m a :=
  Equiv.sigmaCongrRight fun _ ↦ Fintype.equivFin _

/-- Reindex occurrence positions by their support fiber and position inside
that fiber. -/
def positionEquivMonicIndex : Fin d ≃ monicIndex d m a :=
  (Equiv.sigmaFiberEquiv a).symm.trans
    (fiberSigmaEquivMonicIndex d m a)

/-- Conjugate a permutation of a subtype fiber to its canonical finite
ordinal. -/
def fiberPermEquivFinPerm (j : Fin m) :
    Equiv.Perm { i : Fin d // a i = j } ≃*
      Equiv.Perm (Fin (fiberSize d m a j)) :=
  (Fintype.equivFin { i : Fin d // a i = j }).permCongrHom

/-- The tuple stabilizer is the product of the symmetric groups on the
canonical finite fibers. -/
def stabilizerEquivMonicPermutations :
    stabilizer d m a ≃*
      (∀ j : Fin m, Equiv.Perm (Fin (fiberSize d m a j))) :=
  (stabilizerEquivFiberPerm d m a).trans
    (MulEquiv.piCongrRight (fiberPermEquivFinPerm d m a))

/-- The stabilizer action on the root-coordinate polynomial ring. -/
@[instance_reducible]
def stabilizerRootAction :
    MulSemiringAction (stabilizer d m a) (MvPolynomial (Fin d) R) :=
  MulSemiringAction.compHom (MvPolynomial (Fin d) R)
    ((coordinatePermutationRingAut R (Fin d)).comp
      (MulAction.stabilizer (Equiv.Perm (Fin d)) a).subtype)

/-- Scalars commute with the stabilizer action on root coordinates. -/
theorem stabilizerRootSMulCommClass :
    letI := stabilizerRootAction R d m a
    SMulCommClass (stabilizer d m a) R (MvPolynomial (Fin d) R) := by
  letI := stabilizerRootAction R d m a
  constructor
  intro g r p
  change MvPolynomial.rename g.1 (r • p) =
    r • MvPolynomial.rename g.1 p
  simp [Algebra.smul_def]

/-- The canonical sigma-fiber reindexing respects a stabilizer
permutation. -/
theorem sigmaFiberEquiv_equivariant
    (g : stabilizer d m a) (i : Fin d) :
    (Equiv.sigmaFiberEquiv a).symm (g.1 i) =
      Equiv.Perm.sigmaCongrRight
        (stabilizerToFiberPerm d m a g)
          ((Equiv.sigmaFiberEquiv a).symm i) := by
  apply (Equiv.sigmaFiberEquiv a).injective
  simp [stabilizerToFiberPerm]

/-- The final occurrence-to-coefficient reindexing respects the product of
fiber permutations. -/
theorem positionEquivMonicIndex_equivariant
    (g : stabilizer d m a) (i : Fin d) :
    positionEquivMonicIndex d m a (g.1 i) =
      Equiv.Perm.sigmaCongrRight
          (stabilizerEquivMonicPermutations d m a g)
          (positionEquivMonicIndex d m a i) := by
  rw [positionEquivMonicIndex, Equiv.trans_apply,
    sigmaFiberEquiv_equivariant d m a]
  simp [fiberSigmaEquivMonicIndex,
    stabilizerEquivMonicPermutations, fiberPermEquivFinPerm,
    stabilizerEquivFiberPerm, stabilizerToFiberPermHom]

/-- Renaming occurrence variables by the block index intertwines the
stabilizer action with independent permutations of the fibers. -/
theorem rename_stabilizerRootAction_eq_fiberAction
    (g : stabilizer d m a) (p : MvPolynomial (Fin d) R) :
    letI := stabilizerRootAction R d m a
    letI := fiberPermutationAction R (Fin m)
      (fun j ↦ Fin (fiberSize d m a j))
    MvPolynomial.rename (positionEquivMonicIndex d m a) (g • p) =
      stabilizerEquivMonicPermutations d m a g •
        MvPolynomial.rename (positionEquivMonicIndex d m a) p := by
  letI := stabilizerRootAction R d m a
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (fiberSize d m a j))
  change MvPolynomial.rename (positionEquivMonicIndex d m a)
      (MvPolynomial.rename g.1 p) =
    MvPolynomial.rename
      (Equiv.Perm.sigmaCongrRight
        (stabilizerEquivMonicPermutations d m a g))
      (MvPolynomial.rename (positionEquivMonicIndex d m a) p)
  rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
  apply congrArg (fun f ↦ MvPolynomial.rename f p)
  funext i
  exact positionEquivMonicIndex_equivariant d m a g i

/-- Reindexing occurrence variables identifies the stabilizer-fixed ring
with the fixed ring for independent permutations in every support fiber. -/
noncomputable def stabilizerFixedAlgEquivFiberFixed :
    letI := stabilizerRootAction R d m a
    letI := stabilizerRootSMulCommClass R d m a
    letI := fiberPermutationAction R (Fin m)
      (fun j ↦ Fin (fiberSize d m a j))
    letI := fiberPermutationSMulCommClass R (Fin m)
      (fun j ↦ Fin (fiberSize d m a j))
    FixedPoints.subalgebra R (MvPolynomial (Fin d) R)
        (stabilizer d m a) ≃ₐ[R]
      FixedPoints.subalgebra R
        (MvPolynomial (monicIndex d m a) R)
        (∀ j : Fin m, Equiv.Perm (Fin (fiberSize d m a j))) := by
  letI := stabilizerRootAction R d m a
  letI := stabilizerRootSMulCommClass R d m a
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (fiberSize d m a j))
  letI := fiberPermutationSMulCommClass R (Fin m)
    (fun j ↦ Fin (fiberSize d m a j))
  let e := MvPolynomial.renameEquiv R (positionEquivMonicIndex d m a)
  let G := stabilizer d m a
  let H := ∀ j : Fin m, Equiv.Perm (Fin (fiberSize d m a j))
  let A := FixedPoints.subalgebra R (MvPolynomial (Fin d) R) G
  let B := FixedPoints.subalgebra R
    (MvPolynomial (monicIndex d m a) R) H
  let forward : A →ₐ[R] B :=
    { toFun := fun p ↦ ⟨e p.1, fun h ↦ by
          let g := (stabilizerEquivMonicPermutations d m a).symm h
          calc
            h • e p.1 = e (g • p.1) := by
              simpa [g, e] using
                (rename_stabilizerRootAction_eq_fiberAction R d m a g p.1).symm
            _ = e p.1 := congrArg e (p.2 g)⟩
      map_one' := by apply Subtype.ext; exact e.map_one
      map_mul' := fun p q ↦ by apply Subtype.ext; exact e.map_mul p.1 q.1
      map_zero' := by apply Subtype.ext; exact e.map_zero
      map_add' := fun p q ↦ by apply Subtype.ext; exact e.map_add p.1 q.1
      commutes' := fun r ↦ by apply Subtype.ext; exact e.commutes r }
  let backward : B →ₐ[R] A :=
    { toFun := fun p ↦ ⟨e.symm p.1, fun g ↦ by
          apply e.injective
          change MvPolynomial.rename (positionEquivMonicIndex d m a)
              (g • e.symm p.1) =
            MvPolynomial.rename (positionEquivMonicIndex d m a) (e.symm p.1)
          rw [rename_stabilizerRootAction_eq_fiberAction]
          change stabilizerEquivMonicPermutations d m a g • e (e.symm p.1) =
            e (e.symm p.1)
          rw [e.apply_symm_apply]
          exact p.2 (stabilizerEquivMonicPermutations d m a g)⟩
      map_one' := by apply Subtype.ext; exact e.symm.map_one
      map_mul' := fun p q ↦ by apply Subtype.ext; exact e.symm.map_mul p.1 q.1
      map_zero' := by apply Subtype.ext; exact e.symm.map_zero
      map_add' := fun p q ↦ by apply Subtype.ext; exact e.symm.map_add p.1 q.1
      commutes' := fun r ↦ by apply Subtype.ext; exact e.symm.commutes r }
  apply AlgEquiv.ofAlgHom forward backward
  · apply DFunLike.ext _ _
    intro p
    apply Subtype.ext
    exact e.apply_symm_apply p.1
  · apply DFunLike.ext _ _
    intro p
    apply Subtype.ext
    exact e.symm_apply_apply p.1

/-- The blockwise monic coefficient polynomial ring is the fixed ring of
the stabilizer acting on the original occurrence variables. -/
noncomputable def monicCoefficientInvariantAlgEquiv :
    letI := stabilizerRootAction R d m a
    letI := stabilizerRootSMulCommClass R d m a
    MvPolynomial (monicIndex d m a) R ≃ₐ[R]
      FixedPoints.subalgebra R (MvPolynomial (Fin d) R)
        (stabilizer d m a) := by
  letI := stabilizerRootAction R d m a
  letI := stabilizerRootSMulCommClass R d m a
  letI := fiberPermutationAction R (Fin m)
    (fun j ↦ Fin (fiberSize d m a j))
  letI := fiberPermutationSMulCommClass R (Fin m)
    (fun j ↦ Fin (fiberSize d m a j))
  exact (FiniteFiberMonicCoordinates.monicCoefficientInvariantAlgEquiv R m
      (fiberSize d m a)).trans
    (stabilizerFixedAlgEquivFiberFixed R d m a).symm

/-- Scheme form of the assigned-tuple invariant calculation: the affine
quotient by the tuple stabilizer is the blockwise monic coefficient space. -/
noncomputable def monicCoefficientInvariantSchemeIso :
    letI := stabilizerRootAction R d m a
    letI := stabilizerRootSMulCommClass R d m a
    _root_.AlgebraicGeometry.Spec (.of
      (FixedPoints.subalgebra R (MvPolynomial (Fin d) R)
        (stabilizer d m a))) ≅
      _root_.AlgebraicGeometry.Spec
        (.of (MvPolynomial (monicIndex d m a) R)) := by
  letI := stabilizerRootAction R d m a
  letI := stabilizerRootSMulCommClass R d m a
  exact _root_.AlgebraicGeometry.Scheme.Spec.mapIso
    (monicCoefficientInvariantAlgEquiv R d m a).toRingEquiv.toCommRingCatIso.op

end MazurTorsion.AlgebraicGeometry.Jacobian.AssignedTupleMonicCoordinates
