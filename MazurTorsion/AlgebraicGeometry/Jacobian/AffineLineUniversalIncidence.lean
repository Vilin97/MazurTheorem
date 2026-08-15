/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.AdjoinRootBaseChange
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineMonicCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotientFlatBaseChange

/-!
# The affine-line universal incidence quotient

The ordered incidence family over ordered roots is obtained by adjoining a
root of the product of the ordered linear factors.  Vieta identifies that
polynomial with the pullback of the universal monic polynomial from the
invariant coefficient ring.  Thus the ordered incidence algebra is a flat
base change of the universal root algebra.  Flat base change for finite-group
invariants then recovers the universal root algebra as its invariant ring,
without dividing by the order of the symmetric group.

This is the characteristic-free affine calculation needed by the named
downstream consumer `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open Algebra Polynomial TensorProduct

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineUniversalIncidence

open AffineLineMonicCoordinates
open AffineLineSymmetricPower
open FiniteGroupQuotientFlatBaseChange

variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

/-- The universal monic polynomial, transported from free coefficient
coordinates to the invariant ring of ordered roots. -/
noncomputable def invariantUniversalPolynomial :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    Polynomial (FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  exact (Polynomial.freeMonic R n).map
    (monicCoefficientEquivFixedPoints R n).toRingHom

/-- After inclusion into ordered-root coordinates, the invariant universal
polynomial is exactly the product of the ordered linear root factors. -/
theorem invariantUniversalPolynomial_map_inclusion :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    (invariantUniversalPolynomial R n).map
        (algebraMap
          (FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
            (Equiv.Perm (Fin n)))
          (MvPolynomial (Fin n) R)) =
      orderedRootPolynomial R n := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  rw [invariantUniversalPolynomial, Polynomial.map_map]
  exact freeMonic_map_monicCoefficientToRoots R n

omit [Nontrivial R] in
/-- The invariant universal polynomial remains monic. -/
theorem invariantUniversalPolynomial_monic :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    (invariantUniversalPolynomial R n).Monic := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  exact (Polynomial.monic_freeMonic R n).map _

omit [Nontrivial R] in
/-- The root algebra over the invariant coefficient ring is flat. -/
theorem invariantRootAlgebra_flat :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    Module.Flat
      (FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
        (Equiv.Perm (Fin n)))
      (AdjoinRoot (invariantUniversalPolynomial R n)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : Module.Free
      (FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
        (Equiv.Perm (Fin n)))
      (AdjoinRoot (invariantUniversalPolynomial R n)) :=
    (invariantUniversalPolynomial_monic R n).free_adjoinRoot
  infer_instance

/-- The ordered incidence algebra is the scalar extension of the universal
root algebra from symmetric coefficients to ordered roots. -/
noncomputable def orderedIncidenceBaseChangeEquiv :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    MvPolynomial (Fin n) R ⊗[F]
        AdjoinRoot (invariantUniversalPolynomial R n) ≃ₐ[MvPolynomial (Fin n) R]
      AdjoinRoot (orderedRootPolynomial R n) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  exact (AdjoinRootBaseChange.equiv F (MvPolynomial (Fin n) R)
    (invariantUniversalPolynomial R n)).trans
      (AdjoinRoot.algEquivOfEq (MvPolynomial (Fin n) R)
        ((invariantUniversalPolynomial R n).map (algebraMap F _))
        (orderedRootPolynomial R n)
        (invariantUniversalPolynomial_map_inclusion R n))

/-- Invariants of the ordered-incidence base-change algebra are exactly the
universal root algebra over symmetric coefficients. -/
noncomputable def invariantRootEquivBaseChangeFixedPoints :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    AdjoinRoot (invariantUniversalPolynomial R n) ≃ₐ[F]
      FixedPoints.subalgebra F
        (MvPolynomial (Fin n) R ⊗[F]
          AdjoinRoot (invariantUniversalPolynomial R n))
        (Equiv.Perm (Fin n)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI : Module.Flat F
      (AdjoinRoot (invariantUniversalPolynomial R n)) :=
    invariantRootAlgebra_flat R n
  exact AlgEquiv.ofBijective
    (includeRightFixedPoints
      (G := Equiv.Perm (Fin n)) (R := R)
      (A := MvPolynomial (Fin n) R)
      (AdjoinRoot (invariantUniversalPolynomial R n)))
    (bijective_includeRightFixedPoints_of_flat
      (G := Equiv.Perm (Fin n)) (R := R)
      (A := MvPolynomial (Fin n) R)
      (AdjoinRoot (invariantUniversalPolynomial R n)))

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineUniversalIncidence
