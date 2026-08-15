/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.AdjoinRootBaseChange
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineMonicCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotientFlatBaseChange
import MazurTorsion.AlgebraicGeometry.Jacobian.MonicRootFamily

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

open Algebra CategoryTheory Polynomial TensorProduct
open _root_.AlgebraicGeometry

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

/-- The coordinate-permutation action on the ordered incidence root algebra,
transported from its tensor-product presentation.  It permutes the ordered
roots and fixes the distinguished adjoined root. -/
@[instance_reducible]
noncomputable def orderedIncidenceAction :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    MulSemiringAction (Equiv.Perm (Fin n))
      (AdjoinRoot (orderedRootPolynomial R n)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  let e := orderedIncidenceBaseChangeEquiv R n
  exact
    { smul := fun g x ↦ e (g • e.symm x)
      one_smul := fun x ↦ by
        change e ((1 : Equiv.Perm (Fin n)) • e.symm x) = x
        rw [one_smul, e.apply_symm_apply]
      mul_smul := fun g h x ↦ by
        change e ((g * h) • e.symm x) =
          e (g • e.symm (e (h • e.symm x)))
        rw [mul_smul, e.symm_apply_apply]
      smul_zero := fun g ↦ by
        change e (g • e.symm 0) = 0
        rw [map_zero, smul_zero, map_zero]
      smul_add := fun g x y ↦ by
        change e (g • e.symm (x + y)) =
          e (g • e.symm x) + e (g • e.symm y)
        rw [map_add, smul_add, map_add]
      smul_one := fun g ↦ by
        change e (g • e.symm 1) = 1
        rw [map_one, smul_one, map_one]
      smul_mul := fun g x y ↦ by
        change e (g • e.symm (x * y)) =
          e (g • e.symm x) * e (g • e.symm y)
        rw [map_mul, smul_mul', map_mul] }

/-- The transported action fixes the invariant coefficient ring. -/
theorem orderedIncidenceSMulCommClass :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    SMulCommClass (Equiv.Perm (Fin n)) F
      (AdjoinRoot (orderedRootPolynomial R n)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  let e := (orderedIncidenceBaseChangeEquiv R n).restrictScalars F
  constructor
  intro g r x
  change e (g • e.symm (r • x)) = r • e (g • e.symm x)
  calc
    _ = e (g • (r • e.symm x)) :=
      congrArg (fun z ↦ e (g • z))
        (e.symm.toLinearEquiv.map_smul r x)
    _ = e (r • (g • e.symm x)) :=
      congrArg e (smul_comm g r (e.symm x))
    _ = _ := e.toLinearEquiv.map_smul r (g • e.symm x)

/-- The base-change equivalence is equivariant for the tensor-product action
and the transported ordered-incidence action. -/
theorem orderedIncidenceBaseChangeEquiv_smul
    (g : Equiv.Perm (Fin n))
    (x : letI := coordinatePermutationAction R (Fin n)
      letI := coordinatePermutationSMulCommClass R (Fin n)
      let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
        (Equiv.Perm (Fin n))
      MvPolynomial (Fin n) R ⊗[F]
        AdjoinRoot (invariantUniversalPolynomial R n)) :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI := orderedIncidenceAction R n
    orderedIncidenceBaseChangeEquiv R n (g • x) =
      g • orderedIncidenceBaseChangeEquiv R n x := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI := orderedIncidenceAction R n
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  let e := orderedIncidenceBaseChangeEquiv R n
  change e (g • x) = e (g • e.symm (e x))
  rw [e.symm_apply_apply]

/-- Transporting fixed points through the ordered-incidence base-change
equivalence identifies the tensor-model fixed ring with the fixed ring of the
ordered root algebra. -/
noncomputable def baseChangeFixedPointsEquivOrderedIncidenceFixedPoints :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    FixedPoints.subalgebra F
        (MvPolynomial (Fin n) R ⊗[F]
          AdjoinRoot (invariantUniversalPolynomial R n))
        (Equiv.Perm (Fin n)) ≃ₐ[F]
      FixedPoints.subalgebra F
        (AdjoinRoot (orderedRootPolynomial R n))
        (Equiv.Perm (Fin n)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  let e := (orderedIncidenceBaseChangeEquiv R n).restrictScalars F
  exact
    { toFun := fun x ↦ ⟨e x.1, fun g ↦ by
          change e (g • e.symm (e x.1)) = e x.1
          rw [e.symm_apply_apply]
          exact congrArg e (x.2 g)⟩
      invFun := fun x ↦ ⟨e.symm x.1, fun g ↦ by
          apply e.injective
          change e (g • e.symm x.1) = e (e.symm x.1)
          have hx := x.2 g
          change e (g • e.symm x.1) = x.1 at hx
          exact hx.trans (e.apply_symm_apply x.1).symm⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.1)
      map_mul' := fun x y ↦ Subtype.ext (map_mul e x.1 y.1)
      map_add' := fun x y ↦ Subtype.ext (map_add e x.1 y.1)
      commutes' := fun r ↦ Subtype.ext (e.commutes r) }

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

/-- The quotient of the ordered affine incidence algebra by coordinate
permutations is the universal monic root algebra. -/
noncomputable def invariantRootEquivOrderedIncidenceFixedPoints :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    AdjoinRoot (invariantUniversalPolynomial R n) ≃ₐ[F]
      FixedPoints.subalgebra F
        (AdjoinRoot (orderedRootPolynomial R n))
        (Equiv.Perm (Fin n)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  exact (invariantRootEquivBaseChangeFixedPoints R n).trans
    (baseChangeFixedPointsEquivOrderedIncidenceFixedPoints R n)

/-- The affine quotient of the ordered incidence root algebra. -/
noncomputable def orderedIncidenceInvariantScheme :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    Scheme.{u} := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  exact Spec (.of (FixedPoints.subalgebra F
    (AdjoinRoot (orderedRootPolynomial R n)) (Equiv.Perm (Fin n))))

/-- The affine ordered-incidence quotient is the universal monic root
scheme. -/
noncomputable def orderedIncidenceInvariantSchemeIsoRoot :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    orderedIncidenceInvariantScheme R n ≅
      Spec (.of (AdjoinRoot (invariantUniversalPolynomial R n))) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  exact Scheme.Spec.mapIso
    ((invariantRootEquivOrderedIncidenceFixedPoints R n).toRingEquiv.toCommRingCatIso.op)

/-- The structure map from the affine incidence quotient to invariant
coefficient space. -/
noncomputable def orderedIncidenceInvariantProjection :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    orderedIncidenceInvariantScheme R n ⟶ Spec (.of F) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  exact Spec.map (CommRingCat.ofHom (algebraMap F
    (FixedPoints.subalgebra F
      (AdjoinRoot (orderedRootPolynomial R n)) (Equiv.Perm (Fin n)))))

/-- Under the quotient/root-scheme isomorphism, the quotient structure map
is the universal monic root projection. -/
theorem orderedIncidenceInvariantSchemeIsoRoot_hom_comp_projection :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    letI : Fact (invariantUniversalPolynomial R n).Monic :=
      ⟨invariantUniversalPolynomial_monic R n⟩
    (orderedIncidenceInvariantSchemeIsoRoot R n).hom ≫
        MonicRootFamily.projection F (invariantUniversalPolynomial R n) =
      orderedIncidenceInvariantProjection R n := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  letI : Fact (invariantUniversalPolynomial R n).Monic :=
    ⟨invariantUniversalPolynomial_monic R n⟩
  rw [orderedIncidenceInvariantSchemeIsoRoot,
    orderedIncidenceInvariantProjection]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  simp only [Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    Quiver.Hom.unop_op, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    AlgEquiv.toRingEquiv_toRingHom]
  apply RingHom.ext
  intro r
  exact (invariantRootEquivOrderedIncidenceFixedPoints R n).commutes r

instance orderedIncidenceInvariantProjection_isFinite :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    IsFinite (orderedIncidenceInvariantProjection R n) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  letI : Fact (invariantUniversalPolynomial R n).Monic :=
    ⟨invariantUniversalPolynomial_monic R n⟩
  rw [← orderedIncidenceInvariantSchemeIsoRoot_hom_comp_projection]
  infer_instance

instance orderedIncidenceInvariantProjection_flat :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    Flat (orderedIncidenceInvariantProjection R n) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  letI : Fact (invariantUniversalPolynomial R n).Monic :=
    ⟨invariantUniversalPolynomial_monic R n⟩
  rw [← orderedIncidenceInvariantSchemeIsoRoot_hom_comp_projection]
  infer_instance

/-- The affine incidence quotient has constant rank `n` over the symmetric
coefficient space. -/
theorem orderedIncidenceInvariantProjection_finrank :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    letI : SMulCommClass R (Equiv.Perm (Fin n))
        (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
    let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))
    letI := orderedIncidenceAction R n
    letI := orderedIncidenceSMulCommClass R n
    (orderedIncidenceInvariantProjection R n).finrank = fun _ ↦ n := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  letI : SMulCommClass R (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) R) := SMulCommClass.symm _ _ _
  let F := FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
    (Equiv.Perm (Fin n))
  letI := orderedIncidenceAction R n
  letI := orderedIncidenceSMulCommClass R n
  letI : Fact (invariantUniversalPolynomial R n).Monic :=
    ⟨invariantUniversalPolynomial_monic R n⟩
  rw [← orderedIncidenceInvariantSchemeIsoRoot_hom_comp_projection,
    Scheme.Hom.finrank_comp_left_of_isIso]
  calc
    _ = fun _ ↦ (invariantUniversalPolynomial R n).natDegree :=
      MonicRootFamily.projection_finrank F
        (invariantUniversalPolynomial R n)
    _ = fun _ ↦ n := by
      ext x
      rw [invariantUniversalPolynomial,
        Polynomial.natDegree_map_eq_of_injective
          (monicCoefficientEquivFixedPoints R n).injective]
      exact Polynomial.natDegree_freeMonic R n

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineUniversalIncidence
