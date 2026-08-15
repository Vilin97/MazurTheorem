/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.TensorProduct.Pi
import MazurTorsion.AlgebraicGeometry.Jacobian.AdjoinRootBaseChange
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotientFlatBaseChange
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentMonicCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitMonicRootFamily

/-!
# Ordered incidence on a split symmetric-power component

On one component of a split ordered power, map the sheetwise universal monic
polynomials from coefficient coordinates into the stabilizer fixed ring.
Their product of root algebras is flat over that fixed ring.  After extension
to ordered-root coordinates, tensor product commutes with the finite product
and adjoining a root commutes with base change, so the result is the product
of the sheetwise ordered-root incidence algebras.

Transporting the stabilizer action through this presentation and applying
flat invariant base change identifies the invariant ordered-incidence algebra
with the product of universal monic root algebras.  The named downstream
consumer is the split fpqc chart comparison in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open Algebra CategoryTheory Polynomial TensorProduct
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentOrderedIncidence

open AffineLineMonicCoordinates
open FiniteGroupQuotientFlatBaseChange
open SplitComponentMonicCoordinates
open SplitComponentUniversalRoot
open SplitFiniteSymmetricQuotient
open SplitMonicRootFamily
open SplitSymmetricQuotientChart

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- The residual permutation group on one split component. -/
abbrev componentStabilizer :=
  MulAction.stabilizer (Equiv.Perm (Fin d)) c.out

local instance : MulSemiringAction (componentStabilizer d m c)
    (coefficientRing R d m c) :=
  componentStabilizerRootAction R d m c

local instance : SMulCommClass (componentStabilizer d m c) R
    (coefficientRing R d m c) :=
  componentStabilizerRootSMulCommClass R d m c

/-- The fixed coefficient ring for the residual stabilizer action. -/
abbrev invariantCoefficientRing :=
  FixedPoints.subalgebra R (coefficientRing R d m c)
    (componentStabilizer d m c)

/-- The universal monic polynomial on one sheet, expressed over the actual
stabilizer fixed ring. -/
noncomputable def invariantSheetPolynomial (j : Fin m) :
    Polynomial.MonicDegreeEq (invariantCoefficientRing R d m c)
      (sheetMultiplicity d m c j) := by
  exact (sheetPolynomial R d m c j).map
    (componentStabilizerInvariantAlgEquiv R d m c).toRingHom

/-- The product of the universal sheetwise root algebras over the stabilizer
fixed ring. -/
noncomputable abbrev invariantProductRootAlgebra :=
  productRootAlgebra (invariantCoefficientRing R d m c) m
    (sheetMultiplicity d m c) (invariantSheetPolynomial R d m c)

omit [Nontrivial R] in
/-- The product universal-root algebra is flat over the stabilizer fixed
ring. -/
theorem invariantProductRootAlgebra_flat :
    Module.Flat (invariantCoefficientRing R d m c)
      (invariantProductRootAlgebra R d m c) := by
  infer_instance

/-- Including an invariant sheet polynomial into ordered-root coordinates
gives that sheet's product of ordered linear root factors. -/
theorem invariantSheetPolynomial_map_inclusion (j : Fin m) :
    (invariantSheetPolynomial R d m c j).1.map
        (algebraMap (invariantCoefficientRing R d m c)
          (coefficientRing R d m c)) =
      sheetOrderedRootPolynomial R d m c j := by
  rw [invariantSheetPolynomial, Polynomial.MonicDegreeEq.map_coe,
    Polynomial.map_map]
  change (sheetPolynomial R d m c j).1.map
      (componentMonicCoefficientToRoots R d m c).toRingHom = _
  exact sheetPolynomial_map_componentMonicCoefficientToRoots R d m c j

/-- The product of the sheetwise ordered-root incidence algebras. -/
noncomputable def orderedProductRootAlgebra :=
  ∀ j : Fin m, AdjoinRoot (sheetOrderedRootPolynomial R d m c j)

noncomputable instance orderedProductRootAlgebraCommRing :
    CommRing (orderedProductRootAlgebra R d m c) := by
  unfold orderedProductRootAlgebra
  infer_instance

noncomputable instance orderedProductRootAlgebraAlgebra :
    Algebra (coefficientRing R d m c)
      (orderedProductRootAlgebra R d m c) := by
  unfold orderedProductRootAlgebra
  infer_instance

/-- Sheetwise form of ordered-incidence base change. -/
noncomputable def sheetOrderedRootBaseChangeEquiv (j : Fin m) :
    coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
      AdjoinRoot (invariantSheetPolynomial R d m c j).1 ≃ₐ[coefficientRing R d m c]
      AdjoinRoot (sheetOrderedRootPolynomial R d m c j) := by
  rw [← invariantSheetPolynomial_map_inclusion R d m c j]
  exact AdjoinRootBaseChange.equiv
    (invariantCoefficientRing R d m c)
    (coefficientRing R d m c)
    (invariantSheetPolynomial R d m c j).1

/-- The multiblock ordered-incidence algebra is the scalar extension of the
product universal-root algebra from invariant coefficients to ordered-root
coordinates. -/
local instance : SMulCommClass (invariantCoefficientRing R d m c)
    (componentStabilizer d m c) (coefficientRing R d m c) :=
  SMulCommClass.symm _ _ _

local instance invariantBaseChangeCommRing :
    CommRing (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
      (∀ j : Fin m, AdjoinRoot (invariantSheetPolynomial R d m c j).1)) :=
  @Algebra.TensorProduct.instCommRing
    (invariantCoefficientRing R d m c)
    (coefficientRing R d m c)
    (∀ j : Fin m, AdjoinRoot (invariantSheetPolynomial R d m c j).1)
    inferInstance inferInstance inferInstance inferInstance inferInstance

local instance invariantBaseChangeAlgebra :
    Algebra (coefficientRing R d m c)
      (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
        (∀ j : Fin m, AdjoinRoot (invariantSheetPolynomial R d m c j).1)) :=
  @Algebra.TensorProduct.leftAlgebra
    (invariantCoefficientRing R d m c)
    (coefficientRing R d m c)
    (coefficientRing R d m c)
    (∀ j : Fin m, AdjoinRoot (invariantSheetPolynomial R d m c j).1)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance

noncomputable def orderedIncidenceBaseChangeEquiv :
    coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
        invariantProductRootAlgebra R d m c ≃ₐ[coefficientRing R d m c]
      orderedProductRootAlgebra R d m c := by
  classical
  change coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
      invariantProductRootAlgebra R d m c ≃ₐ[coefficientRing R d m c]
    (∀ j : Fin m, AdjoinRoot (sheetOrderedRootPolynomial R d m c j))
  exact (Algebra.TensorProduct.piRight
      (invariantCoefficientRing R d m c)
      (coefficientRing R d m c) (coefficientRing R d m c)
      (fun j ↦ AdjoinRoot (invariantSheetPolynomial R d m c j).1)).trans
    (AlgEquiv.piCongrRight fun j ↦
      sheetOrderedRootBaseChangeEquiv R d m c j)

local instance invariantBaseChangeAction :
    MulSemiringAction (componentStabilizer d m c)
      (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
        invariantProductRootAlgebra R d m c) :=
  MulSemiringAction.instTensorProduct

/-- Conjugate the scalar-extension action through the ordered-incidence
equivalence, as a homomorphism into algebra automorphisms. -/
noncomputable def orderedIncidenceAut :
    componentStabilizer d m c →*
      (orderedProductRootAlgebra R d m c ≃ₐ[invariantCoefficientRing R d m c]
        orderedProductRootAlgebra R d m c) := by
  let e := (orderedIncidenceBaseChangeEquiv R d m c).restrictScalars
    (invariantCoefficientRing R d m c)
  exact (AlgEquiv.autCongr e).toMonoidHom.comp
    (MulSemiringAction.toAlgAut (componentStabilizer d m c)
      (invariantCoefficientRing R d m c)
      (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
        invariantProductRootAlgebra R d m c))

/-- The residual stabilizer action on the ordered-incidence algebra,
transported from its flat base-change presentation. -/
@[instance_reducible]
noncomputable def orderedIncidenceAction :
    MulSemiringAction (componentStabilizer d m c)
      (orderedProductRootAlgebra R d m c) :=
  MulSemiringAction.compHom (orderedProductRootAlgebra R d m c)
    (orderedIncidenceAut R d m c)

/-- The transported action fixes the stabilizer invariant coefficient ring. -/
theorem orderedIncidenceSMulCommClass :
    letI := orderedIncidenceAction R d m c
    SMulCommClass (componentStabilizer d m c)
      (invariantCoefficientRing R d m c)
      (orderedProductRootAlgebra R d m c) := by
  letI := orderedIncidenceAction R d m c
  constructor
  intro g r x
  change orderedIncidenceAut R d m c g (r • x) =
    r • orderedIncidenceAut R d m c g x
  exact (orderedIncidenceAut R d m c g).toLinearEquiv.map_smul r x

/-- The base-change equivalence is equivariant for the tensor action and the
transported ordered-incidence action. -/
theorem orderedIncidenceBaseChangeEquiv_smul
    (g : componentStabilizer d m c)
    (x : coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
      invariantProductRootAlgebra R d m c) :
    letI := orderedIncidenceAction R d m c
    orderedIncidenceBaseChangeEquiv R d m c (g • x) =
      g • orderedIncidenceBaseChangeEquiv R d m c x := by
  letI := orderedIncidenceAction R d m c
  let e := orderedIncidenceBaseChangeEquiv R d m c
  change e (g • x) = e (g • e.symm (e x))
  rw [e.symm_apply_apply]

/-- Transporting fixed points through the multiblock base-change equivalence
identifies the tensor-model fixed ring with the ordered-incidence fixed ring. -/
noncomputable def baseChangeFixedPointsEquivOrderedIncidenceFixedPoints :
    letI := orderedIncidenceAction R d m c
    letI := orderedIncidenceSMulCommClass R d m c
    FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
          invariantProductRootAlgebra R d m c)
        (componentStabilizer d m c) ≃ₐ[invariantCoefficientRing R d m c]
      FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (orderedProductRootAlgebra R d m c)
        (componentStabilizer d m c) := by
  letI := orderedIncidenceAction R d m c
  letI := orderedIncidenceSMulCommClass R d m c
  letI : Algebra (invariantCoefficientRing R d m c)
      (FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
          invariantProductRootAlgebra R d m c)
        (componentStabilizer d m c)) :=
    SubalgebraClass.toAlgebra _
  letI : Algebra (invariantCoefficientRing R d m c)
      (FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (orderedProductRootAlgebra R d m c)
        (componentStabilizer d m c)) :=
    SubalgebraClass.toAlgebra _
  let e₀ := orderedIncidenceBaseChangeEquiv R d m c
  let e := e₀.restrictScalars
    (invariantCoefficientRing R d m c)
  exact
    { toFun := fun x ↦ ⟨e x.1, fun g ↦ by
          change g • e₀ x.1 = e₀ x.1
          rw [← orderedIncidenceBaseChangeEquiv_smul R d m c]
          exact congrArg e₀ (x.2 g)⟩
      invFun := fun x ↦ ⟨e.symm x.1, fun g ↦ by
          change g • e₀.symm x.1 = e₀.symm x.1
          apply e₀.injective
          rw [orderedIncidenceBaseChangeEquiv_smul]
          have he : orderedIncidenceBaseChangeEquiv R d m c
              (e₀.symm x.1) = x.1 := e₀.apply_symm_apply x.1
          rw [he]
          exact x.2 g⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.1)
      map_mul' := fun x y ↦ Subtype.ext (map_mul e x.1 y.1)
      map_add' := fun x y ↦ Subtype.ext (map_add e x.1 y.1)
      commutes' := fun r ↦ Subtype.ext (e.commutes r) }

/-- Flat invariant base change recovers the product universal-root algebra
as the invariants of its ordered-root scalar extension. -/
noncomputable def invariantRootEquivBaseChangeFixedPoints :
    letI : SMulCommClass R (componentStabilizer d m c)
        (coefficientRing R d m c) := SMulCommClass.symm _ _ _
    invariantProductRootAlgebra R d m c ≃ₐ[invariantCoefficientRing R d m c]
      FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
          invariantProductRootAlgebra R d m c)
        (componentStabilizer d m c) := by
  letI : SMulCommClass R (componentStabilizer d m c)
      (coefficientRing R d m c) := SMulCommClass.symm _ _ _
  letI : Module.Flat (invariantCoefficientRing R d m c)
      (invariantProductRootAlgebra R d m c) :=
    invariantProductRootAlgebra_flat R d m c
  letI : Algebra (invariantCoefficientRing R d m c)
      (FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (coefficientRing R d m c ⊗[invariantCoefficientRing R d m c]
          invariantProductRootAlgebra R d m c)
        (componentStabilizer d m c)) :=
    SubalgebraClass.toAlgebra _
  exact AlgEquiv.ofBijective
    (includeRightFixedPoints
      (G := componentStabilizer d m c) (R := R)
      (A := coefficientRing R d m c)
      (invariantProductRootAlgebra R d m c))
    (bijective_includeRightFixedPoints_of_flat
      (G := componentStabilizer d m c) (R := R)
      (A := coefficientRing R d m c)
      (invariantProductRootAlgebra R d m c))

/-- The quotient of the multiblock ordered-incidence algebra by the residual
stabilizer is the product of the universal monic root algebras. -/
noncomputable def invariantRootEquivOrderedIncidenceFixedPoints :
    letI : SMulCommClass R (componentStabilizer d m c)
        (coefficientRing R d m c) := SMulCommClass.symm _ _ _
    letI := orderedIncidenceAction R d m c
    letI := orderedIncidenceSMulCommClass R d m c
    invariantProductRootAlgebra R d m c ≃ₐ[invariantCoefficientRing R d m c]
      FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (orderedProductRootAlgebra R d m c)
        (componentStabilizer d m c) := by
  letI : SMulCommClass R (componentStabilizer d m c)
      (coefficientRing R d m c) := SMulCommClass.symm _ _ _
  letI := orderedIncidenceAction R d m c
  letI := orderedIncidenceSMulCommClass R d m c
  exact (invariantRootEquivBaseChangeFixedPoints R d m c).trans
    (baseChangeFixedPointsEquivOrderedIncidenceFixedPoints R d m c)

/-- The product universal-root projection over the actual stabilizer fixed
coefficient ring. -/
noncomputable abbrev invariantRootProjection :
    letI : SMulCommClass R (componentStabilizer d m c)
        (coefficientRing R d m c) := SMulCommClass.symm _ _ _
    Spec (.of (invariantProductRootAlgebra R d m c)) ⟶
      Spec (.of (invariantCoefficientRing R d m c)) :=
  SplitMonicRootFamily.projection (invariantCoefficientRing R d m c) m
    (sheetMultiplicity d m c) (invariantSheetPolynomial R d m c)

instance invariantRootProjection_isFinite :
    letI : SMulCommClass R (componentStabilizer d m c)
        (coefficientRing R d m c) := SMulCommClass.symm _ _ _
    IsFinite (invariantRootProjection R d m c) := by
  letI : SMulCommClass R (componentStabilizer d m c)
      (coefficientRing R d m c) := SMulCommClass.symm _ _ _
  dsimp only [invariantRootProjection]
  infer_instance

instance invariantRootProjection_flat :
    letI : SMulCommClass R (componentStabilizer d m c)
        (coefficientRing R d m c) := SMulCommClass.symm _ _ _
    Flat (invariantRootProjection R d m c) := by
  letI : SMulCommClass R (componentStabilizer d m c)
      (coefficientRing R d m c) := SMulCommClass.symm _ _ _
  dsimp only [invariantRootProjection]
  infer_instance

/-- The product universal-root projection over the stabilizer fixed ring has
constant rank equal to the symmetric-power degree. -/
theorem invariantRootProjection_finrank :
    letI : SMulCommClass R (componentStabilizer d m c)
        (coefficientRing R d m c) := SMulCommClass.symm _ _ _
    (invariantRootProjection R d m c).finrank = fun _ ↦ d := by
  letI : SMulCommClass R (componentStabilizer d m c)
      (coefficientRing R d m c) := SMulCommClass.symm _ _ _
  exact SplitMonicRootFamily.projection_finrank_of_sheetMultiplicity
    (invariantCoefficientRing R d m c) m d c
    (invariantSheetPolynomial R d m c)

/-- Affine scheme form of the multiblock invariant calculation: the quotient
of ordered incidence on a split component is the product universal-root
scheme over the stabilizer fixed coefficient ring. -/
noncomputable def orderedIncidenceInvariantSchemeIso :
    letI : SMulCommClass R (componentStabilizer d m c)
        (coefficientRing R d m c) := SMulCommClass.symm _ _ _
    letI := orderedIncidenceAction R d m c
    letI := orderedIncidenceSMulCommClass R d m c
    Spec (.of (FixedPoints.subalgebra (invariantCoefficientRing R d m c)
        (orderedProductRootAlgebra R d m c)
        (componentStabilizer d m c))) ≅
      Spec (.of (invariantProductRootAlgebra R d m c)) := by
  letI : SMulCommClass R (componentStabilizer d m c)
      (coefficientRing R d m c) := SMulCommClass.symm _ _ _
  letI := orderedIncidenceAction R d m c
  letI := orderedIncidenceSMulCommClass R d m c
  exact Scheme.Spec.mapIso
    ((invariantRootEquivOrderedIncidenceFixedPoints R d m c).toRingEquiv
      |>.toCommRingCatIso.op)

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentOrderedIncidence
