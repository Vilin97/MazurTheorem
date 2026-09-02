/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Examples
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant
import MazurTorsion.Upstream.AINTLIB.ForMathlib.CartierDual

/-!
# Cartier dual coordinates for finite-free commutative group schemes

This file constructs the actual affine finite-free Cartier dual by transposing the Hopf
operations through the canonical tensor-duality equivalence.  It then identifies the dual of a
represented constant group with the represented diagonalizable group by an explicit Hopf
coordinate equivalence.  In particular, the order-five and order-eleven constant cyclic groups
have genuine geometric Cartier-dual isomorphisms with `μ₅` and `μ₁₁`; no classification
certificate is assumed.
-/

noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.AffineFiniteFreeCommGroupScheme

universe u

/-- The convolution algebra on the linear dual of finite-free Hopf coordinates. -/
abbrev DualCoordinates (R : Type u) (A : Type u) [CommRing R]
    [AddCommGroup A] [Module R A] [Coalgebra R A] :=
  ModularCurves.CartierDual R A

variable {R : Type u} [CommRing R] (G : AffineFiniteFreeCommGroupScheme R)

local instance : Coalgebra R G.coordinates := Bialgebra.toCoalgebra
local instance : Module.Free R G.coordinates := G.property.1
local instance : Module.Finite R G.coordinates := G.property.2

local instance : Module.Free R (DualCoordinates R G.coordinates) :=
  Module.Free.of_equiv
    (WithConv.linearEquiv R (Module.Dual R G.coordinates)).symm

local instance : Module.Finite R (DualCoordinates R G.coordinates) :=
  Module.Finite.equiv
    (WithConv.linearEquiv R (Module.Dual R G.coordinates)).symm

/-- Evaluation of a tensor of convolution functionals on a tensor of coordinates. -/
def canonicalDualTensorMap :
    DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates →ₗ[R]
      Module.Dual R (G.coordinates ⊗[R] G.coordinates) :=
  (TensorProduct.dualDistrib R G.coordinates G.coordinates).comp
    (TensorProduct.map
      (WithConv.linearEquiv R (Module.Dual R G.coordinates)).toLinearMap
      (WithConv.linearEquiv R (Module.Dual R G.coordinates)).toLinearMap)

/-- For finite-free coordinates, the canonical tensor-of-duals map is an equivalence. -/
def dualTensorLinearEquiv :
    DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates ≃ₗ[R]
      Module.Dual R (G.coordinates ⊗[R] G.coordinates) :=
  (TensorProduct.congr
      (WithConv.linearEquiv R (Module.Dual R G.coordinates))
      (WithConv.linearEquiv R (Module.Dual R G.coordinates))).trans
    (TensorProduct.dualDistribEquiv R G.coordinates G.coordinates)

/-- Evaluation of a right-associated triple tensor of convolution functionals. -/
def canonicalDualTripleMap :
    DualCoordinates R G.coordinates ⊗[R]
        (DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates) →ₗ[R]
      Module.Dual R
        (G.coordinates ⊗[R] (G.coordinates ⊗[R] G.coordinates)) :=
  (TensorProduct.dualDistrib R G.coordinates
      (G.coordinates ⊗[R] G.coordinates)).comp
    (TensorProduct.map
      (WithConv.linearEquiv R (Module.Dual R G.coordinates)).toLinearMap
      (canonicalDualTensorMap G))

/-- For finite-free coordinates, canonical triple evaluation is an equivalence. -/
def dualTripleLinearEquiv :
    DualCoordinates R G.coordinates ⊗[R]
        (DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates) ≃ₗ[R]
      Module.Dual R
        (G.coordinates ⊗[R] (G.coordinates ⊗[R] G.coordinates)) :=
  (TensorProduct.congr
      (WithConv.linearEquiv R (Module.Dual R G.coordinates))
      (dualTensorLinearEquiv G)).trans
    (TensorProduct.dualDistribEquiv R G.coordinates
      (G.coordinates ⊗[R] G.coordinates))

@[simp]
theorem canonicalDualTensorMap_tmul_apply_tmul
    (f g : DualCoordinates R G.coordinates) (a b : G.coordinates) :
    canonicalDualTensorMap G (f ⊗ₜ[R] g) (a ⊗ₜ[R] b) =
      f.ofConv a * g.ofConv b := by
  simp [canonicalDualTensorMap]

@[simp]
theorem canonicalDualTripleMap_tmul_tmul_apply_tmul_tmul
    (f g h : DualCoordinates R G.coordinates) (a b c : G.coordinates) :
    canonicalDualTripleMap G (f ⊗ₜ[R] (g ⊗ₜ[R] h))
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      f.ofConv a * (g.ofConv b * h.ofConv c) := by
  simp [canonicalDualTripleMap, canonicalDualTensorMap]

/-- Triple evaluation after reassociating a tensor in the first two dual factors. -/
theorem canonicalDualTripleMap_assoc_tmul_apply_tmul_tmul
    (x : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (h : DualCoordinates R G.coordinates) (a b c : G.coordinates) :
    canonicalDualTripleMap G
        (TensorProduct.assoc R
          (DualCoordinates R G.coordinates)
          (DualCoordinates R G.coordinates)
          (DualCoordinates R G.coordinates) (x ⊗ₜ[R] h))
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      canonicalDualTensorMap G x (a ⊗ₜ[R] b) * h.ofConv c := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [TensorProduct.zero_tmul]
      rw [map_zero, map_zero, zero_mul]
  | add x y hx hy =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hx, hy, add_mul]
  | tmul f g =>
      simp only [TensorProduct.assoc_tmul,
        canonicalDualTripleMap_tmul_tmul_apply_tmul_tmul,
        canonicalDualTensorMap_tmul_apply_tmul]
      rw [mul_assoc]

/-- Triple evaluation with an arbitrary tensor in the last two dual factors. -/
theorem canonicalDualTripleMap_tmul_apply_tmul_tmul
    (f : DualCoordinates R G.coordinates)
    (x : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (a b c : G.coordinates) :
    canonicalDualTripleMap G (f ⊗ₜ[R] x)
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      f.ofConv a * canonicalDualTensorMap G x (b ⊗ₜ[R] c) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [TensorProduct.tmul_zero]
      rw [map_zero, map_zero, mul_zero]
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hx, hy, mul_add]
  | tmul g h =>
      simp only [canonicalDualTripleMap_tmul_tmul_apply_tmul_tmul,
        canonicalDualTensorMap_tmul_apply_tmul]

/-- Transpose multiplication through the canonical tensor-duality equivalence. -/
def dualComul :
    DualCoordinates R G.coordinates →ₗ[R]
      DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates :=
  (dualTensorLinearEquiv G).symm.toLinearMap.comp
    ((LinearMap.mul' R G.coordinates).dualMap.comp
      (WithConv.linearEquiv R (Module.Dual R G.coordinates)).toLinearMap)

/-- Evaluation at the unit is the counit dual to multiplication. -/
def dualCounit : DualCoordinates R G.coordinates →ₗ[R] R where
  toFun f := f.ofConv 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The defining pairing formula for the transposed multiplication. -/
@[simp]
theorem canonicalDualTensorMap_dualComul_apply_tmul
    (f : DualCoordinates R G.coordinates) (a b : G.coordinates) :
    canonicalDualTensorMap G (dualComul G f) (a ⊗ₜ[R] b) = f.ofConv (a * b) := by
  have h := (dualTensorLinearEquiv G).apply_symm_apply
    ((LinearMap.mul' R G.coordinates).dualMap
      ((WithConv.linearEquiv R (Module.Dual R G.coordinates)) f))
  exact DFunLike.congr_fun h (a ⊗ₜ[R] b)

/-- The dual counit is literal evaluation at the coordinate unit. -/
@[simp]
theorem dualCounit_apply (f : DualCoordinates R G.coordinates) :
    dualCounit G f = f.ofConv 1 :=
  rfl

/-- Applying transposed multiplication in the first tensor factor evaluates multiplication in
the first two coordinate factors. -/
theorem canonicalDualTripleMap_assoc_rTensor_dualComul
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (a b c : G.coordinates) :
    canonicalDualTripleMap G
        (TensorProduct.assoc R
          (DualCoordinates R G.coordinates)
          (DualCoordinates R G.coordinates)
          (DualCoordinates R G.coordinates)
          ((dualComul G).rTensor (DualCoordinates R G.coordinates) t))
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      canonicalDualTensorMap G t ((a * b) ⊗ₜ[R] c) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul f g =>
      rw [LinearMap.rTensor_tmul,
        canonicalDualTripleMap_assoc_tmul_apply_tmul_tmul,
        canonicalDualTensorMap_dualComul_apply_tmul,
        canonicalDualTensorMap_tmul_apply_tmul]

/-- Applying transposed multiplication in the second tensor factor evaluates multiplication in
the last two coordinate factors. -/
theorem canonicalDualTripleMap_lTensor_dualComul
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (a b c : G.coordinates) :
    canonicalDualTripleMap G
        ((dualComul G).lTensor (DualCoordinates R G.coordinates) t)
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      canonicalDualTensorMap G t (a ⊗ₜ[R] (b * c)) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      change (0 : R) = 0
      rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul f g =>
      rw [LinearMap.lTensor_tmul,
        canonicalDualTripleMap_tmul_apply_tmul_tmul,
        canonicalDualTensorMap_dualComul_apply_tmul,
        canonicalDualTensorMap_tmul_apply_tmul]

/-- Coassociativity of transposed coordinate multiplication. -/
theorem dualComul_coassoc :
    (TensorProduct.assoc R
      (DualCoordinates R G.coordinates)
      (DualCoordinates R G.coordinates)
      (DualCoordinates R G.coordinates)).toLinearMap ∘ₗ
        (dualComul G).rTensor (DualCoordinates R G.coordinates) ∘ₗ dualComul G =
      (dualComul G).lTensor (DualCoordinates R G.coordinates) ∘ₗ dualComul G := by
  apply LinearMap.ext
  intro f
  apply (dualTripleLinearEquiv G).injective
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a t =>
      induction t using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hx, hy]
      | tmul b c =>
          change canonicalDualTripleMap G
              (TensorProduct.assoc R
                (DualCoordinates R G.coordinates)
                (DualCoordinates R G.coordinates)
                (DualCoordinates R G.coordinates)
                ((dualComul G).rTensor (DualCoordinates R G.coordinates)
                  (dualComul G f)))
              (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
            canonicalDualTripleMap G
              ((dualComul G).lTensor (DualCoordinates R G.coordinates)
                (dualComul G f))
              (a ⊗ₜ[R] (b ⊗ₜ[R] c))
          rw [canonicalDualTripleMap_assoc_rTensor_dualComul,
            canonicalDualTripleMap_lTensor_dualComul,
            canonicalDualTensorMap_dualComul_apply_tmul,
            canonicalDualTensorMap_dualComul_apply_tmul,
            mul_assoc]

/-- Pairing the first dual tensor factor against the coordinate unit. -/
theorem lid_rTensor_dualCounit_apply
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (a : G.coordinates) :
    ((TensorProduct.lid R (DualCoordinates R G.coordinates))
      ((dualCounit G).rTensor (DualCoordinates R G.coordinates) t)).ofConv a =
      canonicalDualTensorMap G t (1 ⊗ₜ[R] a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, WithConv.ofConv_zero, LinearMap.zero_apply]
  | add x y hx hy =>
      simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply, hx, hy]
  | tmul f g =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        canonicalDualTensorMap_tmul_apply_tmul]
      simp only [WithConv.ofConv_smul, LinearMap.smul_apply, dualCounit_apply, smul_eq_mul]

/-- Pairing the second dual tensor factor against the coordinate unit. -/
theorem rid_lTensor_dualCounit_apply
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (a : G.coordinates) :
    ((TensorProduct.rid R (DualCoordinates R G.coordinates))
      ((dualCounit G).lTensor (DualCoordinates R G.coordinates) t)).ofConv a =
      canonicalDualTensorMap G t (a ⊗ₜ[R] 1) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, WithConv.ofConv_zero, LinearMap.zero_apply]
  | add x y hx hy =>
      simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply, hx, hy]
  | tmul f g =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        canonicalDualTensorMap_tmul_apply_tmul]
      simp only [WithConv.ofConv_smul, LinearMap.smul_apply, dualCounit_apply, smul_eq_mul]
      rw [mul_comm]

/-- Left counitality of transposed multiplication. -/
theorem dualCounit_rTensor_comp_dualComul :
    (dualCounit G).rTensor (DualCoordinates R G.coordinates) ∘ₗ dualComul G =
      TensorProduct.mk R _ _ 1 := by
  apply LinearMap.ext
  intro f
  apply (TensorProduct.lid R (DualCoordinates R G.coordinates)).injective
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, lid_rTensor_dualCounit_apply,
    canonicalDualTensorMap_dualComul_apply_tmul, one_mul]
  simp

/-- Right counitality of transposed multiplication. -/
theorem dualCounit_lTensor_comp_dualComul :
    (dualCounit G).lTensor (DualCoordinates R G.coordinates) ∘ₗ dualComul G =
      (TensorProduct.mk R _ _).flip 1 := by
  apply LinearMap.ext
  intro f
  apply (TensorProduct.rid R (DualCoordinates R G.coordinates)).injective
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, rid_lTensor_dualCounit_apply,
    canonicalDualTensorMap_dualComul_apply_tmul, mul_one]
  simp

/-- The finite-free linear dual, with comultiplication transposed from coordinate
multiplication, is a coalgebra. -/
noncomputable instance instCoalgebraDualCoordinates :
    Coalgebra R (DualCoordinates R G.coordinates) where
  comul := dualComul G
  counit := dualCounit G
  coassoc := dualComul_coassoc G
  rTensor_counit_comp_comul := dualCounit_rTensor_comp_dualComul G
  lTensor_counit_comp_comul := dualCounit_lTensor_comp_dualComul G

/-- Canonical pairing turns multiplication of dual tensors into the crossed convolution sum on
the two coordinate comultiplications. -/
theorem canonicalDualTensorMap_mul_apply_tmul
    {I J : Type*} {a b : G.coordinates}
    (ra : Coalgebra.Repr R a I) (rb : Coalgebra.Repr R b J)
    (x y : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates) :
    canonicalDualTensorMap G (x * y) (a ⊗ₜ[R] b) =
      ∑ i ∈ ra.index, ∑ j ∈ rb.index,
        canonicalDualTensorMap G x (ra.left i ⊗ₜ[R] rb.left j) *
          canonicalDualTensorMap G y (ra.right i ⊗ₜ[R] rb.right j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp [add_mul, hx, hz, Finset.sum_add_distrib]
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp [mul_add, hy, hz, Finset.sum_add_distrib]
      | tmul h k =>
          rw [Algebra.TensorProduct.tmul_mul_tmul,
            canonicalDualTensorMap_tmul_apply_tmul,
            ra.convMul_apply, rb.convMul_apply, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [canonicalDualTensorMap_tmul_apply_tmul,
            canonicalDualTensorMap_tmul_apply_tmul]
          ring

/-- The dual counit preserves the convolution unit. -/
theorem dualCounit_one :
    dualCounit G (1 : DualCoordinates R G.coordinates) = 1 := by
  change Coalgebra.counit (R := R) (1 : G.coordinates) = 1
  exact Bialgebra.counit_one

/-- The dual counit preserves convolution multiplication. -/
theorem dualCounit_mul (f g : DualCoordinates R G.coordinates) :
    dualCounit G (f * g) = dualCounit G f * dualCounit G g := by
  change (f * g).ofConv (1 : G.coordinates) = f.ofConv 1 * g.ofConv 1
  rw [LinearMap.convMul_apply, Bialgebra.comul_one]
  simp [Algebra.TensorProduct.one_def]

/-- Transposed multiplication sends the convolution unit to the tensor-product unit. -/
theorem dualComul_one :
    dualComul G (1 : DualCoordinates R G.coordinates) = 1 := by
  apply (dualTensorLinearEquiv G).injective
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a b =>
      change canonicalDualTensorMap G (dualComul G 1) (a ⊗ₜ[R] b) =
        canonicalDualTensorMap G 1 (a ⊗ₜ[R] b)
      rw [canonicalDualTensorMap_dualComul_apply_tmul]
      simp [Algebra.TensorProduct.one_def]

/-- Transposed multiplication preserves convolution multiplication. -/
theorem dualComul_mul (f g : DualCoordinates R G.coordinates) :
    dualComul G (f * g) = dualComul G f * dualComul G g := by
  apply (dualTensorLinearEquiv G).injective
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a b =>
      let ra := Coalgebra.Repr.arbitrary R a
      let rb := Coalgebra.Repr.arbitrary R b
      change canonicalDualTensorMap G (dualComul G (f * g)) (a ⊗ₜ[R] b) =
        canonicalDualTensorMap G (dualComul G f * dualComul G g) (a ⊗ₜ[R] b)
      rw [canonicalDualTensorMap_dualComul_apply_tmul,
        (ra.mul rb).convMul_apply,
        canonicalDualTensorMap_mul_apply_tmul G ra rb]
      simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
        Coalgebra.Repr.mul_right, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [canonicalDualTensorMap_dualComul_apply_tmul,
        canonicalDualTensorMap_dualComul_apply_tmul]

/-- The convolution algebra on finite-free dual coordinates, with multiplication transposed to
comultiplication, is a bialgebra. -/
noncomputable instance instBialgebraDualCoordinates :
    Bialgebra R (DualCoordinates R G.coordinates) :=
  Bialgebra.mk' R (DualCoordinates R G.coordinates)
    (C := instCoalgebraDualCoordinates G)
    (by
      change dualCounit G (1 : DualCoordinates R G.coordinates) = 1
      exact dualCounit_one G)
    (fun {f g} ↦ by
      change dualCounit G (f * g) = dualCounit G f * dualCounit G g
      exact dualCounit_mul G f g)
    (by
      change dualComul G (1 : DualCoordinates R G.coordinates) = 1
      exact dualComul_one G)
    (fun {f g} ↦ by
      change dualComul G (f * g) = dualComul G f * dualComul G g
      exact dualComul_mul G f g)

/-- Swapping dual tensor factors swaps the two coordinate arguments of the canonical pairing. -/
theorem canonicalDualTensorMap_comm_apply_tmul
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (a b : G.coordinates) :
    canonicalDualTensorMap G
        (TensorProduct.comm R _ _ t) (a ⊗ₜ[R] b) =
      canonicalDualTensorMap G t (b ⊗ₜ[R] a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f g =>
      simp [mul_comm]

/-- Commutativity of the original coordinate multiplication makes the dual coalgebra
cocommutative. -/
noncomputable instance instIsCocommDualCoordinates :
    Coalgebra.IsCocomm R (DualCoordinates R G.coordinates) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (dualTensorLinearEquiv G).injective
    apply TensorProduct.ext'
    intro a b
    change canonicalDualTensorMap G
        (TensorProduct.comm R _ _ (dualComul G f)) (a ⊗ₜ[R] b) =
      canonicalDualTensorMap G (dualComul G f) (a ⊗ₜ[R] b)
    rw [canonicalDualTensorMap_comm_apply_tmul,
      canonicalDualTensorMap_dualComul_apply_tmul,
      canonicalDualTensorMap_dualComul_apply_tmul, mul_comm]

/-- Transpose the original Hopf antipode to the finite-free dual coordinates. -/
def dualAntipode :
    DualCoordinates R G.coordinates →ₗ[R] DualCoordinates R G.coordinates :=
  (WithConv.linearEquiv R (Module.Dual R G.coordinates)).symm.toLinearMap.comp
    ((HopfAlgebra.antipode R).dualMap.comp
      (WithConv.linearEquiv R (Module.Dual R G.coordinates)).toLinearMap)

@[simp]
theorem dualAntipode_apply (f : DualCoordinates R G.coordinates) (a : G.coordinates) :
    (dualAntipode G f).ofConv a = f.ofConv (HopfAlgebra.antipode R a) :=
  rfl

/-- Evaluating convolution after applying the dual antipode in the first tensor factor. -/
theorem dualMul_rTensor_dualAntipode_apply
    {I : Type*} {a : G.coordinates} (ra : Coalgebra.Repr R a I)
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates) :
    (LinearMap.mul' R (DualCoordinates R G.coordinates)
        ((dualAntipode G).rTensor (DualCoordinates R G.coordinates) t)).ofConv a =
      ∑ i ∈ ra.index,
        canonicalDualTensorMap G t
          (HopfAlgebra.antipode R (ra.left i) ⊗ₜ[R] ra.right i) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, Finset.sum_add_distrib]
  | tmul f g =>
      rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply, ra.convMul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp

/-- Evaluating convolution after applying the dual antipode in the second tensor factor. -/
theorem dualMul_lTensor_dualAntipode_apply
    {I : Type*} {a : G.coordinates} (ra : Coalgebra.Repr R a I)
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates) :
    (LinearMap.mul' R (DualCoordinates R G.coordinates)
        ((dualAntipode G).lTensor (DualCoordinates R G.coordinates) t)).ofConv a =
      ∑ i ∈ ra.index,
        canonicalDualTensorMap G t
          (ra.left i ⊗ₜ[R] HopfAlgebra.antipode R (ra.right i)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, Finset.sum_add_distrib]
  | tmul f g =>
      rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply, ra.convMul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp

noncomputable instance instHopfAlgebraStructDualCoordinates :
    HopfAlgebraStruct R (DualCoordinates R G.coordinates) where
  toBialgebra := instBialgebraDualCoordinates G
  antipode := dualAntipode G

/-- The transposed antipode is a left convolution inverse for the identity on dual
coordinates. -/
theorem dual_mul_antipode_rTensor_comul :
    LinearMap.mul' R (DualCoordinates R G.coordinates) ∘ₗ
        (dualAntipode G).rTensor (DualCoordinates R G.coordinates) ∘ₗ dualComul G =
      Algebra.linearMap R (DualCoordinates R G.coordinates) ∘ₗ dualCounit G := by
  apply LinearMap.ext
  intro f
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro a
  let ra := Coalgebra.Repr.arbitrary R a
  change (LinearMap.mul' R (DualCoordinates R G.coordinates)
      ((dualAntipode G).rTensor (DualCoordinates R G.coordinates)
        (dualComul G f))).ofConv a =
    (Algebra.linearMap R (DualCoordinates R G.coordinates) (dualCounit G f)).ofConv a
  rw [dualMul_rTensor_dualAntipode_apply G ra]
  simp_rw [canonicalDualTensorMap_dualComul_apply_tmul]
  rw [← map_sum, HopfAlgebra.sum_antipode_mul_eq_smul ra]
  change f.ofConv (Coalgebra.counit (R := R) a • (1 : G.coordinates)) =
    (algebraMap R (DualCoordinates R G.coordinates) (f.ofConv 1)).ofConv a
  rw [map_smul, LinearMap.convAlgebraMap_apply]
  simp [Algebra.smul_def, mul_comm]

/-- The transposed antipode is a right convolution inverse for the identity on dual
coordinates. -/
theorem dual_mul_antipode_lTensor_comul :
    LinearMap.mul' R (DualCoordinates R G.coordinates) ∘ₗ
        (dualAntipode G).lTensor (DualCoordinates R G.coordinates) ∘ₗ dualComul G =
      Algebra.linearMap R (DualCoordinates R G.coordinates) ∘ₗ dualCounit G := by
  apply LinearMap.ext
  intro f
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro a
  let ra := Coalgebra.Repr.arbitrary R a
  change (LinearMap.mul' R (DualCoordinates R G.coordinates)
      ((dualAntipode G).lTensor (DualCoordinates R G.coordinates)
        (dualComul G f))).ofConv a =
    (Algebra.linearMap R (DualCoordinates R G.coordinates) (dualCounit G f)).ofConv a
  rw [dualMul_lTensor_dualAntipode_apply G ra]
  simp_rw [canonicalDualTensorMap_dualComul_apply_tmul]
  rw [← map_sum, HopfAlgebra.sum_mul_antipode_eq_smul ra]
  change f.ofConv (Coalgebra.counit (R := R) a • (1 : G.coordinates)) =
    (algebraMap R (DualCoordinates R G.coordinates) (f.ofConv 1)).ofConv a
  rw [map_smul, LinearMap.convAlgebraMap_apply]
  simp [Algebra.smul_def, mul_comm]

/-- Finite-free commutative Hopf coordinates admit an actual Cartier-dual Hopf algebra. -/
noncomputable instance instHopfAlgebraDualCoordinates :
    HopfAlgebra R (DualCoordinates R G.coordinates) where
  toHopfAlgebraStruct := instHopfAlgebraStructDualCoordinates G
  mul_antipode_rTensor_comul := dual_mul_antipode_rTensor_comul G
  mul_antipode_lTensor_comul := dual_mul_antipode_lTensor_comul G

/-- The actual affine finite-free Cartier dual obtained by transposing all Hopf operations on
coordinates. -/
noncomputable def cartierDual : AffineFiniteFreeCommGroupScheme R where
  obj := Opposite.op
    ⟨CommHopfAlgCat.of R (DualCoordinates R G.coordinates),
      instIsCocommDualCoordinates G⟩
  property := by
    change Module.Free R (DualCoordinates R G.coordinates) ∧
      Module.Finite R (DualCoordinates R G.coordinates)
    exact ⟨inferInstance, inferInstance⟩

section Constant

open FiniteFlatCommGroupScheme

variable (R : Type u) [CommRing R]
variable (M : Type u) [CommGroup M] [Fintype M]

/-- Evaluation at the group element `m`, regarded as an element of the linear Cartier dual of
the constant Hopf algebra. -/
def dualConstantEvaluation (m : M) :
    DualCoordinates R (ConstantCoordinates R M) :=
  WithConv.toConv (ConstantCoordinates.evaluation (R := R) m).toLinearMap

/-- The evaluations at group elements form the dual basis to the delta-function basis of the
constant coordinate ring. -/
def dualConstantBasis :
    Module.Basis M R (DualCoordinates R (ConstantCoordinates R M)) := by
  classical
  exact (ConstantCoordinates.basis R M).dualBasis.map
    (WithConv.linearEquiv R (Module.Dual R (ConstantCoordinates R M))).symm

@[simp]
theorem dualConstantBasis_apply (m : M) :
    dualConstantBasis R M m = dualConstantEvaluation R M m := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro f
  simp [dualConstantBasis, dualConstantEvaluation, ConstantCoordinates.basis,
    Module.Basis.dualBasis_apply, Pi.basisFun_repr]

/-- Convolution of evaluation functionals remembers the multiplication in the indexing
group. -/
@[simp]
theorem dualConstantEvaluation_mul (m n : M) :
    dualConstantEvaluation R M m * dualConstantEvaluation R M n =
      dualConstantEvaluation R M (m * n) := by
  have h := ConstantCoordinates.evaluation_convMul (R := R) (G := M) m n
  have h' := congrArg
    (fun q : WithConv (ConstantCoordinates R M →ₐ[R] R) ↦
      WithConv.toConv q.ofConv.toLinearMap) h
  simpa [dualConstantEvaluation] using h'

/-- Evaluation at the identity is the convolution unit. -/
@[simp]
theorem dualConstantEvaluation_one :
    dualConstantEvaluation R M (1 : M) = 1 := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro f
  change f.down 1 = Coalgebra.counit (R := R) f
  rfl

/-- The dual evaluation basis is linearly identified with the standard group-algebra basis. -/
def dualConstantLinearEquiv :
    DualCoordinates R (ConstantCoordinates R M) ≃ₗ[R] MonoidAlgebra R M :=
  (dualConstantBasis R M).equiv (MonoidAlgebra.basis M R) (Equiv.refl M)

@[simp]
theorem dualConstantLinearEquiv_evaluation (m : M) :
    dualConstantLinearEquiv R M (dualConstantEvaluation R M m) =
      MonoidAlgebra.single m 1 := by
  rw [← dualConstantBasis_apply]
  simpa [dualConstantLinearEquiv, MonoidAlgebra.basis_apply] using
    Module.Basis.equiv_apply (dualConstantBasis R M) m
      (MonoidAlgebra.basis M R) (Equiv.refl M)

theorem dualConstantLinearEquiv_map_one :
    dualConstantLinearEquiv R M 1 = 1 := by
  rw [← dualConstantEvaluation_one (R := R) (M := M),
    dualConstantLinearEquiv_evaluation]
  rfl

theorem dualConstantLinearEquiv_map_mul
    (x y : DualCoordinates R (ConstantCoordinates R M)) :
    dualConstantLinearEquiv R M (x * y) =
      dualConstantLinearEquiv R M x * dualConstantLinearEquiv R M y := by
  classical
  rw [← (dualConstantBasis R M).sum_repr x,
    ← (dualConstantBasis R M).sum_repr y]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm]
  simp [dualConstantBasis_apply, MonoidAlgebra.single_mul_single, smul_smul]

/-- The algebra equivalence from the convolution dual of constant coordinates to the group
algebra. -/
def dualConstantAlgEquiv :
    DualCoordinates R (ConstantCoordinates R M) ≃ₐ[R] MonoidAlgebra R M :=
  AlgEquiv.ofLinearEquiv (dualConstantLinearEquiv R M)
    (dualConstantLinearEquiv_map_one R M)
    (dualConstantLinearEquiv_map_mul R M)

@[simp]
theorem dualConstantAlgEquiv_evaluation (m : M) :
    dualConstantAlgEquiv R M (dualConstantEvaluation R M m) =
      MonoidAlgebra.single m 1 :=
  dualConstantLinearEquiv_evaluation R M m

/-- Transposed multiplication makes every evaluation functional group-like. -/
@[simp]
theorem dualComul_dualConstantEvaluation (m : M) :
    dualComul (FiniteFlatCommGroupScheme.constant R M)
        (dualConstantEvaluation R M m) =
      dualConstantEvaluation R M m ⊗ₜ[R] dualConstantEvaluation R M m := by
  apply (dualTensorLinearEquiv (FiniteFlatCommGroupScheme.constant R M)).injective
  apply TensorProduct.ext'
  intro a b
  change canonicalDualTensorMap (FiniteFlatCommGroupScheme.constant R M)
      (dualComul (FiniteFlatCommGroupScheme.constant R M)
        (dualConstantEvaluation R M m)) (a ⊗ₜ[R] b) =
    canonicalDualTensorMap (FiniteFlatCommGroupScheme.constant R M)
      (dualConstantEvaluation R M m ⊗ₜ[R] dualConstantEvaluation R M m)
        (a ⊗ₜ[R] b)
  rw [canonicalDualTensorMap_dualComul_apply_tmul,
    canonicalDualTensorMap_tmul_apply_tmul]
  rfl

/-- The transposed counit takes every evaluation functional to one. -/
@[simp]
theorem dualCounit_dualConstantEvaluation (m : M) :
    dualCounit (FiniteFlatCommGroupScheme.constant R M)
      (dualConstantEvaluation R M m) = 1 := by
  rfl

/-- Cartier duality exchanges the represented constant Hopf algebra with the represented
diagonalizable Hopf algebra on the same finite commutative group. -/
def dualConstantBialgEquiv :
    DualCoordinates R (ConstantCoordinates R M) ≃ₐc[R] MonoidAlgebra R M := by
  letI hCoalgebra : Coalgebra R (DualCoordinates R (ConstantCoordinates R M)) :=
    instCoalgebraDualCoordinates (FiniteFlatCommGroupScheme.constant R M)
  letI hBialgebra : Bialgebra R (DualCoordinates R (ConstantCoordinates R M)) :=
    instBialgebraDualCoordinates (FiniteFlatCommGroupScheme.constant R M)
  letI hCocomm : Coalgebra.IsCocomm R
      (DualCoordinates R (ConstantCoordinates R M)) :=
    instIsCocommDualCoordinates (FiniteFlatCommGroupScheme.constant R M)
  let e := dualConstantAlgEquiv R M
  let b := dualConstantBasis R M
  let c : DualCoordinates R (ConstantCoordinates R M) ≃ₗc[R] MonoidAlgebra R M :=
    { e.toLinearEquiv with
      counit_comp := by
        apply b.ext
        intro m
        simp [b, dualConstantBasis_apply, e]
      map_comp_comul := by
        apply b.ext
        intro m
        simp only [LinearMap.comp_apply, b, dualConstantBasis_apply]
        rw [dualComul_dualConstantEvaluation]
        simp [e, MonoidAlgebra.comul_single] }
  exact BialgEquiv.mk c e.map_mul

/-- The affine finite-free Cartier dual of a constant group is the corresponding represented
diagonalizable group. -/
def cartierDualConstantIsoDiagonalizable :
    cartierDual (FiniteFlatCommGroupScheme.constant R M) ≅
      FiniteFlatCommGroupScheme.diagonalizable R M :=
  isoOfCoordinateBialgEquiv (dualConstantBialgEquiv R M)

/-- The same genuine Cartier-duality comparison after passing to finite-flat geometric group
schemes. -/
def cartierDualConstantRealizeIsoDiagonalizableScheme :
    (cartierDual (FiniteFlatCommGroupScheme.constant R M)).realize ≅
      FiniteFlatCommGroupScheme.diagonalizableScheme R M :=
  (realizationFunctor R).mapIso (cartierDualConstantIsoDiagonalizable R M)

end Constant

section CyclicConsumers

open FiniteFlatCommGroupScheme

/-- Cartier duality exchanges the represented constant cyclic group with `μₙ`. -/
def cartierDualConstantCyclicRealizeIsoMuScheme
    (R : Type) [CommRing R] (n : ℕ) [NeZero n] :
    (cartierDual (constant R (Multiplicative (ZMod n)))).realize ≅ muScheme R n :=
  cartierDualConstantRealizeIsoDiagonalizableScheme R (Multiplicative (ZMod n))

/-- Five-adic named consumer: the Cartier dual of the represented constant order-five group is
the represented multiplicative order-five group. -/
def cartierDualConstantFiveRealizeIsoMu :
    (cartierDual (constant ℤ (Multiplicative (ZMod 5)))).realize ≅ muScheme ℤ 5 :=
  cartierDualConstantCyclicRealizeIsoMuScheme ℤ 5

/-- Eleven-adic named consumer: the Cartier dual of the represented constant order-eleven
group is the represented multiplicative order-eleven group. -/
def cartierDualConstantElevenRealizeIsoMu :
    (cartierDual (constant ℤ (Multiplicative (ZMod 11)))).realize ≅ muScheme ℤ 11 :=
  cartierDualConstantCyclicRealizeIsoMuScheme ℤ 11

end CyclicConsumers

end AlgebraicGeometry.AffineFiniteFreeCommGroupScheme
