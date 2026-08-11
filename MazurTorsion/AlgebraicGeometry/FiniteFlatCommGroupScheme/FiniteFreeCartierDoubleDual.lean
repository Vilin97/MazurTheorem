/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteFreeCartierDual

/-!
# Biduality for finite-free Cartier duals

The evaluation map from finite-free Hopf coordinates to their linear double dual is compatible
with the algebra and coalgebra structures transposed by Cartier duality.  Consequently the
Cartier dual constructed in `FiniteFreeCartierDual` is involutive up to an actual affine Hopf
isomorphism.

This is a structural theorem about represented finite-free commutative group schemes.  It does
not assert the Oort--Tate dichotomy saying that an arbitrary prime-order model or its Cartier
dual is etale.
-/

noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.AffineFiniteFreeCommGroupScheme

universe u

variable {R : Type u} [CommRing R] (G : AffineFiniteFreeCommGroupScheme R)

local instance : Coalgebra R G.coordinates := Bialgebra.toCoalgebra
local instance : Module.Free R G.coordinates := G.property.1
local instance : Module.Finite R G.coordinates := G.property.2

/-- The exact coordinate type stored in the bundled Cartier dual. -/
abbrev BundledDualCoordinates :=
  (cartierDual G).coordinates

/-- The exact coordinate type stored in the bundled double Cartier dual. -/
abbrev DoubleDualCoordinates :=
  (cartierDual (cartierDual G)).coordinates

/-- Forget the universe-preserving convolution wrapper on the exact bundled dual
coordinates. -/
def bundledDualCoordinatesLinearEquiv :
    BundledDualCoordinates G ≃ₗ[R] Module.Dual R G.coordinates where
  toFun f := f.ofConv
  invFun f := WithConv.toConv f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem bundledDualCoordinatesLinearEquiv_apply
    (f : BundledDualCoordinates G) :
    bundledDualCoordinatesLinearEquiv G f = f.ofConv :=
  rfl

/-- Forget the convolution wrapper on the exact bundled double-dual coordinates. -/
def bundledDoubleDualCoordinatesLinearEquiv :
    DoubleDualCoordinates G ≃ₗ[R]
      Module.Dual R (BundledDualCoordinates G) where
  toFun f := f.ofConv
  invFun f := WithConv.toConv f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Tensor duality written entirely with the coordinate type stored in `cartierDual G`. -/
def bundledDualTensorLinearEquiv :
    BundledDualCoordinates G ⊗[R] BundledDualCoordinates G ≃ₗ[R]
      Module.Dual R (G.coordinates ⊗[R] G.coordinates) :=
  (TensorProduct.congr
      (bundledDualCoordinatesLinearEquiv G)
      (bundledDualCoordinatesLinearEquiv G)).trans
    (TensorProduct.dualDistribEquiv R G.coordinates G.coordinates)

@[simp]
theorem bundledDualTensorLinearEquiv_tmul_apply_tmul
    (f g : BundledDualCoordinates G) (a b : G.coordinates) :
    bundledDualTensorLinearEquiv G (f ⊗ₜ[R] g) (a ⊗ₜ[R] b) =
      f.ofConv a * g.ofConv b := by
  simp [bundledDualTensorLinearEquiv]

/-- The defining pairing for the comultiplication stored in the bundled Cartier dual. -/
theorem bundledDualComul_pairing
    (f : BundledDualCoordinates G) (a b : G.coordinates) :
    bundledDualTensorLinearEquiv G (Coalgebra.comul (R := R) f)
        (a ⊗ₜ[R] b) = f.ofConv (a * b) := by
  exact canonicalDualTensorMap_dualComul_apply_tmul G f a b

/-- Evaluation of a coordinate on an element of its linear Cartier dual. -/
def doubleDualEvaluationLinearMap (a : G.coordinates) :
    BundledDualCoordinates G →ₗ[R] R where
  toFun f := f.ofConv a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A coordinate, regarded as an element of the coordinate algebra of the double Cartier dual. -/
def doubleDualEvaluation (a : G.coordinates) :
    DoubleDualCoordinates G :=
  WithConv.toConv (doubleDualEvaluationLinearMap G a)

/-- Finite freeness identifies coordinates with the exact bundled linear double dual used by
two applications of `cartierDual`. -/
def doubleDualLinearEquiv :
    G.coordinates ≃ₗ[R] DoubleDualCoordinates G :=
  (Module.evalEquiv R G.coordinates).trans
    ((bundledDualCoordinatesLinearEquiv G).dualMap.trans
      (bundledDoubleDualCoordinatesLinearEquiv G).symm)

@[simp]
theorem doubleDualLinearEquiv_apply (a : G.coordinates) :
    doubleDualLinearEquiv G a = doubleDualEvaluation G a :=
  rfl

/-- Evaluation at the coordinate unit is the convolution unit in the double dual. -/
@[simp]
theorem doubleDualEvaluation_one :
    doubleDualEvaluation G (1 : G.coordinates) = 1 := by
  apply (bundledDoubleDualCoordinatesLinearEquiv G).injective
  apply LinearMap.ext
  intro f
  change f.ofConv 1 = Coalgebra.counit (R := R) f
  rfl

/-- Evaluation converts coordinate multiplication into double-dual convolution. -/
@[simp]
theorem doubleDualEvaluation_mul (a b : G.coordinates) :
    doubleDualEvaluation G (a * b) =
      doubleDualEvaluation G a * doubleDualEvaluation G b := by
  apply (bundledDoubleDualCoordinatesLinearEquiv G).injective
  apply LinearMap.ext
  intro f
  change f.ofConv (a * b) =
    LinearMap.mul' R R
      (TensorProduct.map
        (doubleDualEvaluationLinearMap G a)
        (doubleDualEvaluationLinearMap G b)
        (Coalgebra.comul (R := R) f))
  have heval (t : BundledDualCoordinates G ⊗[R]
      BundledDualCoordinates G) :
      LinearMap.mul' R R
          (TensorProduct.map
            (doubleDualEvaluationLinearMap G a)
            (doubleDualEvaluationLinearMap G b) t) =
        bundledDualTensorLinearEquiv G t (a ⊗ₜ[R] b) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul x y =>
        change x.ofConv a * y.ofConv b =
          bundledDualTensorLinearEquiv G (x ⊗ₜ[R] y) (a ⊗ₜ[R] b)
        rw [bundledDualTensorLinearEquiv_tmul_apply_tmul]
  rw [heval, bundledDualComul_pairing]

/-- Tensoring the evaluation equivalence evaluates each tensor factor independently. -/
theorem doubleDualTensorEvaluation
    (t : G.coordinates ⊗[R] G.coordinates)
    (f g : BundledDualCoordinates G) :
    bundledDualTensorLinearEquiv (cartierDual G)
        (TensorProduct.map
          (doubleDualLinearEquiv G).toLinearMap
          (doubleDualLinearEquiv G).toLinearMap t)
        (f ⊗ₜ[R] g) =
      LinearMap.mul' R R (TensorProduct.map f.ofConv g.ofConv t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a b =>
      simp only [TensorProduct.map_tmul,
        bundledDualTensorLinearEquiv_tmul_apply_tmul]
      rfl

/-- Evaluation preserves comultiplication, so finite-free biduality is a coalgebra map. -/
theorem doubleDualLinearEquiv_map_comul (a : G.coordinates) :
    TensorProduct.map
        (doubleDualLinearEquiv G).toLinearMap
        (doubleDualLinearEquiv G).toLinearMap
        (Coalgebra.comul (R := R) a) =
      Coalgebra.comul (R := R) (doubleDualEvaluation G a) := by
  apply (bundledDualTensorLinearEquiv (cartierDual G)).injective
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f g =>
      rw [doubleDualTensorEvaluation]
      rw [bundledDualComul_pairing]
      change LinearMap.mul' R R
          (TensorProduct.map f.ofConv g.ofConv
            (Coalgebra.comul (R := R) a)) = (f * g).ofConv a
      exact (LinearMap.convMul_apply f g a).symm

theorem doubleDualLinearEquiv_map_one :
    doubleDualLinearEquiv G (1 : G.coordinates) = 1 := by
  rw [doubleDualLinearEquiv_apply, doubleDualEvaluation_one]

theorem doubleDualLinearEquiv_map_mul (a b : G.coordinates) :
    doubleDualLinearEquiv G (a * b) =
      doubleDualLinearEquiv G a * doubleDualLinearEquiv G b := by
  simp only [doubleDualLinearEquiv_apply, doubleDualEvaluation_mul]

/-- Evaluation is an algebra equivalence from finite-free coordinates to their double Cartier
dual. -/
def doubleDualAlgEquiv :
    G.coordinates ≃ₐ[R] DoubleDualCoordinates G :=
  AlgEquiv.ofLinearEquiv (doubleDualLinearEquiv G)
    (by rw [doubleDualLinearEquiv_apply, doubleDualEvaluation_one])
    (by
      intro a b
      simp only [doubleDualLinearEquiv_apply, doubleDualEvaluation_mul])

@[simp]
theorem doubleDualAlgEquiv_apply (a : G.coordinates) :
    doubleDualAlgEquiv G a = doubleDualEvaluation G a :=
  rfl

/-- The double-dual counit agrees with the original counit under evaluation. -/
@[simp]
theorem dualCounit_doubleDualEvaluation (a : G.coordinates) :
    Coalgebra.counit (R := R) (doubleDualEvaluation G a) =
      Coalgebra.counit (R := R) a := by
  change (1 : BundledDualCoordinates G).ofConv a =
    Coalgebra.counit (R := R) a
  rfl

/-- Evaluation is a bialgebra equivalence from finite-free Hopf coordinates to their exact
bundled Cartier double dual. -/
def doubleDualBialgEquiv :
    G.coordinates ≃ₐc[R] DoubleDualCoordinates G := by
  let e := doubleDualAlgEquiv G
  let c : G.coordinates ≃ₗc[R] DoubleDualCoordinates G :=
    { e.toLinearEquiv with
      counit_comp := by
        apply LinearMap.ext
        intro a
        change Coalgebra.counit (R := R) (doubleDualEvaluation G a) =
          Coalgebra.counit (R := R) a
        exact dualCounit_doubleDualEvaluation G a
      map_comp_comul := by
        apply LinearMap.ext
        intro a
        change TensorProduct.map
            (doubleDualLinearEquiv G).toLinearMap
            (doubleDualLinearEquiv G).toLinearMap
            (Coalgebra.comul (R := R) a) =
          Coalgebra.comul (R := R) (doubleDualEvaluation G a)
        exact doubleDualLinearEquiv_map_comul G a }
  exact BialgEquiv.mk c e.map_mul

/-- Actual affine finite-free Cartier biduality. -/
def cartierDoubleDualIso :
    G ≅ cartierDual (cartierDual G) :=
  isoOfCoordinateBialgEquiv (doubleDualBialgEquiv G)

/-- Geometric Cartier biduality for the realized finite-flat commutative group scheme. -/
def cartierDoubleDualRealizeIso :
    G.realize ≅ (cartierDual (cartierDual G)).realize :=
  (realizationFunctor R).mapIso (cartierDoubleDualIso G)

end AlgebraicGeometry.AffineFiniteFreeCommGroupScheme
