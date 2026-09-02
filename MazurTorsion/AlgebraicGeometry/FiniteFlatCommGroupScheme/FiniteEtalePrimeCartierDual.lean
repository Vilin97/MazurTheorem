/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AffineRealizationFullness
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtalePrimeGroupSchemeConstant
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteFreeCartierDual

/-!
# Cartier duals of finite-etale prime-order integer group schemes

Cartier duality is contravariantly functorial on finite-free affine Hopf presentations: a
bialgebra equivalence of coordinate rings is transposed to a bialgebra equivalence of their
linear duals.  Combining this explicit transport with full faithfulness of affine realization
and the integral finite-etale prime-order classification identifies the actual Cartier dual of
an affine finite-etale order-`p` model over `Spec ℤ` with `μ_p`.

This is not an Oort--Tate or Raynaud classification of arbitrary finite-flat prime-order models.
The finite-etale hypothesis is essential here; no connected special-fibre classification,
extension theorem, Neron comparison, or fppf-cohomology vanishing statement is supplied.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.AffineFiniteFreeCommGroupScheme

universe u

section Transport

variable {R : Type u} [CommRing R]
variable {G H : AffineFiniteFreeCommGroupScheme R}

local instance : Coalgebra R G.coordinates := Bialgebra.toCoalgebra
local instance : Coalgebra R H.coordinates := Bialgebra.toCoalgebra

local instance : Coalgebra R (DualCoordinates R G.coordinates) :=
  instCoalgebraDualCoordinates G
local instance : Coalgebra R (DualCoordinates R H.coordinates) :=
  instCoalgebraDualCoordinates H

local instance : Bialgebra R (DualCoordinates R G.coordinates) :=
  instBialgebraDualCoordinates G
local instance : Bialgebra R (DualCoordinates R H.coordinates) :=
  instBialgebraDualCoordinates H

/-- Transpose a coordinate bialgebra equivalence.  The inverse coordinate equivalence appears
because linear duality is contravariant. -/
def dualLinearEquivOfBialgEquiv
    (e : G.coordinates ≃ₐc[R] H.coordinates) :
    DualCoordinates R G.coordinates ≃ₗ[R] DualCoordinates R H.coordinates where
  toFun f := WithConv.toConv (f.ofConv.comp e.symm.toLinearMap)
  invFun f := WithConv.toConv (f.ofConv.comp e.toLinearMap)
  left_inv f := by
    apply WithConv.ofConv_injective
    apply LinearMap.ext
    intro a
    exact congrArg f.ofConv (e.symm_apply_apply a)
  right_inv f := by
    apply WithConv.ofConv_injective
    apply LinearMap.ext
    intro a
    exact congrArg f.ofConv (e.apply_symm_apply a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem dualLinearEquivOfBialgEquiv_apply
    (e : G.coordinates ≃ₐc[R] H.coordinates)
    (f : DualCoordinates R G.coordinates) (a : H.coordinates) :
    (dualLinearEquivOfBialgEquiv e f).ofConv a = f.ofConv (e.symm a) :=
  rfl

/-- Transposition preserves convolution multiplication because the inverse coordinate map
preserves comultiplication. -/
theorem dualLinearEquivOfBialgEquiv_map_mul
    (e : G.coordinates ≃ₐc[R] H.coordinates)
    (f g : DualCoordinates R G.coordinates) :
    dualLinearEquivOfBialgEquiv e (f * g) =
      dualLinearEquivOfBialgEquiv e f * dualLinearEquivOfBialgEquiv e g := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro a
  let ra := Coalgebra.Repr.arbitrary R a
  change (f * g).ofConv (e.symm a) =
    (dualLinearEquivOfBialgEquiv e f *
      dualLinearEquivOfBialgEquiv e g).ofConv a
  rw [(ra.induced e.symm).convMul_apply, ra.convMul_apply]
  rfl

/-- Tensor evaluation commutes with transposing a coordinate bialgebra equivalence. -/
theorem canonicalDualTensorMap_map_dualLinearEquivOfBialgEquiv
    (e : G.coordinates ≃ₐc[R] H.coordinates)
    (t : DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates)
    (a b : H.coordinates) :
    canonicalDualTensorMap H
        (TensorProduct.map
          (dualLinearEquivOfBialgEquiv e).toLinearMap
          (dualLinearEquivOfBialgEquiv e).toLinearMap t)
        (a ⊗ₜ[R] b) =
      canonicalDualTensorMap G t (e.symm a ⊗ₜ[R] e.symm b) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul f g =>
      simp only [TensorProduct.map_tmul,
        canonicalDualTensorMap_tmul_apply_tmul,
        dualLinearEquivOfBialgEquiv_apply]

/-- Transposing a bialgebra equivalence gives an actual bialgebra equivalence between the
Cartier-dual coordinate rings. -/
def dualBialgEquivOfBialgEquiv
    (e : G.coordinates ≃ₐc[R] H.coordinates) :
    DualCoordinates R G.coordinates ≃ₐc[R] DualCoordinates R H.coordinates := by
  let c : DualCoordinates R G.coordinates ≃ₗc[R]
      DualCoordinates R H.coordinates :=
    { dualLinearEquivOfBialgEquiv e with
      counit_comp := by
        apply LinearMap.ext
        intro f
        change f.ofConv (e.symm 1) = f.ofConv 1
        rw [map_one]
      map_comp_comul := by
        apply LinearMap.ext
        intro f
        apply (dualTensorLinearEquiv H).injective
        apply TensorProduct.ext'
        intro a b
        change canonicalDualTensorMap H
            (TensorProduct.map
              (dualLinearEquivOfBialgEquiv e).toLinearMap
              (dualLinearEquivOfBialgEquiv e).toLinearMap
              (dualComul G f)) (a ⊗ₜ[R] b) =
          canonicalDualTensorMap H
            (dualComul H (dualLinearEquivOfBialgEquiv e f))
            (a ⊗ₜ[R] b)
        rw [canonicalDualTensorMap_map_dualLinearEquivOfBialgEquiv,
          canonicalDualTensorMap_dualComul_apply_tmul,
          canonicalDualTensorMap_dualComul_apply_tmul,
          dualLinearEquivOfBialgEquiv_apply, map_mul] }
  exact BialgEquiv.mk c (dualLinearEquivOfBialgEquiv_map_mul e)

/-- Extract the covariant coordinate bialgebra equivalence from an affine group-scheme
isomorphism.  Passing through the opposite category accounts for the reversal. -/
def coordinateBialgEquivOfIso (e : G ≅ H) :
    G.coordinates ≃ₐc[R] H.coordinates := by
  let i : G.unop.obj ≅ H.unop.obj :=
    ((AlgebraicGeometry.cocommutativeHopfProperty R).ι.mapIso e.unop).symm
  exact CommHopfAlgCat.isoEquivBialgEquiv
    ((CommHopfAlgCat.ofIsoSelf G.unop.obj) ≪≫ i ≪≫
      (CommHopfAlgCat.ofIsoSelf H.unop.obj).symm)

/-- Cartier duality transports an actual affine finite-free group-scheme isomorphism. -/
def cartierDualIsoOfIso (e : G ≅ H) : cartierDual G ≅ cartierDual H :=
  isoOfCoordinateBialgEquiv
    (dualBialgEquivOfBialgEquiv (coordinateBialgEquivOfIso e))

end Transport

section IntegralFiniteEtale

open FiniteFlatCommGroupScheme

/-- Lift the genuine geometric finite-etale prime-order classification back to its unique
finite-free affine Hopf-coordinate isomorphism. -/
def finiteEtalePrimeAffineIsoConstantInt
    (G : AffineFiniteFreeCommGroupScheme ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hEtale : Etale G.realize.structureMap)
    (horder : G.realize.HasConstantOrder p) :
    G ≅ constant ℤ (Multiplicative (ZMod p)) :=
  preimageRealizeIso
    (finiteEtalePrimeIsoConstantInt G.realize p hp hEtale horder)

/-- The lifted affine isomorphism realizes to the original geometric classification
isomorphism. -/
@[simp]
theorem mapIso_finiteEtalePrimeAffineIsoConstantInt
    (G : AffineFiniteFreeCommGroupScheme ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hEtale : Etale G.realize.structureMap)
    (horder : G.realize.HasConstantOrder p) :
    (realizationFunctor ℤ).mapIso
        (finiteEtalePrimeAffineIsoConstantInt G p hp hEtale horder) =
      finiteEtalePrimeIsoConstantInt G.realize p hp hEtale horder :=
  mapIso_preimageRealizeIso _

/-- The actual Cartier dual of an affine finite-etale prime-order group scheme over `Spec ℤ`
is the represented multiplicative group `μ_p`. -/
def cartierDualFiniteEtalePrimeRealizeIsoMu
    (G : AffineFiniteFreeCommGroupScheme ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hEtale : Etale G.realize.structureMap)
    (horder : G.realize.HasConstantOrder p) :
    (cartierDual G).realize ≅ muScheme ℤ p :=
  (realizationFunctor ℤ).mapIso
      (cartierDualIsoOfIso
        (finiteEtalePrimeAffineIsoConstantInt G p hp hEtale horder)) ≪≫
    cartierDualConstantCyclicRealizeIsoMuScheme ℤ p

/-- Order-five endpoint: a finite-etale order-five affine factor over the integers has actual
Cartier dual `μ₅`. -/
def cartierDualFiniteEtaleFiveRealizeIsoMu
    (G : AffineFiniteFreeCommGroupScheme ℤ)
    (hEtale : Etale G.realize.structureMap)
    (horder : G.realize.HasConstantOrder 5) :
    (cartierDual G).realize ≅ muScheme ℤ 5 :=
  cartierDualFiniteEtalePrimeRealizeIsoMu G 5 (by norm_num) hEtale horder

/-- Order-eleven endpoint: a finite-etale order-eleven affine factor over the integers has actual
Cartier dual `μ₁₁`. -/
def cartierDualFiniteEtaleElevenRealizeIsoMu
    (G : AffineFiniteFreeCommGroupScheme ℤ)
    (hEtale : Etale G.realize.structureMap)
    (horder : G.realize.HasConstantOrder 11) :
    (cartierDual G).realize ≅ muScheme ℤ 11 :=
  cartierDualFiniteEtalePrimeRealizeIsoMu G 11 (by norm_num) hEtale horder

end IntegralFiniteEtale

end AlgebraicGeometry.AffineFiniteFreeCommGroupScheme
