import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Examples
import MazurTorsion.Upstream.AINTLIB.ForMathlib.CartierDual

noncomputable section

open scoped TensorProduct

namespace CartierDualScratch

open AlgebraicGeometry

universe u

abbrev DualCoordinates (R : Type u) (A : Type u) [CommRing R]
    [AddCommGroup A] [Module R A] [Coalgebra R A] :=
  ModularCurves.CartierDual R A

section

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

def canonicalDualTensorMap :
    DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates →ₗ[R]
      Module.Dual R (G.coordinates ⊗[R] G.coordinates) :=
  (TensorProduct.dualDistrib R G.coordinates G.coordinates).comp
    (TensorProduct.map
      (WithConv.linearEquiv R (Module.Dual R G.coordinates)).toLinearMap
      (WithConv.linearEquiv R (Module.Dual R G.coordinates)).toLinearMap)

def basisDualTensorEquiv :
    DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates ≃ₗ[R]
      Module.Dual R (G.coordinates ⊗[R] G.coordinates) := by
  let b := Module.Free.chooseBasis R G.coordinates
  let db := b.dualBasis.map
    (WithConv.linearEquiv R (Module.Dual R G.coordinates)).symm
  exact (db.tensorProduct db).equiv (b.tensorProduct b).dualBasis (Equiv.refl _)

theorem canonicalDualTensorMap_eq_basisDualTensorEquiv :
    canonicalDualTensorMap G = (basisDualTensorEquiv G).toLinearMap := by
  let b := Module.Free.chooseBasis R G.coordinates
  let db := b.dualBasis.map
    (WithConv.linearEquiv R (Module.Dual R G.coordinates)).symm
  apply (db.tensorProduct db).ext
  intro ij
  rcases ij with ⟨i, j⟩
  apply (b.tensorProduct b).ext
  intro kl
  rcases kl with ⟨k, l⟩
  have he :
      (basisDualTensorEquiv G) ((db.tensorProduct db) (i, j)) =
        (b.tensorProduct b).dualBasis (i, j) := by
    simpa [basisDualTensorEquiv, b, db] using
      Module.Basis.equiv_apply (db.tensorProduct db) (i, j)
        (b.tensorProduct b).dualBasis (Equiv.refl _)
  change _ = ((basisDualTensorEquiv G) ((db.tensorProduct db) (i, j)))
    ((b.tensorProduct b) (k, l))
  rw [he]
  simp [canonicalDualTensorMap, b, db, Module.Basis.tensorProduct_apply, mul_comm]

def dualTensorLinearEquiv :
    DualCoordinates R G.coordinates ⊗[R] DualCoordinates R G.coordinates ≃ₗ[R]
      Module.Dual R (G.coordinates ⊗[R] G.coordinates) :=
  LinearEquiv.ofBijective (canonicalDualTensorMap G) (by
    rw [canonicalDualTensorMap_eq_basisDualTensorEquiv G]
    exact (basisDualTensorEquiv G).bijective)

end

end CartierDualScratch
