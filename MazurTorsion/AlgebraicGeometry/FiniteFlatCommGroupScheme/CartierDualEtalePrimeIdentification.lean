/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtalePrimeCartierDual
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteFlatIntAffineFiniteFreeRealization
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteFreeCartierDoubleDual

/-!
# Prime-order factors whose Cartier dual is etale

Finite-free Cartier duality preserves the coordinate rank.  Over `Spec ℤ`, if the Cartier
dual of a prime-order affine finite-flat commutative group scheme is etale, the finite-etale
prime-order classification identifies that dual with the constant group.  Actual Cartier
biduality then identifies the original group scheme with `μ_p`.

The etaleness of the Cartier dual remains an explicit premise.  In particular, this file does
not assert the missing Oort--Tate or Raynaud dichotomy that would deduce dual etaleness from a
connected closed fibre.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.AffineFiniteFreeCommGroupScheme

universe u

variable {R : Type u} [CommRing R]

/-- Cartier duality preserves the finite-free coordinate rank. -/
theorem cartierDual_order (G : AffineFiniteFreeCommGroupScheme R) :
    (cartierDual G).order = G.order := by
  change Module.finrank R (BundledDualCoordinates G) =
    Module.finrank R G.coordinates
  calc
    Module.finrank R (BundledDualCoordinates G) =
        Module.finrank R (Module.Dual R G.coordinates) :=
      (bundledDualCoordinatesLinearEquiv G).finrank_eq
    _ = Module.finrank R G.coordinates :=
      (Module.Free.chooseBasis R G.coordinates).toDualEquiv.finrank_eq.symm

/-- The Cartier dual realization has the same constant order as the original finite-free
realization. -/
theorem cartierDual_realize_hasConstantOrder
    (G : AffineFiniteFreeCommGroupScheme R) :
    (cartierDual G).realize.HasConstantOrder G.order := by
  rw [← cartierDual_order G]
  exact (cartierDual G).realize_hasConstantOrder

section Integral

open FiniteFlatCommGroupScheme

/-- An affine prime-order group scheme over `Spec ℤ` is `μ_p` when its actual Cartier dual
is etale. -/
def realizeIsoMuOfCartierDualEtalePrimeInt
    (G : AffineFiniteFreeCommGroupScheme ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime)
    (horder : G.realize.HasConstantOrder p)
    (hdualEtale : Etale (cartierDual G).realize.structureMap) :
    G.realize ≅ muScheme ℤ p := by
  let s : Spec (.of ℤ) := Classical.choice inferInstance
  have hGorder : G.order = p := calc
    G.order = G.realize.orderAt s := (G.orderAt_eq_order s).symm
    _ = p := by
      simpa [HasConstantOrder] using congrFun horder s
  have hdualOrder : (cartierDual G).realize.HasConstantOrder p := by
    rw [← hGorder]
    exact cartierDual_realize_hasConstantOrder G
  exact cartierDoubleDualRealizeIso G ≪≫
    cartierDualFiniteEtalePrimeRealizeIsoMu
      (cartierDual G) p hp hdualEtale hdualOrder

/-- Order-five integral structural endpoint: dual etaleness identifies a factor with
`\mu_5`. -/
def realizeIsoMuFiveOfCartierDualEtaleInt
    (G : AffineFiniteFreeCommGroupScheme ℤ)
    (horder : G.realize.HasConstantOrder 5)
    (hdualEtale : Etale (cartierDual G).realize.structureMap) :
    G.realize ≅ muScheme ℤ 5 :=
  realizeIsoMuOfCartierDualEtalePrimeInt G 5 (by norm_num) horder hdualEtale

/-- Order-eleven integral structural endpoint: dual etaleness identifies a factor with
`\mu_{11}`. -/
def realizeIsoMuElevenOfCartierDualEtaleInt
    (G : AffineFiniteFreeCommGroupScheme ℤ)
    (horder : G.realize.HasConstantOrder 11)
    (hdualEtale : Etale (cartierDual G).realize.structureMap) :
    G.realize ≅ muScheme ℤ 11 :=
  realizeIsoMuOfCartierDualEtalePrimeInt G 11 (by norm_num) horder hdualEtale

end Integral

end AlgebraicGeometry.AffineFiniteFreeCommGroupScheme

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open AffineFiniteFreeCommGroupScheme

/-- Etaleness of the Cartier dual is independent of the chosen finite-free realization of a
geometric finite-flat group scheme over `Spec ℤ`. -/
theorem affineFiniteFreeModelInt_cartierDual_etale_of_realization
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : G ≅ K.realize)
    (hdualEtale : Etale (cartierDual K).realize.structureMap) :
    Etale
      (cartierDual (affineFiniteFreeModelInt G)).realize.structureMap := by
  let modelIso : affineFiniteFreeModelInt G ≅ K :=
    preimageRealizeIso ((affineFiniteFreeModelIsoInt G).symm ≪≫ e)
  exact etale_structureMap_of_iso
    ((realizationFunctor ℤ).mapIso (cartierDualIsoOfIso modelIso))
    hdualEtale

/-- A geometric prime-order finite-flat group scheme over `Spec ℤ` is `μ_p` when the Cartier
dual of its internally chosen finite-free affine model is etale. -/
def isoMuOfAffineModelCartierDualEtalePrimeInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (horder : G.HasConstantOrder p)
    (hdualEtale : Etale
      (cartierDual (affineFiniteFreeModelInt G)).realize.structureMap) :
    G ≅ muScheme ℤ p := by
  let K := affineFiniteFreeModelInt G
  let e : G ≅ K.realize := affineFiniteFreeModelIsoInt G
  have hKorder : K.realize.HasConstantOrder p := by
    change K.realize.orderAt = Function.const (Spec (.of ℤ)) p
    rw [← orderAt_eq_of_iso e]
    exact horder
  exact e ≪≫
    realizeIsoMuOfCartierDualEtalePrimeInt K p hp hKorder hdualEtale

/-- Realization-independent form of the multiplicative classification: dual etaleness on any
actual finite-free affine realization identifies the geometric factor with `μ_p`. -/
def isoMuOfRealizationCartierDualEtalePrimeInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : G ≅ K.realize)
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (horder : G.HasConstantOrder p)
    (hdualEtale : Etale (cartierDual K).realize.structureMap) :
    G ≅ muScheme ℤ p :=
  isoMuOfAffineModelCartierDualEtalePrimeInt G p hp horder
    (affineFiniteFreeModelInt_cartierDual_etale_of_realization
      G K e hdualEtale)

/-- Integral order-five endpoint for an arbitrary geometric factor whose chosen affine
Cartier dual is etale. -/
def isoMuFiveOfAffineModelCartierDualEtaleInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (horder : G.HasConstantOrder 5)
    (hdualEtale : Etale
      (cartierDual (affineFiniteFreeModelInt G)).realize.structureMap) :
    G ≅ muScheme ℤ 5 :=
  isoMuOfAffineModelCartierDualEtalePrimeInt G 5 (by norm_num) horder hdualEtale

/-- Integral order-eleven endpoint for an arbitrary geometric factor whose chosen affine
Cartier dual is etale. -/
def isoMuElevenOfAffineModelCartierDualEtaleInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (horder : G.HasConstantOrder 11)
    (hdualEtale : Etale
      (cartierDual (affineFiniteFreeModelInt G)).realize.structureMap) :
    G ≅ muScheme ℤ 11 :=
  isoMuOfAffineModelCartierDualEtalePrimeInt G 11 (by norm_num) horder hdualEtale

/-- Integral order-five endpoint whose Cartier-dual etaleness is supplied on any actual
finite-free affine realization. -/
def isoMuFiveOfRealizationCartierDualEtaleInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : G ≅ K.realize)
    (horder : G.HasConstantOrder 5)
    (hdualEtale : Etale (cartierDual K).realize.structureMap) :
    G ≅ muScheme ℤ 5 :=
  isoMuFiveOfAffineModelCartierDualEtaleInt G horder
    (affineFiniteFreeModelInt_cartierDual_etale_of_realization
      G K e hdualEtale)

/-- Integral order-eleven endpoint whose Cartier-dual etaleness is supplied on any actual
finite-free affine realization. -/
def isoMuElevenOfRealizationCartierDualEtaleInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : G ≅ K.realize)
    (horder : G.HasConstantOrder 11)
    (hdualEtale : Etale (cartierDual K).realize.structureMap) :
    G ≅ muScheme ℤ 11 :=
  isoMuElevenOfAffineModelCartierDualEtaleInt G horder
    (affineFiniteFreeModelInt_cartierDual_etale_of_realization
      G K e hdualEtale)

end AlgebraicGeometry.FiniteFlatCommGroupScheme
