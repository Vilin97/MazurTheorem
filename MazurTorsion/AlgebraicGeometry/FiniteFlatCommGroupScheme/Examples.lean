/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.MonoidAlgebra.Module
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Operations
import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic

/-!
# Basic finite-flat commutative group schemes

This file supplies concrete consumers of the finite-flat group-scheme API.  A finite
commutative group `M` gives the diagonalizable group `D(M)` with coordinate Hopf algebra
`R[M]`.  Its standard group-algebra basis proves finite freeness, so this is an actual object
of `FiniteFlatCommGroupScheme (Spec R)`, not merely a functor-of-points calculation.

The cyclic specialization `mu R n = D(Multiplicative (ZMod n))` realizes the roots-of-unity
group scheme.  Its geometric affine points are identified, as a group, with Mathlib's
`rootsOfUnity n B`, and its geometric order is proved to be exactly `n`.
-/

noncomputable section

open CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

universe u

/-- The finite-free affine diagonalizable group with character group `M`. -/
def diagonalizable (R : Type u) [CommRing R]
    (M : Type u) [CommGroup M] [Fintype M] : AffineFiniteFreeCommGroupScheme R where
  obj := Opposite.op
    ⟨CommHopfAlgCat.of R (MonoidAlgebra R M), by
      change Coalgebra.IsCocomm R (MonoidAlgebra R M)
      infer_instance⟩
  property := by
    change Module.Free R (MonoidAlgebra R M) ∧ Module.Finite R (MonoidAlgebra R M)
    constructor <;> infer_instance

/-- The geometric realization of the finite diagonalizable group `D(M)`. -/
abbrev diagonalizableScheme (R : Type u) [CommRing R]
    (M : Type u) [CommGroup M] [Fintype M] :
    FiniteFlatCommGroupScheme (Spec (.of R)) :=
  (diagonalizable R M).realize

/-- Geometric pullback of a diagonalizable scheme is canonically its Hopf-coordinate scalar
extension.  This is the base-change bridge used by the concrete examples below. -/
noncomputable def diagonalizableRealizeBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] [Fintype M] :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (diagonalizableScheme R M) ≅
      ((diagonalizable R M).baseChange (K := K)).realize :=
  (diagonalizable R M).realizeBaseChangeIso

/-- Geometric affine points of `D(M)` are characters of `M`. -/
def diagonalizablePointMulEquiv (R : Type u) [CommRing R]
    (M : Type u) [CommGroup M] [Fintype M]
    (B : Type u) [CommRing B] [Algebra R B] :
    (diagonalizableScheme R M).Point (AffineCommGroupScheme.testObject (R := R) B) ≃*
      (M →* Bˣ) :=
  ((diagonalizable R M).obj.pointMulEquiv B).trans
    (TauCeti.DiagonalizableGroup.pointsMulEquiv (R := R) (A := B) (G := M))

/-- The roots-of-unity group scheme `mu_n = D(Z/nZ)`. -/
abbrev mu (R : Type) [CommRing R] (n : ℕ) [NeZero n] :
    AffineFiniteFreeCommGroupScheme R :=
  diagonalizable R (Multiplicative (ZMod n))

/-- The geometric realization of `mu_n`. -/
abbrev muScheme (R : Type) [CommRing R] (n : ℕ) [NeZero n] :
    FiniteFlatCommGroupScheme (Spec (.of R)) :=
  (mu R n).realize

/-- Geometric base change of `mu_n` agrees with scalar extension of its Hopf coordinates. -/
noncomputable def muRealizeBaseChangeIso
    {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (n : ℕ) [NeZero n] :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (muScheme R n) ≅
      ((mu R n).baseChange (K := K)).realize :=
  (mu R n).realizeBaseChangeIso

/-- Geometric affine points of `mu_n` are exactly `n`th roots of unity. -/
def muPointMulEquiv (R : Type) [CommRing R] (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B] :
    (muScheme R n).Point (AffineCommGroupScheme.testObject (R := R) B) ≃*
      rootsOfUnity n B :=
  ((mu R n).obj.pointMulEquiv B).trans
    (TauCeti.RootsOfUnityGroup.pointsMulEquiv (R := R) (A := B) n)

/-- The finite-free coordinate rank of `mu_n` is `n`. -/
@[simp]
theorem mu_order (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n] :
    (mu R n).order = n := by
  change Module.finrank R (MonoidAlgebra R (Multiplicative (ZMod n))) = n
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (Multiplicative (ZMod n)) R)]
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr
    (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n))).trans (Nat.card_zmod n)

/-- The geometric order function of `mu_n` is constantly `n`. -/
@[simp]
theorem muScheme_orderAt (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n]
    (s : Spec (.of R)) :
    (muScheme R n).orderAt s = n := by
  exact (mu R n).orderAt_eq_order s |>.trans (mu_order R n)

/-- Every geometric affine point of `mu_n` is killed by its geometric order.  This is a
compiled multiplication-kernel consumer: `powerEnd` is the actual group-scheme morphism and
the conclusion computes its value on the point. -/
theorem mapPoint_powerEnd_mu_order_eq_one (R : Type) [CommRing R] [Nontrivial R]
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B]
    (x : (muScheme R n).Point (AffineCommGroupScheme.testObject (R := R) B)) :
    mapPoint (powerEnd (muScheme R n) n)
      (AffineCommGroupScheme.testObject (R := R) B) x = 1 := by
  rw [mapPoint_powerEnd]
  simpa [mu_order] using (mu R n).realize_point_pow_order_eq_one B x

/-- Multiplication by `n` on `mu_n` is the zero group-scheme homomorphism.  The proof uses the
geometric identity point over the coordinate algebra, so this is an equality of morphisms, not
only a statement about points over the base ring. -/
theorem powerEnd_mu_eq_zeroHom (R : Type) [CommRing R] [Nontrivial R]
    (n : ℕ) [NeZero n] :
    powerEnd (muScheme R n) n = zeroHom (muScheme R n) (muScheme R n) := by
  ext
  have h := mapPoint_powerEnd_mu_order_eq_one R n
      (mu R n).coordinates (𝟙 (muScheme R n).obj.X)
  change ((𝟙 (muScheme R n).obj.X) ≫
      (powerEnd (muScheme R n) n).hom.hom.hom.hom) = 1 at h
  have hleft := congrArg Over.Hom.left h
  exact hleft.trans (hom_zeroHom (muScheme R n) (muScheme R n)).symm

/-- The whole of `mu_n` is a certified scheme-theoretic kernel of multiplication by `n`.
This is the concrete multiplication-kernel consumer of the generic kernel API. -/
noncomputable def muPowerKernelPresentation (R : Type) [CommRing R] [Nontrivial R]
    (n : ℕ) [NeZero n] :
    KernelPresentation (powerEnd (muScheme R n) n) :=
  (powerEnd_mu_eq_zeroHom R n).symm ▸
    zeroKernelPresentation (muScheme R n) (muScheme R n)

/-- On every affine test scheme, the geometric multiplication kernel of `mu_n` represents
exactly the subgroup of points whose `n`th power is the identity. -/
noncomputable def muPowerKernelPointMulEquiv (R : Type) [CommRing R] [Nontrivial R]
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B] :
    (muPowerKernelPresentation R n).kernel.Point
        (AffineCommGroupScheme.testObject (R := R) B) ≃*
      (mapPoint (powerEnd (muScheme R n) n)
        (AffineCommGroupScheme.testObject (R := R) B)).ker :=
  (muPowerKernelPresentation R n).pointMulEquiv
    (AffineCommGroupScheme.testObject (R := R) B)

end FiniteFlatCommGroupScheme
end AlgebraicGeometry
