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
open scoped TensorProduct CategoryTheory.MonObj

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

/-- The canonical scalar-extension map from a tensor product of a group algebra to the group
algebra over the new base. -/
def diagonalizableBaseChangeAlgHom
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] :
    K ⊗[R] MonoidAlgebra R M →ₐ[K] MonoidAlgebra K M :=
  Algebra.TensorProduct.lift (Algebra.ofId K (MonoidAlgebra K M))
    (MonoidAlgebra.mapAlgHom M (Algebra.ofId R K)) (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem diagonalizableBaseChangeAlgHom_tmul_single
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] (s : K) (m : M) (r : R) :
    diagonalizableBaseChangeAlgHom (R := R) (K := K) M
        (s ⊗ₜ[R] MonoidAlgebra.single m r) =
      MonoidAlgebra.single m (s * algebraMap R K r) := by
  rw [diagonalizableBaseChangeAlgHom, Algebra.TensorProduct.lift_tmul,
    MonoidAlgebra.mapAlgHom_single]
  simp [MonoidAlgebra.single_mul_single]

/-- Scalar extension commutes with group-algebra coordinates. -/
def diagonalizableBaseChangeAlgEquiv
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] :
    K ⊗[R] MonoidAlgebra R M ≃ₐ[K] MonoidAlgebra K M := by
  let f := diagonalizableBaseChangeAlgHom (R := R) (K := K) M
  let bsource := (MonoidAlgebra.basis M R).baseChange K
  let btarget := MonoidAlgebra.basis M K
  let l := bsource.equiv btarget (Equiv.refl M)
  have hlin : f.toLinearMap = l.toLinearMap := by
    apply bsource.ext
    intro m
    simp [f, l, bsource, btarget, Module.Basis.baseChange_apply,
      MonoidAlgebra.basis_apply, diagonalizableBaseChangeAlgHom_tmul_single]
    simpa [bsource, btarget, Module.Basis.baseChange_apply, MonoidAlgebra.basis_apply]
      using (Module.Basis.equiv_apply bsource m btarget (Equiv.refl M)).symm
  have hbij : Function.Bijective f.toLinearMap := by
    rw [hlin]
    exact l.bijective
  exact AlgEquiv.ofBijective f hbij

@[simp]
theorem diagonalizableBaseChangeAlgEquiv_apply
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] (x : K ⊗[R] MonoidAlgebra R M) :
    diagonalizableBaseChangeAlgEquiv (R := R) (K := K) M x =
      diagonalizableBaseChangeAlgHom (R := R) (K := K) M x := rfl

/-- The group-algebra scalar-extension equivalence preserves counit and comultiplication. -/
def diagonalizableBaseChangeBialgEquiv
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] :
    K ⊗[R] MonoidAlgebra R M ≃ₐc[K] MonoidAlgebra K M := by
  let e := diagonalizableBaseChangeAlgEquiv (R := R) (K := K) M
  let f := diagonalizableBaseChangeAlgHom (R := R) (K := K) M
  have he : e.toLinearMap = f.toLinearMap := rfl
  let bsource := (MonoidAlgebra.basis M R).baseChange K
  let c : K ⊗[R] MonoidAlgebra R M ≃ₗc[K] MonoidAlgebra K M :=
    { e.toLinearEquiv with
      counit_comp := by
        apply bsource.ext
        intro m
        simp only [LinearMap.comp_apply, bsource, Module.Basis.baseChange_apply,
          MonoidAlgebra.basis_apply]
        change Coalgebra.counit (R := K) (e.toLinearMap
            (1 ⊗ₜ[R] MonoidAlgebra.single m 1)) = _
        rw [he]
        change Coalgebra.counit (R := K)
            (f (1 ⊗ₜ[R] MonoidAlgebra.single m 1)) = _
        rw [diagonalizableBaseChangeAlgHom_tmul_single, TensorProduct.counit_tmul]
        simp
      map_comp_comul := by
        apply bsource.ext
        intro m
        simp only [LinearMap.comp_apply, bsource, Module.Basis.baseChange_apply,
          MonoidAlgebra.basis_apply]
        change TensorProduct.map e.toLinearMap e.toLinearMap
              (Coalgebra.comul (R := K)
                (1 ⊗ₜ[R] MonoidAlgebra.single m (1 : R))) =
            Coalgebra.comul (R := K) (e.toLinearMap
              (1 ⊗ₜ[R] MonoidAlgebra.single m 1))
        rw [he]
        change TensorProduct.map f.toLinearMap f.toLinearMap
              (Coalgebra.comul (R := K)
                (1 ⊗ₜ[R] MonoidAlgebra.single m (1 : R))) =
            Coalgebra.comul (R := K)
              (f (1 ⊗ₜ[R] MonoidAlgebra.single m 1))
        rw [TensorProduct.comul_tmul, diagonalizableBaseChangeAlgHom_tmul_single]
        simp only [CommSemiring.comul_apply, MonoidAlgebra.comul_single,
          TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          AlgHom.toLinearMap_apply, map_one, _root_.mul_one]
        change diagonalizableBaseChangeAlgHom (R := R) (K := K) M
              (1 ⊗ₜ[R] MonoidAlgebra.single m 1) ⊗ₜ[K]
            diagonalizableBaseChangeAlgHom (R := R) (K := K) M
              (1 ⊗ₜ[R] MonoidAlgebra.single m 1) =
          MonoidAlgebra.single m 1 ⊗ₜ[K] MonoidAlgebra.single m 1
        simp }
  exact BialgEquiv.mk c e.map_mul

/-- Coordinate scalar extension of a diagonalizable affine group is the named diagonalizable
affine group over the new base. -/
def diagonalizableAffineBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] [Fintype M] :
    (diagonalizable R M).baseChange (K := K) ≅ diagonalizable K M :=
  AffineFiniteFreeCommGroupScheme.isoOfCoordinateBialgEquiv
    (diagonalizableBaseChangeBialgEquiv (R := R) (K := K) M)

/-- Geometric pullback of a diagonalizable scheme is canonically its Hopf-coordinate scalar
extension.  This is the base-change bridge used by the concrete examples below. -/
noncomputable def diagonalizableRealizeBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] [Fintype M] :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (diagonalizableScheme R M) ≅
      ((diagonalizable R M).baseChange (K := K)).realize :=
  (diagonalizable R M).realizeBaseChangeIso

/-- Geometric base change of a diagonalizable finite group scheme is canonically the named
diagonalizable scheme over the new base. -/
noncomputable def diagonalizableBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] [Fintype M] :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (diagonalizableScheme R M) ≅ diagonalizableScheme K M :=
  diagonalizableRealizeBaseChangeIso (R := R) (K := K) M ≪≫
    (AffineFiniteFreeCommGroupScheme.realizationFunctor K).mapIso
      (diagonalizableAffineBaseChangeIso (R := R) (K := K) M)

/-- The named diagonalizable-family base-change isomorphism acts on points of every test
scheme. -/
def diagonalizableBaseChangePointMulEquiv
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : Type u) [CommGroup M] [Fintype M] (X : Over (Spec (.of K))) :
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (diagonalizableScheme R M)).Point X ≃* (diagonalizableScheme K M).Point X :=
  pointMulEquivOfIso (diagonalizableBaseChangeIso (R := R) (K := K) M) X

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

/-- Geometric base change of `mu_n` is canonically the named `mu_n` over the new base. -/
noncomputable def muBaseChangeIso
    {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (n : ℕ) [NeZero n] :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (muScheme R n) ≅
      muScheme K n :=
  diagonalizableBaseChangeIso (R := R) (K := K) (Multiplicative (ZMod n))

/-- The named `mu_n` base-change isomorphism acts on points of every affine test scheme. -/
def muBaseChangePointMulEquiv
    {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (n : ℕ) [NeZero n] (B : Type) [CommRing B] [Algebra K B] :
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (muScheme R n)).Point (AffineCommGroupScheme.testObject (R := K) B) ≃*
      (muScheme K n).Point (AffineCommGroupScheme.testObject (R := K) B) :=
  pointMulEquivOfIso (muBaseChangeIso (R := R) (K := K) n)
    (AffineCommGroupScheme.testObject (R := K) B)

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
