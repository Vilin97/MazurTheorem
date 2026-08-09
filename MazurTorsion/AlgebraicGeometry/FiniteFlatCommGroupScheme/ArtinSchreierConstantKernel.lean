/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdditiveFppfHOneField
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeKernel
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeKernelPresentation
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantSections
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Frobenius

/-!
# The constant prime group is the Artin--Schreier kernel

Over `ZMod p`, the Artin--Schreier endomorphism of the additive group is represented on Hopf
coordinates by `x |-> x^p - x`.  This file constructs that actual endomorphism, constructs the
Hopf-coordinate inclusion of the constant group `Z/pZ`, and proves that the latter is the
canonical scheme-theoretic kernel.

The essential algebraic input is proved over every affine test algebra: algebra maps out of the
function algebra `(ZMod p)^(ZMod p)` are in bijection with roots of `b^p - b`.  Thus the kernel
comparison is a represented functor-of-points theorem, not only a statement about rational
points.
-/

noncomputable section

open CategoryTheory Opposite WithConv
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry
namespace CommGroupScheme.ArtinSchreier

universe u

/-! ## The Artin--Schreier endomorphism -/

variable (R : Type u) [CommRing R] (p : ℕ)

/-- The coordinate-algebra endomorphism sending the additive generator to `x^p - x`. -/
private noncomputable def artinSchreierAlgHom :
    SymmetricAlgebra R R →ₐ[R] SymmetricAlgebra R R :=
  SymmetricAlgebra.lift
    (LinearMap.toSpanSingleton R (SymmetricAlgebra R R)
      ((SymmetricAlgebra.ι R R 1) ^ p - SymmetricAlgebra.ι R R 1))

private theorem artinSchreierAlgHom_ι_one :
    artinSchreierAlgHom R p (SymmetricAlgebra.ι R R 1) =
      (SymmetricAlgebra.ι R R 1) ^ p - SymmetricAlgebra.ι R R 1 := by
  rw [artinSchreierAlgHom, SymmetricAlgebra.lift_ι_apply,
    LinearMap.toSpanSingleton_apply, one_smul]

variable [ExpChar R p]

/-- The Hopf-coordinate Artin--Schreier endomorphism. -/
noncomputable def artinSchreierBialgHom :
    SymmetricAlgebra R R →ₐc[R] SymmetricAlgebra R R :=
  BialgHom.ofAlgHom (artinSchreierAlgHom R p)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      simp [artinSchreierAlgHom_ι_one, SymmetricAlgebra.algebraMapInv_ι,
        zero_pow (expChar_ne_zero R p)])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      simp [artinSchreierAlgHom_ι_one, TauCeti.AdditiveGroup.comul_ι_pow R p,
        SymmetricAlgebra.comul_ι, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel)

@[simp]
theorem artinSchreierBialgHom_ι_one :
    artinSchreierBialgHom R p (SymmetricAlgebra.ι R R 1) =
      (SymmetricAlgebra.ι R R 1) ^ p - SymmetricAlgebra.ι R R 1 :=
  artinSchreierAlgHom_ι_one R p

/-- The affine Hopf presentation of the Artin--Schreier endomorphism. -/
noncomputable def artinSchreierAffine :
    AffineCommGroupScheme.additive R ⟶ AffineCommGroupScheme.additive R :=
  (ObjectProperty.homMk (P := cocommutativeHopfProperty R)
    (CommHopfAlgCat.ofHom (artinSchreierBialgHom R p))).op

/-- The actual geometric Artin--Schreier endomorphism of the additive group. -/
noncomputable def artinSchreierMap :
    AffineCommGroupScheme.additiveScheme R ⟶
      AffineCommGroupScheme.additiveScheme R :=
  (AffineCommGroupScheme.realizationFunctor R).map (artinSchreierAffine R p)

private theorem pointToAlgHom_map_realizationFunctor
    {G H : AffineCommGroupScheme R} (f : G ⟶ H)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point B) :
    H.pointToAlgHom B
        (mapPoint ((AffineCommGroupScheme.realizationFunctor R).map f)
          (AffineCommGroupScheme.testObject (R := R) B) x) =
      (G.pointToAlgHom B x).comp (AffineCommGroupScheme.coordinateMap f) := by
  apply AlgHom.ext
  intro a
  let xleft : Spec (.of B) ⟶ G.scheme := x.left
  change (Spec.preimage (xleft ≫ AffineCommGroupScheme.schemeMap f)).hom a = _
  rw [Spec.preimage_comp]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [AffineCommGroupScheme.schemeMap, Spec.preimage_map]
  rfl

/-- On affine points, the geometric Artin--Schreier map is `b |-> b^p - b`. -/
theorem additivePointMulEquiv_mapPoint_artinSchreierMap
    (B : Type u) [CommRing B] [Algebra R B]
    (x : (AffineCommGroupScheme.additive R).Point B) :
    Multiplicative.toAdd
        (AffineCommGroupScheme.additivePointMulEquiv R B
          (mapPoint (artinSchreierMap R p)
            (AffineCommGroupScheme.testObject (R := R) B) x)) =
      Multiplicative.toAdd
          (AffineCommGroupScheme.additivePointMulEquiv R B x) ^ p -
        Multiplicative.toAdd
          (AffineCommGroupScheme.additivePointMulEquiv R B x) := by
  simp only [AffineCommGroupScheme.additivePointMulEquiv, MulEquiv.trans_apply,
    TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv]
  rw [AffineCommGroupScheme.pointMulEquiv_apply,
    AffineCommGroupScheme.pointMulEquiv_apply]
  change ((AffineCommGroupScheme.additive R).pointToAlgHom B
      (mapPoint ((AffineCommGroupScheme.realizationFunctor R).map
          (artinSchreierAffine R p))
        (AffineCommGroupScheme.testObject (R := R) B) x))
      (SymmetricAlgebra.ι R R 1) = _
  have h := pointToAlgHom_map_realizationFunctor R
    (artinSchreierAffine R p) B x
  rw [h]
  change (AffineCommGroupScheme.additive R).pointToAlgHom B x
    (artinSchreierBialgHom R p (SymmetricAlgebra.ι R R 1)) = _
  rw [artinSchreierBialgHom_ι_one]
  simp only [map_sub, map_pow]

/-! ## The constant Hopf-coordinate inclusion -/

variable (q : ℕ) [Fact q.Prime]

private abbrev PrimeField := ZMod q
private abbrev PrimeIndex := Multiplicative (ZMod q)

/-- The universal `ZMod q`-valued root, as a coordinate on the constant scheme. -/
private def universalRoot :
    FiniteFlatCommGroupScheme.ConstantCoordinates (PrimeField q) (PrimeIndex q) :=
  ULift.up fun a ↦ Multiplicative.toAdd a

private noncomputable def constantToAdditiveAlgHom :
    SymmetricAlgebra (PrimeField q) (PrimeField q) →ₐ[PrimeField q]
      FiniteFlatCommGroupScheme.ConstantCoordinates (PrimeField q) (PrimeIndex q) :=
  SymmetricAlgebra.lift
    (LinearMap.toSpanSingleton (PrimeField q)
      (FiniteFlatCommGroupScheme.ConstantCoordinates (PrimeField q) (PrimeIndex q))
      (universalRoot q))

@[simp]
private theorem constantToAdditiveAlgHom_ι_one :
    constantToAdditiveAlgHom q
        (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) =
      universalRoot q := by
  rw [constantToAdditiveAlgHom, SymmetricAlgebra.lift_ι_apply,
    LinearMap.toSpanSingleton_apply, one_smul]

/-- The Hopf-coordinate map of the constant-group inclusion into the additive group. -/
noncomputable def constantToAdditiveBialgHom :
    SymmetricAlgebra (PrimeField q) (PrimeField q) →ₐc[PrimeField q]
      FiniteFlatCommGroupScheme.ConstantCoordinates (PrimeField q) (PrimeIndex q) :=
  BialgHom.ofAlgHom (constantToAdditiveAlgHom q)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      simp [SymmetricAlgebra.algebraMapInv_ι,
        FiniteFlatCommGroupScheme.ConstantCoordinates.counitAlgHom_apply,
        universalRoot])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      apply (FiniteFlatCommGroupScheme.ConstantCoordinates.tensorEval
        (R := PrimeField q) (G := PrimeIndex q)).injective
      funext ab
      rcases ab with ⟨a, b⟩
      simp [SymmetricAlgebra.comul_ι,
        FiniteFlatCommGroupScheme.ConstantCoordinates.tensorEval_tmul,
        FiniteFlatCommGroupScheme.ConstantCoordinates.tensorEval_comulAlgHom,
        universalRoot])

@[simp]
theorem constantToAdditiveBialgHom_ι_one :
    constantToAdditiveBialgHom q
        (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) =
      universalRoot q :=
  constantToAdditiveAlgHom_ι_one q

/-- The affine constant-group inclusion into the additive group. -/
noncomputable def constantInclusionAffine :
    (FiniteFlatCommGroupScheme.constant (PrimeField q) (PrimeIndex q)).obj ⟶
      AffineCommGroupScheme.additive (PrimeField q) :=
  (ObjectProperty.homMk (P := cocommutativeHopfProperty (PrimeField q))
    (CommHopfAlgCat.ofHom (constantToAdditiveBialgHom q))).op

/-- The actual geometric inclusion `Z/qZ -> G_a`. -/
noncomputable def constantInclusion :
    (FiniteFlatCommGroupScheme.constantScheme (PrimeField q) (PrimeIndex q)).obj ⟶
      AffineCommGroupScheme.additiveScheme (PrimeField q) :=
  (AffineCommGroupScheme.realizationFunctor (PrimeField q)).map
    (constantInclusionAffine q)

/-! ## Polynomial functions on the prime field -/

/-- The symmetric algebra on its rank-one coefficient module is a polynomial algebra. -/
private noncomputable def symmetricPolynomialAlgEquiv :
  SymmetricAlgebra (PrimeField q) (PrimeField q) ≃ₐ[PrimeField q]
      Polynomial (PrimeField q) :=
  (SymmetricAlgebra.equivMvPolynomial
    (Module.Basis.singleton Unit (PrimeField q))).trans
      (MvPolynomial.uniqueAlgEquiv (PrimeField q) Unit)

@[simp]
private theorem symmetricPolynomialAlgEquiv_ι_one :
    symmetricPolynomialAlgEquiv q
      (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) =
      Polynomial.X := by
  change (MvPolynomial.uniqueAlgEquiv (PrimeField q) Unit)
      (SymmetricAlgebra.equivMvPolynomial
        (Module.Basis.singleton Unit (PrimeField q))
        (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1)) = _
  rw [show (1 : PrimeField q) =
    Module.Basis.singleton Unit (PrimeField q) default by simp,
    SymmetricAlgebra.equivMvPolynomial_ι_apply]
  simp

/-- Evaluate a polynomial simultaneously at every element of the prime field. -/
private noncomputable def evalAllPolynomialAlgHom :
    Polynomial (PrimeField q) →ₐ[PrimeField q]
      (PrimeField q → PrimeField q) :=
  AlgHom.pi fun a ↦ Polynomial.aeval a

@[simp]
private theorem evalAllPolynomialAlgHom_apply
    (f : Polynomial (PrimeField q)) (a : PrimeField q) :
    evalAllPolynomialAlgHom q f a = f.eval a := by
  simp [evalAllPolynomialAlgHom, Polynomial.aeval_def]

/-- Every function on a finite prime field is represented by a polynomial. -/
private theorem evalAllPolynomialAlgHom_surjective :
    Function.Surjective (evalAllPolynomialAlgHom q) := by
  intro f
  refine ⟨Lagrange.interpolate Finset.univ (fun a : PrimeField q ↦ a) f, ?_⟩
  funext a
  rw [evalAllPolynomialAlgHom_apply]
  exact Lagrange.eval_interpolate_at_node f Function.injective_id.injOn
    (Finset.mem_univ a)

/-- The only polynomial relation among all prime-field evaluations is `X^q - X`. -/
private theorem ker_evalAllPolynomialAlgHom :
    RingHom.ker (evalAllPolynomialAlgHom q).toRingHom =
      Ideal.span ({Polynomial.X ^ q - Polynomial.X} :
        Set (Polynomial (PrimeField q))) := by
  let P : Polynomial (PrimeField q) := Polynomial.X ^ q - Polynomial.X
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hPdegree : P.natDegree = q := by
    exact FiniteField.X_pow_card_sub_X_natDegree_eq (PrimeField q) hq
  have hPmonic : P.Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hq
  have hPneOne : P ≠ 1 := by
    intro h
    have := hPdegree
    rw [h, Polynomial.natDegree_one] at this
    exact (Nat.ne_of_gt (Nat.zero_lt_one.trans hq)) this.symm
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hf
    have hrem_eval : ∀ a : PrimeField q, (f %ₘ P).eval a = 0 := by
      intro a
      calc
        (f %ₘ P).eval a = f.eval a := by
          rw [Polynomial.modByMonic_eq_sub_mul_div, Polynomial.eval_sub,
            Polynomial.eval_mul]
          simp [P, ZMod.pow_card]
        _ = evalAllPolynomialAlgHom q f a :=
          (evalAllPolynomialAlgHom_apply q f a).symm
        _ = 0 := by
          simpa using congrArg (fun g : PrimeField q → PrimeField q ↦ g a) hf
    have hrem_degree : (f %ₘ P).natDegree < Fintype.card (PrimeField q) := by
      simpa only [ZMod.card, hPdegree] using
        Polynomial.natDegree_modByMonic_lt f hPmonic hPneOne
    have hrem_zero : f %ₘ P = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        (f %ₘ P) Function.injective_id hrem_eval hrem_degree
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hPmonic).mp hrem_zero
  · rintro ⟨g, rfl⟩
    funext a
    simp [evalAllPolynomialAlgHom_apply, ZMod.pow_card]

/-- Reindex functions by additive/multiplicative notation and restore the universe-preserving
constant-coordinate wrapper. -/
private noncomputable def primeFunctionsAlgEquiv :
    (PrimeField q → PrimeField q) ≃ₐ[PrimeField q]
      FiniteFlatCommGroupScheme.ConstantCoordinates (PrimeField q) (PrimeIndex q) :=
  (AlgEquiv.piCongrLeft' (PrimeField q) (fun _ : PrimeField q ↦ PrimeField q)
    (Multiplicative.ofAdd : PrimeField q ≃ PrimeIndex q)).trans
      (ULift.algEquiv (R := PrimeField q)).symm

@[simp]
private theorem primeFunctionsAlgEquiv_apply
    (f : PrimeField q → PrimeField q) (a : PrimeIndex q) :
    (primeFunctionsAlgEquiv q f).down a = f (Multiplicative.toAdd a) :=
  rfl

/-- The concrete constant-coordinate map is simultaneous polynomial evaluation. -/
private theorem constantToAdditiveAlgHom_eq :
    constantToAdditiveAlgHom q =
      (primeFunctionsAlgEquiv q).toAlgHom.comp
        ((evalAllPolynomialAlgHom q).comp
          (symmetricPolynomialAlgEquiv q).toAlgHom) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext_ring
  apply ULift.down_injective
  funext a
  simp [universalRoot]

/-- The Hopf-coordinate inclusion is surjective as a map of coordinate algebras. -/
private theorem constantToAdditiveAlgHom_surjective :
    Function.Surjective (constantToAdditiveAlgHom q) := by
  rw [constantToAdditiveAlgHom_eq]
  exact (primeFunctionsAlgEquiv q).surjective.comp
    ((evalAllPolynomialAlgHom_surjective q).comp
      (symmetricPolynomialAlgEquiv q).surjective)

/-- Any additive point satisfying the Artin--Schreier equation descends uniquely through the
constant-coordinate quotient. -/
private theorem ker_constantToAdditiveAlgHom_le_ker_of_root
    (B : Type) [CommRing B] [Algebra (PrimeField q) B]
    (f : SymmetricAlgebra (PrimeField q) (PrimeField q) →ₐ[PrimeField q] B)
    (hroot : f (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) ^ q =
      f (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1)) :
    RingHom.ker (constantToAdditiveAlgHom q).toRingHom ≤
      RingHom.ker f.toRingHom := by
  intro x hx
  have hxconstant : constantToAdditiveAlgHom q x = 0 := RingHom.mem_ker.mp hx
  have hxpoly : evalAllPolynomialAlgHom q (symmetricPolynomialAlgEquiv q x) = 0 := by
    rw [constantToAdditiveAlgHom_eq] at hxconstant
    apply (primeFunctionsAlgEquiv q).injective
    simpa using hxconstant
  have hdiv : Polynomial.X ^ q - Polynomial.X ∣
      symmetricPolynomialAlgEquiv q x := by
    rw [← Ideal.mem_span_singleton, ← ker_evalAllPolynomialAlgHom q]
    exact RingHom.mem_ker.mpr hxpoly
  obtain ⟨y, hy⟩ := hdiv
  apply RingHom.mem_ker.mpr
  have hxexpr :
      x = ((SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) ^ q -
          SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) *
        (symmetricPolynomialAlgEquiv q).symm y := by
    apply (symmetricPolynomialAlgEquiv q).injective
    simp [hy]
  rw [hxexpr, map_mul, map_sub, map_pow]
  change (f (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) ^ q -
      f (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1)) *
        f ((symmetricPolynomialAlgEquiv q).symm y) = 0
  rw [hroot, sub_self, zero_mul]

/-! ## Exactness on arbitrary affine test algebras -/

/-- The coordinate algebra map of a constant-group point, with the concrete function algebra
exposed despite the universe-preserving wrapper. -/
private def constantPointToConcreteAlgHom
    (B : Type) [CommRing B] [Algebra (PrimeField q) B]
    (x : (FiniteFlatCommGroupScheme.constant
      (PrimeField q) (PrimeIndex q)).obj.Point B) :
    FiniteFlatCommGroupScheme.ConstantCoordinates
      (PrimeField q) (PrimeIndex q) →ₐ[PrimeField q] B := by
  change (FiniteFlatCommGroupScheme.constant
    (PrimeField q) (PrimeIndex q)).obj.coordinates →ₐ[PrimeField q] B
  exact (FiniteFlatCommGroupScheme.constant
    (PrimeField q) (PrimeIndex q)).obj.pointToAlgHom B x

/-- A concrete constant-coordinate algebra map gives the corresponding geometric point. -/
private def constantPointOfConcreteAlgHom
    (B : Type) [CommRing B] [Algebra (PrimeField q) B]
    (f : FiniteFlatCommGroupScheme.ConstantCoordinates
      (PrimeField q) (PrimeIndex q) →ₐ[PrimeField q] B) :
    (FiniteFlatCommGroupScheme.constant
      (PrimeField q) (PrimeIndex q)).obj.Point B := by
  apply (FiniteFlatCommGroupScheme.constant
    (PrimeField q) (PrimeIndex q)).obj.pointOfAlgHom B
  change FiniteFlatCommGroupScheme.ConstantCoordinates
    (PrimeField q) (PrimeIndex q) →ₐ[PrimeField q] B
  exact f

private theorem constantPointToConcreteAlgHom_pointOfConcreteAlgHom
    (B : Type) [CommRing B] [Algebra (PrimeField q) B]
    (f : FiniteFlatCommGroupScheme.ConstantCoordinates
      (PrimeField q) (PrimeIndex q) →ₐ[PrimeField q] B) :
    constantPointToConcreteAlgHom q B (constantPointOfConcreteAlgHom q B f) = f := by
  apply AlgHom.ext
  intro a
  change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom a = f a
  rw [Spec.preimage_map]
  rfl

private theorem pointToAlgHom_mapPoint_constantInclusion
    (B : Type) [CommRing B] [Algebra (PrimeField q) B]
    (x : (FiniteFlatCommGroupScheme.constant
      (PrimeField q) (PrimeIndex q)).obj.Point B) :
    (AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B
        (mapPoint (constantInclusion q)
          (AffineCommGroupScheme.testObject (R := PrimeField q) B) x) =
      (constantPointToConcreteAlgHom q B x).comp
        (constantToAdditiveAlgHom q) := by
  change (AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B
      (mapPoint ((AffineCommGroupScheme.realizationFunctor
          (PrimeField q)).map (constantInclusionAffine q))
        (AffineCommGroupScheme.testObject (R := PrimeField q) B) x) =
    ((FiniteFlatCommGroupScheme.constant
      (PrimeField q) (PrimeIndex q)).obj.pointToAlgHom B x).comp
      (AffineCommGroupScheme.coordinateMap (constantInclusionAffine q))
  rw [pointToAlgHom_map_realizationFunctor]

/-- The additive value of a constant-group point is evaluation of its coordinate map at the
universal prime-field root. -/
private theorem additivePointMulEquiv_mapPoint_constantInclusion
    (B : Type) [CommRing B] [Algebra (PrimeField q) B]
    (x : (FiniteFlatCommGroupScheme.constant
      (PrimeField q) (PrimeIndex q)).obj.Point B) :
    Multiplicative.toAdd
        (AffineCommGroupScheme.additivePointMulEquiv (PrimeField q) B
          (mapPoint (constantInclusion q)
            (AffineCommGroupScheme.testObject (R := PrimeField q) B) x)) =
      constantPointToConcreteAlgHom q B x (universalRoot q) := by
  simp only [AffineCommGroupScheme.additivePointMulEquiv, MulEquiv.trans_apply,
    TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv]
  rw [AffineCommGroupScheme.pointMulEquiv_apply]
  change (AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B
      (mapPoint (constantInclusion q)
        (AffineCommGroupScheme.testObject (R := PrimeField q) B) x)
      (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) = _
  rw [pointToAlgHom_mapPoint_constantInclusion,
    AlgHom.comp_apply, constantToAdditiveAlgHom_ι_one]

private theorem universalRoot_pow : universalRoot q ^ q = universalRoot q := by
  apply ULift.down_injective
  funext a
  simp [universalRoot, ZMod.pow_card]

/-- The geometric constant-group inclusion is injective on every affine test algebra. -/
theorem mapPoint_constantInclusion_injective
    (B : Type) [CommRing B] [Algebra (PrimeField q) B] :
    Function.Injective
      (fun x : (FiniteFlatCommGroupScheme.constant
          (PrimeField q) (PrimeIndex q)).obj.Point B ↦
        mapPoint (constantInclusion q)
          (AffineCommGroupScheme.testObject (R := PrimeField q) B) x) := by
  intro x y hxy
  have hcomp := congrArg
    ((AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B) hxy
  rw [pointToAlgHom_mapPoint_constantInclusion,
    pointToAlgHom_mapPoint_constantInclusion] at hcomp
  have halg : constantPointToConcreteAlgHom q B x =
      constantPointToConcreteAlgHom q B y := by
    apply AlgHom.ext
    intro a
    obtain ⟨b, rfl⟩ := constantToAdditiveAlgHom_surjective q a
    exact DFunLike.congr_fun hcomp b
  have hpre : Spec.preimage x.left = Spec.preimage y.left := by
    apply CommRingCat.hom_ext
    exact congrArg (fun f ↦ f.toRingHom) halg
  apply Over.OverMorphism.ext
  rw [← Spec.map_preimage x.left, ← Spec.map_preimage y.left, hpre]

/-- Every affine constant-group point is killed by the Artin--Schreier endomorphism. -/
theorem mapPoint_artinSchreierMap_constantInclusion_eq_one
    (B : Type) [CommRing B] [Algebra (PrimeField q) B]
    (x : (FiniteFlatCommGroupScheme.constant
      (PrimeField q) (PrimeIndex q)).obj.Point B) :
    mapPoint (artinSchreierMap (PrimeField q) q)
        (AffineCommGroupScheme.testObject (R := PrimeField q) B)
        (mapPoint (constantInclusion q)
          (AffineCommGroupScheme.testObject (R := PrimeField q) B) x) = 1 := by
  apply (AffineCommGroupScheme.additivePointMulEquiv (PrimeField q) B).injective
  rw [Multiplicative.ext_iff]
  rw [map_one]
  change Multiplicative.toAdd
      (AffineCommGroupScheme.additivePointMulEquiv (PrimeField q) B
        (mapPoint (artinSchreierMap (PrimeField q) q)
          (AffineCommGroupScheme.testObject (R := PrimeField q) B)
          (mapPoint (constantInclusion q)
            (AffineCommGroupScheme.testObject (R := PrimeField q) B) x))) = 0
  rw [additivePointMulEquiv_mapPoint_artinSchreierMap,
    additivePointMulEquiv_mapPoint_constantInclusion]
  rw [← map_pow, universalRoot_pow, sub_self]

/-- The represented affine-point sequence `Z/qZ -> G_a -> G_a` is exact over every
`ZMod q`-algebra. -/
theorem constantInclusion_artinSchreierMap_mulExact
    (B : Type) [CommRing B] [Algebra (PrimeField q) B] :
    Function.MulExact
      (mapPoint (constantInclusion q)
        (AffineCommGroupScheme.testObject (R := PrimeField q) B) :
          (FiniteFlatCommGroupScheme.constant
              (PrimeField q) (PrimeIndex q)).obj.Point B →*
            (AffineCommGroupScheme.additiveScheme (PrimeField q)).Point
              (AffineCommGroupScheme.testObject (R := PrimeField q) B))
      (mapPoint (artinSchreierMap (PrimeField q) q)
        (AffineCommGroupScheme.testObject (R := PrimeField q) B)) := by
  intro x
  constructor
  · intro hx
    let b : B := Multiplicative.toAdd
      (AffineCommGroupScheme.additivePointMulEquiv (PrimeField q) B x)
    have hbzero : b ^ q - b = 0 := by
      have h := congrArg
        (fun y ↦ Multiplicative.toAdd
          (AffineCommGroupScheme.additivePointMulEquiv (PrimeField q) B y)) hx
      rw [additivePointMulEquiv_mapPoint_artinSchreierMap] at h
      simpa [b] using h
    have hb :
        (AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B x
            (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) = b := by
      dsimp [b]
      simp only [AffineCommGroupScheme.additivePointMulEquiv,
        MulEquiv.trans_apply, TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv]
      rw [AffineCommGroupScheme.pointMulEquiv_apply]
    have hroot :
        (AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B x
              (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) ^ q =
          (AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B x
            (SymmetricAlgebra.ι (PrimeField q) (PrimeField q) 1) := by
      rw [hb]
      exact sub_eq_zero.mp hbzero
    let f : FiniteFlatCommGroupScheme.ConstantCoordinates
        (PrimeField q) (PrimeIndex q) →ₐ[PrimeField q] B :=
      AlgHom.liftOfSurjective (constantToAdditiveAlgHom q)
        (constantToAdditiveAlgHom_surjective q)
        ((AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B x)
        (ker_constantToAdditiveAlgHom_le_ker_of_root q B
          ((AffineCommGroupScheme.additive (PrimeField q)).pointToAlgHom B x) hroot)
    let z := constantPointOfConcreteAlgHom q B f
    refine ⟨z, ?_⟩
    apply (AffineCommGroupScheme.additivePointMulEquiv (PrimeField q) B).injective
    rw [Multiplicative.ext_iff]
    rw [additivePointMulEquiv_mapPoint_constantInclusion]
    have hfz : constantPointToConcreteAlgHom q B z = f := by
      exact constantPointToConcreteAlgHom_pointOfConcreteAlgHom q B f
    rw [hfz]
    change f (universalRoot q) = b
    rw [← constantToAdditiveAlgHom_ι_one q]
    simp only [f, AlgHom.liftOfSurjective_apply]
    exact hb
  · rintro ⟨z, rfl⟩
    exact mapPoint_artinSchreierMap_constantInclusion_eq_one q B z

/-! ## Comparison with the canonical scheme-theoretic kernel -/

/-- The canonical scheme-theoretic Artin--Schreier kernel. -/
noncomputable abbrev artinSchreierKernel :
    CommGroupScheme (Spec (.of (PrimeField q))) :=
  CommGroupScheme.kernel (artinSchreierMap (PrimeField q) q)

/-- The zero ambient group-scheme morphism from the constant group to the additive group. -/
noncomputable def constantToAdditiveZero :
    (FiniteFlatCommGroupScheme.constantScheme
        (PrimeField q) (PrimeIndex q)).obj ⟶
      AffineCommGroupScheme.additiveScheme (PrimeField q) :=
  InducedCategory.homMk
    ((default : (FiniteFlatCommGroupScheme.constantScheme
        (PrimeField q) (PrimeIndex q)).obj.toGrp ⟶
          Grp.trivial (Over (Spec (.of (PrimeField q))))) ≫
      (default : Grp.trivial (Over (Spec (.of (PrimeField q)))) ⟶
        (AffineCommGroupScheme.additiveScheme (PrimeField q)).toGrp))

/-- Scheme-theoretically, Artin--Schreier annihilates the constant-group inclusion. -/
theorem constantInclusion_comp_artinSchreierMap :
    constantInclusion q ≫ artinSchreierMap (PrimeField q) q =
      constantToAdditiveZero q := by
  ext
  have h := mapPoint_artinSchreierMap_constantInclusion_eq_one q
    (FiniteFlatCommGroupScheme.constant
      (PrimeField q) (PrimeIndex q)).coordinates
    (CategoryStruct.id (FiniteFlatCommGroupScheme.constantScheme
      (PrimeField q) (PrimeIndex q)).obj.X)
  change (((CategoryStruct.id
      (FiniteFlatCommGroupScheme.constantScheme
        (PrimeField q) (PrimeIndex q)).obj.X) ≫
          (constantInclusion q).hom.hom.hom) ≫
      (artinSchreierMap (PrimeField q) q).hom.hom.hom) = 1 at h
  have hleft := congrArg Over.Hom.left h
  change _ = (FiniteFlatCommGroupScheme.constantScheme
      (PrimeField q) (PrimeIndex q)).obj.X.hom ≫
    η[(AffineCommGroupScheme.additiveScheme (PrimeField q)).X].left at hleft
  change _ = (FiniteFlatCommGroupScheme.constantScheme
      (PrimeField q) (PrimeIndex q)).obj.X.hom ≫
    η[(AffineCommGroupScheme.additiveScheme (PrimeField q)).X].left
  simpa using hleft

private theorem constantInclusion_zero_grp :
    (constantInclusion q).hom ≫
        (artinSchreierMap (PrimeField q) q).hom =
      (default : (FiniteFlatCommGroupScheme.constantScheme
          (PrimeField q) (PrimeIndex q)).obj.toGrp ⟶
        Grp.trivial (Over (Spec (.of (PrimeField q))))) ≫
        CommGroupScheme.kernelZero
          (AffineCommGroupScheme.additiveScheme (PrimeField q)) := by
  have h := congrArg (fun f ↦ f.hom)
    (constantInclusion_comp_artinSchreierMap q)
  simpa [constantToAdditiveZero] using h

/-- The canonical comparison from the constant prime group to the ambient Artin--Schreier
kernel. -/
noncomputable def constantSchemeToArtinSchreierKernel :
    (FiniteFlatCommGroupScheme.constantScheme
        (PrimeField q) (PrimeIndex q)).obj ⟶
      artinSchreierKernel q := by
  apply InducedCategory.homMk
  exact pullback.lift (constantInclusion q).hom default
    (constantInclusion_zero_grp q)

@[reassoc]
theorem constantSchemeToArtinSchreierKernel_comp_kernelInclusion :
    constantSchemeToArtinSchreierKernel q ≫
        CommGroupScheme.kernelInclusion
          (artinSchreierMap (PrimeField q) q) =
      constantInclusion q := by
  apply CommGrp.hom_ext
  have hlift := pullback.lift_fst (constantInclusion q).hom
    (default : (FiniteFlatCommGroupScheme.constantScheme
      (PrimeField q) (PrimeIndex q)).obj.toGrp ⟶
        Grp.trivial (Over (Spec (.of (PrimeField q)))))
    (constantInclusion_zero_grp q)
  exact congrArg (fun f ↦ f.hom.hom) hlift

/-- On every affine test algebra, the comparison with the canonical Artin--Schreier kernel is
bijective. -/
theorem constantSchemeToArtinSchreierKernel_point_bijective
    (B : Type) [CommRing B] [Algebra (PrimeField q) B] :
    Function.Bijective
      (mapPoint (constantSchemeToArtinSchreierKernel q)
        (AffineCommGroupScheme.testObject (R := PrimeField q) B) :
          (FiniteFlatCommGroupScheme.constant
              (PrimeField q) (PrimeIndex q)).obj.Point B →*
            (artinSchreierKernel q).Point
              (AffineCommGroupScheme.testObject (R := PrimeField q) B)) := by
  constructor
  · intro x y hxy
    apply mapPoint_constantInclusion_injective q B
    have h := congrArg
      (mapPoint (CommGroupScheme.kernelInclusion
          (artinSchreierMap (PrimeField q) q))
        (AffineCommGroupScheme.testObject (R := PrimeField q) B)) hxy
    simpa only [← MonoidHom.comp_apply, ← CommGroupScheme.mapPoint_comp,
      constantSchemeToArtinSchreierKernel_comp_kernelInclusion] using h
  · intro y
    let x := mapPoint (CommGroupScheme.kernelInclusion
        (artinSchreierMap (PrimeField q) q))
      (AffineCommGroupScheme.testObject (R := PrimeField q) B) y
    have hx : mapPoint (artinSchreierMap (PrimeField q) q)
        (AffineCommGroupScheme.testObject (R := PrimeField q) B) x = 1 :=
      CommGroupScheme.mapPoint_kernelInclusion_eq_one
        (artinSchreierMap (PrimeField q) q)
        (AffineCommGroupScheme.testObject (R := PrimeField q) B) y
    obtain ⟨z, hz⟩ :=
      (constantInclusion_artinSchreierMap_mulExact q B x).mp hx
    refine ⟨z, ?_⟩
    apply CommGroupScheme.kernelInclusion_point_injective
      (artinSchreierMap (PrimeField q) q)
      (AffineCommGroupScheme.testObject (R := PrimeField q) B)
    calc
      mapPoint (CommGroupScheme.kernelInclusion
          (artinSchreierMap (PrimeField q) q))
          (AffineCommGroupScheme.testObject (R := PrimeField q) B)
          (mapPoint (constantSchemeToArtinSchreierKernel q)
            (AffineCommGroupScheme.testObject (R := PrimeField q) B) z) =
        mapPoint (constantInclusion q)
          (AffineCommGroupScheme.testObject (R := PrimeField q) B) z := by
            rw [← MonoidHom.comp_apply, ← CommGroupScheme.mapPoint_comp,
              constantSchemeToArtinSchreierKernel_comp_kernelInclusion]
      _ = x := hz
      _ = mapPoint (CommGroupScheme.kernelInclusion
          (artinSchreierMap (PrimeField q) q))
          (AffineCommGroupScheme.testObject (R := PrimeField q) B) y := rfl

/-- The algebra structure on global sections of a scheme over the prime field. -/
private noncomputable def globalSectionsAlgebraMap
    (T : Over (Spec (.of (PrimeField q)))) :
    PrimeField q →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (PrimeField q))).inv ≫ T.hom.appTop).hom

/-- An affine scheme over the prime field is canonically isomorphic, over the base, to the
affine test object associated to its global sections. -/
private noncomputable def affineOverIsoTestObject
    (T : Over (Spec (.of (PrimeField q)))) [IsAffine T.left] :
    letI := (globalSectionsAlgebraMap q T).toAlgebra
    T ≅ AffineCommGroupScheme.testObject
      (R := PrimeField q) Γ(T.left, ⊤) := by
  letI := (globalSectionsAlgebraMap q T).toAlgebra
  exact Over.isoMk T.left.isoSpec (by
    change T.left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (PrimeField q) Γ(T.left, ⊤))) = T.hom
    rw [RingHom.algebraMap_toAlgebra]
    change T.left.toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (.of (PrimeField q))).inv ≫
          T.hom.appTop) = T.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp)

/-- The represented-point comparison is an isomorphism of commutative group schemes. -/
private noncomputable instance constantSchemeToArtinSchreierKernel_isIso :
    IsIso (constantSchemeToArtinSchreierKernel q) := by
  let G := (FiniteFlatCommGroupScheme.constantScheme
    (PrimeField q) (PrimeIndex q)).obj
  let H := artinSchreierKernel q
  let f : G.X ⟶ H.X := (constantSchemeToArtinSchreierKernel q).hom.hom.hom
  letI : IsAffine G.X.left := by
    change IsAffine (Spec (.of
      (FiniteFlatCommGroupScheme.ConstantCoordinates
        (PrimeField q) (PrimeIndex q))))
    infer_instance
  letI : IsAffine
      (AffineCommGroupScheme.additiveScheme (PrimeField q)).X.left := by
    change IsAffine (Spec (.of
      (SymmetricAlgebra (PrimeField q) (PrimeField q))))
    infer_instance
  letI : IsAffine (𝟙_ (Over (Spec (.of (PrimeField q))))).left := by
    change IsAffine (Spec (.of (PrimeField q)))
    infer_instance
  letI : IsAffine H.X.left := by
    letI : IsAffine (CommGroupScheme.kernelScheme
        (artinSchreierMap (PrimeField q) q)) := by
      exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
        (CommGroupScheme.underlyingHom
          (artinSchreierMap (PrimeField q) q))
        (η[(AffineCommGroupScheme.additiveScheme (PrimeField q)).X].left)
    exact IsAffine.of_isIso
      (CommGroupScheme.kernelSchemeIso
        (artinSchreierMap (PrimeField q) q)).hom
  let BG := Γ(G.X.left, ⊤)
  let BH := Γ(H.X.left, ⊤)
  letI : Algebra (PrimeField q) BG :=
    (globalSectionsAlgebraMap q G.X).toAlgebra
  letI : Algebra (PrimeField q) BH :=
    (globalSectionsAlgebraMap q H.X).toAlgebra
  let eG : G.X ≅ AffineCommGroupScheme.testObject
      (R := PrimeField q) BG := affineOverIsoTestObject q G.X
  let eH : H.X ≅ AffineCommGroupScheme.testObject
      (R := PrimeField q) BH := affineOverIsoTestObject q H.X
  obtain ⟨x, hx⟩ :=
    (constantSchemeToArtinSchreierKernel_point_bijective q BH).2 eH.inv
  let g : H.X ⟶ G.X := eH.hom ≫ x
  have hx' : x ≫ f = eH.inv := by
    change x ≫ (constantSchemeToArtinSchreierKernel q).hom.hom.hom =
      eH.inv at hx
    simpa [f] using hx
  have hgf : g ≫ f = 𝟙 H.X := by
    dsimp [g]
    rw [Category.assoc, hx', eH.hom_inv_id]
  have hfg : f ≫ g = 𝟙 G.X := by
    apply (cancel_epi eG.inv).1
    apply (constantSchemeToArtinSchreierKernel_point_bijective q BG).1
    change (eG.inv ≫ (f ≫ g)) ≫ f =
      (eG.inv ≫ 𝟙 G.X) ≫ f
    simp only [Category.assoc, hgf, Category.comp_id]
  let e : G.X ≅ H.X :=
    { hom := f
      inv := g
      hom_inv_id := hfg
      inv_hom_id := hgf }
  haveI : IsIso f := e.isIso_hom
  haveI : IsIso ((Over.forget (Spec (.of (PrimeField q)))).map
      (constantSchemeToArtinSchreierKernel q).hom.hom.hom) := by
    exact (inferInstance : IsIso
      ((Over.forget (Spec (.of (PrimeField q)))).map f))
  haveI : IsIso (constantSchemeToArtinSchreierKernel q).hom.hom.hom :=
    isIso_of_reflects_iso _ (Over.forget (Spec (.of (PrimeField q))))
  haveI : IsIso ((Mon.forget (Over (Spec (.of (PrimeField q))))).map
      (constantSchemeToArtinSchreierKernel q).hom.hom) := by
    change IsIso (constantSchemeToArtinSchreierKernel q).hom.hom.hom
    infer_instance
  haveI : IsIso (constantSchemeToArtinSchreierKernel q).hom.hom :=
    isIso_of_reflects_iso _
      (Mon.forget (Over (Spec (.of (PrimeField q)))))
  haveI : IsIso ((Grp.forget₂Mon (Over (Spec (.of (PrimeField q))))).map
      (constantSchemeToArtinSchreierKernel q).hom) := by
    change IsIso (constantSchemeToArtinSchreierKernel q).hom.hom
    infer_instance
  haveI : IsIso (constantSchemeToArtinSchreierKernel q).hom :=
    isIso_of_reflects_iso _
      (Grp.forget₂Mon (Over (Spec (.of (PrimeField q)))))
  haveI : IsIso ((CommGrp.forget₂Grp
      (Over (Spec (.of (PrimeField q))))).map
      (constantSchemeToArtinSchreierKernel q)) := by
    change IsIso (constantSchemeToArtinSchreierKernel q).hom
    infer_instance
  exact isIso_of_reflects_iso _
    (CommGrp.forget₂Grp (Over (Spec (.of (PrimeField q)))))

/-- The constant prime group is canonically the scheme-theoretic Artin--Schreier kernel. -/
noncomputable def constantSchemeArtinSchreierKernelIso :
    (FiniteFlatCommGroupScheme.constantScheme
        (PrimeField q) (PrimeIndex q)).obj ≅
      artinSchreierKernel q :=
  asIso (constantSchemeToArtinSchreierKernel q)

@[simp]
theorem constantSchemeArtinSchreierKernelIso_hom :
    (constantSchemeArtinSchreierKernelIso q).hom =
      constantSchemeToArtinSchreierKernel q :=
  rfl

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The five-adic residue-field instance of the actual Artin--Schreier kernel comparison. -/
noncomputable def constantSchemeArtinSchreierKernelIsoAtFive :
    (FiniteFlatCommGroupScheme.constantScheme
        (ZMod 5) (Multiplicative (ZMod 5))).obj ≅
      CommGroupScheme.kernel (artinSchreierMap (ZMod 5) 5) := by
  exact constantSchemeArtinSchreierKernelIso 5

/-- The eleven-adic residue-field instance of the actual Artin--Schreier kernel comparison. -/
noncomputable def constantSchemeArtinSchreierKernelIsoAtEleven :
    (FiniteFlatCommGroupScheme.constantScheme
        (ZMod 11) (Multiplicative (ZMod 11))).obj ≅
      CommGroupScheme.kernel (artinSchreierMap (ZMod 11) 11) := by
  exact constantSchemeArtinSchreierKernelIso 11

end CommGroupScheme.ArtinSchreier
end AlgebraicGeometry
