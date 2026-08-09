/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeKummer
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfQuotient

/-!
# The power map on the multiplicative group is fppf

This file identifies the coordinate map of the geometric `n`th-power endomorphism of `G_m`
with Laurent substitution `T ↦ T ^ n`.  For positive `n`, the resulting morphism is finite
free, hence faithfully flat and locally of finite presentation.
-/

noncomputable section

open CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace AlgebraicGeometry
namespace CommGroupScheme.MultiplicativeKummer

universe u

variable (R : Type u) [CommRing R]

/-- Laurent substitution on exponents induced by multiplication by `n`. -/
noncomputable def powerCoordinateBialgHom (n : ℕ) :
    R[T;T⁻¹] →ₐc[R] R[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainBialgHom R
    (nsmulAddMonoidHom (α := ℤ) n)

@[simp]
theorem powerCoordinateBialgHom_T (n : ℕ) (k : ℤ) :
    powerCoordinateBialgHom R n (LaurentPolynomial.T k) =
      LaurentPolynomial.T (n * k) := by
  change AddMonoidAlgebra.mapDomain (nsmulAddMonoidHom n)
      (AddMonoidAlgebra.single k 1) =
    AddMonoidAlgebra.single (n * k) 1
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

/-- The affine Hopf-coordinate morphism defined by Laurent substitution. -/
noncomputable def powerMapAffine (n : ℕ) :
    AffineCommGroupScheme.multiplicative R ⟶
      AffineCommGroupScheme.multiplicative R :=
  (ObjectProperty.homMk (P := cocommutativeHopfProperty R)
    (CommHopfAlgCat.ofHom (powerCoordinateBialgHom R n))).op

@[simp]
theorem coordinateMap_powerMapAffine (n : ℕ) :
    AffineCommGroupScheme.coordinateMap (powerMapAffine R n) =
      powerCoordinateBialgHom R n :=
  rfl

@[simp]
theorem coordinateMap_powerMapAffine_T (n : ℕ) (k : ℤ) :
    AffineCommGroupScheme.coordinateMap (powerMapAffine R n)
        (LaurentPolynomial.T k) = LaurentPolynomial.T (n * k) := by
  exact powerCoordinateBialgHom_T R n k

/-- Geometric realization of Laurent substitution is the intrinsic power endomorphism. -/
theorem realization_powerMapAffine (n : ℕ) :
    (AffineCommGroupScheme.realizationFunctor R).map (powerMapAffine R n) =
      powerMap R n := by
  ext
  let G := AffineCommGroupScheme.multiplicativeScheme R
  let A := R[T;T⁻¹]
  let a : G.Point (AffineCommGroupScheme.testObject (R := R) A) :=
    ((AffineCommGroupScheme.realizationFunctor R).map
      (powerMapAffine R n)).hom.hom.hom
  let b : G.Point (AffineCommGroupScheme.testObject (R := R) A) :=
    (powerMap R n).hom.hom.hom
  change a.left = b.left
  apply congrArg Over.Hom.left
  let q : G.Point (AffineCommGroupScheme.testObject (R := R) A) := 𝟙 G.X
  have hpower := CommGroupScheme.mapPoint_powerEnd
    G n (AffineCommGroupScheme.testObject (R := R) A) q
  have hb : b = q ^ n := by
    change (𝟙 G.X) ≫ (powerMap R n).hom.hom.hom = q ^ n at hpower
    rw [Category.id_comp] at hpower
    exact hpower
  rw [hb]
  let e := AffineCommGroupScheme.multiplicativePointMulEquiv R A
  have hq : e q = (LaurentPolynomial.isUnit_T (R := R) 1).unit := by
    apply Units.ext
    change (TauCeti.MultiplicativeGroup.unitOfPoint
      (((AffineCommGroupScheme.multiplicative R).pointMulEquiv A q).ofConv) : A) = _
    rw [TauCeti.MultiplicativeGroup.unitOfPoint_val,
      AffineCommGroupScheme.pointMulEquiv_apply]
    change (Spec.preimage q.left).hom (LaurentPolynomial.T 1) = _
    change (Spec.preimage (𝟙 (Spec (.of A)))).hom (LaurentPolynomial.T 1) = _
    rw [Spec.preimage_id]
    exact (LaurentPolynomial.isUnit_T (R := R) 1).unit_spec.symm
  apply e.injective
  rw [map_pow, hq]
  apply Units.ext
  change (TauCeti.MultiplicativeGroup.unitOfPoint
      (((AffineCommGroupScheme.multiplicative R).pointMulEquiv A a).ofConv) : A) = _
  rw [TauCeti.MultiplicativeGroup.unitOfPoint_val,
    AffineCommGroupScheme.pointMulEquiv_apply]
  change (Spec.preimage a.left).hom
      (LaurentPolynomial.T 1) = _
  change (Spec.preimage (AffineCommGroupScheme.schemeMap (powerMapAffine R n))).hom
      (LaurentPolynomial.T 1) = _
  rw [AffineCommGroupScheme.schemeMap, Spec.preimage_map]
  change (AffineCommGroupScheme.coordinateMap (powerMapAffine R n))
      (LaurentPolynomial.T 1) = _
  rw [coordinateMap_powerMapAffine_T]
  change LaurentPolynomial.T (n * 1) =
    ((LaurentPolynomial.isUnit_T (R := R) 1).unit ^ n : A)
  rw [IsUnit.unit_spec, LaurentPolynomial.T_pow]

/-- Evaluation from the universal root algebra to Laurent polynomials, with the base Laurent
variable acting through `T ↦ T ^ n` and the adjoined root acting as `T`. -/
noncomputable def powerRootForward (n : ℕ) :
    RootAlgebra R[T;T⁻¹]
        (LaurentPolynomial.isUnit_T (R := R) 1).unit n →+* R[T;T⁻¹] :=
  AdjoinRoot.lift (powerCoordinateBialgHom R n).toAlgHom.toRingHom
    (LaurentPolynomial.T 1) (by
      simp [rootPolynomial, powerCoordinateBialgHom_T,
        LaurentPolynomial.T_pow])

@[simp]
theorem powerRootForward_root (n : ℕ) :
    powerRootForward R n
        (AdjoinRoot.root (rootPolynomial R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n)) =
      LaurentPolynomial.T 1 := by
  simp [powerRootForward]

@[simp]
theorem powerRootForward_of (n : ℕ) (x : R[T;T⁻¹]) :
    powerRootForward R n
        (algebraMap R[T;T⁻¹]
          (RootAlgebra R[T;T⁻¹]
            (LaurentPolynomial.isUnit_T (R := R) 1).unit n) x) =
      powerCoordinateBialgHom R n x := by
  simp [powerRootForward]

/-- Laurent evaluation in the distinguished unit of the universal root algebra. -/
noncomputable def powerRootBackward (n : ℕ) (hn : n ≠ 0) :
    R[T;T⁻¹] →+*
      RootAlgebra R[T;T⁻¹]
        (LaurentPolynomial.isUnit_T (R := R) 1).unit n :=
  LaurentPolynomial.eval₂
    (algebraMap R
      (RootAlgebra R[T;T⁻¹]
        (LaurentPolynomial.isUnit_T (R := R) 1).unit n))
    (rootUnit R[T;T⁻¹]
      (LaurentPolynomial.isUnit_T (R := R) 1).unit n hn)

@[simp]
theorem powerRootBackward_T (n : ℕ) (hn : n ≠ 0) (k : ℤ) :
    powerRootBackward R n hn (LaurentPolynomial.T k) =
      ((rootUnit R[T;T⁻¹]
        (LaurentPolynomial.isUnit_T (R := R) 1).unit n hn) ^ k).val := by
  simp [powerRootBackward]

@[simp]
theorem powerRootBackward_C (n : ℕ) (hn : n ≠ 0) (r : R) :
    powerRootBackward R n hn (LaurentPolynomial.C r) =
      algebraMap R
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n) r := by
  simp [powerRootBackward]

@[simp]
theorem powerLaurentUnit_zpow (k : ℤ) :
    ((((LaurentPolynomial.isUnit_T (R := R) 1).unit) ^ k :
      R[T;T⁻¹]ˣ) : R[T;T⁻¹]) = LaurentPolynomial.T k := by
  cases k with
  | ofNat m =>
      change (((LaurentPolynomial.isUnit_T (R := R) 1).unit ^ m :
        R[T;T⁻¹]ˣ) : R[T;T⁻¹]) = LaurentPolynomial.T (m : ℤ)
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec,
        LaurentPolynomial.T_pow]
      simp
  | negSucc m =>
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      have hinv :
          ((((LaurentPolynomial.isUnit_T (R := R) 1).unit)⁻¹ :
            R[T;T⁻¹]ˣ) : R[T;T⁻¹]) = LaurentPolynomial.T (-1) := by
        rw [← (LaurentPolynomial.isUnit_T (R := R) 1).mul_left_inj]
        change
          (((LaurentPolynomial.isUnit_T (R := R) 1).unit⁻¹ :
            R[T;T⁻¹]ˣ) : R[T;T⁻¹]) *
              ((LaurentPolynomial.isUnit_T (R := R) 1).unit : R[T;T⁻¹]) = _
        rw [Units.inv_mul]
        rw [← LaurentPolynomial.T_add, neg_add_cancel,
          LaurentPolynomial.T_zero]
      rw [hinv, LaurentPolynomial.T_pow]
      congr 1
      omega

theorem powerRootForward_comp_powerRootBackward (n : ℕ) (hn : n ≠ 0) :
    (powerRootForward R n).comp (powerRootBackward R n hn) =
      RingHom.id R[T;T⁻¹] := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    change powerRootForward R n
        (powerRootBackward R n hn (LaurentPolynomial.C r)) =
      LaurentPolynomial.C r
    rw [powerRootBackward_C,
      IsScalarTower.algebraMap_apply R R[T;T⁻¹]
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n),
      powerRootForward_of]
    rw [LaurentPolynomial.C_eq_algebraMap]
    exact (powerCoordinateBialgHom R n).toAlgHom.commutes r
  · intro k
    change powerRootForward R n
        (powerRootBackward R n hn (LaurentPolynomial.T k)) =
      LaurentPolynomial.T k
    rw [powerRootBackward_T]
    let v := rootUnit R[T;T⁻¹]
      (LaurentPolynomial.isUnit_T (R := R) 1).unit n hn
    have hv :
        Units.map (powerRootForward R n).toMonoidHom v =
          (LaurentPolynomial.isUnit_T (R := R) 1).unit := by
      apply Units.ext
      change powerRootForward R n
          (AdjoinRoot.root (rootPolynomial R[T;T⁻¹]
            (LaurentPolynomial.isUnit_T (R := R) 1).unit n)) =
        LaurentPolynomial.T 1
      rw [powerRootForward_root]
    change powerRootForward R n ((v ^ k).val) = LaurentPolynomial.T k
    change
      ((Units.map (powerRootForward R n).toMonoidHom (v ^ k) :
        R[T;T⁻¹]ˣ) : R[T;T⁻¹]) = LaurentPolynomial.T k
    rw [(Units.map (powerRootForward R n).toMonoidHom).map_zpow, hv,
      powerLaurentUnit_zpow]

theorem powerRootBackward_comp_powerCoordinate (n : ℕ) (hn : n ≠ 0) :
    (powerRootBackward R n hn).comp
        (powerCoordinateBialgHom R n).toAlgHom.toRingHom =
      algebraMap R[T;T⁻¹]
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    change powerRootBackward R n hn
        (powerCoordinateBialgHom R n (LaurentPolynomial.C r)) =
      algebraMap R[T;T⁻¹]
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n)
        (LaurentPolynomial.C r)
    have hc : powerCoordinateBialgHom R n (LaurentPolynomial.C r) =
        LaurentPolynomial.C r := by
      rw [LaurentPolynomial.C_eq_algebraMap]
      exact (powerCoordinateBialgHom R n).toAlgHom.commutes r
    rw [hc, powerRootBackward_C]
    exact IsScalarTower.algebraMap_apply R R[T;T⁻¹]
      (RootAlgebra R[T;T⁻¹]
        (LaurentPolynomial.isUnit_T (R := R) 1).unit n) r
  · intro k
    change powerRootBackward R n hn
        (powerCoordinateBialgHom R n (LaurentPolynomial.T k)) =
      algebraMap R[T;T⁻¹]
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n)
        (LaurentPolynomial.T k)
    rw [powerCoordinateBialgHom_T, powerRootBackward_T]
    let v := rootUnit R[T;T⁻¹]
      (LaurentPolynomial.isUnit_T (R := R) 1).unit n hn
    let j := algebraMap R[T;T⁻¹]
      (RootAlgebra R[T;T⁻¹]
        (LaurentPolynomial.isUnit_T (R := R) 1).unit n)
    change (v ^ ((n : ℤ) * k)).val = j (LaurentPolynomial.T k)
    rw [zpow_mul, zpow_natCast, rootUnit_pow]
    change
      (((Units.map j.toMonoidHom
          (LaurentPolynomial.isUnit_T (R := R) 1).unit) ^ k :
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n)ˣ)).val =
        j (LaurentPolynomial.T k)
    rw [← (Units.map j.toMonoidHom).map_zpow, Units.coe_map,
      powerLaurentUnit_zpow]
    rfl

theorem powerRootBackward_comp_powerRootForward (n : ℕ) (hn : n ≠ 0) :
    (powerRootBackward R n hn).comp (powerRootForward R n) =
      RingHom.id
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n) := by
  apply AdjoinRoot.ringHom_ext
  · rw [RingHom.comp_assoc]
    change (powerRootBackward R n hn).comp
        ((powerRootForward R n).comp
          (algebraMap R[T;T⁻¹]
            (RootAlgebra R[T;T⁻¹]
              (LaurentPolynomial.isUnit_T (R := R) 1).unit n))) = _
    rw [show (powerRootForward R n).comp
        (algebraMap R[T;T⁻¹]
          (RootAlgebra R[T;T⁻¹]
            (LaurentPolynomial.isUnit_T (R := R) 1).unit n)) =
        (powerCoordinateBialgHom R n).toAlgHom.toRingHom by
          exact AdjoinRoot.lift_comp_of _]
    rw [powerRootBackward_comp_powerCoordinate]
    rfl
  · change powerRootBackward R n hn
        (powerRootForward R n
          (AdjoinRoot.root (rootPolynomial R[T;T⁻¹]
            (LaurentPolynomial.isUnit_T (R := R) 1).unit n))) = _
    rw [powerRootForward_root, powerRootBackward_T]
    simp [rootUnit_val]

/-- The universal root algebra is the target Laurent ring for substitution `T ↦ T ^ n`. -/
noncomputable def powerRootEquiv (n : ℕ) (hn : n ≠ 0) :
    RootAlgebra R[T;T⁻¹]
        (LaurentPolynomial.isUnit_T (R := R) 1).unit n ≃+* R[T;T⁻¹] :=
  RingEquiv.ofRingHom (powerRootForward R n) (powerRootBackward R n hn)
    (powerRootForward_comp_powerRootBackward R n hn)
    (powerRootBackward_comp_powerRootForward R n hn)

theorem powerRootEquiv_comp_algebraMap (n : ℕ) (hn : n ≠ 0) :
    (powerRootEquiv R n hn).toRingHom.comp
        (algebraMap R[T;T⁻¹]
          (RootAlgebra R[T;T⁻¹]
            (LaurentPolynomial.isUnit_T (R := R) 1).unit n)) =
      (powerCoordinateBialgHom R n).toAlgHom.toRingHom := by
  change (powerRootForward R n).comp
      (algebraMap R[T;T⁻¹]
        (RootAlgebra R[T;T⁻¹]
          (LaurentPolynomial.isUnit_T (R := R) 1).unit n)) = _
  exact AdjoinRoot.lift_comp_of _

/-- Positive-power Laurent substitution is faithfully flat. -/
theorem powerCoordinate_faithfullyFlat [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    (powerCoordinateBialgHom R n).toAlgHom.toRingHom.FaithfullyFlat := by
  rw [← powerRootEquiv_comp_algebraMap R n hn]
  exact RingHom.FaithfullyFlat.respectsIso.1 _ (powerRootEquiv R n hn)
    (rootAlgebra_faithfullyFlat R[T;T⁻¹]
      (LaurentPolynomial.isUnit_T (R := R) 1).unit n hn)

/-- Laurent substitution is finitely presented. -/
theorem powerCoordinate_finitePresentation
    (n : ℕ) (hn : n ≠ 0) :
    (powerCoordinateBialgHom R n).toAlgHom.toRingHom.FinitePresentation := by
  rw [← powerRootEquiv_comp_algebraMap R n hn]
  exact RingHom.finitePresentation_respectsIso.1 _ (powerRootEquiv R n hn)
    (rootAlgebra_finitePresentation R[T;T⁻¹]
      (LaurentPolynomial.isUnit_T (R := R) 1).unit n)

/-- The underlying morphism of the intrinsic geometric power map is the spectrum map of
Laurent substitution. -/
theorem underlyingHom_powerMap_eq_schemeMap (n : ℕ) :
    CommGroupScheme.underlyingHom (powerMap R n) =
      AffineCommGroupScheme.schemeMap (powerMapAffine R n) := by
  rw [← realization_powerMapAffine R n]
  exact AffineCommGroupScheme.realizationFunctor_map_left (powerMapAffine R n)

/-- A positive power map on `G_m` is flat and surjective. -/
theorem powerMap_flat_and_surjective [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    Flat (CommGroupScheme.underlyingHom (powerMap R n)) ∧
      Surjective (CommGroupScheme.underlyingHom (powerMap R n)) := by
  rw [underlyingHom_powerMap_eq_schemeMap R n]
  change Flat
      (Spec.map (CommRingCat.ofHom
        (powerCoordinateBialgHom R n).toAlgHom.toRingHom)) ∧
    Surjective
      (Spec.map (CommRingCat.ofHom
        (powerCoordinateBialgHom R n).toAlgHom.toRingHom))
  exact (flat_and_surjective_SpecMap_iff _).mpr
    (powerCoordinate_faithfullyFlat R n hn)

/-- A positive power map on `G_m` is locally of finite presentation. -/
theorem powerMap_locallyOfFinitePresentation
    (n : ℕ) (hn : n ≠ 0) :
    LocallyOfFinitePresentation
      (CommGroupScheme.underlyingHom (powerMap R n)) := by
  rw [underlyingHom_powerMap_eq_schemeMap R n]
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom
      (powerCoordinateBialgHom R n).toAlgHom.toRingHom))
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (powerCoordinate_finitePresentation R n hn)

/-- The actual no-hypothesis fppf quotient presentation of the positive power map on `G_m`.
Its kernel is the canonical scheme-theoretic power kernel. -/
noncomputable def multiplicativePowerFppfQuotientPresentation [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    CommGroupScheme.FppfQuotientPresentation
      (CommGroupScheme.kernelInclusion (powerMap R n)) where
  quotient := AffineCommGroupScheme.multiplicativeScheme R
  project := powerMap R n
  project_flat := (powerMap_flat_and_surjective R n hn).1
  project_surjective := (powerMap_flat_and_surjective R n hn).2
  project_lfp := powerMap_locallyOfFinitePresentation R n hn
  kernelIso := Iso.refl _
  kernelIso_hom_kernelInclusion := by simp

end CommGroupScheme.MultiplicativeKummer
end AlgebraicGeometry
