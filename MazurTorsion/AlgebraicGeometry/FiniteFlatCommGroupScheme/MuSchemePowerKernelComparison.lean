/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Examples
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeKummer
import Mathlib.AlgebraicGeometry.Pullbacks
import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Inclusion

/-!
# The roots-of-unity model is the geometric power kernel

This file compares the finite-free diagonalizable model `muScheme R n` with the canonical
scheme-theoretic kernel of the `n`th-power endomorphism of `G_m`.  The comparison is made by
the actual Hopf-coordinate inclusion and is promoted from its affine-points universal property
to an isomorphism of commutative group schemes.
-/

noncomputable section

open CategoryTheory Opposite WithConv
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace AlgebraicGeometry
namespace CommGroupScheme.MultiplicativeKummer

variable (R : Type) [CommRing R]

/-- The additive-to-multiplicative algebra equivalence preserves the standard basis. -/
@[simp]
theorem toMultiplicativeAlgEquiv_single (M : Type) [AddCommMonoid M]
    (m : M) (r : R) :
    AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) R M
        (AddMonoidAlgebra.single m r) =
      MonoidAlgebra.single (Multiplicative.ofAdd m) r := by
  simp only [AddMonoidAlgebra.toMultiplicativeAlgEquiv, AlgEquiv.coe_mk,
    AddMonoidAlgebra.toMultiplicative, Equiv.coe_fn_mk,
    AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single,
    MonoidAlgebra.ofCoeff_single]

/-- The coordinate algebra map sending the Laurent generator to the standard cyclic
group-algebra generator. -/
noncomputable def muToMultiplicativeAlgHom (n : ℕ) :
    R[T;T⁻¹] →ₐ[R] MonoidAlgebra R (Multiplicative (ZMod n)) :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) R (ZMod n)).toAlgHom.comp
    (AddMonoidAlgebra.mapDomainAlgHom R R (Int.castAddHom (ZMod n)))

@[simp]
theorem muToMultiplicativeAlgHom_T (n : ℕ) (k : ℤ) :
    muToMultiplicativeAlgHom R n (LaurentPolynomial.T k) =
      MonoidAlgebra.single (Multiplicative.ofAdd (k : ZMod n)) 1 := by
  simp only [muToMultiplicativeAlgHom, AlgHom.comp_apply,
    AddMonoidAlgebra.mapDomainAlgHom_apply, LaurentPolynomial.T,
    AddMonoidAlgebra.mapDomain_single]
  exact toMultiplicativeAlgEquiv_single R (ZMod n)
    ((Int.castAddHom (ZMod n)) k) 1

/-- The Hopf-coordinate map underlying the inclusion `mu_n -> G_m`. -/
noncomputable def muToMultiplicativeBialgHom (n : ℕ) :
    R[T;T⁻¹] →ₐc[R] MonoidAlgebra R (Multiplicative (ZMod n)) :=
  BialgHom.ofAlgHom (muToMultiplicativeAlgHom R n)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro k
        change Coalgebra.counit (R := R)
            (muToMultiplicativeAlgHom R n (LaurentPolynomial.T k)) =
          Coalgebra.counit (R := R) (LaurentPolynomial.T k : R[T;T⁻¹])
        rw [muToMultiplicativeAlgHom_T]
        simp
      · ext)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro k
        change Algebra.TensorProduct.map (muToMultiplicativeAlgHom R n)
            (muToMultiplicativeAlgHom R n)
            (Coalgebra.comul (R := R) (LaurentPolynomial.T k : R[T;T⁻¹])) =
          Coalgebra.comul (R := R)
            (muToMultiplicativeAlgHom R n (LaurentPolynomial.T k))
        rw [LaurentPolynomial.comul_T, Algebra.TensorProduct.map_tmul,
          muToMultiplicativeAlgHom_T, MonoidAlgebra.comul_single]
        simp
      · ext)

@[simp]
theorem muToMultiplicativeBialgHom_T (n : ℕ) (k : ℤ) :
    muToMultiplicativeBialgHom R n (LaurentPolynomial.T k) =
      MonoidAlgebra.single (Multiplicative.ofAdd (k : ZMod n)) 1 := by
  exact muToMultiplicativeAlgHom_T R n k

/-- The affine commutative-group morphism `mu_n -> G_m` induced by the cyclic quotient on
character groups. -/
noncomputable def muInclusionAffine (n : ℕ) [NeZero n] :
    (FiniteFlatCommGroupScheme.mu R n).obj ⟶ AffineCommGroupScheme.multiplicative R :=
  (ObjectProperty.homMk (P := cocommutativeHopfProperty R)
    (CommHopfAlgCat.ofHom (muToMultiplicativeBialgHom R n))).op

@[simp]
theorem coordinateMap_muInclusionAffine (n : ℕ) [NeZero n] :
    AffineCommGroupScheme.coordinateMap (muInclusionAffine R n) =
      muToMultiplicativeBialgHom R n := rfl

@[simp]
theorem coordinateMap_muInclusionAffine_T (n : ℕ) [NeZero n] (k : ℤ) :
    AffineCommGroupScheme.coordinateMap (muInclusionAffine R n)
        (LaurentPolynomial.T k) =
      MonoidAlgebra.single (Multiplicative.ofAdd (k : ZMod n)) 1 := by
  have h := DFunLike.congr_fun (coordinateMap_muInclusionAffine R n)
    (LaurentPolynomial.T k)
  exact h.trans (muToMultiplicativeBialgHom_T R n k)

@[simp]
theorem coordinateMap_muInclusionAffine_T_one (n : ℕ) [NeZero n] :
    AffineCommGroupScheme.coordinateMap (muInclusionAffine R n)
        (LaurentPolynomial.T 1) =
      MonoidAlgebra.single (TauCeti.RootsOfUnityGroup.generator n) 1 := by
  rw [coordinateMap_muInclusionAffine_T]
  congr 2
  exact TauCeti.RootsOfUnityGroup.toMultiplicativeZMod_ofAdd_one n

/-- The actual geometric inclusion `mu_n -> G_m`. -/
noncomputable def muInclusion (n : ℕ) [NeZero n] :
    (FiniteFlatCommGroupScheme.muScheme R n).obj ⟶
      AffineCommGroupScheme.multiplicativeScheme R :=
  (AffineCommGroupScheme.realizationFunctor R).map (muInclusionAffine R n)

/-- Mapping an affine geometric point is contravariant composition with the corresponding
Hopf-coordinate map. -/
theorem pointToAlgHom_map_realizationFunctor
    {G H : AffineCommGroupScheme R} (f : G ⟶ H)
    (B : Type) [CommRing B] [Algebra R B]
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

/-- The coordinate algebra map of a `mu_n` point, with the concrete cyclic group algebra
exposed despite the finite-free wrapper. -/
def muPointToConcreteAlgHom
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B]
    (x : (FiniteFlatCommGroupScheme.mu R n).obj.Point B) :
    MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] B := by
  change (FiniteFlatCommGroupScheme.mu R n).obj.coordinates →ₐ[R] B
  exact (FiniteFlatCommGroupScheme.mu R n).obj.pointToAlgHom B x

/-- A concrete cyclic coordinate map gives the corresponding geometric `mu_n` point. -/
def muPointOfConcreteAlgHom
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B]
    (f : MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] B) :
    (FiniteFlatCommGroupScheme.mu R n).obj.Point B := by
  apply (FiniteFlatCommGroupScheme.mu R n).obj.pointOfAlgHom B
  change MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] B
  exact f

@[simp]
theorem muPointToConcreteAlgHom_pointOfConcreteAlgHom
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B]
    (f : MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] B) :
    muPointToConcreteAlgHom R n B (muPointOfConcreteAlgHom R n B f) = f := by
  apply AlgHom.ext
  intro a
  change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom a = f a
  rw [Spec.preimage_map]
  rfl

/-- On affine points, the Hopf-coordinate inclusion is the ordinary inclusion of roots of
unity into the unit group. -/
@[simp]
theorem multiplicativePointMulEquiv_mapPoint_muInclusion
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B]
    (x : (FiniteFlatCommGroupScheme.mu R n).obj.Point B) :
    AffineCommGroupScheme.multiplicativePointMulEquiv R B
        (mapPoint (muInclusion R n)
          (AffineCommGroupScheme.testObject (R := R) B) x) =
      ((TauCeti.RootsOfUnityGroup.pointsMulEquiv n
        (toConv (muPointToConcreteAlgHom R n B x)) :
          rootsOfUnity n B) : Bˣ) := by
  let y := mapPoint (muInclusion R n)
    (AffineCommGroupScheme.testObject (R := R) B) x
  apply Units.ext
  calc
    ((AffineCommGroupScheme.multiplicativePointMulEquiv R B y : Bˣ) : B) =
        (AffineCommGroupScheme.multiplicative R).pointToAlgHom B y
          (LaurentPolynomial.T 1) := by
      change (TauCeti.MultiplicativeGroup.unitOfPoint
          (((AffineCommGroupScheme.multiplicative R).pointMulEquiv B y).ofConv) : B) = _
      rw [TauCeti.MultiplicativeGroup.unitOfPoint_val,
        AffineCommGroupScheme.pointMulEquiv_apply]
    _ = (FiniteFlatCommGroupScheme.mu R n).obj.pointToAlgHom B x
          (AffineCommGroupScheme.coordinateMap (muInclusionAffine R n)
            (LaurentPolynomial.T 1)) := by
      have hmap := pointToAlgHom_map_realizationFunctor R
        (muInclusionAffine R n) B x
      exact congrArg (fun q ↦ q (LaurentPolynomial.T 1)) hmap
    _ = (FiniteFlatCommGroupScheme.mu R n).obj.pointToAlgHom B x
          (MonoidAlgebra.single (TauCeti.RootsOfUnityGroup.generator n) 1) := by
      exact congrArg ((FiniteFlatCommGroupScheme.mu R n).obj.pointToAlgHom B x)
        (coordinateMap_muInclusionAffine_T_one R n)
    _ = (((TauCeti.RootsOfUnityGroup.pointsMulEquiv n
        (toConv (muPointToConcreteAlgHom R n B x)) :
          rootsOfUnity n B) : Bˣ) : B) := by
      rw [TauCeti.RootsOfUnityGroup.pointsMulEquiv_apply]
      rfl

/-- The geometric `mu_n` inclusion is injective on every affine test object. -/
theorem mapPoint_muInclusion_injective
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B] :
    Function.Injective
      (fun x : (FiniteFlatCommGroupScheme.mu R n).obj.Point B ↦
        mapPoint (muInclusion R n)
          (AffineCommGroupScheme.testObject (R := R) B) x) := by
  intro x y hxy
  have hu := congrArg
    (AffineCommGroupScheme.multiplicativePointMulEquiv R B) hxy
  rw [multiplicativePointMulEquiv_mapPoint_muInclusion,
    multiplicativePointMulEquiv_mapPoint_muInclusion] at hu
  have hroots :
      TauCeti.RootsOfUnityGroup.pointsMulEquiv n
          (toConv (muPointToConcreteAlgHom R n B x)) =
        TauCeti.RootsOfUnityGroup.pointsMulEquiv n
          (toConv (muPointToConcreteAlgHom R n B y)) := by
    apply Subtype.ext
    exact hu
  have hconv := (TauCeti.RootsOfUnityGroup.pointsMulEquiv
    (R := R) (A := B) n).injective hroots
  have halg : muPointToConcreteAlgHom R n B x =
      muPointToConcreteAlgHom R n B y :=
    congrArg WithConv.ofConv hconv
  have hpre : Spec.preimage x.left = Spec.preimage y.left := by
    apply CommRingCat.hom_ext
    exact congrArg (fun f ↦ f.toRingHom) halg
  apply Over.OverMorphism.ext
  rw [← Spec.map_preimage x.left, ← Spec.map_preimage y.left, hpre]

/-- Every affine `mu_n` point maps to a multiplicative point killed by the `n`th-power map. -/
theorem mapPoint_powerMap_muInclusion_eq_one
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B]
    (x : (FiniteFlatCommGroupScheme.mu R n).obj.Point B) :
    mapPoint (powerMap R n) (AffineCommGroupScheme.testObject (R := R) B)
        (mapPoint (muInclusion R n)
          (AffineCommGroupScheme.testObject (R := R) B) x) = 1 := by
  rw [CommGroupScheme.mapPoint_powerEnd]
  apply (AffineCommGroupScheme.multiplicativePointMulEquiv R B).injective
  rw [map_pow, map_one, multiplicativePointMulEquiv_mapPoint_muInclusion]
  exact (mem_rootsOfUnity n _).mp
    (SetLike.coe_mem (TauCeti.RootsOfUnityGroup.pointsMulEquiv n
      (toConv (muPointToConcreteAlgHom R n B x))))

/-- The represented affine-point sequence `mu_n -> G_m -> G_m` is exact. -/
theorem muInclusion_powerMap_mulExact
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B] :
    Function.MulExact
      (mapPoint (muInclusion R n)
        (AffineCommGroupScheme.testObject (R := R) B) :
          (FiniteFlatCommGroupScheme.mu R n).obj.Point B →*
            (AffineCommGroupScheme.multiplicativeScheme R).Point
              (AffineCommGroupScheme.testObject (R := R) B))
      (mapPoint (powerMap R n)
        (AffineCommGroupScheme.testObject (R := R) B)) := by
  intro q
  constructor
  · intro hq
    let u := AffineCommGroupScheme.multiplicativePointMulEquiv R B q
    have hu : u ^ n = 1 := by
      rw [← map_pow, ← CommGroupScheme.mapPoint_powerEnd]
      rw [hq, map_one]
    let zeta : rootsOfUnity n B := ⟨u, (mem_rootsOfUnity n _).mpr hu⟩
    let f : WithConv
        (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] B) :=
      (TauCeti.RootsOfUnityGroup.pointsMulEquiv
        (R := R) (A := B) n).symm zeta
    let z := muPointOfConcreteAlgHom R n B f.ofConv
    refine ⟨z, ?_⟩
    apply (AffineCommGroupScheme.multiplicativePointMulEquiv R B).injective
    rw [multiplicativePointMulEquiv_mapPoint_muInclusion]
    change ((TauCeti.RootsOfUnityGroup.pointsMulEquiv n
      (toConv (muPointToConcreteAlgHom R n B z)) : rootsOfUnity n B) : Bˣ) = u
    rw [muPointToConcreteAlgHom_pointOfConcreteAlgHom]
    change (((TauCeti.RootsOfUnityGroup.pointsMulEquiv
      (R := R) (A := B) n) f : rootsOfUnity n B) : Bˣ) = u
    rw [show (TauCeti.RootsOfUnityGroup.pointsMulEquiv
      (R := R) (A := B) n) f = zeta by
        exact MulEquiv.apply_symm_apply _ zeta]
  · rintro ⟨x, rfl⟩
    exact mapPoint_powerMap_muInclusion_eq_one R n B x

/-- The zero ambient group-scheme morphism from `mu_n` to `G_m`. -/
noncomputable def muToMultiplicativeZero
    (n : ℕ) [NeZero n] :
    (FiniteFlatCommGroupScheme.muScheme R n).obj ⟶
      AffineCommGroupScheme.multiplicativeScheme R :=
  InducedCategory.homMk
    ((default : (FiniteFlatCommGroupScheme.muScheme R n).obj.toGrp ⟶
        Grp.trivial (Over (Spec (.of R)))) ≫
      (default : Grp.trivial (Over (Spec (.of R))) ⟶
        (AffineCommGroupScheme.multiplicativeScheme R).toGrp))

/-- Scheme-theoretically, the power map annihilates the Hopf-coordinate inclusion. -/
theorem muInclusion_comp_powerMap
    (n : ℕ) [NeZero n] :
    muInclusion R n ≫ powerMap R n =
      muToMultiplicativeZero R n := by
  ext
  have h := mapPoint_powerMap_muInclusion_eq_one R n
    (FiniteFlatCommGroupScheme.mu R n).coordinates
    (CategoryStruct.id (FiniteFlatCommGroupScheme.muScheme R n).obj.X)
  change (((CategoryStruct.id
      (FiniteFlatCommGroupScheme.muScheme R n).obj.X) ≫
        (muInclusion R n).hom.hom.hom) ≫
      (powerMap R n).hom.hom.hom) = 1 at h
  have hleft := congrArg Over.Hom.left h
  change _ = (FiniteFlatCommGroupScheme.muScheme R n).obj.X.hom ≫
    η[(AffineCommGroupScheme.multiplicativeScheme R).X].left at hleft
  change _ = (FiniteFlatCommGroupScheme.muScheme R n).obj.X.hom ≫
    η[(AffineCommGroupScheme.multiplicativeScheme R).X].left
  simpa using hleft

private theorem muInclusion_zero_grp
    (n : ℕ) [NeZero n] :
    (muInclusion R n).hom ≫ (powerMap R n).hom =
      (default : (FiniteFlatCommGroupScheme.muScheme R n).obj.toGrp ⟶
        Grp.trivial (Over (Spec (.of R)))) ≫
        CommGroupScheme.kernelZero
          (AffineCommGroupScheme.multiplicativeScheme R) := by
  have h := congrArg (fun q ↦ q.hom) (muInclusion_comp_powerMap R n)
  simpa [muToMultiplicativeZero] using h

/-- The canonical comparison from the finite-free roots-of-unity model to the ambient power
kernel. -/
noncomputable def muSchemeToPowerKernel
    (n : ℕ) [NeZero n] :
    (FiniteFlatCommGroupScheme.muScheme R n).obj ⟶ powerKernel R n := by
  apply InducedCategory.homMk
  exact pullback.lift (muInclusion R n).hom default
    (muInclusion_zero_grp R n)

@[reassoc]
theorem muSchemeToPowerKernel_comp_kernelInclusion
    (n : ℕ) [NeZero n] :
    muSchemeToPowerKernel R n ≫
        CommGroupScheme.kernelInclusion (powerMap R n) =
      muInclusion R n := by
  apply CommGrp.hom_ext
  have hlift := pullback.lift_fst (muInclusion R n).hom
    (default : (FiniteFlatCommGroupScheme.muScheme R n).obj.toGrp ⟶
      Grp.trivial (Over (Spec (.of R)))) (muInclusion_zero_grp R n)
  exact congrArg (fun q ↦ q.hom.hom) hlift

/-- On every affine test object, the comparison with the canonical power kernel is bijective. -/
theorem muSchemeToPowerKernel_point_bijective
    (n : ℕ) [NeZero n]
    (B : Type) [CommRing B] [Algebra R B] :
    Function.Bijective
      (mapPoint (muSchemeToPowerKernel R n)
        (AffineCommGroupScheme.testObject (R := R) B) :
          (FiniteFlatCommGroupScheme.mu R n).obj.Point B →*
            (powerKernel R n).Point
              (AffineCommGroupScheme.testObject (R := R) B)) := by
  constructor
  · intro x y hxy
    apply mapPoint_muInclusion_injective R n B
    have h := congrArg
      (mapPoint (CommGroupScheme.kernelInclusion (powerMap R n))
        (AffineCommGroupScheme.testObject (R := R) B)) hxy
    simpa only [← MonoidHom.comp_apply, ← CommGroupScheme.mapPoint_comp,
      muSchemeToPowerKernel_comp_kernelInclusion] using h
  · intro y
    let q := mapPoint (CommGroupScheme.kernelInclusion (powerMap R n))
      (AffineCommGroupScheme.testObject (R := R) B) y
    have hq : mapPoint (powerMap R n)
        (AffineCommGroupScheme.testObject (R := R) B) q = 1 :=
      CommGroupScheme.mapPoint_kernelInclusion_eq_one (powerMap R n)
        (AffineCommGroupScheme.testObject (R := R) B) y
    obtain ⟨x, hx⟩ := (muInclusion_powerMap_mulExact R n B q).mp hq
    refine ⟨x, ?_⟩
    apply CommGroupScheme.kernelInclusion_point_injective (powerMap R n)
      (AffineCommGroupScheme.testObject (R := R) B)
    calc
      mapPoint (CommGroupScheme.kernelInclusion (powerMap R n))
          (AffineCommGroupScheme.testObject (R := R) B)
          (mapPoint (muSchemeToPowerKernel R n)
            (AffineCommGroupScheme.testObject (R := R) B) x) =
        mapPoint (muInclusion R n)
          (AffineCommGroupScheme.testObject (R := R) B) x := by
            rw [← MonoidHom.comp_apply, ← CommGroupScheme.mapPoint_comp,
              muSchemeToPowerKernel_comp_kernelInclusion]
      _ = q := hx
      _ = mapPoint (CommGroupScheme.kernelInclusion (powerMap R n))
          (AffineCommGroupScheme.testObject (R := R) B) y := rfl

/-- The algebra structure on the global sections of a scheme over `Spec R`. -/
private noncomputable def globalSectionsAlgebraMap
    (T : Over (Spec (.of R))) : R →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ T.hom.appTop).hom

/-- An affine scheme over `Spec R` is canonically isomorphic, over the base, to the affine
test object associated to its global sections. -/
private noncomputable def affineOverIsoTestObject
    (T : Over (Spec (.of R))) [IsAffine T.left] :
    letI := (globalSectionsAlgebraMap R T).toAlgebra
    T ≅ AffineCommGroupScheme.testObject (R := R) Γ(T.left, ⊤) := by
  letI := (globalSectionsAlgebraMap R T).toAlgebra
  exact Over.isoMk T.left.isoSpec (by
    change T.left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (algebraMap R Γ(T.left, ⊤))) = T.hom
    rw [RingHom.algebraMap_toAlgebra]
    change T.left.toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ T.hom.appTop) = T.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp)

/-- The comparison is an isomorphism.  The proof uses its actual affine-points universal
property, applied to the global-section test algebras of source and target. -/
private noncomputable instance muSchemeToPowerKernel_isIso
    (n : ℕ) [NeZero n] : IsIso (muSchemeToPowerKernel R n) := by
  let G := (FiniteFlatCommGroupScheme.muScheme R n).obj
  let H := powerKernel R n
  let f : G.X ⟶ H.X := (muSchemeToPowerKernel R n).hom.hom.hom
  letI : IsAffine G.X.left := by
    change IsAffine
      (Spec (.of (MonoidAlgebra R (Multiplicative (ZMod n)))))
    infer_instance
  letI : IsAffine
      (AffineCommGroupScheme.multiplicativeScheme R).X.left := by
    change IsAffine (Spec (.of R[T;T⁻¹]))
    infer_instance
  letI : IsAffine (𝟙_ (Over (Spec (.of R)))).left := by
    change IsAffine (Spec (.of R))
    infer_instance
  letI : IsAffine H.X.left := by
    letI : IsAffine (CommGroupScheme.kernelScheme (powerMap R n)) := by
      exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
        (CommGroupScheme.underlyingHom (powerMap R n))
        (η[(AffineCommGroupScheme.multiplicativeScheme R).X].left)
    exact IsAffine.of_isIso
      (CommGroupScheme.kernelSchemeIso (powerMap R n)).hom
  let BG := Γ(G.X.left, ⊤)
  let BH := Γ(H.X.left, ⊤)
  letI : Algebra R BG := (globalSectionsAlgebraMap R G.X).toAlgebra
  letI : Algebra R BH := (globalSectionsAlgebraMap R H.X).toAlgebra
  let eG : G.X ≅ AffineCommGroupScheme.testObject (R := R) BG :=
    affineOverIsoTestObject R G.X
  let eH : H.X ≅ AffineCommGroupScheme.testObject (R := R) BH :=
    affineOverIsoTestObject R H.X
  obtain ⟨x, hx⟩ :=
    (muSchemeToPowerKernel_point_bijective R n BH).2 eH.inv
  let g : H.X ⟶ G.X := eH.hom ≫ x
  have hx' : x ≫ f = eH.inv := by
    change x ≫ (muSchemeToPowerKernel R n).hom.hom.hom = eH.inv at hx
    simpa [f] using hx
  have hgf : g ≫ f = 𝟙 H.X := by
    dsimp [g]
    rw [Category.assoc, hx', eH.hom_inv_id]
  have hfg : f ≫ g = 𝟙 G.X := by
    apply (cancel_epi eG.inv).1
    apply (muSchemeToPowerKernel_point_bijective R n BG).1
    change (eG.inv ≫ (f ≫ g)) ≫ f = (eG.inv ≫ 𝟙 G.X) ≫ f
    simp only [Category.assoc, hgf, Category.comp_id]
  let e : G.X ≅ H.X :=
    { hom := f
      inv := g
      hom_inv_id := hfg
      inv_hom_id := hgf }
  haveI : IsIso f := e.isIso_hom
  haveI : IsIso ((Over.forget (Spec (.of R))).map
      (muSchemeToPowerKernel R n).hom.hom.hom) := by
    exact (inferInstance : IsIso ((Over.forget (Spec (.of R))).map f))
  haveI : IsIso (muSchemeToPowerKernel R n).hom.hom.hom :=
    isIso_of_reflects_iso _ (Over.forget (Spec (.of R)))
  haveI : IsIso ((Mon.forget (Over (Spec (.of R)))).map
      (muSchemeToPowerKernel R n).hom.hom) := by
    change IsIso (muSchemeToPowerKernel R n).hom.hom.hom
    infer_instance
  haveI : IsIso (muSchemeToPowerKernel R n).hom.hom :=
    isIso_of_reflects_iso _ (Mon.forget (Over (Spec (.of R))))
  haveI : IsIso ((Grp.forget₂Mon (Over (Spec (.of R)))).map
      (muSchemeToPowerKernel R n).hom) := by
    change IsIso (muSchemeToPowerKernel R n).hom.hom
    infer_instance
  haveI : IsIso (muSchemeToPowerKernel R n).hom :=
    isIso_of_reflects_iso _ (Grp.forget₂Mon (Over (Spec (.of R))))
  haveI : IsIso ((CommGrp.forget₂Grp (Over (Spec (.of R)))).map
      (muSchemeToPowerKernel R n)) := by
    change IsIso (muSchemeToPowerKernel R n).hom
    infer_instance
  exact isIso_of_reflects_iso _ (CommGrp.forget₂Grp (Over (Spec (.of R))))

/-- The finite-free roots-of-unity group scheme is canonically the scheme-theoretic kernel of
the `n`th-power endomorphism of `G_m`. -/
noncomputable def muSchemePowerKernelIso (n : ℕ) [NeZero n] :
    (FiniteFlatCommGroupScheme.muScheme R n).obj ≅ powerKernel R n :=
  asIso (muSchemeToPowerKernel R n)

@[simp]
theorem muSchemePowerKernelIso_hom (n : ℕ) [NeZero n] :
    (muSchemePowerKernelIso R n).hom = muSchemeToPowerKernel R n :=
  rfl

end CommGroupScheme.MultiplicativeKummer
end AlgebraicGeometry
