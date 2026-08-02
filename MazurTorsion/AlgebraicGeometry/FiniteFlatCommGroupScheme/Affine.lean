/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic
import MazurTorsion.Upstream.AINTLIB.ForMathlib.CartierDual
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Affine finite-flat commutative group schemes

This file gives the affine coordinate-algebra side of finite-flat commutative group schemes.  An
affine commutative group scheme over `Spec R` is encoded contravariantly by a commutative,
cocommutative Hopf `R`-algebra.  The crucial bridge is not merely an equality of underlying sets:
`pointMulEquiv` identifies morphisms `Spec B ⟶ Spec A` over `Spec R` with the convolution group
of `R`-algebra maps `A →ₐ[R] B`.

The theorem `AffineFiniteFreeCommGroupScheme.point_pow_order_eq_one` transports the integrated
AINTLIB theorem `deligne_point_pow_eq_one` across this geometric equivalence.  The constant-rank
finite-locally-free version is then obtained by localization at every maximal ideal and descent.

Scalar extension is functorial on the Hopf presentation, compatible with convolution-valued
affine points, compatible with local rank, and compatible with geometric pullback as an
isomorphism of internal commutative group objects.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open WithConv
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- Cocommutative objects in the category of commutative Hopf algebras over `R`. -/
def cocommutativeHopfProperty (R : Type u) [CommRing R] :
    ObjectProperty (CommHopfAlgCat.{u} R) :=
  fun A ↦ Coalgebra.IsCocomm R A

/-- Affine commutative group schemes over `Spec R`, encoded contravariantly by their commutative,
cocommutative coordinate Hopf algebras. -/
abbrev AffineCommGroupScheme (R : Type u) [CommRing R] :=
  ((cocommutativeHopfProperty R).FullSubcategory)ᵒᵖ

namespace AffineCommGroupScheme

variable {R : Type u} [CommRing R]

/-- The coordinate Hopf algebra of an affine commutative group scheme. -/
abbrev coordinates (G : AffineCommGroupScheme R) : CommHopfAlgCat.{u} R := G.unop.obj

instance (G : AffineCommGroupScheme R) : Coalgebra.IsCocomm R G.coordinates :=
  G.unop.property

/-- Relative affine spectrum, from commutative `R`-algebras to schemes over `Spec R`. -/
abbrev relativeSpecFunctor (R : Type u) [CommRing R] :
    (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (Spec (.of R)) :=
  (commAlgCatEquivUnder (CommRingCat.of R)).functor.op ⋙
    (Over.opEquivOpUnder (CommRingCat.of R)).inverse ⋙
      Over.post Scheme.Spec

noncomputable instance : PreservesFiniteProducts (relativeSpecFunctor R) := by
  change PreservesFiniteProducts
    (((commAlgCatEquivUnder (CommRingCat.of R)).functor.op ⋙
      (Over.opEquivOpUnder (CommRingCat.of R)).inverse) ⋙
        Over.post Scheme.Spec)
  infer_instance

/-- Relative affine spectrum is fully faithful. -/
def relativeSpecFullyFaithful : (relativeSpecFunctor R).FullyFaithful := by
  change (((commAlgCatEquivUnder (CommRingCat.of R)).functor.op ⋙
    (Over.opEquivOpUnder (CommRingCat.of R)).inverse) ⋙
      Over.post Scheme.Spec).FullyFaithful
  exact Functor.FullyFaithful.ofFullyFaithful _

noncomputable instance : (relativeSpecFunctor R).Braided :=
  .ofChosenFiniteProducts _

/-- A commutative, cocommutative Hopf algebra as a commutative group object in the opposite
category of commutative algebras.  Its multiplication on points is convolution. -/
abbrev coordinateCommGroup (A : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R A] :
    CommGrp ((CommAlgCat.{u} R)ᵒᵖ) where
  X := Opposite.op (CommAlgCat.of R A)

/-- The underlying affine scheme. -/
abbrev scheme (G : AffineCommGroupScheme R) : Scheme.{u} := Spec (.of G.coordinates)

/-- The structure morphism to `Spec R`. -/
def structureMap (G : AffineCommGroupScheme R) : G.scheme ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates))

/-- The geometric commutative group scheme constructed from the coordinate Hopf algebra. -/
abbrev toCommGroupScheme (G : AffineCommGroupScheme R) : CommGroupScheme (Spec (.of R)) :=
  (relativeSpecFunctor R).mapCommGrp.obj (coordinateCommGroup G.coordinates)

@[simp]
theorem toCommGroupScheme_X_left (G : AffineCommGroupScheme R) :
    G.toCommGroupScheme.X.left = G.scheme := rfl

@[simp]
theorem toCommGroupScheme_X_hom (G : AffineCommGroupScheme R) :
    G.toCommGroupScheme.X.hom = G.structureMap := rfl

/-- The contravariant coordinate map associated to a morphism of affine group schemes. -/
abbrev coordinateMap {G H : AffineCommGroupScheme R} (f : G ⟶ H) :
    H.coordinates →ₐc[R] G.coordinates :=
  f.unop.hom.hom

/-- The underlying morphism of affine schemes. -/
def schemeMap {G H : AffineCommGroupScheme R} (f : G ⟶ H) : G.scheme ⟶ H.scheme :=
  Spec.map (CommRingCat.ofHom (coordinateMap f).toAlgHom.toRingHom)

@[simp]
theorem schemeMap_id (G : AffineCommGroupScheme R) :
    schemeMap (CategoryStruct.id G) = 𝟙 G.scheme := by
  rw [schemeMap, Spec.map_eq_id]
  ext x
  rfl

@[simp]
theorem schemeMap_comp {G H K : AffineCommGroupScheme R} (f : G ⟶ H) (g : H ⟶ K) :
    schemeMap (f ≫ g) = schemeMap f ≫ schemeMap g := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rw [Spec.map_inj]
  ext x
  rfl

@[reassoc (attr := simp)]
theorem schemeMap_comp_structureMap {G H : AffineCommGroupScheme R} (f : G ⟶ H) :
    schemeMap f ≫ H.structureMap = G.structureMap := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rw [Spec.map_inj]
  ext r
  exact (coordinateMap f).toAlgHom.commutes r

/-- Contravariant Hopf morphisms as morphisms of commutative group objects in opposite
commutative algebras. -/
def coordinateCommGroupFunctor (R : Type u) [CommRing R] :
    AffineCommGroupScheme R ⥤ CommGrp ((CommAlgCat.{u} R)ᵒᵖ) where
  obj G := coordinateCommGroup G.coordinates
  map f := by
    let φ : (coordinateCommGroup (R := R) _).X ⟶
        (coordinateCommGroup (R := R) _).X :=
      (CommAlgCat.ofHom f.unop.hom.hom.toAlgHom).op
    exact InducedCategory.homMk (Grp.homMk φ)
  map_id G := by ext; rfl
  map_comp f g := by ext; rfl

/-- Geometric realization of affine commutative group schemes, functorial in Hopf morphisms. -/
def realizationFunctor (R : Type u) [CommRing R] :
    AffineCommGroupScheme R ⥤ CommGroupScheme (Spec (.of R)) :=
  coordinateCommGroupFunctor R ⋙ (relativeSpecFunctor R).mapCommGrp

@[simp]
theorem realizationFunctor_obj (G : AffineCommGroupScheme R) :
    (realizationFunctor R).obj G = G.toCommGroupScheme := rfl

@[simp]
theorem realizationFunctor_map_left {G H : AffineCommGroupScheme R} (f : G ⟶ H) :
    ((realizationFunctor R).map f).hom.hom.hom.left = schemeMap f := rfl

/-- Scalar extension of affine commutative group schemes, functorial in Hopf morphisms. -/
def baseChangeFunctor {K : Type u} [CommRing K] [Algebra R K] :
    AffineCommGroupScheme R ⥤ AffineCommGroupScheme K :=
  ((cocommutativeHopfProperty K).lift
    ((cocommutativeHopfProperty R).ι ⋙
      TauCeti.CommHopfAlgCat.baseChangeFunctor (K := K)) (fun G ↦ by
        letI : Coalgebra.IsCocomm R G.obj := G.property
        change Coalgebra.IsCocomm K (K ⊗[R] G.obj)
        infer_instance)).op

/-- Scalar extension of one affine commutative group scheme. -/
abbrev baseChange {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineCommGroupScheme R) : AffineCommGroupScheme K :=
  (baseChangeFunctor (R := R) (K := K)).obj G

@[simp]
theorem baseChange_coordinates {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineCommGroupScheme R) :
    (G.baseChange (K := K)).coordinates = K ⊗[R] G.coordinates := rfl

@[simp]
theorem baseChange_coordinateMap {K : Type u} [CommRing K] [Algebra R K]
    {G H : AffineCommGroupScheme R} (f : G ⟶ H) :
    coordinateMap ((baseChangeFunctor (R := R) (K := K)).map f) =
      (TauCeti.CommHopfAlgCat.baseChangeMap (K := K) f.unop.hom).hom := rfl

private abbrev geometricCommGroup (R : Type u) [CommRing R]
    (A : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R A] :
    CommGroupScheme (Spec (.of R)) :=
  (relativeSpecFunctor R).mapCommGrp.obj (coordinateCommGroup (R := R) A)

private lemma relativeSpecFunctor_tensorUnit_hom (R : Type u) [CommRing R] :
    ((relativeSpecFunctor R).obj (𝟙_ (CommAlgCat.{u} R)ᵒᵖ)).hom =
      𝟙 (Spec (.of R)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (.of R))
  rw [Spec.map_eq_id]
  ext r
  rfl

private lemma relativeSpecFunctor_ε_left (R : Type u) [CommRing R] :
    (Functor.LaxMonoidal.ε (relativeSpecFunctor R)).left =
      𝟙 (Spec (.of R)) := by
  let q : Spec (.of R) ⟶ Spec (.of R) :=
    (Functor.LaxMonoidal.ε (relativeSpecFunctor R)).left
  change q = 𝟙 (Spec (.of R))
  have h := (Functor.LaxMonoidal.ε (relativeSpecFunctor R)).w
  rw [relativeSpecFunctor_tensorUnit_hom] at h
  change q ≫ 𝟙 (Spec (.of R)) = 𝟙 (Spec (.of R)) at h
  simpa using h

private lemma relativeSpecFunctor_map_fst_left (R : Type u) [CommRing R]
    (A B : CommAlgCat.{u} R) :
    ((relativeSpecFunctor R).map
      (SemiCartesianMonoidalCategory.fst (op A) (op B))).left =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := R) (A := A) (B := B))) := by
  rfl

private lemma relativeSpecFunctor_map_snd_left (R : Type u) [CommRing R]
    (A B : CommAlgCat.{u} R) :
    ((relativeSpecFunctor R).map
      (SemiCartesianMonoidalCategory.snd (op A) (op B))).left =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := R) (A := A) (B := B)).toRingHom) := by
  rfl

private lemma relativeSpecFunctor_μ_left (R : Type u) [CommRing R]
    (A B : CommAlgCat.{u} R) :
    (Functor.LaxMonoidal.μ (relativeSpecFunctor R) (op A) (op B)).left =
      (pullbackSpecIso R A B).hom := by
  let q : pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Spec (.of (TensorProduct R A B)) :=
    (Functor.LaxMonoidal.μ (relativeSpecFunctor R) (op A) (op B)).left
  change q = (pullbackSpecIso R A B).hom
  rw [← cancel_mono (pullbackSpecIso R A B).inv]
  apply pullback.hom_ext
  · have h := congrArg Over.Hom.left
      (Functor.Monoidal.μ_fst (relativeSpecFunctor R) (op A) (op B))
    change q ≫ ((relativeSpecFunctor R).map
      (SemiCartesianMonoidalCategory.fst (op A) (op B))).left =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) at h
    rw [relativeSpecFunctor_map_fst_left] at h
    rw [Iso.hom_inv_id, Category.id_comp]
    rw [Category.assoc, pullbackSpecIso_inv_fst]
    exact h
  · have h := congrArg Over.Hom.left
      (Functor.Monoidal.μ_snd (relativeSpecFunctor R) (op A) (op B))
    change q ≫ ((relativeSpecFunctor R).map
      (SemiCartesianMonoidalCategory.snd (op A) (op B))).left =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) at h
    rw [relativeSpecFunctor_map_snd_left] at h
    rw [Iso.hom_inv_id, Category.id_comp]
    rw [Category.assoc, pullbackSpecIso_inv_snd]
    exact h

private lemma geometricCommGroup_one_left {R : Type u} [CommRing R]
    (A : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R A] :
    η[(geometricCommGroup R A).X].left =
      Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R A).toRingHom) := by
  let q : Spec (.of R) ⟶ Spec (.of A) :=
    ((relativeSpecFunctor R).map η[(coordinateCommGroup (R := R) A).X]).left
  change (Functor.LaxMonoidal.ε (relativeSpecFunctor R)).left ≫ q = _
  rw [relativeSpecFunctor_ε_left]
  change q = _
  rfl

private lemma geometricCommGroup_mul_left {R : Type u} [CommRing R]
    (A : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R A] :
    μ[(geometricCommGroup R A).X].left =
      (pullbackSpecIso R A A).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom R A).toRingHom) := by
  change (Functor.LaxMonoidal.μ (relativeSpecFunctor R)
      (coordinateCommGroup (R := R) A).X
      (coordinateCommGroup (R := R) A).X).left ≫
    ((relativeSpecFunctor R).map
      μ[(coordinateCommGroup (R := R) A).X]).left = _
  rw [relativeSpecFunctor_μ_left]
  rfl

section GeometricBaseChange

variable {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]

local notation "scalarSpecMap" =>
  Spec.map (CommRingCat.ofHom (algebraMap k K))

private def baseChangePullbackIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    ((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X.left ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap :=
  Iso.refl _

private def baseChangeTargetSpecIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    Spec (.of (TensorProduct k K A)) ≅
      (geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X.left :=
  Iso.refl _

private def baseChangeSwappedPullbackIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    ((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X.left ≅
      pullback scalarSpecMap
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  baseChangePullbackIso (K := K) A ≪≫ pullbackSymmetry
    (Spec.map (CommRingCat.ofHom (algebraMap k A))) scalarSpecMap

private lemma baseChangePullbackIso_hom_fst (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    (baseChangePullbackIso (K := K) A).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          scalarSpecMap =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap := by
  rfl

private lemma baseChangePullbackIso_hom_snd (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    (baseChangePullbackIso (K := K) A).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          scalarSpecMap =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap := by
  rfl

private lemma baseChangeSwappedPullbackIso_hom_fst
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (baseChangeSwappedPullbackIso (K := K) A).hom ≫
        pullback.fst scalarSpecMap
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap := by
  change ((baseChangePullbackIso (K := K) A).hom ≫
      (pullbackSymmetry _ _).hom) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
    baseChangePullbackIso_hom_snd]

private lemma baseChangeSwappedPullbackIso_hom_snd
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (baseChangeSwappedPullbackIso (K := K) A).hom ≫
        pullback.snd scalarSpecMap
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap := by
  change ((baseChangePullbackIso (K := K) A).hom ≫
      (pullbackSymmetry _ _).hom) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd,
    baseChangePullbackIso_hom_fst]

private def baseChangeTargetPullbackIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    (geometricCommGroup K
      (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X.left ≅
      pullback scalarSpecMap
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  (baseChangeTargetSpecIso (K := K) A).symm ≪≫
    (pullbackSpecIso k K A).symm

private def baseChangeUnderlyingSchemeIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    ((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X.left ≅
      (geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X.left :=
  baseChangeSwappedPullbackIso (K := K) A ≪≫
    (baseChangeTargetPullbackIso (K := K) A).symm

private lemma baseChangeUnderlyingSchemeIso_hom_comp_targetPullbackIso_hom
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (baseChangeUnderlyingSchemeIso (K := K) A).hom ≫
        (baseChangeTargetPullbackIso (K := K) A).hom =
      (baseChangeSwappedPullbackIso (K := K) A).hom := by
  simp [baseChangeUnderlyingSchemeIso]

private def baseChangeUnderlyingIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    ((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X ≅
      (geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X :=
  Over.isoMk (baseChangeUnderlyingSchemeIso (K := K) A)
    (by
      change (((baseChangeSwappedPullbackIso A).hom ≫
          (pullbackSpecIso k K A).hom) ≫
          (baseChangeTargetSpecIso A).hom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (TensorProduct k K A))) =
        pullback.snd _ _
      change (((baseChangeSwappedPullbackIso A).hom ≫
          (pullbackSpecIso k K A).hom) ≫ 𝟙 _) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (TensorProduct k K A))) =
        pullback.snd _ _
      rw [Category.comp_id]
      rw [Category.assoc, pullbackSpecIso_hom_fst']
      exact baseChangeSwappedPullbackIso_hom_fst (K := K) A)

private lemma baseChange_one_left_fst (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    η[((Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A)).X].left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          scalarSpecMap =
      scalarSpecMap ≫ η[(geometricCommGroup k A).X].left := by
  change ((Functor.LaxMonoidal.ε (Over.pullback scalarSpecMap)) ≫
    (Over.pullback scalarSpecMap).map
      η[(geometricCommGroup k A).X]).left ≫ pullback.fst _ _ = _
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
    pullback.lift_fst]
  have h := pullback.condition
    (f := (𝟙_ (Over (Spec (.of k)))).hom) (g := scalarSpecMap)
  change pullback.fst _ _ = pullback.snd _ _ ≫ scalarSpecMap at h
  rw [h, Category.assoc]
  rw [Over.ε_pullback_left]
  simp

private lemma baseChange_counit_spec (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    scalarSpecMap ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.counitAlgHom k A).toRingHom) =
      Spec.map (CommRingCat.ofHom
          (Bialgebra.counitAlgHom K (TensorProduct k K A)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := k) (A := K) (B := A)).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext a
  change algebraMap k K ((Bialgebra.counitAlgHom k A) a) =
    Bialgebra.counitAlgHom K (TensorProduct k K A) (1 ⊗ₜ[k] a)
  simp [Algebra.smul_def]

private lemma baseChangeUnderlyingIso_one (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    η[((Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A)).X] ≫
        (baseChangeUnderlyingIso (K := K) A).hom =
      η[(geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X] := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  let p : (geometricCommGroup K
      (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X.left ≅
      pullback scalarSpecMap
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    baseChangeTargetPullbackIso A
  let q : ((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X.left ≅
      pullback scalarSpecMap
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    baseChangeSwappedPullbackIso A
  rw [← cancel_mono p.hom]
  rw [Category.assoc]
  change η[((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X].left ≫
      (baseChangeUnderlyingSchemeIso A).hom ≫
        (baseChangeTargetPullbackIso A).hom = _
  rw [baseChangeUnderlyingSchemeIso_hom_comp_targetPullbackIso_hom]
  change η[((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X].left ≫ q.hom =
    η[(geometricCommGroup K
      (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X].left ≫ p.hom
  have q_fst : q.hom ≫ pullback.fst scalarSpecMap
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap := by
    exact baseChangeSwappedPullbackIso_hom_fst (K := K) A
  have q_snd : q.hom ≫ pullback.snd scalarSpecMap
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap := by
    exact baseChangeSwappedPullbackIso_hom_snd (K := K) A
  have p_fst : p.hom ≫ pullback.fst scalarSpecMap
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap K (TensorProduct k K A))) := by
    dsimp [p, baseChangeTargetPullbackIso, baseChangeTargetSpecIso]
    exact pullbackSpecIso_inv_fst' k K A
  have p_snd : p.hom ≫ pullback.snd scalarSpecMap
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := k) (A := K) (B := A)).toRingHom) := by
    dsimp [p, baseChangeTargetPullbackIso, baseChangeTargetSpecIso]
    exact pullbackSpecIso_inv_snd k K A
  apply pullback.hom_ext
  · rw [Category.assoc, q_fst, Category.assoc, p_fst]
    calc
      η[((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X].left ≫ pullback.snd _ _ =
          (𝟙_ (Over (Spec (.of K)))).hom :=
        (η[((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X]).w
      _ = 𝟙 (Spec (.of K)) := rfl
      _ = η[(geometricCommGroup K
          (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X].left ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap K (TensorProduct k K A))) := by
        symm
        exact (η[(geometricCommGroup K
          (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X]).w
  · rw [Category.assoc, q_snd, Category.assoc, p_snd]
    rw [baseChange_one_left_fst]
    rw [geometricCommGroup_one_left, geometricCommGroup_one_left]
    exact baseChange_counit_spec (K := K) A

private def baseChangeProjectionToOld (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    ((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X.left ⟶
      (geometricCommGroup k A).X.left :=
  (baseChangePullbackIso (K := K) A).hom ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      scalarSpecMap

private lemma geometricBaseChange_mul_left_fst
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    μ[((Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A)).X].left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          scalarSpecMap =
      (Functor.LaxMonoidal.μ (Over.pullback scalarSpecMap)
        (geometricCommGroup k A).X (geometricCommGroup k A).X).left ≫
        pullback.fst
          ((geometricCommGroup k A).X ⊗
            (geometricCommGroup k A).X).hom scalarSpecMap ≫
        μ[(geometricCommGroup k A).X].left := by
  change ((Functor.LaxMonoidal.μ (Over.pullback scalarSpecMap)
      (geometricCommGroup k A).X (geometricCommGroup k A).X) ≫
      (Over.pullback scalarSpecMap).map
        μ[(geometricCommGroup k A).X]).left ≫ pullback.fst _ _ = _
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
    pullback.lift_fst]

private abbrev baseChangeCoordinate (A : CommHopfAlgCat.{u} k) :=
  TensorProduct k K A

private def baseChangeFactorLeft (A : CommHopfAlgCat.{u} k) :
    A →ₐ[k]
      (baseChangeCoordinate (K := K) A ⊗[K]
        baseChangeCoordinate (K := K) A) :=
  ((Algebra.TensorProduct.includeLeft
    (R := K) (S := K) (A := baseChangeCoordinate (K := K) A)
      (B := baseChangeCoordinate (K := K) A)).restrictScalars k).comp
    (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A))

private def baseChangeFactorRight (A : CommHopfAlgCat.{u} k) :
    A →ₐ[k]
      (baseChangeCoordinate (K := K) A ⊗[K]
        baseChangeCoordinate (K := K) A) :=
  ((Algebra.TensorProduct.includeRight
    (R := K) (A := baseChangeCoordinate (K := K) A)
      (B := baseChangeCoordinate (K := K) A)).restrictScalars k).comp
    (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A))

private def baseChangeTensorRestriction (A : CommHopfAlgCat.{u} k) :
    (A ⊗[k] A) →ₐ[k]
      (baseChangeCoordinate (K := K) A ⊗[K]
        baseChangeCoordinate (K := K) A) :=
  Algebra.TensorProduct.lift (baseChangeFactorLeft (K := K) A)
    (baseChangeFactorRight (K := K) A) (fun _ _ ↦ .all _ _)

@[simp]
private lemma baseChangeTensorRestriction_tmul (A : CommHopfAlgCat.{u} k)
    (a b : A) :
    baseChangeTensorRestriction (K := K) A (a ⊗ₜ[k] b) =
      ((1 ⊗ₜ[k] a) ⊗ₜ[K] (1 ⊗ₜ[k] b)) := by
  simp [baseChangeTensorRestriction, baseChangeFactorLeft,
    baseChangeFactorRight]

private lemma baseChange_comul_includeRight (A : CommHopfAlgCat.{u} k) :
    ((Bialgebra.comulAlgHom K
        (baseChangeCoordinate (K := K) A)).restrictScalars k).comp
        (Algebra.TensorProduct.includeRight
          (R := k) (A := K) (B := A)) =
      (baseChangeTensorRestriction (K := K) A).comp
        (Bialgebra.comulAlgHom k A) := by
  apply AlgHom.ext
  intro a
  change Coalgebra.comul (R := K) (A := baseChangeCoordinate (K := K) A)
      (1 ⊗ₜ[k] a) =
    baseChangeTensorRestriction (K := K) A (Coalgebra.comul (R := k) a)
  change (Bialgebra.comulAlgHom K (baseChangeCoordinate (K := K) A))
      (1 ⊗ₜ[k] a) = _
  rw [Bialgebra.TensorProduct.comulAlgHom_def]
  simp only [AlgHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  have h : ∀ z : A ⊗[k] A,
      (Algebra.TensorProduct.tensorTensorTensorComm k K k K K K A A)
          (1 ⊗ₜ[k] z) =
        baseChangeTensorRestriction (K := K) A z := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
    | tmul x y =>
        rw [baseChangeTensorRestriction_tmul]
        rw [show (1 : K ⊗[K] K) =
            ((1 : K) ⊗ₜ[K] (1 : K)) by
          exact Algebra.TensorProduct.one_def]
        exact Algebra.TensorProduct.tensorTensorTensorComm_tmul 1 1 x y
  exact h _

private lemma includeLeft_comp_baseChangeTensorRestriction
    (A : CommHopfAlgCat.{u} k) :
    (baseChangeTensorRestriction (K := K) A).comp
        (Algebra.TensorProduct.includeLeft
          (R := k) (S := k) (A := A) (B := A)) =
      ((Algebra.TensorProduct.includeLeft
          (R := K) (S := K)
          (A := baseChangeCoordinate (K := K) A)
          (B := baseChangeCoordinate (K := K) A)).restrictScalars k).comp
        (Algebra.TensorProduct.includeRight
          (R := k) (A := K) (B := A)) := by
  apply AlgHom.ext
  intro a
  simp [baseChangeTensorRestriction, baseChangeFactorLeft,
    baseChangeFactorRight]

private lemma includeRight_comp_baseChangeTensorRestriction
    (A : CommHopfAlgCat.{u} k) :
    (baseChangeTensorRestriction (K := K) A).comp
        (Algebra.TensorProduct.includeRight
          (R := k) (A := A) (B := A)) =
      ((Algebra.TensorProduct.includeRight
          (R := K)
          (A := baseChangeCoordinate (K := K) A)
          (B := baseChangeCoordinate (K := K) A)).restrictScalars k).comp
        (Algebra.TensorProduct.includeRight
          (R := k) (A := K) (B := A)) := by
  apply AlgHom.ext
  intro a
  simp [baseChangeTensorRestriction, baseChangeFactorLeft,
    baseChangeFactorRight]

private abbrev baseChangeTargetProjectionToOld
    (A : CommHopfAlgCat.{u} k) :
    Spec (.of (baseChangeCoordinate (K := K) A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight
      (R := k) (A := K) (B := A)).toRingHom)

private lemma baseChangeTargetProjectionToOld_structure
    (A : CommHopfAlgCat.{u} k) :
    baseChangeTargetProjectionToOld (K := K) A ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom
          (algebraMap K (baseChangeCoordinate (K := K) A))) ≫
        scalarSpecMap := by
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

private def baseChangeTargetProductToOldProduct
    (A : CommHopfAlgCat.{u} k) :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (baseChangeCoordinate (K := K) A))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (baseChangeCoordinate (K := K) A)))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  pullback.lift
    (pullback.fst _ _ ≫ baseChangeTargetProjectionToOld (K := K) A)
    (pullback.snd _ _ ≫ baseChangeTargetProjectionToOld (K := K) A)
    (by
      simp only [Category.assoc, baseChangeTargetProjectionToOld_structure]
      rw [← Category.assoc, pullback.condition, Category.assoc])

private lemma baseChangeTargetProductToOldProduct_fst
    (A : CommHopfAlgCat.{u} k) :
    baseChangeTargetProductToOldProduct (K := K) A ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.fst _ _ ≫
        baseChangeTargetProjectionToOld (K := K) A := by
  exact pullback.lift_fst _ _ _

private lemma baseChangeTargetProductToOldProduct_snd
    (A : CommHopfAlgCat.{u} k) :
    baseChangeTargetProductToOldProduct (K := K) A ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.snd _ _ ≫
        baseChangeTargetProjectionToOld (K := K) A := by
  exact pullback.lift_snd _ _ _

private def baseChangeTargetTensorToOldProduct
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    ((geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X ⊗
      (geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X).left ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  baseChangeTargetProductToOldProduct (K := K) A

private lemma baseChangeTargetTensorToOldProduct_fst
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    baseChangeTargetTensorToOldProduct (K := K) A ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.fst _ _ ≫
        baseChangeTargetProjectionToOld (K := K) A := by
  exact baseChangeTargetProductToOldProduct_fst (K := K) A

private lemma baseChangeTargetTensorToOldProduct_snd
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    baseChangeTargetTensorToOldProduct (K := K) A ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.snd _ _ ≫
        baseChangeTargetProjectionToOld (K := K) A := by
  exact baseChangeTargetProductToOldProduct_snd (K := K) A

private lemma baseChangeTargetProductToOldProduct_spec
    (A : CommHopfAlgCat.{u} k) :
    baseChangeTargetProductToOldProduct (K := K) A ≫
        (pullbackSpecIso k A A).hom =
      (pullbackSpecIso K (baseChangeCoordinate (K := K) A)
          (baseChangeCoordinate (K := K) A)).hom ≫
        Spec.map (CommRingCat.ofHom
          (baseChangeTensorRestriction (K := K) A).toRingHom) := by
  rw [← cancel_mono (pullbackSpecIso k A A).inv]
  apply pullback.hom_ext
  · simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      baseChangeTargetProductToOldProduct_fst,
      pullbackSpecIso_inv_fst]
    rw [← cancel_epi
      (pullbackSpecIso K (baseChangeCoordinate (K := K) A)
        (baseChangeCoordinate (K := K) A)).inv]
    conv_lhs => rw [← Category.assoc, pullbackSpecIso_inv_fst]
    conv_rhs => rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext a
    exact AlgHom.congr_fun
      (includeLeft_comp_baseChangeTensorRestriction (K := K) A).symm a
  · simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      baseChangeTargetProductToOldProduct_snd,
      pullbackSpecIso_inv_snd]
    rw [← cancel_epi
      (pullbackSpecIso K (baseChangeCoordinate (K := K) A)
        (baseChangeCoordinate (K := K) A)).inv]
    conv_lhs => rw [← Category.assoc, pullbackSpecIso_inv_snd]
    conv_rhs => rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext a
    exact AlgHom.congr_fun
      (includeRight_comp_baseChangeTensorRestriction (K := K) A).symm a

private lemma geometricCommGroup_baseChange_mul_projection
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    μ[(geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X].left ≫
        baseChangeTargetProjectionToOld (K := K) A =
      baseChangeTargetProductToOldProduct (K := K) A ≫
        μ[(geometricCommGroup k A).X].left := by
  have hcomul :
      Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom K
            (baseChangeCoordinate (K := K) A)).toRingHom) ≫
          baseChangeTargetProjectionToOld (K := K) A =
        Spec.map (CommRingCat.ofHom
            (baseChangeTensorRestriction (K := K) A).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Bialgebra.comulAlgHom k A).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext a
    exact AlgHom.congr_fun (baseChange_comul_includeRight (K := K) A) a
  rw [geometricCommGroup_mul_left, geometricCommGroup_mul_left]
  change
    ((pullbackSpecIso K (baseChangeCoordinate (K := K) A)
        (baseChangeCoordinate (K := K) A)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Bialgebra.comulAlgHom K
          (baseChangeCoordinate (K := K) A)).toRingHom)) ≫
        baseChangeTargetProjectionToOld (K := K) A =
      baseChangeTargetProductToOldProduct (K := K) A ≫
        ((pullbackSpecIso k A A).hom ≫
          Spec.map (CommRingCat.ofHom
            (Bialgebra.comulAlgHom k A).toRingHom))
  conv_lhs =>
    rw [Category.assoc, hcomul, ← Category.assoc,
      ← baseChangeTargetProductToOldProduct_spec, Category.assoc]

private lemma baseChangeTargetPullbackIso_hom_snd_projection
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (baseChangeTargetPullbackIso (K := K) A).hom ≫
        pullback.snd scalarSpecMap
          (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      baseChangeTargetProjectionToOld (K := K) A := by
  dsimp [baseChangeTargetPullbackIso, baseChangeTargetSpecIso,
    baseChangeTargetProjectionToOld]
  exact pullbackSpecIso_inv_snd k K A

private lemma baseChangeUnderlyingSchemeIso_hom_projection
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (baseChangeUnderlyingSchemeIso (K := K) A).hom ≫
        baseChangeTargetProjectionToOld (K := K) A =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        scalarSpecMap := by
  rw [← baseChangeTargetPullbackIso_hom_snd_projection]
  rw [← Category.assoc,
    baseChangeUnderlyingSchemeIso_hom_comp_targetPullbackIso_hom]
  exact baseChangeSwappedPullbackIso_hom_snd (K := K) A

private def baseChangeTargetProjectionToOldScheme
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X.left ⟶
      (geometricCommGroup k A).X.left :=
  baseChangeTargetProjectionToOld (K := K) A

private lemma baseChangeUnderlyingIso_hom_projection_typed
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (baseChangeUnderlyingIso (K := K) A).hom.left ≫
        baseChangeTargetProjectionToOldScheme (K := K) A =
      baseChangeProjectionToOld (K := K) A := by
  exact baseChangeUnderlyingSchemeIso_hom_projection (K := K) A

private def baseChangeTargetTensorToOldTensor
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    ((geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X ⊗
      (geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X).left ⟶
      ((geometricCommGroup k A).X ⊗
        (geometricCommGroup k A).X).left :=
  baseChangeTargetProductToOldProduct (K := K) A

private lemma baseChangeTargetTensorToOldTensor_fst
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    baseChangeTargetTensorToOldTensor (K := K) A ≫
        (CartesianMonoidalCategory.fst
          (geometricCommGroup k A).X
          (geometricCommGroup k A).X).left =
      (CartesianMonoidalCategory.fst
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X).left ≫
        baseChangeTargetProjectionToOldScheme (K := K) A := by
  exact baseChangeTargetProductToOldProduct_fst (K := K) A

private lemma baseChangeTargetTensorToOldTensor_snd
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    baseChangeTargetTensorToOldTensor (K := K) A ≫
        (CartesianMonoidalCategory.snd
          (geometricCommGroup k A).X
          (geometricCommGroup k A).X).left =
      (CartesianMonoidalCategory.snd
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X).left ≫
        baseChangeTargetProjectionToOldScheme (K := K) A := by
  exact baseChangeTargetProductToOldProduct_snd (K := K) A

private lemma baseChange_product_projection_compatibility
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (Functor.LaxMonoidal.μ (Over.pullback scalarSpecMap)
        (geometricCommGroup k A).X (geometricCommGroup k A).X).left ≫
        pullback.fst
          ((pullback.fst (geometricCommGroup k A).X.hom
              (geometricCommGroup k A).X.hom) ≫
            (geometricCommGroup k A).X.hom) scalarSpecMap =
      ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
        baseChangeTargetTensorToOldTensor (K := K) A := by
  have hfirst :
      (Functor.LaxMonoidal.μ (Over.pullback scalarSpecMap)
        (geometricCommGroup k A).X (geometricCommGroup k A).X).left ≫
          pullback.fst
            ((pullback.fst (geometricCommGroup k A).X.hom
                (geometricCommGroup k A).X.hom) ≫
              (geometricCommGroup k A).X.hom) scalarSpecMap ≫
          pullback.fst (geometricCommGroup k A).X.hom
            (geometricCommGroup k A).X.hom =
        pullback.fst
            (pullback.snd (geometricCommGroup k A).X.hom scalarSpecMap)
            (pullback.snd (geometricCommGroup k A).X.hom scalarSpecMap) ≫
          pullback.fst (geometricCommGroup k A).X.hom scalarSpecMap := by
    exact Over.μ_pullback_left_fst_fst' (f := scalarSpecMap)
      (geometricCommGroup k A).X.hom (geometricCommGroup k A).X.hom
  have hsecond :
      (Functor.LaxMonoidal.μ (Over.pullback scalarSpecMap)
        (geometricCommGroup k A).X (geometricCommGroup k A).X).left ≫
          pullback.fst
            ((pullback.fst (geometricCommGroup k A).X.hom
                (geometricCommGroup k A).X.hom) ≫
              (geometricCommGroup k A).X.hom) scalarSpecMap ≫
          pullback.snd (geometricCommGroup k A).X.hom
            (geometricCommGroup k A).X.hom =
        pullback.snd
            (pullback.snd (geometricCommGroup k A).X.hom scalarSpecMap)
            (pullback.snd (geometricCommGroup k A).X.hom scalarSpecMap) ≫
          pullback.fst (geometricCommGroup k A).X.hom scalarSpecMap := by
    exact Over.μ_pullback_left_fst_snd' (f := scalarSpecMap)
      (geometricCommGroup k A).X.hom (geometricCommGroup k A).X.hom
  have htensor_fst :
      ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
        (CartesianMonoidalCategory.fst
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X).left =
      (CartesianMonoidalCategory.fst
        ((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X
        ((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X).left ≫
        (baseChangeUnderlyingIso (K := K) A).hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left
      (CartesianMonoidalCategory.tensorHom_fst
        (baseChangeUnderlyingIso (K := K) A).hom
        (baseChangeUnderlyingIso (K := K) A).hom)
  have htensor_snd :
      ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
        (CartesianMonoidalCategory.snd
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X
          (geometricCommGroup K
            (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X).left =
      (CartesianMonoidalCategory.snd
        ((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X
        ((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X).left ≫
        (baseChangeUnderlyingIso (K := K) A).hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left
      (CartesianMonoidalCategory.tensorHom_snd
        (baseChangeUnderlyingIso (K := K) A).hom
        (baseChangeUnderlyingIso (K := K) A).hom)
  have hrightfirst :
      (((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
        baseChangeTargetTensorToOldTensor (K := K) A) ≫
          (CartesianMonoidalCategory.fst
            (geometricCommGroup k A).X
            (geometricCommGroup k A).X).left =
        (CartesianMonoidalCategory.fst
          ((Over.pullback scalarSpecMap).mapCommGrp.obj
            (geometricCommGroup k A)).X
          ((Over.pullback scalarSpecMap).mapCommGrp.obj
            (geometricCommGroup k A)).X).left ≫
            baseChangeProjectionToOld (K := K) A := by
    rw [Category.assoc, baseChangeTargetTensorToOldTensor_fst,
      ← Category.assoc, htensor_fst, Category.assoc,
      baseChangeUnderlyingIso_hom_projection_typed]
  have hrightsecond :
      (((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
        baseChangeTargetTensorToOldTensor (K := K) A) ≫
          (CartesianMonoidalCategory.snd
            (geometricCommGroup k A).X
            (geometricCommGroup k A).X).left =
        (CartesianMonoidalCategory.snd
          ((Over.pullback scalarSpecMap).mapCommGrp.obj
            (geometricCommGroup k A)).X
          ((Over.pullback scalarSpecMap).mapCommGrp.obj
            (geometricCommGroup k A)).X).left ≫
            baseChangeProjectionToOld (K := K) A := by
    rw [Category.assoc, baseChangeTargetTensorToOldTensor_snd,
      ← Category.assoc, htensor_snd, Category.assoc,
      baseChangeUnderlyingIso_hom_projection_typed]
  apply pullback.hom_ext
  · exact hfirst.trans hrightfirst.symm
  · exact hsecond.trans hrightsecond.symm

private def baseChangeSourceTensorToOldTensor
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    (((Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A)).X ⊗
      ((Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A)).X).left ⟶
      ((geometricCommGroup k A).X ⊗
        (geometricCommGroup k A).X).left :=
  (Functor.LaxMonoidal.μ (Over.pullback scalarSpecMap)
      (geometricCommGroup k A).X (geometricCommGroup k A).X).left ≫
    pullback.fst
      ((pullback.fst (geometricCommGroup k A).X.hom
          (geometricCommGroup k A).X.hom) ≫
        (geometricCommGroup k A).X.hom) scalarSpecMap

private lemma geometricBaseChange_mul_projection_typed
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    μ[((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X].left ≫
        baseChangeProjectionToOld (K := K) A =
      baseChangeSourceTensorToOldTensor (K := K) A ≫
        μ[(geometricCommGroup k A).X].left := by
  exact geometricBaseChange_mul_left_fst (K := K) A

private lemma baseChange_tensor_projection_compatibility_typed
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    baseChangeSourceTensorToOldTensor (K := K) A =
      ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
        baseChangeTargetTensorToOldTensor (K := K) A := by
  exact baseChange_product_projection_compatibility (K := K) A

private lemma geometricCommGroup_baseChange_mul_projection_typed
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] :
    μ[(geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X].left ≫
        baseChangeTargetProjectionToOldScheme (K := K) A =
      baseChangeTargetTensorToOldTensor (K := K) A ≫
        μ[(geometricCommGroup k A).X].left := by
  exact geometricCommGroup_baseChange_mul_projection (K := K) A

private lemma baseChangeUnderlyingIso_mul (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    μ[((Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A)).X] ≫
        (baseChangeUnderlyingIso (K := K) A).hom =
      ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
        (baseChangeUnderlyingIso (K := K) A).hom) ≫
        μ[(geometricCommGroup K
          (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X] := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  let p : (geometricCommGroup K
      (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X.left ≅
      pullback scalarSpecMap
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    baseChangeTargetPullbackIso A
  rw [← cancel_mono p.hom]
  apply pullback.hom_ext
  · have hp : p.hom ≫ pullback.fst scalarSpecMap
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
        (geometricCommGroup K
          (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X.hom := by
      dsimp [p, baseChangeTargetPullbackIso, baseChangeTargetSpecIso]
      exact pullbackSpecIso_inv_fst' k K A
    simp only [Category.assoc, hp]
    exact ((μ[((Over.pullback scalarSpecMap).mapCommGrp.obj
      (geometricCommGroup k A)).X] ≫
        (baseChangeUnderlyingIso (K := K) A).hom).w).trans
      ((((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom) ≫
        μ[(geometricCommGroup K
          (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X]).w).symm
  · have hpold : p.hom ≫ pullback.snd scalarSpecMap
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
        baseChangeTargetProjectionToOldScheme (K := K) A := by
      exact baseChangeTargetPullbackIso_hom_snd_projection (K := K) A
    simp only [Category.assoc, hpold]
    change
      μ[((Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A)).X].left ≫
          ((baseChangeUnderlyingIso (K := K) A).hom.left ≫
            baseChangeTargetProjectionToOldScheme (K := K) A) =
        ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
          (μ[(geometricCommGroup K
              (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X].left ≫
            baseChangeTargetProjectionToOldScheme (K := K) A)
    calc
      μ[((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X].left ≫
          ((baseChangeUnderlyingIso (K := K) A).hom.left ≫
            baseChangeTargetProjectionToOldScheme (K := K) A) =
        μ[((Over.pullback scalarSpecMap).mapCommGrp.obj
          (geometricCommGroup k A)).X].left ≫
          baseChangeProjectionToOld (K := K) A := by
            rw [baseChangeUnderlyingIso_hom_projection_typed]
      _ = baseChangeSourceTensorToOldTensor (K := K) A ≫
            μ[(geometricCommGroup k A).X].left := by
              exact geometricBaseChange_mul_projection_typed (K := K) A
      _ = (((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
            baseChangeTargetTensorToOldTensor (K := K) A) ≫
          μ[(geometricCommGroup k A).X].left := by
            rw [baseChange_tensor_projection_compatibility_typed]
      _ = ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
          (baseChangeTargetTensorToOldTensor (K := K) A ≫
            μ[(geometricCommGroup k A).X].left) := Category.assoc _ _ _
      _ = ((baseChangeUnderlyingIso (K := K) A).hom ⊗ₘ
          (baseChangeUnderlyingIso (K := K) A).hom).left ≫
          (μ[(geometricCommGroup K
              (TauCeti.CommHopfAlgCat.baseChange (K := K) A)).X].left ≫
            baseChangeTargetProjectionToOldScheme (K := K) A) := by
              rw [geometricCommGroup_baseChange_mul_projection_typed]

private def baseChangeCommGroupIso (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] :
    (Over.pullback scalarSpecMap).mapCommGrp.obj
        (geometricCommGroup k A) ≅
      geometricCommGroup K
        (TauCeti.CommHopfAlgCat.baseChange (K := K) A) :=
  CommGrp.mkIso (baseChangeUnderlyingIso (K := K) A)
    (baseChangeUnderlyingIso_one (K := K) A)
    (baseChangeUnderlyingIso_mul (K := K) A)

/-- The affine spectrum of scalar-extended Hopf coordinates is canonically the geometric
pullback of the original affine spectrum. -/
def baseChangeSchemeIso (G : AffineCommGroupScheme k) :
    pullback G.structureMap scalarSpecMap ≅
      (G.baseChange (K := K)).scheme :=
  baseChangeUnderlyingSchemeIso (K := K) G.coordinates

/-- Scalar extension on affine Hopf coordinates agrees with geometric base change as an
isomorphism of internal commutative group schemes, not just as an isomorphism of schemes. -/
def realizationBaseChangeIso (G : AffineCommGroupScheme k) :
    (Over.pullback scalarSpecMap).mapCommGrp.obj G.toCommGroupScheme ≅
      (G.baseChange (K := K)).toCommGroupScheme :=
  baseChangeCommGroupIso (K := K) G.coordinates

end GeometricBaseChange

/-- `Spec B` as an object over `Spec R`. -/
def testObject (B : Type u) [CommRing B] [Algebra R B] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))

/-- The affine test-scheme points of `G`, expressed geometrically as morphisms over `Spec R`. -/
abbrev Point (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :=
  testObject (R := R) B ⟶ G.toCommGroupScheme.X

/-- Affine points carry the canonical group law induced by the constructed internal group
scheme.  This globally exposes the same instance that is otherwise available only in the
`CategoryTheory.MonObj` scope. -/
noncomputable instance pointCommGroup (G : AffineCommGroupScheme R)
    (B : Type u) [CommRing B] [Algebra R B] : CommGroup (G.Point B) :=
  CategoryTheory.Hom.commGroup

/-- Recover the coordinate `R`-algebra map from a geometric affine point. -/
def pointToAlgHom (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point B) : G.coordinates →ₐ[R] B :=
  let xleft : Spec (.of B) ⟶ Spec (.of G.coordinates) := x.left
  { (Spec.preimage xleft).hom with
    commutes' := by
      intro r
      have h := congrArg Spec.preimage x.w
      rw [toCommGroupScheme_X_hom] at h
      change Spec.preimage (xleft ≫ G.structureMap) =
        Spec.preimage (testObject (R := R) B).hom at h
      rw [Spec.preimage_comp] at h
      simpa [structureMap, testObject, xleft] using
        congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of B ↦ f.hom r) h }

/-- Turn a coordinate `R`-algebra map into a morphism of affine schemes over `Spec R`. -/
def pointOfAlgHom (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B]
    (f : G.coordinates →ₐ[R] B) : G.Point B :=
  by
    change testObject (R := R) B ⟶ Over.mk G.structureMap
    exact Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      rw [Spec.map_inj]
      ext r
      exact f.commutes r)

/-- Geometric affine points are exactly coordinate-algebra maps. -/
def pointEquiv (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :
    G.Point B ≃ WithConv (G.coordinates →ₐ[R] B) where
  toFun x := toConv (G.pointToAlgHom B x)
  invFun f := G.pointOfAlgHom B f.ofConv
  left_inv x := by
    apply Over.OverMorphism.ext
    exact Spec.map_preimage x.left
  right_inv f := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom))).hom a = f.ofConv a
    rw [Spec.preimage_map]
    rfl

/-- Algebra maps out of a Hopf algebra are the points of its opposite-algebra group object. -/
def coordinatePointEquiv (A : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R A]
    (B : Type u) [CommRing B] [Algebra R B] :
    (Opposite.op (CommAlgCat.of R B) ⟶ (coordinateCommGroup (R := R) A).X) ≃
      WithConv (A →ₐ[R] B) where
  toFun f := toConv f.unop.hom
  invFun f := (CommAlgCat.ofHom f.ofConv).op
  left_inv f := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    rfl
  right_inv f := by
    apply WithConv.ofConv_injective
    rfl

/-- The preceding point equivalence respects the actual internal group law and convolution. -/
def coordinatePointMulEquiv (A : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R A]
    (B : Type u) [CommRing B] [Algebra R B] :
    (Opposite.op (CommAlgCat.of R B) ⟶ (coordinateCommGroup (R := R) A).X) ≃*
      WithConv (A →ₐ[R] B) where
  __ := coordinatePointEquiv (R := R) A B
  map_mul' x y := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    change (x * y).unop.hom a =
      ((toConv x.unop.hom) * (toConv y.unop.hom)).ofConv a
    rw [AlgHom.convMul_apply, CategoryTheory.Hom.mul_def]
    simp only [unop_comp, CommAlgCat.hom_comp, CommAlgCat.mul_op_of_unop_hom,
      CommAlgCat.lift_unop_hom, AlgHom.comp_apply]
    rw [Bialgebra.comulAlgHom_apply]

/-- Full faithfulness of relative spectrum respects multiplication on group-valued hom-sets. -/
def relativeSpecPointMulEquiv (A : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R A]
    (B : Type u) [CommRing B] [Algebra R B] :
    (Opposite.op (CommAlgCat.of R B) ⟶ (coordinateCommGroup (R := R) A).X) ≃*
      (testObject (R := R) B ⟶
        ((relativeSpecFunctor R).mapCommGrp.obj (coordinateCommGroup (R := R) A)).X) where
  __ := (relativeSpecFullyFaithful (R := R)).homEquiv
  map_mul' x y := (relativeSpecFunctor R).map_mul x y

/-- The affine point equivalence respects the geometric group law and convolution. -/
def pointMulEquiv (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :
    G.Point B ≃* WithConv (G.coordinates →ₐ[R] B) :=
  (relativeSpecPointMulEquiv (R := R) G.coordinates B).symm.trans
    (coordinatePointMulEquiv (R := R) G.coordinates B)

@[simp]
theorem pointMulEquiv_apply (G : AffineCommGroupScheme R)
    (B : Type u) [CommRing B] [Algebra R B] (x : G.Point B) :
    G.pointMulEquiv B x = toConv (G.pointToAlgHom B x) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  let x' : (relativeSpecFunctor R).obj (Opposite.op (CommAlgCat.of R B)) ⟶
      (relativeSpecFunctor R).obj
        (Opposite.op (CommAlgCat.of R G.coordinates)) := x
  let f := (relativeSpecFullyFaithful (R := R)).preimage x'
  change f.unop.hom a = (Spec.preimage x.left).hom a
  have hx := (relativeSpecFullyFaithful (R := R)).map_preimage x'
  dsimp [relativeSpecFunctor, f, x'] at hx
  have hleft : Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) = x.left :=
    congrArg Over.Hom.left hx
  have hpre := congrArg Spec.preimage hleft
  calc
    f.unop.hom a =
        (Spec.preimage (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom))).hom a := by
      rw [Spec.preimage_map]
      rfl
    _ = (Spec.preimage x.left).hom a := congrArg
      (fun g : CommRingCat.of G.coordinates ⟶ CommRingCat.of B ↦ g.hom a) hpre

/-- Points of a scalar-extended affine group scheme agree, as a group, with the original
points after restricting scalars on the value algebra. -/
def baseChangePointMulEquiv {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineCommGroupScheme R)
    (B : Type u) [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower R K B] :
    (G.baseChange (K := K)).Point B ≃* G.Point B :=
  ((G.baseChange (K := K)).pointMulEquiv B).trans
    ((TauCeti.AlgHom.baseChangePointsMulEquiv
      (k := R) (K := K) (A := G.coordinates) (R := B)).symm.trans
        (G.pointMulEquiv B).symm)

@[simp]
theorem pointMulEquiv_baseChangePointMulEquiv
    {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineCommGroupScheme R)
    (B : Type u) [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower R K B]
    (x : (G.baseChange (K := K)).Point B) :
    G.pointMulEquiv B (G.baseChangePointMulEquiv B x) =
      (TauCeti.AlgHom.baseChangePointsMulEquiv
        (k := R) (K := K) (A := G.coordinates) (R := B)).symm
          ((G.baseChange (K := K)).pointMulEquiv B x) := by
  change G.pointMulEquiv B ((G.pointMulEquiv B).symm
    ((TauCeti.AlgHom.baseChangePointsMulEquiv
      (k := R) (K := K) (A := G.coordinates) (R := B)).symm
        ((G.baseChange (K := K)).pointMulEquiv B x))) = _
  exact (G.pointMulEquiv B).apply_symm_apply _

end AffineCommGroupScheme

/-- The property that the coordinate algebra is finite free over the base. -/
def affineFiniteFreeProperty (R : Type u) [CommRing R] :
    ObjectProperty (AffineCommGroupScheme R) :=
  fun G ↦ Module.Free R G.coordinates ∧ Module.Finite R G.coordinates

/-- Affine commutative group schemes with finite-free coordinate algebra. -/
abbrev AffineFiniteFreeCommGroupScheme (R : Type u) [CommRing R] :=
  (affineFiniteFreeProperty R).FullSubcategory

namespace AffineFiniteFreeCommGroupScheme

variable {R : Type u} [CommRing R]

abbrev toAffineCommGroupScheme (G : AffineFiniteFreeCommGroupScheme R) := G.obj
abbrev coordinates (G : AffineFiniteFreeCommGroupScheme R) := G.obj.coordinates
abbrev scheme (G : AffineFiniteFreeCommGroupScheme R) := G.obj.scheme
abbrev structureMap (G : AffineFiniteFreeCommGroupScheme R) := G.obj.structureMap
abbrev Point (G : AffineFiniteFreeCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :=
  G.obj.Point B

instance (G : AffineFiniteFreeCommGroupScheme R) : Module.Free R G.coordinates := G.property.1
instance (G : AffineFiniteFreeCommGroupScheme R) : Module.Finite R G.coordinates := G.property.2

instance (G : AffineFiniteFreeCommGroupScheme R) : IsFinite G.structureMap := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance (G : AffineFiniteFreeCommGroupScheme R) : Flat G.structureMap := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates)))
  rw [Flat.SpecMap_iff]
  change (algebraMap R G.coordinates).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The finite-flat geometric group scheme realized from finite-free Hopf coordinates. -/
def realize (G : AffineFiniteFreeCommGroupScheme R) :
    FiniteFlatCommGroupScheme (Spec (.of R)) where
  obj := G.obj.toCommGroupScheme
  property := by
    change IsFinite G.structureMap ∧ Flat G.structureMap
    exact ⟨inferInstance, inferInstance⟩

@[simp]
theorem realize_scheme (G : AffineFiniteFreeCommGroupScheme R) :
    G.realize.scheme = G.scheme := rfl

@[simp]
theorem realize_structureMap (G : AffineFiniteFreeCommGroupScheme R) :
    G.realize.structureMap = G.structureMap := rfl

/-- Scalar extension preserves finite-free affine commutative group schemes. -/
def baseChangeFunctor {K : Type u} [CommRing K] [Algebra R K] :
    AffineFiniteFreeCommGroupScheme R ⥤ AffineFiniteFreeCommGroupScheme K :=
  (affineFiniteFreeProperty K).lift
    ((affineFiniteFreeProperty R).ι ⋙
      AffineCommGroupScheme.baseChangeFunctor (R := R) (K := K)) (fun G ↦ by
        letI : Module.Free R G.obj.coordinates := G.property.1
        letI : Module.Finite R G.obj.coordinates := G.property.2
        change Module.Free K (K ⊗[R] G.obj.coordinates) ∧
          Module.Finite K (K ⊗[R] G.obj.coordinates)
        constructor <;> infer_instance)

/-- Scalar extension of one finite-free affine commutative group scheme. -/
abbrev baseChange {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineFiniteFreeCommGroupScheme R) : AffineFiniteFreeCommGroupScheme K :=
  (baseChangeFunctor (R := R) (K := K)).obj G

/-- Coordinate scalar extension of a finite-free affine realization agrees with geometric
base change in the category of finite-flat commutative group schemes. -/
def realizeBaseChangeIso {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineFiniteFreeCommGroupScheme R) :
    (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G.realize ≅
      (G.baseChange (K := K)).realize :=
  ObjectProperty.isoMk _
    (AffineCommGroupScheme.realizationBaseChangeIso (K := K) G.obj)

/-- The order of an affine finite-free group scheme is the rank of its coordinate algebra. -/
def order (G : AffineFiniteFreeCommGroupScheme R) : ℕ := Module.finrank R G.coordinates

/-- Finite-free order is invariant under scalar extension. -/
theorem baseChange_order {K : Type u} [CommRing K] [Algebra R K]
    [StrongRankCondition R] [StrongRankCondition K]
    (G : AffineFiniteFreeCommGroupScheme R) :
    (G.baseChange (K := K)).order = G.order :=
  by
    change Module.finrank K (K ⊗[R] G.coordinates) = Module.finrank R G.coordinates
    exact Module.finrank_baseChange

/-- The geometric rank function agrees everywhere with the finite-free coordinate rank. -/
theorem orderAt_eq_order (G : AffineFiniteFreeCommGroupScheme R) (x : Spec (.of R)) :
    G.structureMap.finrank x = G.order := by
  change (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates))).finrank x =
    Module.finrank R G.coordinates
  exact (Scheme.Hom.finrank_SpecMap_algebraMap R G.coordinates x).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := G.coordinates)) x)

/-- Deligne's order theorem in geometric affine-point form: every `Spec B`-point over `Spec R`
is killed by the rank of the finite-free coordinate algebra. -/
theorem point_pow_order_eq_one (G : AffineFiniteFreeCommGroupScheme R)
    (B : Type u) [CommRing B] [Algebra R B] (x : G.Point B) :
    x ^ G.order = 1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI : Subsingleton R := hR
    have hB : (0 : B) = 1 := by
      simpa using congrArg (algebraMap R B) (show (0 : R) = 1 from Subsingleton.elim _ _)
    letI : Subsingleton B := subsingleton_of_zero_eq_one hB
    apply (G.obj.pointEquiv B).injective
    exact Subsingleton.elim _ _
  letI : Nontrivial R := hR
  rcases subsingleton_or_nontrivial B with hB | hB
  · letI : Subsingleton B := hB
    apply (G.obj.pointEquiv B).injective
    exact Subsingleton.elim _ _
  letI : Nontrivial B := hB
  let f := G.obj.pointToAlgHom B x
  have hf : f.toLinearMap ≠ 0 := by
    intro h
    have h1 : (1 : B) = 0 := calc
      1 = f.toLinearMap 1 := by simp
      _ = (0 : G.coordinates →ₗ[R] B) 1 := LinearMap.congr_fun h 1
      _ = 0 := rfl
    exact one_ne_zero h1
  letI : Nontrivial (G.coordinates →ₗ[R] B) := nontrivial_of_ne f.toLinearMap 0 hf
  apply (G.obj.pointMulEquiv B).injective
  rw [map_pow, map_one]
  rw [AffineCommGroupScheme.pointMulEquiv_apply]
  exact ModularCurves.CartierDual.deligne_point_pow_eq_one f

/-- Deligne's theorem for points of the constructed geometric realization. -/
theorem realize_point_pow_order_eq_one (G : AffineFiniteFreeCommGroupScheme R)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.realize.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ G.order = 1 :=
  G.point_pow_order_eq_one B x

/-- The constructed realization has constant geometric order equal to the coordinate rank. -/
theorem realize_hasConstantOrder (G : AffineFiniteFreeCommGroupScheme R) :
    G.realize.HasConstantOrder G.order := by
  funext s
  exact G.orderAt_eq_order s

/-- Pointwise geometric-rank form of Deligne's theorem for the constructed realization. -/
theorem realize_point_pow_orderAt_eq_one (G : AffineFiniteFreeCommGroupScheme R)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.realize.Point (AffineCommGroupScheme.testObject (R := R) B))
    (s : Spec (.of R)) :
    x ^ G.realize.orderAt s = 1 := by
  have hs : G.realize.orderAt s = G.order := by
    simpa [FiniteFlatCommGroupScheme.HasConstantOrder] using
      congrFun G.realize_hasConstantOrder s
  rw [hs]
  exact G.realize_point_pow_order_eq_one B x

end AffineFiniteFreeCommGroupScheme

/-- The property that the coordinate algebra is finite and flat over the base. -/
def affineFiniteFlatProperty (R : Type u) [CommRing R] :
    ObjectProperty (AffineCommGroupScheme R) :=
  fun G ↦ Module.Finite R G.coordinates ∧ Module.Flat R G.coordinates

/-- Affine commutative group schemes with finite-flat coordinate algebra.  Unlike the finite-free
subcategory, these objects do not carry a globally chosen numerical order. -/
abbrev AffineFiniteFlatCommGroupScheme (R : Type u) [CommRing R] :=
  (affineFiniteFlatProperty R).FullSubcategory

namespace AffineFiniteFlatCommGroupScheme

variable {R : Type u} [CommRing R]

abbrev toAffineCommGroupScheme (G : AffineFiniteFlatCommGroupScheme R) := G.obj
abbrev coordinates (G : AffineFiniteFlatCommGroupScheme R) := G.obj.coordinates
abbrev scheme (G : AffineFiniteFlatCommGroupScheme R) := G.obj.scheme
abbrev structureMap (G : AffineFiniteFlatCommGroupScheme R) := G.obj.structureMap
abbrev Point (G : AffineFiniteFlatCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :=
  G.obj.Point B

instance (G : AffineFiniteFlatCommGroupScheme R) : Module.Finite R G.coordinates := G.property.1
instance (G : AffineFiniteFlatCommGroupScheme R) : Module.Flat R G.coordinates := G.property.2

instance (G : AffineFiniteFlatCommGroupScheme R) : IsFinite G.structureMap := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance (G : AffineFiniteFlatCommGroupScheme R) : Flat G.structureMap := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates)))
  rw [Flat.SpecMap_iff]
  change (algebraMap R G.coordinates).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The finite-flat geometric group scheme realized from finite-flat Hopf coordinates. -/
def realize (G : AffineFiniteFlatCommGroupScheme R) :
    FiniteFlatCommGroupScheme (Spec (.of R)) where
  obj := G.obj.toCommGroupScheme
  property := by
    change IsFinite G.structureMap ∧ Flat G.structureMap
    exact ⟨inferInstance, inferInstance⟩

@[simp]
theorem realize_scheme (G : AffineFiniteFlatCommGroupScheme R) :
    G.realize.scheme = G.scheme := rfl

@[simp]
theorem realize_structureMap (G : AffineFiniteFlatCommGroupScheme R) :
    G.realize.structureMap = G.structureMap := rfl

/-- Scalar extension preserves finite-flat affine commutative group schemes. -/
def baseChangeFunctor {K : Type u} [CommRing K] [Algebra R K] :
    AffineFiniteFlatCommGroupScheme R ⥤ AffineFiniteFlatCommGroupScheme K :=
  (affineFiniteFlatProperty K).lift
    ((affineFiniteFlatProperty R).ι ⋙
      AffineCommGroupScheme.baseChangeFunctor (R := R) (K := K)) (fun G ↦ by
        letI : Module.Finite R G.obj.coordinates := G.property.1
        letI : Module.Flat R G.obj.coordinates := G.property.2
        change Module.Finite K (K ⊗[R] G.obj.coordinates) ∧
          Module.Flat K (K ⊗[R] G.obj.coordinates)
        constructor <;> infer_instance)

/-- Scalar extension of one finite-flat affine commutative group scheme. -/
abbrev baseChange {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineFiniteFlatCommGroupScheme R) : AffineFiniteFlatCommGroupScheme K :=
  (baseChangeFunctor (R := R) (K := K)).obj G

/-- Coordinate scalar extension of a finite-flat affine realization agrees with geometric
base change in the category of finite-flat commutative group schemes. -/
def realizeBaseChangeIso {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineFiniteFlatCommGroupScheme R) :
    (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G.realize ≅
      (G.baseChange (K := K)).realize :=
  ObjectProperty.isoMk _
    (AffineCommGroupScheme.realizationBaseChangeIso (K := K) G.obj)

/-- The local rank of finite-flat coordinates is compatible with scalar extension. -/
theorem baseChange_structureMap_finrank {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineFiniteFlatCommGroupScheme R) (s : Spec (.of K)) :
    (G.baseChange (K := K)).structureMap.finrank s =
      G.structureMap.finrank (Spec.map (CommRingCat.ofHom (algebraMap R K)) s) := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap K (K ⊗[R] G.coordinates)))).finrank s =
    (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates))).finrank
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) s)
  rw [Scheme.Hom.finrank_SpecMap_algebraMap K (K ⊗[R] G.coordinates) s,
    Scheme.Hom.finrank_SpecMap_algebraMap R G.coordinates
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) s)]
  exact Module.rankAtStalk_baseChange s

/-- Constant geometric order of a finite-flat affine realization survives arbitrary scalar
extension, including over disconnected bases. -/
theorem baseChange_realize_hasConstantOrder
    {K : Type u} [CommRing K] [Algebra R K]
    (G : AffineFiniteFlatCommGroupScheme R) (n : ℕ)
    (hG : G.realize.HasConstantOrder n) :
    (G.baseChange (K := K)).realize.HasConstantOrder n := by
  funext s
  change (G.baseChange (K := K)).structureMap.finrank s = n
  rw [G.baseChange_structureMap_finrank]
  rw [← G.realize_structureMap]
  exact congrFun hG (Spec.map (CommRingCat.ofHom (algebraMap R K)) s)

/-- Algebraic localization and descent for Deligne's order theorem.  Finite flatness is used to
make the coordinate algebra free after localizing at a maximal ideal; the constant-rank
hypothesis supplies one exponent on all components of the base. -/
theorem algPoint_pow_eq_one_of_constantRank
    {A B : Type u} [CommRing A] [CommRing B]
    [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    [Module.Finite R A] [Module.Flat R A] [Algebra R B]
    (n : ℕ) (hA : ∀ s : PrimeSpectrum R, Module.rankAtStalk A s = n)
    (f : A →ₐ[R] B) :
    (toConv f : WithConv (A →ₐ[R] B)) ^ n = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  let Mₚ : (P : Ideal R) → [P.IsMaximal] → Type u :=
    fun P _ ↦ Localization.AtPrime P ⊗[R] B
  let loc : (P : Ideal R) → [P.IsMaximal] → B →ₗ[R] Mₚ P :=
    fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) B 1
  letI : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (loc P) := by
    intro P hP
    apply (isLocalizedModule_iff_isBaseChange P.primeCompl
      (Localization.AtPrime P) (loc P)).mpr
    exact TensorProduct.isBaseChange R B (Localization.AtPrime P)
  apply Module.eq_of_localization_maximal Mₚ loc
  intro P hP
  let K := Localization.AtPrime P
  let BK := K ⊗[R] B
  let iB : B →ₐ[R] BK := Algebra.TensorProduct.includeRight
  let mapped : WithConv (A →ₐ[R] BK) :=
    TauCeti.AlgHom.mapValue iB (toConv f)
  let e : WithConv (A →ₐ[R] BK) ≃*
      WithConv (K ⊗[R] A →ₐ[K] BK) :=
    TauCeti.AlgHom.baseChangePointsMulEquiv
  let localPoint : WithConv (K ⊗[R] A →ₐ[K] BK) := e mapped
  letI : Module.Free K (K ⊗[R] A) := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank K (K ⊗[R] A) = n := by
    rw [← Module.rankAtStalk_eq_finrank_tensorProduct
      (⟨P, hP.isPrime⟩ : PrimeSpectrum R)]
    exact hA (⟨P, hP.isPrime⟩ : PrimeSpectrum R)
  have hlocal : localPoint ^ n = 1 := by
    rw [← hrank]
    rcases subsingleton_or_nontrivial BK with hBK | hBK
    · letI : Subsingleton BK := hBK
      exact Subsingleton.elim _ _
    · letI : Nontrivial BK := hBK
      have hf : localPoint.ofConv.toLinearMap ≠ 0 := by
        intro h
        have h1 : (1 : BK) = 0 := calc
          1 = localPoint.ofConv.toLinearMap 1 := by simp
          _ = (0 : (K ⊗[R] A) →ₗ[K] BK) 1 := LinearMap.congr_fun h 1
          _ = 0 := rfl
        exact one_ne_zero h1
      letI : Nontrivial ((K ⊗[R] A) →ₗ[K] BK) :=
        nontrivial_of_ne localPoint.ofConv.toLinearMap 0 hf
      exact ModularCurves.CartierDual.deligne_point_pow_eq_one localPoint.ofConv
  have hmapped : mapped ^ n = 1 := by
    apply e.injective
    calc
      e (mapped ^ n) = (e mapped) ^ n := map_pow e mapped n
      _ = localPoint ^ n := rfl
      _ = 1 := hlocal
      _ = e 1 := (map_one e).symm
  have hmapped' :
      TauCeti.AlgHom.mapValue iB ((toConv f : WithConv (A →ₐ[R] B)) ^ n) =
        TauCeti.AlgHom.mapValue iB 1 := by
    simpa only [map_pow, map_one, mapped] using hmapped
  have heval := congrArg (fun q : WithConv (A →ₐ[R] BK) ↦ q.ofConv a) hmapped'
  simpa [Mₚ, loc, K, BK, iB, mapped, TauCeti.AlgHom.mapValue_apply,
    Algebra.TensorProduct.tmul_one_eq_one_tmul] using heval

/-- Every affine point of a finite-flat affine group scheme of constant rank `n` is killed by
`n`.  This is the global finite-locally-free geometric form of Deligne's theorem. -/
theorem point_pow_eq_one_of_constantRank (G : AffineFiniteFlatCommGroupScheme R)
    (n : ℕ) (hG : ∀ s : Spec (.of R), G.structureMap.finrank s = n)
    (B : Type u) [CommRing B] [Algebra R B] (x : G.Point B) :
    x ^ n = 1 := by
  apply (G.obj.pointMulEquiv B).injective
  rw [map_pow, map_one, AffineCommGroupScheme.pointMulEquiv_apply]
  apply algPoint_pow_eq_one_of_constantRank n
  intro s
  have hs := hG s
  change (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates))).finrank s = n at hs
  rw [Scheme.Hom.finrank_SpecMap_algebraMap] at hs
  exact hs

/-- Strong geometric form for the constructed finite-flat realization: a constant-order
certificate on the geometric structure morphism kills every affine test point by that order. -/
theorem realize_point_pow_eq_one_of_hasConstantOrder
    (G : AffineFiniteFlatCommGroupScheme R) (n : ℕ)
    (hG : G.realize.HasConstantOrder n)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.realize.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ n = 1 := by
  apply G.point_pow_eq_one_of_constantRank n (B := B) (x := x)
  intro s
  rw [← G.realize_structureMap]
  exact congrFun hG s

/-- Over a local base, finite flat coordinates are free, so Deligne's theorem gives the honest
finite-flat geometric point statement. -/
theorem point_pow_finrank_eq_one_of_isLocalRing (G : AffineFiniteFlatCommGroupScheme R)
    [IsLocalRing R] (B : Type u) [CommRing B] [Algebra R B] (x : G.Point B) :
    x ^ Module.finrank R G.coordinates = 1 := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · letI : Subsingleton B := hB
    apply (G.obj.pointEquiv B).injective
    exact Subsingleton.elim _ _
  letI : Nontrivial B := hB
  letI : Module.Free R G.coordinates := Module.free_of_flat_of_isLocalRing
  let f := G.obj.pointToAlgHom B x
  have hf : f.toLinearMap ≠ 0 := by
    intro h
    have h1 : (1 : B) = 0 := calc
      1 = f.toLinearMap 1 := by simp
      _ = (0 : G.coordinates →ₗ[R] B) 1 := LinearMap.congr_fun h 1
      _ = 0 := rfl
    exact one_ne_zero h1
  letI : Nontrivial (G.coordinates →ₗ[R] B) := nontrivial_of_ne f.toLinearMap 0 hf
  apply (G.obj.pointMulEquiv B).injective
  rw [map_pow, map_one]
  rw [AffineCommGroupScheme.pointMulEquiv_apply]
  exact ModularCurves.CartierDual.deligne_point_pow_eq_one f

end AffineFiniteFlatCommGroupScheme

namespace FiniteFlatCommGroupScheme

variable {R : Type u} [CommRing R]

/-- A certificate that a geometric finite-flat commutative group scheme over `Spec R` is presented
by a finite-free commutative, cocommutative coordinate Hopf algebra.  Constructed realizations have
a canonical such certificate; the structure also records presentations of pre-existing geometric
objects. -/
structure AffineFiniteFreePresentation (G : FiniteFlatCommGroupScheme (Spec (.of R))) where
  /-- The finite-free coordinate Hopf presentation. -/
  hopf : AffineFiniteFreeCommGroupScheme R
  /-- Identification of the underlying geometric scheme with the spectrum of the coordinates. -/
  schemeIso : G.scheme ≅ hopf.scheme
  /-- The scheme identification lies over `Spec R`. -/
  schemeIso_hom_structureMap : schemeIso.hom ≫ hopf.structureMap = G.structureMap
  /-- Compatibility of geometric group-valued points with convolution points. -/
  pointMulEquiv : ∀ (B : Type u) [CommRing B] [Algebra R B],
    G.Point (AffineCommGroupScheme.testObject (R := R) B) ≃* hopf.Point B
  /-- The point equivalence is induced by the displayed scheme isomorphism, rather than an
  unrelated abstract equivalence of groups. -/
  pointMulEquiv_left : ∀ (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)),
    (pointMulEquiv B x).left = x.left ≫ schemeIso.hom
  /-- The geometric rank agrees with the coordinate-algebra rank on the whole affine base. -/
  order_eq : G.HasConstantOrder hopf.order

namespace AffineFiniteFreePresentation

variable {G : FiniteFlatCommGroupScheme (Spec (.of R))}

/-- Deligne's theorem transported all the way to a point of a geometric finite-flat commutative
group scheme carrying an explicit affine finite-free Hopf presentation. -/
theorem point_pow_order_eq_one (P : G.AffineFiniteFreePresentation)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ P.hopf.order = 1 := by
  apply (P.pointMulEquiv B).injective
  rw [map_pow, map_one]
  exact P.hopf.point_pow_order_eq_one B (P.pointMulEquiv B x)

/-- Pointwise-rank form of the geometric order theorem.  This formulation remains meaningful on
the geometric side and records explicitly where constant order enters. -/
theorem point_pow_orderAt_eq_one (P : G.AffineFiniteFreePresentation)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) (s : Spec (.of R)) :
    x ^ G.orderAt s = 1 := by
  have hs : G.orderAt s = P.hopf.order := by
    simpa [HasConstantOrder] using congrFun P.order_eq s
  rw [hs]
  exact P.point_pow_order_eq_one B x

end AffineFiniteFreePresentation

end FiniteFlatCommGroupScheme

namespace AffineFiniteFreeCommGroupScheme

variable {R : Type u} [CommRing R]

/-- The canonical finite-free Hopf presentation of the constructed geometric realization. -/
def presentation (G : AffineFiniteFreeCommGroupScheme R) :
    FiniteFlatCommGroupScheme.AffineFiniteFreePresentation G.realize where
  hopf := G
  schemeIso := Iso.refl _
  schemeIso_hom_structureMap := rfl
  pointMulEquiv := by
    intro B _ _
    change G.obj.Point B ≃* G.obj.Point B
    exact MulEquiv.refl _
  pointMulEquiv_left := by
    intro B _ _ x
    change x.left = x.left ≫ 𝟙 _
    rw [Category.comp_id]
  order_eq := G.realize_hasConstantOrder

/-- Every finite-free commutative, cocommutative Hopf algebra has its canonical geometric
finite-flat realization.  This permanent theorem is the destination of the checked Challenge
bridge. -/
theorem exists_geometric_realization (G : AffineFiniteFreeCommGroupScheme R) :
    ∃ (H : FiniteFlatCommGroupScheme (Spec (.of R)))
      (P : H.AffineFiniteFreePresentation), P.hopf = G :=
  ⟨G.realize, G.presentation, rfl⟩

end AffineFiniteFreeCommGroupScheme

end AlgebraicGeometry
