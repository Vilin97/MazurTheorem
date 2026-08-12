/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic
import MazurTorsion.Upstream.AINTLIB.ForMathlib.CartierDual
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Affine finite-flat commutative group schemes

This file gives the affine coordinate-algebra side of finite-flat commutative group schemes.  An
affine commutative group scheme over `Spec R` is encoded contravariantly by a commutative,
cocommutative Hopf `R`-algebra.  The crucial bridge is not merely an equality of underlying sets:
`pointMulEquiv` identifies morphisms `Spec B ⟶ Spec A` over `Spec R` with the convolution group
of `R`-algebra maps `A →ₐ[R] B`.

The theorem `AffineFiniteFreeCommGroupScheme.point_pow_order_eq_one` transports the integrated
AINTLIB theorem `deligne_point_pow_eq_one` across this geometric equivalence.  Its finite-flat
analogue is proved over a local base, where finite flat modules are free.  No global
finite-locally-free descent is asserted here: that requires compatibility of convolution powers
with localization and a local-to-global argument.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open WithConv

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

/-- The underlying affine scheme. -/
abbrev scheme (G : AffineCommGroupScheme R) : Scheme.{u} := Spec (.of G.coordinates)

/-- The structure morphism to `Spec R`. -/
def structureMap (G : AffineCommGroupScheme R) : G.scheme ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates))

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

/-- `Spec B` as an object over `Spec R`. -/
def testObject (B : Type u) [CommRing B] [Algebra R B] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))

/-- The affine test-scheme points of `G`, expressed geometrically as morphisms over `Spec R`. -/
abbrev Point (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :=
  testObject (R := R) B ⟶ Over.mk G.structureMap

/-- Recover the coordinate `R`-algebra map from a geometric affine point. -/
def pointToAlgHom (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point B) : G.coordinates →ₐ[R] B :=
  let xleft : Spec (.of B) ⟶ Spec (.of G.coordinates) := x.left
  { (Spec.preimage xleft).hom with
    commutes' := by
      intro r
      have h := congrArg Spec.preimage x.w
      simpa [Spec.preimage_comp, structureMap, testObject, xleft] using
        congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of B ↦ f.hom r) h }

/-- Turn a coordinate `R`-algebra map into a morphism of affine schemes over `Spec R`. -/
def pointOfAlgHom (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B]
    (f : G.coordinates →ₐ[R] B) : G.Point B :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
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

noncomputable instance (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :
    CommGroup (G.Point B) :=
  (G.pointEquiv B).commGroup

/-- The affine point equivalence respects the geometric group law and convolution. -/
def pointMulEquiv (G : AffineCommGroupScheme R) (B : Type u) [CommRing B] [Algebra R B] :
    G.Point B ≃* WithConv (G.coordinates →ₐ[R] B) :=
  (G.pointEquiv B).mulEquiv

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

/-- The order of an affine finite-free group scheme is the rank of its coordinate algebra. -/
def order (G : AffineFiniteFreeCommGroupScheme R) : ℕ := Module.finrank R G.coordinates

/-- The geometric rank function agrees everywhere with the finite-free coordinate rank. -/
theorem orderAt_eq_order (G : AffineFiniteFreeCommGroupScheme R) (x : Spec (.of R)) :
    G.structureMap.finrank x = G.order := by
  change (Spec.map (CommRingCat.ofHom (algebraMap R G.coordinates))).finrank x =
    Module.finrank R G.coordinates
  exact (Scheme.Hom.finrank_SpecMap_algebraMap R G.coordinates x).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := G.coordinates)) x)

/-- Deligne's order theorem in geometric affine-point form: every `Spec B`-point over `Spec R`
is killed by the rank of the finite-free coordinate algebra. -/
theorem point_pow_order_eq_one (G : AffineFiniteFreeCommGroupScheme R) [Nontrivial R]
    (B : Type u) [CommRing B] [Algebra R B] [Nontrivial B] (x : G.Point B) :
    x ^ G.order = 1 := by
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
  exact ModularCurves.CartierDual.deligne_point_pow_eq_one f

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

/-- Over a local base, finite flat coordinates are free, so Deligne's theorem gives the honest
finite-flat geometric point statement. -/
theorem point_pow_finrank_eq_one_of_isLocalRing (G : AffineFiniteFlatCommGroupScheme R)
    [IsLocalRing R] (B : Type u) [CommRing B] [Algebra R B] [Nontrivial B] (x : G.Point B) :
    x ^ Module.finrank R G.coordinates = 1 := by
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
  exact ModularCurves.CartierDual.deligne_point_pow_eq_one f

end AffineFiniteFlatCommGroupScheme

namespace FiniteFlatCommGroupScheme

variable {R : Type u} [CommRing R]

/-- A certificate that a geometric finite-flat commutative group scheme over `Spec R` is presented
by a finite-free commutative, cocommutative coordinate Hopf algebra.

The point-group equivalence is explicit data because the current library does not yet package the
categorical equivalence between affine group objects over `Spec R` and Hopf `R`-algebras.  Requiring
the certificate keeps this interface usable without postulating that missing equivalence. -/
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
theorem point_pow_order_eq_one (P : G.AffineFiniteFreePresentation) [Nontrivial R]
    (B : Type u) [CommRing B] [Algebra R B] [Nontrivial B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) :
    x ^ P.hopf.order = 1 := by
  apply (P.pointMulEquiv B).injective
  rw [map_pow, map_one]
  exact P.hopf.point_pow_order_eq_one B (P.pointMulEquiv B x)

/-- Pointwise-rank form of the geometric order theorem.  This formulation remains meaningful on
the geometric side and records explicitly where constant order enters. -/
theorem point_pow_orderAt_eq_one (P : G.AffineFiniteFreePresentation) [Nontrivial R]
    (B : Type u) [CommRing B] [Algebra R B] [Nontrivial B]
    (x : G.Point (AffineCommGroupScheme.testObject (R := R) B)) (s : Spec (.of R)) :
    x ^ G.orderAt s = 1 := by
  have hs : G.orderAt s = P.hopf.order := by
    simpa [HasConstantOrder] using congrFun P.order_eq s
  rw [hs]
  exact P.point_pow_order_eq_one B x

end AffineFiniteFreePresentation

end FiniteFlatCommGroupScheme

end AlgebraicGeometry
