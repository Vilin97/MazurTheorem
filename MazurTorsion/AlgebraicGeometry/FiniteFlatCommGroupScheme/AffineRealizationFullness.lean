/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.RaynaudRealizedFactorMapUniqueness

/-!
# Full faithfulness of affine group-scheme realization

Relative spectrum does not merely preserve maps supplied on Hopf coordinates.  Every morphism
between two affine group schemes obtained from commutative cocommutative Hopf algebras uniquely
comes from a Hopf-coordinate morphism.  The inverse is furnished by Mathlib's equivalence between
commutative Hopf algebras and cogroup objects in commutative algebras; cocommutativity turns those
cogroups into the internal commutative groups used by the geometric realization.

Restricting this equivalence to finite-free Hopf coordinates and the full finite-flat geometric
subcategory proves the actual fullness bridge missing from the generic-fibre uniqueness API.  In
particular, an
arbitrary geometric morphism or isomorphism between two realized models has a checked affine
preimage whose realization is the original map.  Composing this preimage with realized-map
generic-fibre uniqueness determines arbitrary geometric maps between realized models.  The final
coefficient-five and coefficient-eleven endpoints apply this to actual morphisms between the
constant and multiplicative prime-factor models.

This does not assert that every finite-flat group scheme over an affine base has already been
identified with a chosen Hopf-coordinate realization.  For project factors, that object-level
identification is supplied by the existing admissible-factor isomorphism; the theorem here removes
the separate morphism-level fullness obstruction.
-/

noncomputable section

open CategoryTheory
open IsDedekindDomain HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

namespace AlgebraicGeometry

universe u

namespace AffineCommGroupScheme

/-- Internal commutative-group morphisms between cocommutative Hopf coordinates uniquely recover
the contravariant Hopf morphism. -/
def coordinateCommGroupFunctorFullyFaithful
    (R : Type u) [CommRing R] :
    (coordinateCommGroupFunctor R).FullyFaithful where
  preimage {G H} f :=
    (ObjectProperty.homMk
      ((commHopfAlgCatEquivCogrpCommAlgCat R).inverse.map f.hom.op)).op

/-- Relative spectrum upgrades the Hopf/internal-group equivalence to a fully faithful geometric
realization of affine commutative group schemes. -/
def realizationFunctorFullyFaithful (R : Type u) [CommRing R] :
    (realizationFunctor R).FullyFaithful :=
  (coordinateCommGroupFunctorFullyFaithful R).comp
    (relativeSpecFullyFaithful (R := R)).mapCommGrp

end AffineCommGroupScheme

namespace AffineFiniteFreeCommGroupScheme

/-- Restricting affine realization to finite-free Hopf coordinates and the full finite-flat
geometric subcategory remains fully faithful. -/
def realizationFunctorFullyFaithful (R : Type u) [CommRing R] :
    (realizationFunctor R).FullyFaithful where
  preimage f := ObjectProperty.homMk
    ((AffineCommGroupScheme.realizationFunctorFullyFaithful R).preimage f.hom)
  map_preimage f := by
    apply ObjectProperty.hom_ext
    exact (AffineCommGroupScheme.realizationFunctorFullyFaithful R).map_preimage f.hom
  preimage_map f := by
    apply ObjectProperty.hom_ext
    exact (AffineCommGroupScheme.realizationFunctorFullyFaithful R).preimage_map f.hom

/-- Recover the unique Hopf-coordinate morphism underlying an arbitrary geometric morphism
between two finite-free realized models. -/
def preimageRealizeMap
    {R : Type u} [CommRing R]
    {G H : AffineFiniteFreeCommGroupScheme R}
    (f : G.realize ⟶ H.realize) : G ⟶ H :=
  (realizationFunctorFullyFaithful R).preimage f

/-- Realizing the recovered Hopf-coordinate morphism gives the original arbitrary geometric
morphism, not merely an extensionally equal coordinate function. -/
@[simp]
theorem realizeMap_preimageRealizeMap
    {R : Type u} [CommRing R]
    {G H : AffineFiniteFreeCommGroupScheme R}
    (f : G.realize ⟶ H.realize) :
    realizeMap (preimageRealizeMap f) = f :=
  (realizationFunctorFullyFaithful R).map_preimage f

/-- The categorical Hopf preimage has exactly the coordinate ring map obtained directly from
`Spec.preimage` of the underlying geometric morphism.  Thus the equivalence-based fullness proof
agrees with direct affine-Spec reconstruction on functions. -/
theorem coordinateMap_preimageRealizeMap
    {R : Type u} [CommRing R]
    {G H : AffineFiniteFreeCommGroupScheme R}
    (f : G.realize ⟶ H.realize) :
    (AffineCommGroupScheme.coordinateMap (preimageRealizeMap f).hom).toAlgHom.toRingHom =
      (Spec.preimage (FiniteFlatCommGroupScheme.hom f)).hom := by
  have hmap := congrArg FiniteFlatCommGroupScheme.hom
    (realizeMap_preimageRealizeMap f)
  change Spec.map (CommRingCat.ofHom
      (AffineCommGroupScheme.coordinateMap (preimageRealizeMap f).hom).toAlgHom.toRingHom) =
    FiniteFlatCommGroupScheme.hom f at hmap
  have hpreimage := congrArg Spec.preimage hmap
  rw [Spec.preimage_map] at hpreimage
  exact congrArg (fun q : CommRingCat.of H.coordinates ⟶ CommRingCat.of G.coordinates ↦ q.hom)
    hpreimage

/-- Recover the unique affine Hopf-coordinate isomorphism underlying an arbitrary geometric
isomorphism between finite-free realized models. -/
def preimageRealizeIso
    {R : Type u} [CommRing R]
    {G H : AffineFiniteFreeCommGroupScheme R}
    (e : G.realize ≅ H.realize) : G ≅ H :=
  (realizationFunctorFullyFaithful R).preimageIso e

/-- Mapping the recovered affine isomorphism through geometric realization returns the supplied
geometric isomorphism. -/
@[simp]
theorem mapIso_preimageRealizeIso
    {R : Type u} [CommRing R]
    {G H : AffineFiniteFreeCommGroupScheme R}
    (e : G.realize ≅ H.realize) :
    (realizationFunctor R).mapIso (preimageRealizeIso e) = e :=
  (realizationFunctorFullyFaithful R).isoEquiv.apply_symm_apply e

/-- Arbitrary geometric morphisms between finite-free realized models are determined by their
actual geometric generic fibres.  Fullness first recovers their Hopf-coordinate maps, after which
`realizeMap_ext_of_geometricGenericFiber_eq` supplies the uniqueness. -/
theorem hom_ext_of_geometricGenericFiber_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : AffineFiniteFreeCommGroupScheme A} {f g : G.realize ⟶ H.realize}
    (hfg :
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map f =
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map g) :
    f = g := by
  have hrealized := realizeMap_ext_of_geometricGenericFiber_eq
    (f := preimageRealizeMap f) (g := preimageRealizeMap g) (by simpa using hfg)
  simpa using hrealized

open FiniteFlatCommGroupScheme

/-- Arbitrary actual geometric maps from the constant order-five factor to `mu_5` over the
five-adic completion integers are determined by geometric generic-fibre base change. -/
theorem constantMu_hom_ext_of_completionGeometricGenericFiberAtFive_eq
    {f g :
      constantScheme
          (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ⟶
        muScheme (atFive.adicCompletionIntegers ℚ) 5}
    (hfg :
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atFive.adicCompletionIntegers ℚ)
            (atFive.adicCompletion ℚ))))).map f =
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atFive.adicCompletionIntegers ℚ)
            (atFive.adicCompletion ℚ))))).map g) :
    f = g :=
  hom_ext_of_geometricGenericFiber_eq hfg

/-- Arbitrary actual geometric maps from the constant order-eleven factor to `mu_11` over the
eleven-adic completion integers are determined by geometric generic-fibre base change. -/
theorem constantMu_hom_ext_of_completionGeometricGenericFiberAtEleven_eq
    {f g :
      constantScheme
          (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ⟶
        muScheme (atEleven.adicCompletionIntegers ℚ) 11}
    (hfg :
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atEleven.adicCompletionIntegers ℚ)
            (atEleven.adicCompletion ℚ))))).map f =
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atEleven.adicCompletionIntegers ℚ)
            (atEleven.adicCompletion ℚ))))).map g) :
    f = g :=
  hom_ext_of_geometricGenericFiber_eq hfg

end AffineFiniteFreeCommGroupScheme

end AlgebraicGeometry
