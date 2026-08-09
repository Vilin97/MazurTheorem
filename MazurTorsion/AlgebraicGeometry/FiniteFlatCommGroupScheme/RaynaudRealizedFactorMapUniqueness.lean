/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.RaynaudPrimeFactorUniqueness

/-!
# Generic-fibre uniqueness for realized prime-factor maps

The existing affine generic-fibre theorem determines an integral Hopf-coordinate morphism from
its generic fibre.  Here that uniqueness is transported through the actual geometric realization
and its base-change comparison.  Thus equality of the geometric generic fibres of two realized
integral maps implies equality of the realized finite-flat group-scheme maps themselves.

The coefficient-five and coefficient-eleven endpoints apply this statement to the concrete
constant and multiplicative prime-factor models over completed local rings.  These are uniqueness
theorems for maps that are already supplied on Hopf coordinates.  They do not prove that an
arbitrary geometric morphism comes from Hopf coordinates, extend a generic-fibre morphism over the
integral base, or compare arbitrary connected--étale data.  Those require, respectively,
realization fullness, Raynaud extension, and universal identity-component/maximal-étale-quotient
properties absent from the current API.
-/

noncomputable section

open CategoryTheory
open IsDedekindDomain HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

namespace AlgebraicGeometry.AffineFiniteFreeCommGroupScheme

universe u

/-- Geometric realization is faithful on morphisms of affine finite-free commutative group
schemes. -/
theorem realizeMap_injective
    {R : Type u} [CommRing R]
    {G H : AffineFiniteFreeCommGroupScheme R} :
    Function.Injective (fun f : G ⟶ H ↦ realizeMap f) := by
  intro f g hfg
  apply ObjectProperty.hom_ext
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro a
  have hscheme := congrArg FiniteFlatCommGroupScheme.hom hfg
  change Spec.map (CommRingCat.ofHom
      (AffineCommGroupScheme.coordinateMap f.hom).toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom
      (AffineCommGroupScheme.coordinateMap g.hom).toAlgHom.toRingHom) at hscheme
  rw [Spec.map_inj] at hscheme
  exact congrArg (fun q : CommRingCat.of H.coordinates ⟶ CommRingCat.of G.coordinates ↦ q.hom a)
    hscheme

/-- Equality of actual geometric generic-fibre maps determines the realized integral morphism.
The comparison is not definitional: naturality of `realizeBaseChangeIso` transports the geometric
premise back to coordinate scalar extension before affine generic-fibre faithfulness applies. -/
theorem realizeMap_ext_of_geometricGenericFiber_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : AffineFiniteFreeCommGroupScheme A} {f g : G ⟶ H}
    (hfg :
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map (realizeMap f) =
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map (realizeMap g)) :
    realizeMap f = realizeMap g := by
  have hrealized :
      realizeMap ((baseChangeFunctor (R := A) (K := F)).map f) =
        realizeMap ((baseChangeFunctor (R := A) (K := F)).map g) := by
    apply (cancel_epi (realizeBaseChangeIso (K := F) G).hom).1
    rw [← realizeBaseChangeIso_naturality (K := F) f,
      ← realizeBaseChangeIso_naturality (K := F) g, hfg]
  have hcoordinate :
      (baseChangeFunctor (R := A) (K := F)).map f =
        (baseChangeFunctor (R := A) (K := F)).map g :=
    realizeMap_injective hrealized
  rw [hom_ext_of_genericFiber_eq hcoordinate]

open FiniteFlatCommGroupScheme

/-- Actual geometric maps from the constant order-five model to `mu_5` over the five-adic
completion integers are determined by their geometric generic fibres. -/
theorem constantMu_realizeMap_ext_of_completionGenericFiberAtFive_eq
    {f g :
      FiniteFlatCommGroupScheme.constant
          (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ⟶
        mu (atFive.adicCompletionIntegers ℚ) 5}
    (hfg :
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atFive.adicCompletionIntegers ℚ)
            (atFive.adicCompletion ℚ))))).map
          (realizeMap f :
            constantScheme
                (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ⟶
              muScheme (atFive.adicCompletionIntegers ℚ) 5) =
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atFive.adicCompletionIntegers ℚ)
            (atFive.adicCompletion ℚ))))).map
          (realizeMap g :
            constantScheme
                (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ⟶
              muScheme (atFive.adicCompletionIntegers ℚ) 5)) :
    (realizeMap f :
      constantScheme (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ⟶
        muScheme (atFive.adicCompletionIntegers ℚ) 5) =
      (realizeMap g :
        constantScheme (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ⟶
          muScheme (atFive.adicCompletionIntegers ℚ) 5) :=
  realizeMap_ext_of_geometricGenericFiber_eq hfg

/-- Actual geometric maps from the constant order-eleven model to `mu_11` over the eleven-adic
completion integers are determined by their geometric generic fibres. -/
theorem constantMu_realizeMap_ext_of_completionGenericFiberAtEleven_eq
    {f g :
      FiniteFlatCommGroupScheme.constant
          (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ⟶
        mu (atEleven.adicCompletionIntegers ℚ) 11}
    (hfg :
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atEleven.adicCompletionIntegers ℚ)
            (atEleven.adicCompletion ℚ))))).map
          (realizeMap f :
            constantScheme
                (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ⟶
              muScheme (atEleven.adicCompletionIntegers ℚ) 11) =
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atEleven.adicCompletionIntegers ℚ)
            (atEleven.adicCompletion ℚ))))).map
          (realizeMap g :
            constantScheme
                (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ⟶
              muScheme (atEleven.adicCompletionIntegers ℚ) 11)) :
    (realizeMap f :
      constantScheme (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ⟶
        muScheme (atEleven.adicCompletionIntegers ℚ) 11) =
      (realizeMap g :
        constantScheme (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ⟶
          muScheme (atEleven.adicCompletionIntegers ℚ) 11) :=
  realizeMap_ext_of_geometricGenericFiber_eq hfg

end AlgebraicGeometry.AffineFiniteFreeCommGroupScheme
