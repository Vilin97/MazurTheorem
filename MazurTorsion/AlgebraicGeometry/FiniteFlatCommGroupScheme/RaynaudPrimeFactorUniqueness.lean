/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Examples
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.RaynaudCompletionUniquenessConsumers

/-!
# Generic-fibre uniqueness for the constant and multiplicative prime factors

Finite-free Hopf coordinates are finite flat, so the affine finite-free category embeds fully
faithfully in the affine finite-flat category.  The embedding commutes definitionally with
coordinate scalar extension.  Consequently the generic-fibre faithfulness theorem for affine
finite-flat group schemes applies to the existing finite-free constant and `mu` models.

The final theorems specialize this uniqueness statement to the actual constant and
multiplicative factor models at the five- and eleven-adic completions.  They only compare maps
or isomorphisms that have already been supplied over the integral base.  No theorem in this file
extends a generic-fibre map, constructs a factor isomorphism, or supplies the still-separate
Raynaud classification input.
-/

noncomputable section

open CategoryTheory
open IsDedekindDomain HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

namespace AlgebraicGeometry

universe u

/-- Finite-free affine Hopf coordinates are finite flat over the base. -/
theorem affineFiniteFreeProperty_le_affineFiniteFlatProperty
    (R : Type u) [CommRing R] :
    affineFiniteFreeProperty R ≤ affineFiniteFlatProperty R := by
  intro G hG
  letI : Module.Free R G.coordinates := hG.1
  exact ⟨hG.2, inferInstance⟩

namespace AffineFiniteFreeCommGroupScheme

/-- The identity-on-coordinates inclusion of affine finite-free group schemes into affine
finite-flat group schemes. -/
abbrev toFiniteFlatFunctor (R : Type u) [CommRing R] :
    AffineFiniteFreeCommGroupScheme R ⥤ AffineFiniteFlatCommGroupScheme R :=
  ObjectProperty.ιOfLE (affineFiniteFreeProperty_le_affineFiniteFlatProperty R)

/-- The finite-free-to-finite-flat inclusion is fully faithful. -/
def toFiniteFlatFunctorFullyFaithful (R : Type u) [CommRing R] :
    (toFiniteFlatFunctor R).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE
    (affineFiniteFreeProperty_le_affineFiniteFlatProperty R)

@[simp]
theorem toFiniteFlatFunctor_obj_obj (R : Type u) [CommRing R]
    (G : AffineFiniteFreeCommGroupScheme R) :
    ((toFiniteFlatFunctor R).obj G).obj = G.obj :=
  rfl

@[simp]
theorem toFiniteFlatFunctor_map_hom (R : Type u) [CommRing R]
    {G H : AffineFiniteFreeCommGroupScheme R} (f : G ⟶ H) :
    ((toFiniteFlatFunctor R).map f).hom = f.hom :=
  rfl

/-- The finite-free-to-finite-flat inclusion commutes with scalar extension on objects. -/
@[simp]
theorem toFiniteFlatFunctor_baseChange_obj
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : AffineFiniteFreeCommGroupScheme R) :
    (AffineFiniteFlatCommGroupScheme.baseChangeFunctor (R := R) (K := K)).obj
        ((toFiniteFlatFunctor R).obj G) =
      (toFiniteFlatFunctor K).obj
        ((baseChangeFunctor (R := R) (K := K)).obj G) :=
  rfl

/-- The finite-free-to-finite-flat inclusion commutes with scalar extension on morphisms. -/
@[simp]
theorem toFiniteFlatFunctor_baseChange_map
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {G H : AffineFiniteFreeCommGroupScheme R} (f : G ⟶ H) :
    (AffineFiniteFlatCommGroupScheme.baseChangeFunctor (R := R) (K := K)).map
        ((toFiniteFlatFunctor R).map f) =
      (toFiniteFlatFunctor K).map
        ((baseChangeFunctor (R := R) (K := K)).map f) :=
  rfl

/-- Morphisms between affine finite-free group schemes over a domain are determined by their
generic fibres.  This is the finite-free specialization of finite-flat generic-fibre
faithfulness. -/
theorem hom_ext_of_genericFiber_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : AffineFiniteFreeCommGroupScheme A} {f g : G ⟶ H}
    (hfg :
      (baseChangeFunctor (R := A) (K := F)).map f =
        (baseChangeFunctor (R := A) (K := F)).map g) :
    f = g := by
  apply (toFiniteFlatFunctor A).map_injective
  apply AffineFiniteFlatCommGroupScheme.hom_ext_of_genericFiber_eq
    (A := A) (F := F)
  exact congrArg (toFiniteFlatFunctor F).map hfg

/-- Isomorphisms between fixed affine finite-free models are determined by their generic-fibre
morphisms.  This is a uniqueness theorem and does not construct an integral isomorphism. -/
theorem iso_ext_of_genericFiber_hom_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : AffineFiniteFreeCommGroupScheme A} (e e' : G ≅ H)
    (h :
      (baseChangeFunctor (R := A) (K := F)).map e.hom =
        (baseChangeFunctor (R := A) (K := F)).map e'.hom) :
    e = e' := by
  apply Iso.ext
  exact hom_ext_of_genericFiber_eq h

open FiniteFlatCommGroupScheme

/-- Two supplied maps from the constant order-five factor to `mu_5` over the five-adic
completion integers agree if their already-extended generic-fibre maps agree. -/
theorem constantMu_hom_ext_of_completionGenericFiberAtFive_eq
    {f g :
      FiniteFlatCommGroupScheme.constant
          (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ⟶
        mu (atFive.adicCompletionIntegers ℚ) 5}
    (hfg :
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map f =
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map g) :
    f = g :=
  hom_ext_of_genericFiber_eq hfg

/-- Two supplied isomorphisms from the constant order-five factor to `mu_5` over the five-adic
completion integers agree if their already-extended generic-fibre morphisms agree.  This does
not assert that such an isomorphism exists. -/
theorem constantMu_iso_ext_of_completionGenericFiberAtFive_hom_eq
    (e e' :
      FiniteFlatCommGroupScheme.constant
          (atFive.adicCompletionIntegers ℚ) (Multiplicative (ZMod 5)) ≅
        mu (atFive.adicCompletionIntegers ℚ) 5)
    (h :
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map e.hom =
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map e'.hom) :
    e = e' :=
  iso_ext_of_genericFiber_hom_eq e e' h

/-- Two supplied maps from the constant order-eleven factor to `mu_11` over the eleven-adic
completion integers agree if their already-extended generic-fibre maps agree. -/
theorem constantMu_hom_ext_of_completionGenericFiberAtEleven_eq
    {f g :
      FiniteFlatCommGroupScheme.constant
          (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ⟶
        mu (atEleven.adicCompletionIntegers ℚ) 11}
    (hfg :
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map f =
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map g) :
    f = g :=
  hom_ext_of_genericFiber_eq hfg

/-- Two supplied isomorphisms from the constant order-eleven factor to `mu_11` over the
eleven-adic completion integers agree if their already-extended generic-fibre morphisms agree.
This does not assert that such an isomorphism exists. -/
theorem constantMu_iso_ext_of_completionGenericFiberAtEleven_hom_eq
    (e e' :
      FiniteFlatCommGroupScheme.constant
          (atEleven.adicCompletionIntegers ℚ) (Multiplicative (ZMod 11)) ≅
        mu (atEleven.adicCompletionIntegers ℚ) 11)
    (h :
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map e.hom =
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map e'.hom) :
    e = e' :=
  iso_ext_of_genericFiber_hom_eq e e' h

end AffineFiniteFreeCommGroupScheme

end AlgebraicGeometry
