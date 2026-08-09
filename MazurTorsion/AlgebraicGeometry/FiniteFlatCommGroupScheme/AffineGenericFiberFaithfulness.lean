/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine

/-!
# Faithfulness of generic-fibre base change for affine finite-flat group schemes

If the scalar map `R → K` is injective, scalar extension is faithful on morphisms of affine
finite-flat commutative group schemes.  Contravariantly, equality after scalar extension can be
tested on coordinate functions of the form `1 ⊗ a`; flatness of the target coordinate module
makes `a ↦ 1 ⊗ a` injective.

This is the uniqueness half of the generic-fibre extension interface used by Raynaud-style
arguments.  It neither constructs an integral extension nor classifies prime-order factors.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.AffineFiniteFlatCommGroupScheme

universe u

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]

/-- Scalar extension along an injective scalar map is injective on morphisms of affine
finite-flat commutative group schemes. -/
theorem baseChangeFunctor_map_injective
    (hRK : Function.Injective (algebraMap R K))
    {G H : AffineFiniteFlatCommGroupScheme R} :
    Function.Injective
      (fun f : G ⟶ H ↦
        (baseChangeFunctor (R := R) (K := K)).map f) := by
  intro f g hfg
  apply ObjectProperty.hom_ext
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro a
  have hbase :
      (TauCeti.CommHopfAlgCat.baseChangeMap (K := K) f.hom.unop.hom).hom
          (1 ⊗ₜ[R] a) =
        (TauCeti.CommHopfAlgCat.baseChangeMap (K := K) g.hom.unop.hom).hom
          (1 ⊗ₜ[R] a) := by
    have h := congrArg
      (fun q ↦ AffineCommGroupScheme.coordinateMap q.hom (1 ⊗ₜ[R] a)) hfg
    exact h
  apply Algebra.TensorProduct.includeRight_injective
      (A := K) (B := G.coordinates) hRK
  change (1 ⊗ₜ[R] f.hom.unop.hom a : K ⊗[R] G.coordinates) =
    1 ⊗ₜ[R] g.hom.unop.hom a
  rw [← TauCeti.CommHopfAlgCat.baseChangeMap_apply_tmul
      (K := K) f.hom.unop.hom 1 a,
    ← TauCeti.CommHopfAlgCat.baseChangeMap_apply_tmul
      (K := K) g.hom.unop.hom 1 a]
  exact hbase

/-- Categorical form of `baseChangeFunctor_map_injective`: injective scalar extension is a
faithful functor on affine finite-flat commutative group schemes. -/
theorem baseChangeFunctor_faithful
    (hRK : Function.Injective (algebraMap R K)) :
    (baseChangeFunctor (R := R) (K := K)).Faithful where
  map_injective := fun {X Y} ↦
    baseChangeFunctor_map_injective (G := X) (H := Y) hRK

/-- Two integral morphisms agreeing after injective scalar extension agree already over the
base.  This is the direct uniqueness interface for a fixed pair of integral models. -/
theorem hom_ext_of_baseChange_eq
    (hRK : Function.Injective (algebraMap R K))
    {G H : AffineFiniteFlatCommGroupScheme R} {f g : G ⟶ H}
    (hfg : (baseChangeFunctor (R := R) (K := K)).map f =
      (baseChangeFunctor (R := R) (K := K)).map g) :
    f = g :=
  baseChangeFunctor_map_injective hRK hfg

/-- Isomorphisms between fixed affine finite-flat models are uniquely determined by their
scalar extensions.  Existence of such an extension remains a separate Raynaud input. -/
theorem iso_ext_of_baseChange_hom_eq
    (hRK : Function.Injective (algebraMap R K))
    {G H : AffineFiniteFlatCommGroupScheme R} (e e' : G ≅ H)
    (h : (baseChangeFunctor (R := R) (K := K)).map e.hom =
      (baseChangeFunctor (R := R) (K := K)).map e'.hom) :
    e = e' := by
  apply Iso.ext
  exact hom_ext_of_baseChange_eq hRK h

/-- Over a domain, morphisms between affine finite-flat models are determined by their generic
fibres.  No unramifiedness assumption is needed for this uniqueness statement; unramifiedness
belongs to the separate existence/classification theorem. -/
theorem hom_ext_of_genericFiber_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : AffineFiniteFlatCommGroupScheme A} {f g : G ⟶ H}
    (hfg : (baseChangeFunctor (R := A) (K := F)).map f =
      (baseChangeFunctor (R := A) (K := F)).map g) :
    f = g :=
  hom_ext_of_baseChange_eq (IsFractionRing.injective A F) hfg

/-- Integral isomorphisms between fixed affine finite-flat models are determined by their
generic-fibre morphisms.  This is a checked uniqueness consumer, not an extension theorem. -/
theorem iso_ext_of_genericFiber_hom_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : AffineFiniteFlatCommGroupScheme A} (e e' : G ≅ H)
    (h : (baseChangeFunctor (R := A) (K := F)).map e.hom =
      (baseChangeFunctor (R := A) (K := F)).map e'.hom) :
    e = e' := by
  apply Iso.ext
  exact hom_ext_of_genericFiber_eq h

end AlgebraicGeometry.AffineFiniteFlatCommGroupScheme
