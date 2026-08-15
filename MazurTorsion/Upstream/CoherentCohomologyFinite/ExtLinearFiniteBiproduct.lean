/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Linear Ext equivalences for isomorphisms and finite biproducts

In a linear abelian category, the standard Ext equivalences induced by
isomorphisms and finite biproducts respect the coefficient-ring action.
This file packages those additive equivalences as linear equivalences.
-/


open CategoryTheory Limits

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction

universe u v w t

variable {R : Type t} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasExt.{w} C]

/-- Postcomposition with an isomorphism is a linear equivalence on Ext. -/
noncomputable def postcompIsoLinearEquiv
    {X Y Z : C} (e : Y ≅ Z) (n : ℕ) :
    Abelian.Ext X Y n ≃ₗ[R] Abelian.Ext X Z n where
  toAddEquiv := postcompIsoAddEquiv e n
  map_smul' r x := by
    simp [postcompIsoAddEquiv]

/-- Precomposition with an isomorphism is a linear equivalence on Ext. -/
noncomputable def precompIsoLinearEquiv
    {X Y Z : C} (e : X ≅ Y) (n : ℕ) :
    Abelian.Ext Y Z n ≃ₗ[R] Abelian.Ext X Z n where
  toAddEquiv := precompIsoAddEquiv e n
  map_smul' r x := by
    simp [precompIsoAddEquiv]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction

namespace CategoryTheory.Abelian.Ext

universe u v w t

variable {R : Type t} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasExt.{w} C]

/-- Ext in the first variable sends a finite biproduct to the product,
as a coefficient-linear equivalence. -/
noncomputable def biproductLinearEquiv
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) :
    Abelian.Ext c.pt Y n ≃ₗ[R]
      ∀ i, Abelian.Ext (X i) Y n where
  toAddEquiv := Abelian.Ext.biproductAddEquiv hc Y n
  map_smul' r x := by
    ext i
    simp [Abelian.Ext.biproductAddEquiv]

/-- Ext in the second variable sends a finite biproduct to the product,
as a coefficient-linear equivalence. -/
noncomputable def addLinearEquivBiproduct
    (X : C) {J : Type*} [Fintype J] {Y : J → C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : ℕ) :
    Abelian.Ext X c.pt n ≃ₗ[R]
      ∀ i, Abelian.Ext X (Y i) n where
  toAddEquiv := Abelian.Ext.addEquivBiproduct X hc n
  map_smul' r x := by
    ext i
    simp [Abelian.Ext.addEquivBiproduct]

end CategoryTheory.Abelian.Ext

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u v w t

variable {R : Type t} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasExt.{w} C]

/-- Ext-finiteness is invariant under an isomorphism in the covariant
variable. -/
theorem extFinite_congr_right
    {X Y Z : C} (e : Y ≅ Z) (n : ℕ)
    [Module.Finite R (Abelian.Ext X Z n)] :
    Module.Finite R (Abelian.Ext X Y n) :=
  Module.Finite.equiv
    (ExtAdjunction.postcompIsoLinearEquiv
      (R := R) e n).symm

/-- Ext-finiteness is invariant under an isomorphism in the
contravariant variable. -/
theorem extFinite_congr_left
    {X Y Z : C} (e : X ≅ Y) (n : ℕ)
    [Module.Finite R (Abelian.Ext X Z n)] :
    Module.Finite R (Abelian.Ext Y Z n) :=
  Module.Finite.equiv
    (ExtAdjunction.precompIsoLinearEquiv
      (R := R) e n).symm

/-- Ext into a finite biproduct is finite when Ext into every summand is
finite. -/
theorem extFinite_biproduct_right
    (X : C) {J : Type*} [Fintype J]
    {Y : J → C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : ℕ)
    (hfinite :
      ∀ j, Module.Finite R (Abelian.Ext X (Y j) n)) :
    Module.Finite R (Abelian.Ext X c.pt n) := by
  letI :
      ∀ j, Module.Finite R (Abelian.Ext X (Y j) n) :=
    hfinite
  letI :
      Module.Finite R
        (∀ j, Abelian.Ext X (Y j) n) := by
    infer_instance
  exact
    Module.Finite.equiv
      (Abelian.Ext.addLinearEquivBiproduct
        (R := R) X hc n).symm

/-- Ext out of a finite biproduct is finite when Ext out of every
summand is finite. -/
theorem extFinite_biproduct_left
    {J : Type*} [Fintype J]
    {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ)
    (hfinite :
      ∀ j, Module.Finite R (Abelian.Ext (X j) Y n)) :
    Module.Finite R (Abelian.Ext c.pt Y n) := by
  letI :
      ∀ j, Module.Finite R (Abelian.Ext (X j) Y n) :=
    hfinite
  letI :
      Module.Finite R
        (∀ j, Abelian.Ext (X j) Y n) := by
    infer_instance
  exact
    Module.Finite.equiv
      (Abelian.Ext.biproductLinearEquiv
        (R := R) hc Y n).symm

/-- An additive functor carries a finite coproduct to a biproduct.
Consequently, Ext into its image is finite whenever Ext into the image
of each summand is finite. -/
theorem extFinite_obj_finiteCoproduct
    {A : Type*} [Category A] [Preadditive A]
    [HasColimits A]
    (F : A ⥤ C) [F.Additive]
    (X : C) {J : Type*} [Fintype J]
    (Y : J → A) (n : ℕ)
    (hfinite :
      ∀ j, Module.Finite R
        (Abelian.Ext X (F.obj (Y j)) n)) :
    Module.Finite R
      (Abelian.Ext X (F.obj (∐ Y)) n) := by
  let c : Bicone (fun j => F.obj (Y j)) :=
    Bicone.ofColimitCocone
      (colimit.isColimit
        (Discrete.functor fun j => F.obj (Y j)))
  have hc : c.IsBilimit :=
    biconeIsBilimitOfColimitCoconeOfIsColimit
      (colimit.isColimit
        (Discrete.functor fun j => F.obj (Y j)))
  letI :
      Module.Finite R
        (Abelian.Ext X (∐ fun j => F.obj (Y j)) n) :=
    extFinite_biproduct_right X hc n hfinite
  exact
    extFinite_congr_right
      (PreservesCoproduct.iso F Y) n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
