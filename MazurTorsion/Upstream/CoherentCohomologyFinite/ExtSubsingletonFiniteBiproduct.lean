/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Ext vanishing and finite biproducts

Ext in either variable sends a finite biproduct to a finite product.
Thus positive-degree Ext vanishing is preserved by finite biproducts
and by the image of a finite coproduct under an additive functor.
-/


open CategoryTheory Limits

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u v w

/-- Ext vanishing in the covariant variable is preserved by finite
biproducts. -/
theorem ext_subsingleton_finite_coproduct_right
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C]
    {J : Type*} [Fintype J]
    (X : C) (Y : J → C) (n : ℕ)
    (hY : ∀ j, Subsingleton (Abelian.Ext.{w} X (Y j) n)) :
    Subsingleton (Abelian.Ext.{w} X (∐ Y) n) := by
  let c : Bicone Y :=
    Bicone.ofColimitCocone
      (colimit.isColimit (Discrete.functor Y))
  let hc : c.IsBilimit :=
    biconeIsBilimitOfColimitCoconeOfIsColimit
      (colimit.isColimit (Discrete.functor Y))
  let e :
      Abelian.Ext.{w} X c.pt n ≃+
        ((j : J) → Abelian.Ext.{w} X (Y j) n) :=
    Abelian.Ext.addEquivBiproduct X hc n
  letI (j : J) :
      Subsingleton (Abelian.Ext.{w} X (Y j) n) :=
    hY j
  exact
    ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩

/--
An additive functor carries a finite coproduct to a biproduct, so Ext
into its image vanishes when Ext into every mapped summand vanishes.
-/
theorem ext_subsingleton_obj_finiteCoproduct
    {A : Type*} [Category A] [Preadditive A] [HasColimits A]
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C]
    (F : A ⥤ C) [F.Additive]
    (X : C) {J : Type*} [Fintype J]
    (Y : J → A) (n : ℕ)
    (hY :
      ∀ j, Subsingleton
        (Abelian.Ext.{w} X (F.obj (Y j)) n)) :
    Subsingleton
      (Abelian.Ext.{w} X (F.obj (∐ Y)) n) := by
  have hsum :
      Subsingleton
        (Abelian.Ext.{w} X
          (∐ fun j => F.obj (Y j)) n) :=
    ext_subsingleton_finite_coproduct_right
      X (fun j => F.obj (Y j)) n hY
  let E :=
    ExtAdjunction.postcompIsoAddEquiv
      (X := X)
      (Z := F.obj (∐ Y))
      (PreservesCoproduct.iso F Y).symm n
  exact
    ⟨fun x y =>
      E.symm.injective
        (hsum.elim (E.symm x) (E.symm y))⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
