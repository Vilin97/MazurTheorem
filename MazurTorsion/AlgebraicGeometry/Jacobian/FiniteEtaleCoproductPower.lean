/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleRelativeProduct
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Finite étale coproducts and their ordered powers

A finite family of finite étale schemes over one base assembles into one
finite étale scheme by disjoint union.  Its relative ordered power contains
the relative product of the original family, by using the `i`-th coproduct
inclusion in the `i`-th coordinate.  The construction is compatible with a
further map of bases and with maps from every family member to one target.

The named downstream consumer is the coherent split support chart in
`FiniteSupportEtaleCoordinates`: its separately chosen support neighborhoods
become one split finite cover before applying the symmetric-quotient model.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleCoproductPower

/-- The disjoint union of a finite family over its common base. -/
noncomputable abbrev familyCoproduct (S : Scheme.{u}) (n : ℕ)
    (X : Fin n → Over S) : Over S :=
  Over.mk (Sigma.desc fun i ↦ (X i).hom)

/-- Inclusion of one member into the disjoint family over the base. -/
noncomputable def inclusion (S : Scheme.{u}) (n : ℕ)
    (X : Fin n → Over S) (i : Fin n) :
    X i ⟶ familyCoproduct S n X :=
  Over.homMk (Sigma.ι (fun j ↦ (X j).left) i) (by
    exact Sigma.ι_desc (fun j ↦ (X j).hom) i)

/-- A disjoint union of étale morphisms to the same target is étale. -/
theorem familyCoproduct_etale (S : Scheme.{u}) (n : ℕ)
    (X : Fin n → Over S) (hX : ∀ i, Etale (X i).hom) :
    Etale (familyCoproduct S n X).hom := by
  letI : IsZariskiLocalAtSource (@Etale) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Etale) (Q := RingHom.Etale)
  exact IsZariskiLocalAtSource.sigmaDesc hX

/-- Put the `i`-th family member into the `i`-th coordinate of the ordered
power of the disjoint union. -/
noncomputable def productToCoproductPower (S : Scheme.{u}) (n : ℕ)
    (X : Fin n → Over S) :
    ∏ᶜ X ⟶ ∏ᶜ fun _ : Fin n ↦ familyCoproduct S n X :=
  Limits.Pi.map (fun i ↦ inclusion S n X i)

@[reassoc]
theorem productToCoproductPower_comp_projection
    (S : Scheme.{u}) (n : ℕ) (X : Fin n → Over S) (i : Fin n) :
    productToCoproductPower S n X ≫
        Pi.π (fun _ : Fin n ↦ familyCoproduct S n X) i =
      Pi.π X i ≫ inclusion S n X i :=
  Limits.Pi.map_π (fun i ↦ inclusion S n X i) i

/-- Regard the relative product of the family over a further original
base. -/
noncomputable abbrev productOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S) :
    Over T :=
  Over.mk ((∏ᶜ X).hom ≫ s)

/-- Regard the ordered power of the family coproduct over a further
original base. -/
noncomputable abbrev coproductPowerOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S) :
    Over T :=
  Over.mk ((∏ᶜ fun _ : Fin n ↦ familyCoproduct S n X).hom ≫ s)

/-- The product-to-power map, transported along a further base morphism. -/
noncomputable def productToCoproductPowerOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S) :
    productOverOriginalBase S T s n X ⟶
      coproductPowerOverOriginalBase S T s n X :=
  Over.homMk (productToCoproductPower S n X).left (by
    have h := (productToCoproductPower S n X).w
    exact congrArg (fun a ↦ a ≫ s) h)

/-- The disjoint family maps to a target over an original base whenever
each member does. -/
noncomputable def coproductToTarget
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S)
    (C : Over T) (g : ∀ i, (X i).left ⟶ C.left)
    (hg : ∀ i, g i ≫ C.hom = (X i).hom ≫ s) :
    Over.mk ((familyCoproduct S n X).hom ≫ s) ⟶ C :=
  Over.homMk (Sigma.desc g) (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (fun j ↦ (X j).left) i ≫ Sigma.desc g ≫ C.hom =
      Sigma.ι (fun j ↦ (X j).left) i ≫
        Sigma.desc (fun j ↦ (X j).hom) ≫ s
    calc
      _ = g i ≫ C.hom := by rw [← Category.assoc, Sigma.ι_desc]
      _ = (X i).hom ≫ s := hg i
      _ = _ := by rw [← Category.assoc, Sigma.ι_desc])

@[reassoc]
theorem inclusion_comp_coproductToTarget
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S)
    (C : Over T) (g : ∀ i, (X i).left ⟶ C.left)
    (hg : ∀ i, g i ≫ C.hom = (X i).hom ≫ s) (i : Fin n) :
    (inclusion S n X i).left ≫
        (coproductToTarget S T s n X C g hg).left = g i :=
  Sigma.ι_desc g i

/-- Map the relative product directly to the ordered power of a target over
the original base. -/
noncomputable def productToTargetPower
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S)
    (C : Over T) (g : ∀ i, (X i).left ⟶ C.left)
    (hg : ∀ i, g i ≫ C.hom = (X i).hom ≫ s) :
    productOverOriginalBase S T s n X ⟶ ∏ᶜ fun _ : Fin n ↦ C :=
  Pi.lift (fun i ↦ Over.homMk ((Pi.π X i).left ≫ g i) (by
    have hπ := (Pi.π X i).w
    calc
      (Pi.π X i).left ≫ g i ≫ C.hom =
          (Pi.π X i).left ≫ ((X i).hom ≫ s) := by rw [hg i]
      _ = ((∏ᶜ X).hom ≫ s) := by
        simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ s) hπ))

/-- Forget every coordinate of the coproduct power to the target over the
original base. -/
noncomputable def coproductPowerToTargetPower
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S)
    (C : Over T) (g : ∀ i, (X i).left ⟶ C.left)
    (hg : ∀ i, g i ≫ C.hom = (X i).hom ≫ s) :
    coproductPowerOverOriginalBase S T s n X ⟶
      ∏ᶜ fun _ : Fin n ↦ C :=
  Pi.lift (fun i ↦
    Over.homMk
      ((Pi.π (fun _ : Fin n ↦ familyCoproduct S n X) i).left ≫
        (coproductToTarget S T s n X C g hg).left)
      (by
        have hπ :=
          (Pi.π (fun _ : Fin n ↦ familyCoproduct S n X) i).w
        have ht := (coproductToTarget S T s n X C g hg).w
        calc
          (Pi.π (fun _ : Fin n ↦ familyCoproduct S n X) i).left ≫
                (coproductToTarget S T s n X C g hg).left ≫ C.hom =
              (Pi.π (fun _ : Fin n ↦ familyCoproduct S n X) i).left ≫
                ((familyCoproduct S n X).hom ≫ s) := by
                  rw [ht]
                  rfl
          _ = ((∏ᶜ fun _ : Fin n ↦ familyCoproduct S n X).hom ≫ s) := by
            simpa only [Category.assoc] using
              congrArg (fun a ↦ a ≫ s) hπ))

/-- Inserting every family member into the coproduct power and then
forgetting to the target is exactly the original coordinatewise map. -/
theorem productToCoproductPower_comp_targetPower
    (S T : Scheme.{u}) (s : S ⟶ T) (n : ℕ) (X : Fin n → Over S)
    (C : Over T) (g : ∀ i, (X i).left ⟶ C.left)
    (hg : ∀ i, g i ≫ C.hom = (X i).hom ≫ s) :
    productToCoproductPowerOverOriginalBase S T s n X ≫
        coproductPowerToTargetPower S T s n X C g hg =
      productToTargetPower S T s n X C g hg := by
  apply Pi.hom_ext
  intro i
  unfold coproductPowerToTargetPower productToTargetPower
  rw [Category.assoc, Pi.lift_π, Pi.lift_π]
  apply Over.OverMorphism.ext
  change (productToCoproductPower S n X ≫
        Pi.π (fun _ : Fin n ↦ familyCoproduct S n X) i).left ≫
      (coproductToTarget S T s n X C g hg).left =
    (Pi.π X i).left ≫ g i
  rw [congrArg Over.Hom.left
      (productToCoproductPower_comp_projection S n X i)]
  change ((Pi.π X i).left ≫ (inclusion S n X i).left) ≫
      (coproductToTarget S T s n X C g hg).left =
    (Pi.π X i).left ≫ g i
  rw [Category.assoc,
    inclusion_comp_coproductToTarget S T s n X C g hg i]

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleCoproductPower
