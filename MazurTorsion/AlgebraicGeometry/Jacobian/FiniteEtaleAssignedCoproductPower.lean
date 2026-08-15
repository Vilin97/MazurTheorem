/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleCoproductPower

/-!
# Assigned coordinates in a finite étale coproduct power

The number `m` of distinct local support neighborhoods need not equal the
degree `d` of an ordered divisor.  An assignment `a : Fin d → Fin m` says
which neighborhood contains each ordered occurrence.  Repeated coordinates
therefore select the same coproduct member and contribute multiplicity to
one graph factor.

This file separates the family size from the power degree in the coproduct-
power construction and records compatibility with maps to an original
target.  The named downstream consumer is the distinct-support fpqc chart in
`FiniteSupportEtaleCoordinates`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleAssignedCoproductPower

open FiniteEtaleCoproductPower

/-- The relative product whose `i`-th coordinate uses the family member
selected by `a i`. -/
noncomputable abbrev assignedProduct (S : Scheme.{u}) (m d : ℕ)
    (X : Fin m → Over S) (a : Fin d → Fin m) : Over S :=
  ∏ᶜ fun i : Fin d ↦ X (a i)

/-- Repeat or reorder the factors of the full family product according to
an assignment. -/
noncomputable def productToAssignedProduct
    (S : Scheme.{u}) (m d : ℕ) (X : Fin m → Over S)
    (a : Fin d → Fin m) :
    (∏ᶜ X) ⟶ assignedProduct S m d X a :=
  Pi.lift (fun i ↦ Pi.π X (a i))

@[reassoc]
theorem productToAssignedProduct_comp_projection
    (S : Scheme.{u}) (m d : ℕ) (X : Fin m → Over S)
    (a : Fin d → Fin m) (i : Fin d) :
    productToAssignedProduct S m d X a ≫
        Pi.π (fun i : Fin d ↦ X (a i)) i =
      Pi.π X (a i) :=
  Pi.lift_π _ i

/-- Insert each assigned family member into the matching coordinate of the
ordered power of the whole disjoint family. -/
noncomputable def assignedProductToCoproductPower
    (S : Scheme.{u}) (m d : ℕ) (X : Fin m → Over S)
    (a : Fin d → Fin m) :
    assignedProduct S m d X a ⟶
      ∏ᶜ fun _ : Fin d ↦ familyCoproduct S m X :=
  Limits.Pi.map (fun i ↦ inclusion S m X (a i))

@[reassoc]
theorem assignedProductToCoproductPower_comp_projection
    (S : Scheme.{u}) (m d : ℕ) (X : Fin m → Over S)
    (a : Fin d → Fin m) (i : Fin d) :
    assignedProductToCoproductPower S m d X a ≫
        Pi.π (fun _ : Fin d ↦ familyCoproduct S m X) i =
      Pi.π (fun i : Fin d ↦ X (a i)) i ≫ inclusion S m X (a i) :=
  Limits.Pi.map_π (fun i ↦ inclusion S m X (a i)) i

/-- Regard the assigned relative product over a further original base. -/
noncomputable abbrev assignedProductOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) (a : Fin d → Fin m) : Over T :=
  Over.mk ((assignedProduct S m d X a).hom ≫ s)

/-- Regard the full family product over a further original base. -/
noncomputable abbrev productOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (m : ℕ)
    (X : Fin m → Over S) : Over T :=
  Over.mk ((∏ᶜ X).hom ≫ s)

/-- Repeat or reorder the full family product over a further original
base. -/
noncomputable def productToAssignedProductOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) (a : Fin d → Fin m) :
    productOverOriginalBase S T s m X ⟶
      assignedProductOverOriginalBase S T s m d X a :=
  Over.homMk (productToAssignedProduct S m d X a).left (by
    have h := (productToAssignedProduct S m d X a).w
    exact congrArg (fun q ↦ q ≫ s) h)

/-- Regard the degree-`d` power of the family coproduct over a further
original base. -/
noncomputable abbrev assignedCoproductPowerOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) : Over T :=
  Over.mk ((∏ᶜ fun _ : Fin d ↦ familyCoproduct S m X).hom ≫ s)

/-- The assigned product-to-power map over a further original base. -/
noncomputable def assignedProductToCoproductPowerOverOriginalBase
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) (a : Fin d → Fin m) :
    assignedProductOverOriginalBase S T s m d X a ⟶
      assignedCoproductPowerOverOriginalBase S T s m d X :=
  Over.homMk (assignedProductToCoproductPower S m d X a).left (by
    have h := (assignedProductToCoproductPower S m d X a).w
    exact congrArg (fun q ↦ q ≫ s) h)

/-- Map the assigned relative product directly to the degree-`d` power of a
target over the original base. -/
noncomputable def assignedProductToTargetPower
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) (a : Fin d → Fin m)
    (C : Over T) (g : ∀ j, (X j).left ⟶ C.left)
    (hg : ∀ j, g j ≫ C.hom = (X j).hom ≫ s) :
    assignedProductOverOriginalBase S T s m d X a ⟶
      ∏ᶜ fun _ : Fin d ↦ C :=
  Pi.lift (fun i ↦ Over.homMk
    ((Pi.π (fun i : Fin d ↦ X (a i)) i).left ≫ g (a i)) (by
      have hπ := (Pi.π (fun i : Fin d ↦ X (a i)) i).w
      calc
        (Pi.π (fun i : Fin d ↦ X (a i)) i).left ≫ g (a i) ≫ C.hom =
            (Pi.π (fun i : Fin d ↦ X (a i)) i).left ≫
              ((X (a i)).hom ≫ s) := by rw [hg (a i)]
        _ = (assignedProduct S m d X a).hom ≫ s := by
          simpa only [Category.assoc] using
            congrArg (fun q ↦ q ≫ s) hπ))

/-- Forget every coordinate of the assigned coproduct power to the target. -/
noncomputable def assignedCoproductPowerToTargetPower
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) (C : Over T)
    (g : ∀ j, (X j).left ⟶ C.left)
    (hg : ∀ j, g j ≫ C.hom = (X j).hom ≫ s) :
    assignedCoproductPowerOverOriginalBase S T s m d X ⟶
      ∏ᶜ fun _ : Fin d ↦ C :=
  Pi.lift (fun i ↦ Over.homMk
    ((Pi.π (fun _ : Fin d ↦ familyCoproduct S m X) i).left ≫
      (coproductToTarget S T s m X C g hg).left) (by
        have hπ :=
          (Pi.π (fun _ : Fin d ↦ familyCoproduct S m X) i).w
        have ht := (coproductToTarget S T s m X C g hg).w
        calc
          (Pi.π (fun _ : Fin d ↦ familyCoproduct S m X) i).left ≫
                (coproductToTarget S T s m X C g hg).left ≫ C.hom =
              (Pi.π (fun _ : Fin d ↦ familyCoproduct S m X) i).left ≫
                ((familyCoproduct S m X).hom ≫ s) := by
                  rw [ht]
                  rfl
          _ = (∏ᶜ fun _ : Fin d ↦ familyCoproduct S m X).hom ≫ s := by
            simpa only [Category.assoc] using
              congrArg (fun q ↦ q ≫ s) hπ))

/-- The underlying scheme map of the assigned target map has the expected
coordinate projection. -/
theorem assignedProductToTargetPower_comp_projection_left
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) (a : Fin d → Fin m)
    (C : Over T) (g : ∀ j, (X j).left ⟶ C.left)
    (hg : ∀ j, g j ≫ C.hom = (X j).hom ≫ s) (i : Fin d) :
    (assignedProductToTargetPower S T s m d X a C g hg ≫
        Pi.π (fun _ : Fin d ↦ C) i).left =
      (Pi.π (fun i : Fin d ↦ X (a i)) i).left ≫ g (a i) :=
  congrArg Over.Hom.left (Pi.lift_π _ i)

/-- Assigned coproduct insertion followed by the target map is exactly the
coordinatewise map from each selected family member. -/
theorem assignedProductToCoproductPower_comp_targetPower
    (S T : Scheme.{u}) (s : S ⟶ T) (m d : ℕ)
    (X : Fin m → Over S) (a : Fin d → Fin m)
    (C : Over T) (g : ∀ j, (X j).left ⟶ C.left)
    (hg : ∀ j, g j ≫ C.hom = (X j).hom ≫ s) :
    assignedProductToCoproductPowerOverOriginalBase S T s m d X a ≫
        assignedCoproductPowerToTargetPower S T s m d X C g hg =
      assignedProductToTargetPower S T s m d X a C g hg := by
  apply Pi.hom_ext
  intro i
  unfold assignedCoproductPowerToTargetPower assignedProductToTargetPower
  rw [Category.assoc, Pi.lift_π, Pi.lift_π]
  apply Over.OverMorphism.ext
  change (assignedProductToCoproductPower S m d X a ≫
        Pi.π (fun _ : Fin d ↦ familyCoproduct S m X) i).left ≫
      (coproductToTarget S T s m X C g hg).left =
    (Pi.π (fun i : Fin d ↦ X (a i)) i).left ≫ g (a i)
  rw [congrArg Over.Hom.left
    (assignedProductToCoproductPower_comp_projection S m d X a i)]
  change ((Pi.π (fun i : Fin d ↦ X (a i)) i).left ≫
      (inclusion S m X (a i)).left) ≫
        (coproductToTarget S T s m X C g hg).left =
    (Pi.π (fun i : Fin d ↦ X (a i)) i).left ≫ g (a i)
  rw [Category.assoc,
    inclusion_comp_coproductToTarget S T s m X C g hg (a i)]

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleAssignedCoproductPower
