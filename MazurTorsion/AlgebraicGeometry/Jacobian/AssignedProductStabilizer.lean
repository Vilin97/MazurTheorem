/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleAssignedCoproductPower
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitTupleStabilizer

/-!
# Stabilizer actions on assigned relative products

An assignment `a : Fin d → Fin m` selects one member of a finite family for
each ordered occurrence.  Its tuple stabilizer permutes only occurrences
with the same assigned member, hence acts canonically on the dependent
relative product `∏ i, X (a i)`.  The insertion of this assigned product into
the ordered power of the family coproduct is equivariant.

The named downstream consumer is the occurrence-wise étale chart in
`FiniteSupportEtaleCoordinates`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AssignedProductStabilizer

open FiniteEtaleAssignedCoproductPower
open FiniteEtaleCoproductPower
open SplitFiniteSymmetricQuotient
open SplitTupleStabilizer

variable (S : Scheme.{u}) (m d : ℕ) (X : Fin m → Over S)
variable (a : Fin d → Fin m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- Reindex the assigned dependent product by a permutation that stabilizes
the assignment. -/
noncomputable def permutationHom
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) :
    assignedProduct S m d X a ⟶ assignedProduct S m d X a :=
  Pi.lift fun i ↦
    Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i) ≫
      eqToHom (congrArg X (stabilizer_apply_eq d m a g i))

@[reassoc]
theorem permutationHom_comp_projection
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) (i : Fin d) :
    permutationHom S m d X a g ≫
        Pi.π (fun j : Fin d ↦ X (a j)) i =
      Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i) ≫
        eqToHom (congrArg X (stabilizer_apply_eq d m a g i)) :=
  Pi.lift_π _ i

/-- The identity stabilizer acts identically on the assigned product. -/
theorem permutationHom_one :
    permutationHom S m d X a 1 = 𝟙 (assignedProduct S m d X a) := by
  apply Pi.hom_ext
  intro i
  rw [permutationHom_comp_projection, Category.id_comp]
  simp

/-- Stabilizer reindexing is compatible with multiplication. -/
theorem permutationHom_mul
    (g h : MulAction.stabilizer (Equiv.Perm (Fin d)) a) :
    permutationHom S m d X a (g * h) =
      permutationHom S m d X a g ≫ permutationHom S m d X a h := by
  apply Pi.hom_ext
  intro i
  rw [permutationHom_comp_projection, Category.assoc,
    permutationHom_comp_projection, ← Category.assoc,
    permutationHom_comp_projection]
  simp

/-- Transporting one family member along equality of its index and then
inserting it into the family coproduct is the original insertion. -/
theorem eqToHom_comp_inclusion {j k : Fin m} (h : j = k) :
    eqToHom (congrArg X h) ≫ inclusion S m X k = inclusion S m X j := by
  subst k
  simp

/-- Apply a family of morphisms coordinatewise to an assigned product. -/
noncomputable def assignedMap (Y : Over S) (f : ∀ j, X j ⟶ Y) :
    assignedProduct S m d X a ⟶ PermutationPower.power S (Fin d) Y :=
  Limits.Pi.map fun i ↦ f (a i)

@[reassoc]
theorem assignedMap_comp_projection (Y : Over S) (f : ∀ j, X j ⟶ Y)
    (i : Fin d) :
    assignedMap S m d X a Y f ≫ Pi.π (fun _ : Fin d ↦ Y) i =
      Pi.π (fun i : Fin d ↦ X (a i)) i ≫ f (a i) :=
  Limits.Pi.map_π _ i

/-- Mapping a full indexed family and then repeating by an assignment agrees
with first repeating the source family and then applying its assigned map. -/
theorem productToAssignedProduct_comp_assignedMap
    (Y : Over S) (f : ∀ j, X j ⟶ Y) :
    productToAssignedProduct S m d X a ≫
        assignedMap S m d X a Y f =
      Limits.Pi.map f ≫ assignmentRepeatHom S m d Y a := by
  apply Pi.hom_ext
  intro i
  calc
    (productToAssignedProduct S m d X a ≫
          assignedMap S m d X a Y f) ≫
        Pi.π (fun _ : Fin d ↦ Y) i =
      productToAssignedProduct S m d X a ≫
        (Pi.π (fun i : Fin d ↦ X (a i)) i ≫ f (a i)) := by
          rw [Category.assoc, assignedMap_comp_projection]
    _ = (productToAssignedProduct S m d X a ≫
          Pi.π (fun i : Fin d ↦ X (a i)) i) ≫ f (a i) :=
      (Category.assoc _ _ _).symm
    _ = Pi.π X (a i) ≫ f (a i) := by
      rw [productToAssignedProduct_comp_projection]
    _ = Limits.Pi.map f ≫ Pi.π (fun _ : Fin m ↦ Y) (a i) :=
      (Limits.Pi.map_π f (a i)).symm
    _ = Limits.Pi.map f ≫
        (assignmentRepeatHom S m d Y a ≫
          Pi.π (fun _ : Fin d ↦ Y) i) := by
      rw [assignmentRepeatHom_comp_projection]
    _ = (Limits.Pi.map f ≫ assignmentRepeatHom S m d Y a) ≫
        Pi.π (fun _ : Fin d ↦ Y) i :=
      (Category.assoc _ _ _).symm

/-- Transporting a family member and then applying its indexed map is the
map attached to the original index. -/
theorem eqToHom_comp_familyMap (Y : Over S) (f : ∀ j, X j ⟶ Y)
    {j k : Fin m} (h : j = k) :
    eqToHom (congrArg X h) ≫ f k = f j := by
  subst k
  simp

/-- Apply a morphism of indexed families coordinatewise to an assigned
product. -/
noncomputable def assignedFamilyMap (Y : Fin m → Over S)
    (f : ∀ j, X j ⟶ Y j) :
    assignedProduct S m d X a ⟶ assignedProduct S m d Y a :=
  Limits.Pi.map fun i ↦ f (a i)

@[reassoc]
theorem assignedFamilyMap_comp_projection (Y : Fin m → Over S)
    (f : ∀ j, X j ⟶ Y j) (i : Fin d) :
    assignedFamilyMap S m d X a Y f ≫ Pi.π (fun i : Fin d ↦ Y (a i)) i =
      Pi.π (fun i : Fin d ↦ X (a i)) i ≫ f (a i) :=
  Limits.Pi.map_π _ i

/-- Transport along equality of family indices commutes with a morphism of
dependent families. -/
theorem eqToHom_comp_familyMap_eq (Y : Fin m → Over S)
    (f : ∀ j, X j ⟶ Y j) {j k : Fin m} (h : j = k) :
    eqToHom (congrArg X h) ≫ f k =
      f j ≫ eqToHom (congrArg Y h) := by
  subst k
  simp

/-- A product projection transported along equality of family indices is
the projection at the target index. -/
theorem projection_comp_eqToHom {j k : Fin m} (h : j = k) :
    Pi.π X j ≫ eqToHom (congrArg X h) = Pi.π X k := by
  subst k
  simp

/-- The induced stabilizer action on the underlying assigned-product
scheme. -/
noncomputable def action :
    SchemeAction (MulAction.stabilizer (Equiv.Perm (Fin d)) a)
      (assignedProduct S m d X a).left where
  hom g := (permutationHom S m d X a g).left
  hom_one := congrArg Over.Hom.left (permutationHom_one S m d X a)
  hom_mul g h := congrArg Over.Hom.left
    (permutationHom_mul S m d X a g h)

/-- Every coordinatewise family map to a constant target is equivariant for
the assignment stabilizer. -/
theorem assignedMap_equivariant (Y : Over S) (f : ∀ j, X j ⟶ Y)
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) :
    (action S m d X a).hom g ≫ (assignedMap S m d X a Y f).left =
      (assignedMap S m d X a Y f).left ≫
        (PermutationPower.action S (Fin d) Y).hom g.1 := by
  change (permutationHom S m d X a g ≫
      assignedMap S m d X a Y f).left =
    (assignedMap S m d X a Y f ≫
      PermutationPower.permutationHom S (Fin d) Y g.1).left
  apply congrArg Over.Hom.left
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, Category.assoc, assignedMap_comp_projection,
    PermutationPower.permutationHom_comp_π,
    assignedMap_comp_projection, ← Category.assoc,
    permutationHom_comp_projection, Category.assoc,
    eqToHom_comp_familyMap S m X Y f
      (stabilizer_apply_eq d m a g i)]

/-- Every coordinatewise morphism of indexed families is equivariant for
the assignment stabilizer actions on its source and target. -/
theorem assignedFamilyMap_equivariant (Y : Fin m → Over S)
    (f : ∀ j, X j ⟶ Y j)
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) :
    (action S m d X a).hom g ≫
        (assignedFamilyMap S m d X a Y f).left =
      (assignedFamilyMap S m d X a Y f).left ≫
        (action S m d Y a).hom g := by
  change (permutationHom S m d X a g ≫
      assignedFamilyMap S m d X a Y f).left =
    (assignedFamilyMap S m d X a Y f ≫
      permutationHom S m d Y a g).left
  apply congrArg Over.Hom.left
  apply Pi.hom_ext
  intro i
  calc
    (permutationHom S m d X a g ≫
          assignedFamilyMap S m d X a Y f) ≫
        Pi.π (fun j : Fin d ↦ Y (a j)) i =
      permutationHom S m d X a g ≫
        (Pi.π (fun j : Fin d ↦ X (a j)) i ≫ f (a i)) := by
          rw [Category.assoc, assignedFamilyMap_comp_projection]
    _ = (permutationHom S m d X a g ≫
          Pi.π (fun j : Fin d ↦ X (a j)) i) ≫ f (a i) :=
      (Category.assoc _ _ _).symm
    _ = (Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i) ≫
          eqToHom (congrArg X (stabilizer_apply_eq d m a g i))) ≫
        f (a i) := by rw [permutationHom_comp_projection]
    _ = Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i) ≫
        (eqToHom (congrArg X (stabilizer_apply_eq d m a g i)) ≫
          f (a i)) := Category.assoc _ _ _
    _ = Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i) ≫
        (f (a (g.1 i)) ≫
          eqToHom (congrArg Y (stabilizer_apply_eq d m a g i))) := by
      rw [eqToHom_comp_familyMap_eq S m X Y f
        (stabilizer_apply_eq d m a g i)]
    _ = (Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i) ≫
          f (a (g.1 i))) ≫
        eqToHom (congrArg Y (stabilizer_apply_eq d m a g i)) :=
      (Category.assoc _ _ _).symm
    _ = (assignedFamilyMap S m d X a Y f ≫
          Pi.π (fun j : Fin d ↦ Y (a j)) (g.1 i)) ≫
        eqToHom (congrArg Y (stabilizer_apply_eq d m a g i)) := by
      rw [assignedFamilyMap_comp_projection]
    _ = assignedFamilyMap S m d X a Y f ≫
        (Pi.π (fun j : Fin d ↦ Y (a j)) (g.1 i) ≫
          eqToHom (congrArg Y (stabilizer_apply_eq d m a g i))) :=
      Category.assoc _ _ _
    _ = assignedFamilyMap S m d X a Y f ≫
        (permutationHom S m d Y a g ≫
          Pi.π (fun j : Fin d ↦ Y (a j)) i) := by
      rw [permutationHom_comp_projection]
    _ = (assignedFamilyMap S m d X a Y f ≫
          permutationHom S m d Y a g) ≫
        Pi.π (fun j : Fin d ↦ Y (a j)) i :=
      (Category.assoc _ _ _).symm

/-- Repeating a full family-product point according to the assignment lands
in the fixed locus of the assignment stabilizer. -/
theorem productToAssignedProduct_invariant
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) :
    productToAssignedProduct S m d X a ≫
        permutationHom S m d X a g =
      productToAssignedProduct S m d X a := by
  apply Pi.hom_ext
  intro i
  calc
    (productToAssignedProduct S m d X a ≫
          permutationHom S m d X a g) ≫
        Pi.π (fun j : Fin d ↦ X (a j)) i =
      productToAssignedProduct S m d X a ≫
        (Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i) ≫
          eqToHom (congrArg X (stabilizer_apply_eq d m a g i))) := by
            rw [Category.assoc, permutationHom_comp_projection]
    _ = (productToAssignedProduct S m d X a ≫
          Pi.π (fun j : Fin d ↦ X (a j)) (g.1 i)) ≫
        eqToHom (congrArg X (stabilizer_apply_eq d m a g i)) :=
      (Category.assoc _ _ _).symm
    _ = Pi.π X (a (g.1 i)) ≫
        eqToHom (congrArg X (stabilizer_apply_eq d m a g i)) := by
      rw [productToAssignedProduct_comp_projection]
    _ = Pi.π X (a i) := projection_comp_eqToHom S m X
      (stabilizer_apply_eq d m a g i)
    _ = productToAssignedProduct S m d X a ≫
        Pi.π (fun j : Fin d ↦ X (a j)) i :=
      (productToAssignedProduct_comp_projection S m d X a i).symm

/-- Assigned-product insertion is equivariant for the tuple stabilizer and
the ambient coordinate-permutation action. -/
theorem insertion_equivariant
    (g : MulAction.stabilizer (Equiv.Perm (Fin d)) a) :
    (action S m d X a).hom g ≫
        (assignedProductToCoproductPower S m d X a).left =
      (assignedProductToCoproductPower S m d X a).left ≫
        (PermutationPower.action S (Fin d)
          (familyCoproduct S m X)).hom g.1 := by
  change (permutationHom S m d X a g ≫
      assignedProductToCoproductPower S m d X a).left =
    (assignedProductToCoproductPower S m d X a ≫
      PermutationPower.permutationHom S (Fin d)
        (familyCoproduct S m X) g.1).left
  apply congrArg Over.Hom.left
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, Category.assoc,
    assignedProductToCoproductPower_comp_projection,
    PermutationPower.permutationHom_comp_π,
    assignedProductToCoproductPower_comp_projection,
    ← Category.assoc, permutationHom_comp_projection]
  rw [Category.assoc, eqToHom_comp_inclusion S m X
    (stabilizer_apply_eq d m a g i)]

end MazurTorsion.AlgebraicGeometry.Jacobian.AssignedProductStabilizer
