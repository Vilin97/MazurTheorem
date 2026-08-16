/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleAssignedCoproductPower
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitTupleStabilizer
import Mathlib.AlgebraicGeometry.Morphisms.Flat

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

/-- At a point obtained by repeating a family-product point, the residue
field morphisms of two occurrence projections in the same assignment fiber
agree.  This retains the scheme-theoretic residue correlation, rather than
only equality of the two underlying projected points. -/
theorem residuePoint_productToAssignedProduct_projection_eq
    (y : (∏ᶜ fun j : Fin m ↦ X j).left)
    (i k : Fin d) (h : a i = a k) :
    (assignedProduct S m d X a).left.fromSpecResidueField
          ((productToAssignedProduct S m d X a).left y) ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) i).left ≫
          (eqToHom (congrArg X h)).left =
      (assignedProduct S m d X a).left.fromSpecResidueField
          ((productToAssignedProduct S m d X a).left y) ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) k).left := by
  let r := (productToAssignedProduct S m d X a).left
  let e := Spec.map (r.residueFieldMap y)
  haveI : Flat e := by infer_instance
  haveI : Surjective e := by infer_instance
  letI : Epi e := Flat.epi_of_flat_of_surjective e
  have he : e ≫
      (assignedProduct S m d X a).left.fromSpecResidueField
        ((productToAssignedProduct S m d X a).left y) =
      (∏ᶜ fun j : Fin m ↦ X j).left.fromSpecResidueField y ≫
        (productToAssignedProduct S m d X a).left := by
    simpa only [r, e] using
      r.SpecMap_residueFieldMap_fromSpecResidueField y
  rw [← cancel_epi e]
  simp only [← Category.assoc, he]
  have hi := congrArg Over.Hom.left
    (productToAssignedProduct_comp_projection S m d X a i)
  change (productToAssignedProduct S m d X a).left ≫
      (Pi.π (fun l : Fin d ↦ X (a l)) i).left =
    (Pi.π X (a i)).left at hi
  have hk := congrArg Over.Hom.left
    (productToAssignedProduct_comp_projection S m d X a k)
  change (productToAssignedProduct S m d X a).left ≫
      (Pi.π (fun l : Fin d ↦ X (a l)) k).left =
    (Pi.π X (a k)).left at hk
  simp only [Category.assoc, hi, hk]
  rw [← Category.assoc]
  have hp := congrArg Over.Hom.left (projection_comp_eqToHom S m X h)
  change (Pi.π X (a i)).left ≫ (eqToHom (congrArg X h)).left =
    (Pi.π X (a k)).left at hp
  exact congrArg
    (fun f ↦ (∏ᶜ fun j : Fin m ↦ X j).left.fromSpecResidueField y ≫ f) hp

/-- A morphism taking a point to a repeated family-product point has equal
residue-field composites along any two occurrence projections in the same
assignment fiber. -/
theorem residuePoint_map_toProductToAssignedProduct_projection_eq
    (B : Scheme.{u})
    (f : B ⟶ (assignedProduct S m d X a).left) (s : B)
    (y : (∏ᶜ fun j : Fin m ↦ X j).left)
    (hs : f s = (productToAssignedProduct S m d X a).left y)
    (i k : Fin d) (h : a i = a k) :
    B.fromSpecResidueField s ≫ f ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) i).left ≫
          (eqToHom (congrArg X h)).left =
      B.fromSpecResidueField s ≫ f ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) k).left := by
  have hf := f.SpecMap_residueFieldMap_fromSpecResidueField s
  have hproj :
      (assignedProduct S m d X a).left.fromSpecResidueField (f s) ≫
          (Pi.π (fun l : Fin d ↦ X (a l)) i).left ≫
            (eqToHom (congrArg X h)).left =
        (assignedProduct S m d X a).left.fromSpecResidueField (f s) ≫
          (Pi.π (fun l : Fin d ↦ X (a l)) k).left := by
    let e := Spec.map
      ((assignedProduct S m d X a).left.residueFieldCongr hs).hom
    letI : IsIso e := by infer_instance
    have he : e ≫
        (assignedProduct S m d X a).left.fromSpecResidueField (f s) =
      (assignedProduct S m d X a).left.fromSpecResidueField
        ((productToAssignedProduct S m d X a).left y) := by
      exact Scheme.residueFieldCongr_fromSpecResidueField hs
    rw [← cancel_epi e]
    simp only [← Category.assoc, he]
    exact residuePoint_productToAssignedProduct_projection_eq
      S m d X a y i k h
  let e := Spec.map (f.residueFieldMap s)
  have hf' : e ≫
      (assignedProduct S m d X a).left.fromSpecResidueField (f s) =
    B.fromSpecResidueField s ≫ f := hf
  calc
    B.fromSpecResidueField s ≫ f ≫
          (Pi.π (fun l : Fin d ↦ X (a l)) i).left ≫
            (eqToHom (congrArg X h)).left =
        (e ≫ (assignedProduct S m d X a).left.fromSpecResidueField
          (f s)) ≫
            (Pi.π (fun l : Fin d ↦ X (a l)) i).left ≫
              (eqToHom (congrArg X h)).left := by
      simp only [← Category.assoc]
      rw [hf']
    _ = e ≫
        ((assignedProduct S m d X a).left.fromSpecResidueField (f s) ≫
          (Pi.π (fun l : Fin d ↦ X (a l)) i).left ≫
            (eqToHom (congrArg X h)).left) := by
      simp only [Category.assoc]
    _ = e ≫
        ((assignedProduct S m d X a).left.fromSpecResidueField (f s) ≫
          (Pi.π (fun l : Fin d ↦ X (a l)) k).left) :=
      congrArg (fun g ↦ e ≫ g) hproj
    _ = (e ≫ (assignedProduct S m d X a).left.fromSpecResidueField
          (f s)) ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) k).left := by
      simp only [Category.assoc]
    _ = B.fromSpecResidueField s ≫ f ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) k).left := by
      simp only [← Category.assoc]
      rw [hf']

/-- The preceding residue-field equality with both projections transported
to any fixed member of their common assignment fiber. -/
theorem residuePoint_map_toProductToAssignedProduct_projection_eq_to_target
    (B : Scheme.{u})
    (f : B ⟶ (assignedProduct S m d X a).left) (s : B)
    (y : (∏ᶜ fun j : Fin m ↦ X j).left)
    (hs : f s = (productToAssignedProduct S m d X a).left y)
    (b : Fin m) (i k : Fin d) (hi : a i = b) (hk : a k = b) :
    B.fromSpecResidueField s ≫ f ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) i).left ≫
          (eqToHom (congrArg X hi)).left =
      B.fromSpecResidueField s ≫ f ≫
        (Pi.π (fun l : Fin d ↦ X (a l)) k).left ≫
          (eqToHom (congrArg X hk)).left := by
  have hres := residuePoint_map_toProductToAssignedProduct_projection_eq
    S m d X a B f s y hs i k (hi.trans hk.symm)
  have hpost := congrArg
    (fun g ↦ g ≫ (eqToHom (congrArg X hk)).left) hres
  have ht := congrArg Over.Hom.left
    (eqToHom_trans (congrArg X (hi.trans hk.symm)) (congrArg X hk))
  change (eqToHom (congrArg X (hi.trans hk.symm))).left ≫
      (eqToHom (congrArg X hk)).left =
    (eqToHom ((congrArg X (hi.trans hk.symm)).trans
      (congrArg X hk))).left at ht
  have hp : (congrArg X (hi.trans hk.symm)).trans (congrArg X hk) =
      congrArg X hi := Subsingleton.elim _ _
  rw [hp] at ht
  simpa only [Category.assoc, ht] using hpost

/-- Equality after restriction to the residue-field point implies equality
of the underlying morphism values at that point. -/
theorem apply_eq_of_fromSpecResidueField_comp_eq
    {B Y : Scheme.{u}} (s : B) (f g : B ⟶ Y)
    (h : B.fromSpecResidueField s ≫ f =
      B.fromSpecResidueField s ≫ g) :
    f s = g s := by
  let r := B.fromSpecResidueField s
  let x := IsLocalRing.closedPoint (B.residueField s)
  have hx : r x = s := Scheme.fromSpecResidueField_apply s x
  have hp := congrArg (fun e ↦ e x) h
  change (r ≫ f) x = (r ≫ g) x at hp
  calc
    f s = f (r x) := congrArg f hx.symm
    _ = (r ≫ f) x := (Scheme.Hom.comp_apply r f x).symm
    _ = (r ≫ g) x := hp
    _ = g (r x) := Scheme.Hom.comp_apply r g x
    _ = g s := congrArg g hx

/-- A point belongs to a finite infimum of opens when it belongs to every
member.  Packaging the finite-intersection coercion behind a theorem keeps
large geometric applications opaque to the kernel. -/
theorem mem_iInf_opens_of_forall_mem
    {Y : Scheme.{u}} {I : Type*} [Finite I]
    (U : I → Y.Opens) (y : Y) (hy : ∀ i, y ∈ U i) :
    y ∈ ⨅ i, U i := by
  change y ∈ (((⨅ i, U i) : Y.Opens) : Set _)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact hy

/-- Membership in an inverse-image open is witnessed by membership of the
image point. -/
theorem mem_preimageOpen_of_apply_mem
    {B Y : Scheme.{u}} (f : B ⟶ Y) (U : Y.Opens) (s : B)
    (hs : f s ∈ U) : s ∈ f ⁻¹ᵁ U :=
  hs

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
