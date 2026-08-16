/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantSplitRefinement

/-!
# Sheet transitions induced by actions on split finite schemes

An equivariant action on a split finite scheme sends a sheet above one base
point to a uniquely determined sheet above the translated base point.  The
resulting sheet transition satisfies the expected cocycle law.  At a fixed
base point it is a genuine permutation, with the covariant scheme-action
convention producing a left action of the opposite group on sheet labels.

The named downstream consumer is the block-stable occurrence chart in
`GeometricAssignedAffineChart`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteActionSheets

open SplitFiniteBaseChange

variable {G : Type} [Group G]
variable (S : Scheme.{u}) (m : ℕ)

/-- The point in the `j`-th sheet above `s`. -/
noncomputable def sheetPoint (j : Fin m) (s : S) :
    (splitFinite S m).left :=
  (sheetInclusion S m j).left s

/-- The `j`-th sheet point projects to its specified base point. -/
theorem sheetPoint_projection (j : Fin m) (s : S) :
    (splitFinite S m).hom (sheetPoint S m j s) = s := by
  have h := congrArg (fun f ↦ f s) (sheetInclusion S m j).w
  simpa [sheetPoint] using h

/-- With the identity split presentation, the extracted base coordinate is
the structural-map image. -/
theorem splitPointBase_refl (x : (splitFinite S m).left) :
    splitPointBase S m (splitFinite S m) (Iso.refl _) x =
      (splitFinite S m).hom x := by
  have hd := splitPoint_decomposition S m (splitFinite S m) (Iso.refl _) x
  have hp := congrArg (splitFinite S m).hom hd
  have hSheetMap := Sigma.ι_desc
    (fun _ : ULift.{u} (Fin m) ↦ 𝟙 S)
    (ULift.up (splitPointSheet S m (splitFinite S m) (Iso.refl _) x))
  have hSheetPoint := congrArg
    (fun f : S ⟶ S ↦
      f (splitPointBase S m (splitFinite S m) (Iso.refl _) x))
    hSheetMap
  change (splitFinite S m).hom
      ((sheetInclusion S m
        (splitPointSheet S m (splitFinite S m) (Iso.refl _) x)).left
          (splitPointBase S m (splitFinite S m) (Iso.refl _) x)) =
    splitPointBase S m (splitFinite S m) (Iso.refl _) x at hSheetPoint
  rw [hSheetPoint] at hp
  simpa using hp.symm

variable (α : SchemeAction G (splitFinite S m).left)
variable (β : SchemeAction G S)
variable (hα : ∀ g : G,
  α.hom g ≫ (splitFinite S m).hom =
    (splitFinite S m).hom ≫ β.hom g)

/-- The label of the sheet containing the translate of the `j`-th sheet
point above `s`. -/
noncomputable def sheetTransition (g : G) (s : S) (j : Fin m) : Fin m :=
  splitPointSheet S m (splitFinite S m) (Iso.refl _)
    (α.hom g (sheetPoint S m j s))

include hα in
/-- An action map sends a sheet point to the extracted sheet above the
translated base point. -/
theorem action_sheetPoint (g : G) (s : S) (j : Fin m) :
    α.hom g (sheetPoint S m j s) =
      sheetPoint S m (sheetTransition S m α g s j) (β.hom g s) := by
  have hd := splitPoint_decomposition S m (splitFinite S m) (Iso.refl _)
    (α.hom g (sheetPoint S m j s))
  have hb : splitPointBase S m (splitFinite S m) (Iso.refl _)
      (α.hom g (sheetPoint S m j s)) = β.hom g s := by
    rw [splitPointBase_refl]
    have he := congrArg
      (fun e : (splitFinite S m).left ⟶ S ↦
        e (sheetPoint S m j s)) (hα g)
    change (splitFinite S m).hom
        (α.hom g (sheetPoint S m j s)) =
      β.hom g ((splitFinite S m).hom (sheetPoint S m j s)) at he
    rw [sheetPoint_projection] at he
    exact he
  change α.hom g (sheetPoint S m j s) =
    sheetPoint S m (sheetTransition S m α g s j)
      (splitPointBase S m (splitFinite S m) (Iso.refl _)
        (α.hom g (sheetPoint S m j s))) at hd
  rw [hb] at hd
  exact hd

/-- Distinct sheet labels give distinct points above a fixed base point. -/
theorem sheetPoint_injective (s : S) :
    Function.Injective (fun j : Fin m ↦ sheetPoint S m j s) := by
  intro i j hij
  let e := sigmaMk (fun _ : ULift.{u} (Fin m) ↦ S)
  have hi : e.symm (sheetPoint S m i s) = ⟨ULift.up i, s⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (sigmaMk_mk
      (fun _ : ULift.{u} (Fin m) ↦ S) (ULift.up i) s).symm
  have hj : e.symm (sheetPoint S m j s) = ⟨ULift.up j, s⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (sigmaMk_mk
      (fun _ : ULift.{u} (Fin m) ↦ S) (ULift.up j) s).symm
  have hcoord := congrArg (fun x ↦ (e.symm x).1.down) hij
  simpa [hi, hj] using hcoord

/-- For a fixed group element and source sheet, the destination sheet is a
locally constant function of the base point. -/
theorem sheetTransition_isLocallyConstant (g : G) (j : Fin m) :
    IsLocallyConstant (fun s : S ↦ sheetTransition S m α g s j) := by
  let e := sigmaMk (fun _ : ULift.{u} (Fin m) ↦ S)
  have hindex : Continuous
      (fun x : Σ _ : ULift.{u} (Fin m), S ↦ x.1.down) := by
    rw [continuous_def]
    intro t ht
    rw [isOpen_sigma_iff]
    intro i
    change IsOpen { _s : S | i.down ∈ t }
    by_cases hi : i.down ∈ t
    · simp [hi]
    · simp [hi]
  apply (IsLocallyConstant.iff_continuous _).2
  change Continuous
    (fun s : S ↦ (e.symm (α.hom g (sheetPoint S m j s))).1.down)
  exact hindex.comp
    (e.symm.continuous.comp
      ((α.hom g).continuous.comp (sheetInclusion S m j).left.continuous))

include hα in
/-- Sheet transitions satisfy the group-action cocycle law, with the second
transition evaluated at the translated base point. -/
theorem sheetTransition_mul (g h : G) (s : S) (j : Fin m) :
    sheetTransition S m α (g * h) s j =
      sheetTransition S m α h (β.hom g s)
        (sheetTransition S m α g s j) := by
  apply sheetPoint_injective S m (β.hom (g * h) s)
  change
    sheetPoint S m (sheetTransition S m α (g * h) s j)
        (β.hom (g * h) s) =
      sheetPoint S m
        (sheetTransition S m α h (β.hom g s)
          (sheetTransition S m α g s j)) (β.hom (g * h) s)
  calc
    _ = α.hom (g * h) (sheetPoint S m j s) :=
      (action_sheetPoint S m α β hα (g * h) s j).symm
    _ = α.hom h (α.hom g (sheetPoint S m j s)) := by
      rw [α.hom_mul]
      rfl
    _ = α.hom h
        (sheetPoint S m (sheetTransition S m α g s j)
          (β.hom g s)) := by
      rw [action_sheetPoint S m α β hα g s j]
    _ = sheetPoint S m
        (sheetTransition S m α h (β.hom g s)
          (sheetTransition S m α g s j))
        (β.hom h (β.hom g s)) :=
      action_sheetPoint S m α β hα h (β.hom g s)
        (sheetTransition S m α g s j)
    _ = _ := by rw [β.hom_mul]; rfl

include β hα in
/-- The identity element fixes every sheet label. -/
theorem sheetTransition_one (s : S) (j : Fin m) :
    sheetTransition S m α 1 s j = j := by
  apply sheetPoint_injective S m (β.hom 1 s)
  change
    sheetPoint S m (sheetTransition S m α 1 s j) (β.hom 1 s) =
      sheetPoint S m j (β.hom 1 s)
  calc
    _ = α.hom 1 (sheetPoint S m j s) :=
      (action_sheetPoint S m α β hα 1 s j).symm
    _ = sheetPoint S m j s := by rw [α.hom_one]; rfl
    _ = sheetPoint S m j (β.hom 1 s) := by
      rw [β.hom_one]
      exact congrArg (sheetPoint S m j)
        (ConcreteCategory.id_apply s).symm

/-- Every group element gives a bijection from the sheet labels above a
point to the sheet labels above its translate. -/
noncomputable def sheetTransitionPerm (g : G) (s : S) :
    Equiv.Perm (Fin m) where
  toFun := sheetTransition S m α g s
  invFun := sheetTransition S m α g⁻¹ (β.hom g s)
  left_inv j := by
    calc
      _ = sheetTransition S m α (g * g⁻¹) s j :=
        (sheetTransition_mul S m α β hα g g⁻¹ s j).symm
      _ = j := by
        rw [mul_inv_cancel, sheetTransition_one S m α β hα]
  right_inv j := by
    have hcancel : β.hom g⁻¹ (β.hom g s) = s := by
      have hmul := congrArg (fun e : S ⟶ S ↦ e s) (β.hom_mul g g⁻¹)
      rw [mul_inv_cancel, β.hom_one] at hmul
      exact hmul.symm.trans (ConcreteCategory.id_apply s)
    calc
      _ = sheetTransition S m α g
          (β.hom g⁻¹ (β.hom g s))
          (sheetTransition S m α g⁻¹ (β.hom g s) j) := by
        rw [hcancel]
      _ = sheetTransition S m α (g⁻¹ * g) (β.hom g s) j :=
        (sheetTransition_mul S m α β hα g⁻¹ g (β.hom g s) j).symm
      _ = j := by
        rw [inv_mul_cancel, sheetTransition_one S m α β hα]

/-- At a fixed base point, the covariant scheme-action convention gives a
left action of the opposite group on sheet labels. -/
@[implicit_reducible]
noncomputable def fixedSheetMulAction (s : S)
    (hs : ∀ g : G, β.hom g s = s) : MulAction Gᵐᵒᵖ (Fin m) where
  smul g j := sheetTransition S m α g.unop s j
  one_smul j := sheetTransition_one S m α β hα s j
  mul_smul g h j := by
    change sheetTransition S m α (g * h).unop s j =
      sheetTransition S m α g.unop s
        (sheetTransition S m α h.unop s j)
    rw [MulOpposite.unop_mul, sheetTransition_mul S m α β hα, hs]

/-- Every element acts by a permutation of the sheets above a fixed base
point. -/
noncomputable def fixedSheetPerm (s : S)
    (hs : ∀ g : G, β.hom g s = s) (g : G) : Equiv.Perm (Fin m) where
  toFun := sheetTransition S m α g s
  invFun := sheetTransition S m α g⁻¹ s
  left_inv j := by
    calc
      _ = sheetTransition S m α g⁻¹ (β.hom g s)
          (sheetTransition S m α g s j) := by rw [hs]
      _ = sheetTransition S m α (g * g⁻¹) s j :=
        (sheetTransition_mul S m α β hα g g⁻¹ s j).symm
      _ = j := by
        rw [mul_inv_cancel, sheetTransition_one S m α β hα]
  right_inv j := by
    calc
      _ = sheetTransition S m α g (β.hom g⁻¹ s)
          (sheetTransition S m α g⁻¹ s j) := by rw [hs]
      _ = sheetTransition S m α (g⁻¹ * g) s j :=
        (sheetTransition_mul S m α β hα g⁻¹ g s j).symm
      _ = j := by
        rw [inv_mul_cancel, sheetTransition_one S m α β hα]

variable [Finite G]

/-- The locus on which every sheet transition agrees with its value at the
chosen base point. -/
def constantTransitionSet (s₀ : S) : Set S :=
  ⋂ g : G, ⋂ j : Fin m,
    {s | sheetTransition S m α g s j = sheetTransition S m α g s₀ j}

/-- The simultaneous constant-transition locus is clopen. -/
theorem constantTransitionSet_isClopen (s₀ : S) :
    IsClopen (constantTransitionSet S m α s₀) := by
  apply isClopen_iInter_of_finite
  intro g
  apply isClopen_iInter_of_finite
  intro j
  exact (sheetTransition_isLocallyConstant S m α g j).isClopen_fiber _

omit [Finite G] in
/-- Membership in the constant-transition locus is the family of all
transition equalities. -/
theorem mem_constantTransitionSet_iff (s₀ s : S) :
    s ∈ constantTransitionSet S m α s₀ ↔
      ∀ (g : G) (j : Fin m),
        sheetTransition S m α g s j = sheetTransition S m α g s₀ j := by
  simp only [constantTransitionSet, Set.mem_iInter, Set.mem_setOf_eq]

omit [Finite G] in
/-- The chosen point belongs to its constant-transition locus. -/
theorem self_mem_constantTransitionSet (s₀ : S) :
    s₀ ∈ constantTransitionSet S m α s₀ :=
  (mem_constantTransitionSet_iff S m α s₀ s₀).2 fun _ _ ↦ rfl

omit [Finite G] in
include hα in
/-- Translating two points with the same full sheet-transition signature
again gives two points with the same signature. -/
theorem constantTransitionSet_map_mem_general (s₀ : S)
    {s : S} (hs : s ∈ constantTransitionSet S m α s₀) (h : G) :
    β.hom h s ∈ constantTransitionSet S m α (β.hom h s₀) := by
  rw [mem_constantTransitionSet_iff]
  intro g j
  let p := sheetTransitionPerm S m α β hα h s₀
  let k : Fin m := p.symm j
  have hk₀ : sheetTransition S m α h s₀ k = j := by
    exact p.apply_symm_apply j
  have hsEq : ∀ (a : G) (i : Fin m),
      sheetTransition S m α a s i = sheetTransition S m α a s₀ i :=
    (mem_constantTransitionSet_iff S m α s₀ s).1 hs
  have hk : sheetTransition S m α h s k = j :=
    (hsEq h k).trans hk₀
  calc
    sheetTransition S m α g (β.hom h s) j =
        sheetTransition S m α g (β.hom h s)
          (sheetTransition S m α h s k) := by rw [hk]
    _ = sheetTransition S m α (h * g) s k :=
      (sheetTransition_mul S m α β hα h g s k).symm
    _ = sheetTransition S m α (h * g) s₀ k := hsEq (h * g) k
    _ = sheetTransition S m α g (β.hom h s₀)
        (sheetTransition S m α h s₀ k) :=
      sheetTransition_mul S m α β hα h g s₀ k
    _ = sheetTransition S m α g (β.hom h s₀) j := by rw [hk₀]

omit [Finite G] in
include hα in
/-- When the chosen point is fixed, its constant-transition locus is
preserved pointwise by every action map. -/
theorem constantTransitionSet_map_mem (s₀ : S)
    (hs₀ : ∀ g : G, β.hom g s₀ = s₀)
    {s : S} (hs : s ∈ constantTransitionSet S m α s₀) (h : G) :
    β.hom h s ∈ constantTransitionSet S m α s₀ := by
  rw [mem_constantTransitionSet_iff]
  intro g j
  let p := fixedSheetPerm S m α β hα s₀ hs₀ h
  let k : Fin m := p.symm j
  have hk₀ : sheetTransition S m α h s₀ k = j := by
    exact p.apply_symm_apply j
  have hsEq : ∀ (a : G) (i : Fin m),
      sheetTransition S m α a s i = sheetTransition S m α a s₀ i :=
    (mem_constantTransitionSet_iff S m α s₀ s).1 hs
  have hk : sheetTransition S m α h s k = j :=
    (hsEq h k).trans hk₀
  calc
    sheetTransition S m α g (β.hom h s) j =
        sheetTransition S m α g (β.hom h s)
          (sheetTransition S m α h s k) := by rw [hk]
    _ = sheetTransition S m α (h * g) s k :=
      (sheetTransition_mul S m α β hα h g s k).symm
    _ = sheetTransition S m α (h * g) s₀ k := hsEq (h * g) k
    _ = sheetTransition S m α g (β.hom h s₀)
        (sheetTransition S m α h s₀ k) :=
      sheetTransition_mul S m α β hα h g s₀ k
    _ = sheetTransition S m α g s₀ j := by rw [hs₀ h, hk₀]

/-- The union of the full transition-signature loci met by the orbit of a
chosen point.  Distinct loci in this union are disjoint, while repeated
signatures merely give the same locus. -/
def orbitTransitionSet (s₀ : S) : Set S :=
  ⋃ h : G, constantTransitionSet S m α (β.hom h s₀)

/-- The orbit-transition locus is clopen because both the acting group and
the sheet set are finite. -/
theorem orbitTransitionSet_isClopen (s₀ : S) :
    IsClopen (orbitTransitionSet S m α β s₀) := by
  apply isClopen_iUnion_of_finite
  intro h
  exact constantTransitionSet_isClopen S m α (β.hom h s₀)

omit [Finite G] in
/-- Every translate of the chosen point belongs to the orbit-transition
locus. -/
theorem orbit_mem_orbitTransitionSet (s₀ : S) (h : G) :
    β.hom h s₀ ∈ orbitTransitionSet S m α β s₀ := by
  rw [orbitTransitionSet]
  exact Set.mem_iUnion.2
    ⟨h, self_mem_constantTransitionSet S m α (β.hom h s₀)⟩

omit [Finite G] in
include hα in
/-- The orbit-transition locus is preserved by every action map. -/
theorem orbitTransitionSet_map_mem (s₀ : S)
    {s : S} (hs : s ∈ orbitTransitionSet S m α β s₀) (h : G) :
    β.hom h s ∈ orbitTransitionSet S m α β s₀ := by
  rw [orbitTransitionSet] at hs ⊢
  obtain ⟨k, hsk⟩ := Set.mem_iUnion.1 hs
  have hmap := constantTransitionSet_map_mem_general S m α β hα
    (β.hom k s₀) hsk h
  have hkh := congrArg (fun e : S ⟶ S ↦ e s₀) (β.hom_mul k h)
  change β.hom (k * h) s₀ = β.hom h (β.hom k s₀) at hkh
  rw [← hkh] at hmap
  exact Set.mem_iUnion.2 ⟨k * h, hmap⟩

/-- The orbit-transition locus as an open subscheme of the base. -/
noncomputable def orbitTransitionOpen (s₀ : S) : S.Opens :=
  ⟨orbitTransitionSet S m α β s₀,
    (orbitTransitionSet_isClopen S m α β s₀).isOpen⟩

include hα in
/-- The union of transition-signature pieces along any finite orbit is a
stable clopen neighborhood of that orbit. -/
theorem orbitTransitionOpen_isStable (s₀ : S) :
    β.IsStableOpen (orbitTransitionOpen S m α β s₀) := by
  intro h
  apply SetLike.ext
  intro s
  change β.hom h s ∈ orbitTransitionSet S m α β s₀ ↔
    s ∈ orbitTransitionSet S m α β s₀
  constructor
  · intro hs
    have hback := orbitTransitionSet_map_mem S m α β hα s₀ hs h⁻¹
    have hcancel : β.hom h⁻¹ (β.hom h s) = s := by
      have hmul := congrArg (fun e : S ⟶ S ↦ e s) (β.hom_mul h h⁻¹)
      rw [mul_inv_cancel, β.hom_one] at hmul
      exact hmul.symm.trans (ConcreteCategory.id_apply s)
    rwa [hcancel] at hback
  · intro hs
    exact orbitTransitionSet_map_mem S m α β hα s₀ hs h

/-- The constant-transition locus as an open subscheme of the base. -/
noncomputable def constantTransitionOpen (s₀ : S) : S.Opens :=
  ⟨constantTransitionSet S m α s₀,
    (constantTransitionSet_isClopen S m α s₀).isOpen⟩

include hα in
/-- Around a fixed base point, simultaneous constancy of all sheet
transitions defines a stable clopen neighborhood. -/
theorem constantTransitionOpen_isStable (s₀ : S)
    (hs₀ : ∀ g : G, β.hom g s₀ = s₀) :
    β.IsStableOpen (constantTransitionOpen S m α s₀) := by
  intro h
  apply SetLike.ext
  intro s
  change β.hom h s ∈ constantTransitionSet S m α s₀ ↔
    s ∈ constantTransitionSet S m α s₀
  constructor
  · intro hs
    have hback := constantTransitionSet_map_mem S m α β hα s₀ hs₀
      hs h⁻¹
    have hcancel : β.hom h⁻¹ (β.hom h s) = s := by
      have hmul := congrArg (fun e : S ⟶ S ↦ e s) (β.hom_mul h h⁻¹)
      rw [mul_inv_cancel, β.hom_one] at hmul
      exact hmul.symm.trans (ConcreteCategory.id_apply s)
    rwa [hcancel] at hback
  · intro hs
    exact constantTransitionSet_map_mem S m α β hα s₀ hs₀ hs h

omit [Finite G] in
include hα in
/-- If one sheet transition is constant on an open, the action map on that
source sheet is exactly the base action followed by the corresponding
target-sheet inclusion.  No stability of the open is required: its image is
allowed to lie in the translated open. -/
theorem sheetMap_eq_on_open
    {U : S.Opens}
    (g : G) (j p : Fin m)
    (hp : ∀ s : U.toScheme,
      sheetTransition S m α g (U.ι s) j = p) :
    U.ι ≫ (sheetInclusion S m j).left ≫ α.hom g =
      U.ι ≫ β.hom g ≫ (sheetInclusion S m p).left := by
  let lhs : U.toScheme ⟶ (splitFinite S m).left :=
    U.ι ≫ (sheetInclusion S m j).left ≫ α.hom g
  let ιp : S ⟶ (splitFinite S m).left :=
    (sheetInclusion S m p).left
  letI : IsOpenImmersion ιp := by
    change IsOpenImmersion
      (Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) (ULift.up p))
    infer_instance
  have hrange : Set.range lhs ⊆ Set.range ιp := by
    rintro y ⟨s, rfl⟩
    refine ⟨β.hom g (U.ι s), ?_⟩
    change sheetPoint S m p (β.hom g (U.ι s)) =
      α.hom g (sheetPoint S m j (U.ι s))
    rw [← hp s]
    exact (action_sheetPoint S m α β hα g (U.ι s) j).symm
  let l : U.toScheme ⟶ S := IsOpenImmersion.lift ιp lhs hrange
  have hlift : l ≫ ιp = lhs := IsOpenImmersion.lift_fac ιp lhs hrange
  have hιp : ιp ≫ (splitFinite S m).hom = 𝟙 S := by
    exact (sheetInclusion S m p).w
  have hιj : (sheetInclusion S m j).left ≫
      (splitFinite S m).hom = 𝟙 S :=
    (sheetInclusion S m j).w
  have hl : l = U.ι ≫ β.hom g := by
    calc
      l = l ≫ 𝟙 S := (Category.comp_id l).symm
      _ = l ≫ (ιp ≫ (splitFinite S m).hom) := by rw [hιp]
      _ = (l ≫ ιp) ≫ (splitFinite S m).hom :=
        (Category.assoc _ _ _).symm
      _ = lhs ≫ (splitFinite S m).hom := by rw [hlift]
      _ = U.ι ≫ (sheetInclusion S m j).left ≫ α.hom g ≫
          (splitFinite S m).hom := rfl
      _ = U.ι ≫ (sheetInclusion S m j).left ≫
          ((splitFinite S m).hom ≫ β.hom g) := by rw [hα]
      _ = U.ι ≫ ((sheetInclusion S m j).left ≫
          (splitFinite S m).hom) ≫ β.hom g := by
        simp only [Category.assoc]
      _ = U.ι ≫ β.hom g := by rw [hιj, Category.id_comp]
  change lhs = (U.ι ≫ β.hom g) ≫ ιp
  calc
    lhs = l ≫ ιp := hlift.symm
    _ = (U.ι ≫ β.hom g) ≫ ιp := by rw [hl]

include hα in
/-- On the signature piece through `s₀`, every sheet map is given exactly
by the transition label measured at `s₀`. -/
theorem sheetMap_eq_on_constantTransitionOpen
    (s₀ : S) (g : G) (j : Fin m) :
    (constantTransitionOpen S m α s₀).ι ≫
          (sheetInclusion S m j).left ≫ α.hom g =
      (constantTransitionOpen S m α s₀).ι ≫ β.hom g ≫
        (sheetInclusion S m (sheetTransition S m α g s₀ j)).left := by
  apply sheetMap_eq_on_open S m α β hα
  intro s
  exact (mem_constantTransitionSet_iff S m α s₀
    ((constantTransitionOpen S m α s₀).ι s)).1 s.property g j

omit [Finite G] in
include hα in
/-- If one sheet transition is constant on a stable open, the action map on
that source sheet is exactly the restricted base action followed by the
corresponding target-sheet inclusion.  This upgrades the pointwise sheet
label to an equality of scheme morphisms. -/
theorem sheetMap_eq_on_stableOpen
    {U : S.Opens} (hU : β.IsStableOpen U)
    (g : G) (j p : Fin m)
    (hp : ∀ s : U.toScheme,
      sheetTransition S m α g (U.ι s) j = p) :
    U.ι ≫ (sheetInclusion S m j).left ≫ α.hom g =
      (β.restrict hU).hom g ≫ U.ι ≫ (sheetInclusion S m p).left := by
  let lhs : U.toScheme ⟶ (splitFinite S m).left :=
    U.ι ≫ (sheetInclusion S m j).left ≫ α.hom g
  let ιp : S ⟶ (splitFinite S m).left :=
    (sheetInclusion S m p).left
  letI : IsOpenImmersion ιp := by
    change IsOpenImmersion
      (Sigma.ι (fun _ : ULift.{u} (Fin m) ↦ S) (ULift.up p))
    infer_instance
  have hrange : Set.range lhs ⊆ Set.range ιp := by
    rintro y ⟨s, rfl⟩
    refine ⟨β.hom g (U.ι s), ?_⟩
    change sheetPoint S m p (β.hom g (U.ι s)) =
      α.hom g (sheetPoint S m j (U.ι s))
    rw [← hp s]
    exact (action_sheetPoint S m α β hα g (U.ι s) j).symm
  let l : U.toScheme ⟶ S := IsOpenImmersion.lift ιp lhs hrange
  have hlift : l ≫ ιp = lhs := IsOpenImmersion.lift_fac ιp lhs hrange
  have hιp : ιp ≫ (splitFinite S m).hom = 𝟙 S := by
    exact (sheetInclusion S m p).w
  have hιj : (sheetInclusion S m j).left ≫
      (splitFinite S m).hom = 𝟙 S :=
    (sheetInclusion S m j).w
  have hl : l = (β.restrict hU).hom g ≫ U.ι := by
    calc
      l = l ≫ 𝟙 S := (Category.comp_id l).symm
      _ = l ≫ (ιp ≫ (splitFinite S m).hom) := by rw [hιp]
      _ = (l ≫ ιp) ≫ (splitFinite S m).hom :=
        (Category.assoc _ _ _).symm
      _ = lhs ≫ (splitFinite S m).hom := by rw [hlift]
      _ = U.ι ≫ (sheetInclusion S m j).left ≫ α.hom g ≫
          (splitFinite S m).hom := rfl
      _ = U.ι ≫ (sheetInclusion S m j).left ≫
          ((splitFinite S m).hom ≫ β.hom g) := by rw [hα]
      _ = U.ι ≫ ((sheetInclusion S m j).left ≫
          (splitFinite S m).hom) ≫ β.hom g := by
        simp only [Category.assoc]
      _ = U.ι ≫ β.hom g := by rw [hιj, Category.id_comp]
      _ = (β.restrict hU).hom g ≫ U.ι :=
        (Scheme.Hom.resLE_comp_ι (β.hom g) (hU.le_preimage g)).symm
  change lhs = (β.restrict hU).hom g ≫ (U.ι ≫ ιp)
  calc
    lhs = l ≫ ιp := hlift.symm
    _ = ((β.restrict hU).hom g ≫ U.ι) ≫ ιp := by rw [hl]
    _ = (β.restrict hU).hom g ≫ (U.ι ≫ ιp) :=
      Category.assoc _ _ _

/-- If a sheet over a refinement point maps to a fixed point of the original
finite source, then every translated sheet over the corresponding orbit point
maps to that same fixed point.  This is the orbitwise replacement for a
generally nonexistent fixed point of the fpqc refinement itself. -/
theorem orbit_sheet_maps_fixed_point
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (τ : SchemeAction G Y) (f : X ⟶ Y)
    (q : Spec (.of R) ⟶ Y) (σ : SchemeAction G X)
    (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    (n : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin n → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R n =
      pullback.snd f q)
    (x : X) (s : (EquivariantFpqcRefinement.refinement τ q).left)
    (j : Fin n)
    (hj : pullback.fst f
          (EquivariantFpqcRefinement.projection τ q 1 ≫ q)
          ((EquivariantSplitRefinement.directSplitIso τ f q n E hE).inv.left
            (sheetPoint
              (EquivariantFpqcRefinement.refinement τ q).left n j s)) = x)
    (hx : ∀ g : G, σ.hom g x = x) (g : G) :
    pullback.fst f
        (EquivariantFpqcRefinement.projection τ q 1 ≫ q)
        ((EquivariantSplitRefinement.directSplitIso τ f q n E hE).inv.left
          (sheetPoint (EquivariantFpqcRefinement.refinement τ q).left n
            (sheetTransition
              (EquivariantFpqcRefinement.refinement τ q).left n
              (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
              g s j)
            ((EquivariantFpqcRefinement.refinementAction τ q).hom g s))) =
      x := by
  have he := congrArg
    (fun e ↦ e (sheetPoint
      (EquivariantFpqcRefinement.refinement τ q).left n j s))
    (EquivariantSplitRefinement.splitAction_toOriginal_equivariant
      τ f q σ hf n E hE g)
  change
    pullback.fst f
        (EquivariantFpqcRefinement.projection τ q 1 ≫ q)
        ((EquivariantSplitRefinement.directSplitIso τ f q n E hE).inv.left
          ((EquivariantSplitRefinement.splitAction τ f q σ hf n E hE).hom g
            (sheetPoint
              (EquivariantFpqcRefinement.refinement τ q).left n j s))) =
      σ.hom g
        (pullback.fst f
          (EquivariantFpqcRefinement.projection τ q 1 ≫ q)
          ((EquivariantSplitRefinement.directSplitIso τ f q n E hE).inv.left
            (sheetPoint
              (EquivariantFpqcRefinement.refinement τ q).left n j s))) at he
  rw [hj, hx g] at he
  rw [← action_sheetPoint
    (EquivariantFpqcRefinement.refinement τ q).left n
    (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
    (EquivariantFpqcRefinement.refinementAction τ q)
    (EquivariantSplitRefinement.splitAction_equivariant
      τ f q σ hf n E hE) g s j]
  exact he

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteActionSheets
