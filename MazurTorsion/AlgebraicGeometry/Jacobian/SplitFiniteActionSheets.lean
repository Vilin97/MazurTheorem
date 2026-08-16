/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.AffineClopen
import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantSplitRefinement
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient

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

open AffineClopen
open FiniteGroupQuotient
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

/-- Extracting the sheet label of a point inserted in the `j`-th sheet
returns `j`. -/
theorem sheetPoint_sheet (j : Fin m) (s : S) :
    splitPointSheet S m (splitFinite S m) (Iso.refl _)
      (sheetPoint S m j s) = j := by
  let e := sigmaMk (fun _ : ULift.{u} (Fin m) ↦ S)
  have hj : e.symm (sheetPoint S m j s) = ⟨ULift.up j, s⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (sigmaMk_mk
      (fun _ : ULift.{u} (Fin m) ↦ S) (ULift.up j) s).symm
  change (e.symm (sheetPoint S m j s)).1.down = j
  rw [hj]

/-- The sheet coordinate of the split finite scheme is locally constant. -/
theorem splitPointSheet_refl_isLocallyConstant :
    IsLocallyConstant (fun x : (splitFinite S m).left ↦
      splitPointSheet S m (splitFinite S m) (Iso.refl _) x) := by
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
  exact hindex.comp e.symm.continuous

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

include hα in
/-- The action on an arbitrary point of a split finite scheme is determined
by its extracted base point and sheet label. -/
theorem action_point_decomposition (g : G)
    (x : (splitFinite S m).left) :
    α.hom g x =
      sheetPoint S m
        (sheetTransition S m α g ((splitFinite S m).hom x)
          (splitPointSheet S m (splitFinite S m) (Iso.refl _) x))
        (β.hom g ((splitFinite S m).hom x)) := by
  have hd := splitPoint_decomposition S m
    (splitFinite S m) (Iso.refl _) x
  change x = sheetPoint S m
    (splitPointSheet S m (splitFinite S m) (Iso.refl _) x)
    (splitPointBase S m (splitFinite S m) (Iso.refl _) x) at hd
  rw [splitPointBase_refl] at hd
  calc
    α.hom g x = α.hom g
        (sheetPoint S m
          (splitPointSheet S m (splitFinite S m) (Iso.refl _) x)
          ((splitFinite S m).hom x)) := congrArg (α.hom g) hd
    _ = _ := action_sheetPoint S m α β hα g _ _

include hα in
/-- Extracting the sheet after applying the action gives the corresponding
transition label. -/
theorem splitPointSheet_action (g : G)
    (x : (splitFinite S m).left) :
    splitPointSheet S m (splitFinite S m) (Iso.refl _) (α.hom g x) =
      sheetTransition S m α g ((splitFinite S m).hom x)
        (splitPointSheet S m (splitFinite S m) (Iso.refl _) x) := by
  rw [action_point_decomposition S m α β hα]
  exact sheetPoint_sheet S m _ _

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

/-- The union of the source sheets reached from `j₀` along the orbit of
`s₀`, restricted over the corresponding transition-signature loci. -/
def selectedOrbitSheetSet (s₀ : S) (j₀ : Fin m) :
    Set (splitFinite S m).left :=
  ⋃ h : G,
    ((splitFinite S m).hom ⁻¹'
      constantTransitionSet S m α (β.hom h s₀)) ∩
    {x | splitPointSheet S m (splitFinite S m) (Iso.refl _) x =
      sheetTransition S m α h s₀ j₀}

/-- The selected orbit-sheet union is open and closed in the split finite
source. -/
theorem selectedOrbitSheetSet_isClopen (s₀ : S) (j₀ : Fin m) :
    IsClopen (selectedOrbitSheetSet S m α β s₀ j₀) := by
  apply isClopen_iUnion_of_finite
  intro h
  apply IsClopen.inter
  · exact (constantTransitionSet_isClopen S m α (β.hom h s₀)).preimage
      (splitFinite S m).hom.continuous
  · exact (splitPointSheet_refl_isLocallyConstant S m).isClopen_fiber _

omit [Finite G] in
/-- The actual translated sheet point belongs to the selected orbit-sheet
union. -/
theorem orbit_sheetPoint_mem_selectedOrbitSheetSet
    (s₀ : S) (j₀ : Fin m) (h : G) :
    sheetPoint S m (sheetTransition S m α h s₀ j₀) (β.hom h s₀) ∈
      selectedOrbitSheetSet S m α β s₀ j₀ := by
  rw [selectedOrbitSheetSet]
  apply Set.mem_iUnion.2
  refine ⟨h, ?_⟩
  constructor
  · change (splitFinite S m).hom
        (sheetPoint S m (sheetTransition S m α h s₀ j₀) (β.hom h s₀)) ∈
      constantTransitionSet S m α (β.hom h s₀)
    rw [sheetPoint_projection]
    exact self_mem_constantTransitionSet S m α (β.hom h s₀)
  · change splitPointSheet S m (splitFinite S m) (Iso.refl _)
      (sheetPoint S m (sheetTransition S m α h s₀ j₀)
        (β.hom h s₀)) = sheetTransition S m α h s₀ j₀
    exact sheetPoint_sheet S m _ _

omit [Finite G] in
include hα in
/-- The selected orbit-sheet union is preserved by every action map. -/
theorem selectedOrbitSheetSet_map_mem
    (s₀ : S) (j₀ : Fin m)
    {x : (splitFinite S m).left}
    (hx : x ∈ selectedOrbitSheetSet S m α β s₀ j₀) (h : G) :
    α.hom h x ∈ selectedOrbitSheetSet S m α β s₀ j₀ := by
  rw [selectedOrbitSheetSet] at hx ⊢
  obtain ⟨k, hxbase, hxsheet⟩ := Set.mem_iUnion.1 hx
  apply Set.mem_iUnion.2
  refine ⟨k * h, ?_, ?_⟩
  · have hmap := constantTransitionSet_map_mem_general S m α β hα
      (β.hom k s₀) hxbase h
    have hcover := congrArg (fun e : (splitFinite S m).left ⟶ S ↦ e x)
      (hα h)
    change (splitFinite S m).hom (α.hom h x) =
      β.hom h ((splitFinite S m).hom x) at hcover
    have hkh := congrArg (fun e : S ⟶ S ↦ e s₀) (β.hom_mul k h)
    change β.hom (k * h) s₀ = β.hom h (β.hom k s₀) at hkh
    change (splitFinite S m).hom (α.hom h x) ∈
      constantTransitionSet S m α (β.hom (k * h) s₀)
    rw [hcover, hkh]
    exact hmap
  · change splitPointSheet S m (splitFinite S m) (Iso.refl _)
      (α.hom h x) = sheetTransition S m α (k * h) s₀ j₀
    change splitPointSheet S m (splitFinite S m) (Iso.refl _) x =
      sheetTransition S m α k s₀ j₀ at hxsheet
    rw [splitPointSheet_action S m α β hα, hxsheet]
    have hsig := (mem_constantTransitionSet_iff S m α
      (β.hom k s₀) ((splitFinite S m).hom x)).1 hxbase
    calc
      sheetTransition S m α h ((splitFinite S m).hom x)
          (sheetTransition S m α k s₀ j₀) =
        sheetTransition S m α h (β.hom k s₀)
          (sheetTransition S m α k s₀ j₀) :=
        hsig h (sheetTransition S m α k s₀ j₀)
      _ = sheetTransition S m α (k * h) s₀ j₀ :=
        (sheetTransition_mul S m α β hα k h s₀ j₀).symm

/-- The selected orbit-sheet union as an open subscheme of the split finite
source. -/
noncomputable def selectedOrbitSheetOpen (s₀ : S) (j₀ : Fin m) :
    (splitFinite S m).left.Opens :=
  ⟨selectedOrbitSheetSet S m α β s₀ j₀,
    (selectedOrbitSheetSet_isClopen S m α β s₀ j₀).isOpen⟩

/-- Over an affine base, the selected orbit-sheet open is affine. -/
theorem selectedOrbitSheetOpen_isAffine [IsAffine S]
    (s₀ : S) (j₀ : Fin m) :
    IsAffineOpen (selectedOrbitSheetOpen S m α β s₀ j₀) := by
  letI : IsAffine (splitFinite S m).left := by
    change IsAffine (∐ fun _ : ULift.{u} (Fin m) ↦ S)
    infer_instance
  exact isAffineOpen_of_isClopen
    (selectedOrbitSheetSet_isClopen S m α β s₀ j₀)

include hα in
/-- The selected orbit-sheet open is stable under the split source action. -/
theorem selectedOrbitSheetOpen_isStable (s₀ : S) (j₀ : Fin m) :
    α.IsStableOpen (selectedOrbitSheetOpen S m α β s₀ j₀) := by
  intro h
  apply SetLike.ext
  intro x
  change α.hom h x ∈ selectedOrbitSheetSet S m α β s₀ j₀ ↔
    x ∈ selectedOrbitSheetSet S m α β s₀ j₀
  constructor
  · intro hx
    have hback := selectedOrbitSheetSet_map_mem S m α β hα
      s₀ j₀ hx h⁻¹
    have hcancel : α.hom h⁻¹ (α.hom h x) = x := by
      have hmul := congrArg (fun e : (splitFinite S m).left ⟶
        (splitFinite S m).left ↦ e x) (α.hom_mul h h⁻¹)
      rw [mul_inv_cancel, α.hom_one] at hmul
      exact hmul.symm.trans (ConcreteCategory.id_apply x)
    rwa [hcancel] at hback
  · intro hx
    exact selectedOrbitSheetSet_map_mem S m α β hα s₀ j₀ hx h

/-- The action restricted to the selected orbit-sheet open. -/
noncomputable def selectedOrbitSheetAction (s₀ : S) (j₀ : Fin m) :
    SchemeAction G
      (selectedOrbitSheetOpen S m α β s₀ j₀).toScheme :=
  α.restrict (selectedOrbitSheetOpen_isStable S m α β hα s₀ j₀)

include hα in
/-- Inclusion of the selected orbit-sheet open is equivariant. -/
theorem selectedOrbitSheetOpen_inclusion_equivariant
    (s₀ : S) (j₀ : Fin m) (g : G) :
    (selectedOrbitSheetAction S m α β hα s₀ j₀).hom g ≫
        (selectedOrbitSheetOpen S m α β s₀ j₀).ι =
      (selectedOrbitSheetOpen S m α β s₀ j₀).ι ≫ α.hom g :=
  Scheme.Hom.resLE_comp_ι (α.hom g)
    ((selectedOrbitSheetOpen_isStable S m α β hα s₀ j₀).le_preimage g)

/-- Over an affine base, the restricted selected orbit-sheet action has
affine orbit neighbourhoods. -/
theorem selectedOrbitSheetAction_hasAffineOrbit [IsAffine S]
    (s₀ : S) (j₀ : Fin m) :
    HasAffineOrbit (selectedOrbitSheetAction S m α β hα s₀ j₀) := by
  letI : IsAffine
      (selectedOrbitSheetOpen S m α β s₀ j₀).toScheme :=
    selectedOrbitSheetOpen_isAffine S m α β s₀ j₀
  exact hasAffineOrbit_of_isAffine _

/-- The finite-group quotient of the selected orbit-sheet chart. -/
noncomputable def selectedOrbitSheetQuotient [IsAffine S]
    (s₀ : S) (j₀ : Fin m) : Scheme.{u} := by
  letI : IsAffine
      (selectedOrbitSheetOpen S m α β s₀ j₀).toScheme :=
    selectedOrbitSheetOpen_isAffine S m α β s₀ j₀
  exact quotient (selectedOrbitSheetAction S m α β hα s₀ j₀)
    (selectedOrbitSheetAction_hasAffineOrbit S m α β hα s₀ j₀)

/-- The canonical projection from the selected orbit-sheet chart to its
finite-group quotient. -/
noncomputable def selectedOrbitSheetQuotientπ [IsAffine S]
    (s₀ : S) (j₀ : Fin m) :
    (selectedOrbitSheetOpen S m α β s₀ j₀).toScheme ⟶
      selectedOrbitSheetQuotient S m α β hα s₀ j₀ := by
  letI : IsAffine
      (selectedOrbitSheetOpen S m α β s₀ j₀).toScheme :=
    selectedOrbitSheetOpen_isAffine S m α β s₀ j₀
  exact quotientπ (selectedOrbitSheetAction S m α β hα s₀ j₀)
    (selectedOrbitSheetAction_hasAffineOrbit S m α β hα s₀ j₀)

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

/-- The map from the selected orbit-sheet open back to the original finite
source. -/
noncomputable def selectedOrbitSheetToOriginal
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (τ : SchemeAction G Y) (f : X ⟶ Y)
    (q : Spec (.of R) ⟶ Y) (σ : SchemeAction G X)
    (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    (n : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin n → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R n =
      pullback.snd f q)
    (s : (EquivariantFpqcRefinement.refinement τ q).left)
    (j : Fin n) :
    (selectedOrbitSheetOpen
      (EquivariantFpqcRefinement.refinement τ q).left n
      (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
      (EquivariantFpqcRefinement.refinementAction τ q) s j).toScheme ⟶ X :=
  (selectedOrbitSheetOpen
      (EquivariantFpqcRefinement.refinement τ q).left n
      (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
      (EquivariantFpqcRefinement.refinementAction τ q) s j).ι ≫
    (EquivariantSplitRefinement.directSplitIso τ f q n E hE).inv.left ≫
    pullback.fst f (EquivariantFpqcRefinement.projection τ q 1 ≫ q)

/-- The selected orbit-sheet open maps equivariantly back to the original
finite source.  This is the morphism to which finite-group quotient descent
will be applied. -/
theorem selectedOrbitSheetToOriginal_equivariant
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (τ : SchemeAction G Y) (f : X ⟶ Y)
    (q : Spec (.of R) ⟶ Y) (σ : SchemeAction G X)
    (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    (n : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin n → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R n =
      pullback.snd f q)
    (s : (EquivariantFpqcRefinement.refinement τ q).left)
    (j : Fin n) (g : G) :
    (selectedOrbitSheetAction
        (EquivariantFpqcRefinement.refinement τ q).left n
        (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
        (EquivariantFpqcRefinement.refinementAction τ q)
        (EquivariantSplitRefinement.splitAction_equivariant
          τ f q σ hf n E hE) s j).hom g ≫
      (selectedOrbitSheetOpen
        (EquivariantFpqcRefinement.refinement τ q).left n
        (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
        (EquivariantFpqcRefinement.refinementAction τ q) s j).ι ≫
      (EquivariantSplitRefinement.directSplitIso τ f q n E hE).inv.left ≫
      pullback.fst f (EquivariantFpqcRefinement.projection τ q 1 ≫ q) =
    (selectedOrbitSheetOpen
        (EquivariantFpqcRefinement.refinement τ q).left n
        (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
        (EquivariantFpqcRefinement.refinementAction τ q) s j).ι ≫
      (EquivariantSplitRefinement.directSplitIso τ f q n E hE).inv.left ≫
      pullback.fst f (EquivariantFpqcRefinement.projection τ q 1 ≫ q) ≫
      σ.hom g := by
  rw [← Category.assoc,
    selectedOrbitSheetOpen_inclusion_equivariant
      (EquivariantFpqcRefinement.refinement τ q).left n
      (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
      (EquivariantFpqcRefinement.refinementAction τ q)
      (EquivariantSplitRefinement.splitAction_equivariant
        τ f q σ hf n E hE) s j g]
  simp only [Category.assoc]
  rw [EquivariantSplitRefinement.splitAction_toOriginal_equivariant]

/-- The named selected-orbit map is equivariant. -/
theorem selectedOrbitSheetToOriginal_equivariant'
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (τ : SchemeAction G Y) (f : X ⟶ Y)
    (q : Spec (.of R) ⟶ Y) (σ : SchemeAction G X)
    (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    (n : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin n → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R n =
      pullback.snd f q)
    (s : (EquivariantFpqcRefinement.refinement τ q).left)
    (j : Fin n) (g : G) :
    (selectedOrbitSheetAction
        (EquivariantFpqcRefinement.refinement τ q).left n
        (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
        (EquivariantFpqcRefinement.refinementAction τ q)
        (EquivariantSplitRefinement.splitAction_equivariant
          τ f q σ hf n E hE) s j).hom g ≫
      selectedOrbitSheetToOriginal τ f q σ hf n E hE s j =
    selectedOrbitSheetToOriginal τ f q σ hf n E hE s j ≫ σ.hom g :=
  selectedOrbitSheetToOriginal_equivariant τ f q σ hf n E hE s j g

/-- Quotient descent of the selected orbit-sheet map to an affine original
source. -/
noncomputable def selectedOrbitSheetDescendedMap
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (τ : SchemeAction G Y) (f : X ⟶ Y)
    (q : Spec (.of R) ⟶ Y) (σ : SchemeAction G X)
    (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    (n : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin n → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R n =
      pullback.snd f q)
    (s : (EquivariantFpqcRefinement.refinement τ q).left)
    (j : Fin n)
    [IsAffine (EquivariantFpqcRefinement.refinement τ q).left]
    [IsAffine X] :
    selectedOrbitSheetQuotient
        (EquivariantFpqcRefinement.refinement τ q).left n
        (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
        (EquivariantFpqcRefinement.refinementAction τ q)
        (EquivariantSplitRefinement.splitAction_equivariant
          τ f q σ hf n E hE) s j ⟶
      quotient σ (hasAffineOrbit_of_isAffine σ) := by
  letI : IsAffine
      (selectedOrbitSheetOpen
        (EquivariantFpqcRefinement.refinement τ q).left n
        (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
        (EquivariantFpqcRefinement.refinementAction τ q) s j).toScheme :=
    selectedOrbitSheetOpen_isAffine
      (EquivariantFpqcRefinement.refinement τ q).left n
      (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
      (EquivariantFpqcRefinement.refinementAction τ q) s j
  exact EquivariantFiniteGroupQuotient.descendedMap
    (selectedOrbitSheetAction
      (EquivariantFpqcRefinement.refinement τ q).left n
      (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
      (EquivariantFpqcRefinement.refinementAction τ q)
      (EquivariantSplitRefinement.splitAction_equivariant
        τ f q σ hf n E hE) s j)
    σ
    (selectedOrbitSheetAction_hasAffineOrbit
      (EquivariantFpqcRefinement.refinement τ q).left n
      (EquivariantSplitRefinement.splitAction τ f q σ hf n E hE)
      (EquivariantFpqcRefinement.refinementAction τ q)
      (EquivariantSplitRefinement.splitAction_equivariant
        τ f q σ hf n E hE) s j)
    (hasAffineOrbit_of_isAffine σ)
    (selectedOrbitSheetToOriginal τ f q σ hf n E hE s j)
    (selectedOrbitSheetToOriginal_equivariant' τ f q σ hf n E hE s j)

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteActionSheets
