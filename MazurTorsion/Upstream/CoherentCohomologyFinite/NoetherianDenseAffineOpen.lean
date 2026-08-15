/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.AlgebraicGeometry.Limits

/-!
# Dense affine opens in Noetherian schemes

A Noetherian scheme has finitely many irreducible components.  For each
component, remove all the other components and choose an affine open
inside the resulting nonempty exclusive locus.  These affine opens are
pairwise disjoint, so their finite union is affine.  It is dense because
it meets every irreducible component in a nonempty open subset.

This gives a single dense affine domain on which a rational map from a
Noetherian scheme can be constructed.
-/

open AlgebraicGeometry TopologicalSpace
open scoped Function

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- A dense affine open subscheme of a scheme. -/
structure DenseAffineOpenData (X : Scheme.{u}) where
  openSubset : X.Opens
  isAffineOpen_openSubset : IsAffineOpen openSubset
  dense_openSubset : Dense (openSubset : Set X)

namespace DenseAffineOpenData

variable {X : Scheme.{u}} (D : DenseAffineOpenData X)

/-- The dense affine open as a scheme. -/
abbrev domain : Scheme.{u} :=
  D.openSubset

/-- The inclusion of the dense affine open. -/
abbrev inclusion : D.domain ⟶ X :=
  D.openSubset.ι

instance : IsAffine D.domain :=
  D.isAffineOpen_openSubset

instance : IsOpenImmersion D.inclusion :=
  inferInstance

/-- The inclusion has dense image. -/
theorem dense_range_inclusion :
    Dense (Set.range D.inclusion.base) := by
  simpa [Scheme.Opens.range_ι] using D.dense_openSubset

/-- Into a locally Noetherian scheme, the dense affine open inclusion
is quasi-compact. -/
theorem quasiCompact_inclusion [IsLocallyNoetherian X] :
    QuasiCompact D.inclusion :=
  inferInstance

end DenseAffineOpenData

/-- Affine opens chosen inside the exclusive locus of every irreducible
component of a Noetherian scheme. -/
structure NoetherianComponentAffineOpenData
    (X : Scheme.{u}) [IsNoetherian X] where
  componentOpen : irreducibleComponents X → X.Opens
  isAffineOpen_componentOpen :
    ∀ Z, IsAffineOpen (componentOpen Z)
  nonempty_componentOpen :
    ∀ Z, (componentOpen Z : Set X).Nonempty
  componentOpen_le_exclusive :
    ∀ Z, componentOpen Z ≤ X.irreducibleComponentOpen Z.1

namespace NoetherianComponentAffineOpenData

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The exclusive open locus of an irreducible component has closure
equal to that component. -/
theorem closure_irreducibleComponentOpen
    (Z : irreducibleComponents X) :
    closure
        ((X.irreducibleComponentOpen Z.1 : X.Opens) : Set X) =
      Z.1 := by
  change
    closure
        (⋃₀ (irreducibleComponents X \ {Z.1}))ᶜ =
      Z.1
  exact
    closure_sUnion_irreducibleComponents_sdiff_singleton
      finite_irreducibleComponents_of_isNoetherian Z.1 Z.2

/-- The exclusive open locus of an irreducible component is nonempty. -/
theorem irreducibleComponentOpen_nonempty
    (Z : irreducibleComponents X) :
    ((X.irreducibleComponentOpen Z.1 : X.Opens) : Set X).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hclosure := closure_irreducibleComponentOpen Z
  rw [h, closure_empty] at hclosure
  exact Z.2.1.nonempty.ne_empty hclosure.symm

/-- The exclusive open locus is contained in its irreducible
component. -/
theorem irreducibleComponentOpen_le_component
    (Z : irreducibleComponents X) :
    ((X.irreducibleComponentOpen Z.1 : X.Opens) : Set X) ⊆
      Z.1 := by
  intro x hx
  have hx' :
      x ∈ closure
        ((X.irreducibleComponentOpen Z.1 : X.Opens) : Set X) :=
    subset_closure hx
  rwa [closure_irreducibleComponentOpen Z] at hx'

/-- Distinct irreducible components have disjoint exclusive loci. -/
theorem pairwise_disjoint_irreducibleComponentOpen :
    Pairwise
      (Disjoint on
        fun Z : irreducibleComponents X =>
          X.irreducibleComponentOpen Z.1) := by
  intro Z W hZW
  change
    Disjoint
      (X.irreducibleComponentOpen Z.1)
      (X.irreducibleComponentOpen W.1)
  rw [← Opens.coe_disjoint]
  refine Set.disjoint_left.2 ?_
  intro x hxZ hxW
  have hxWComponent : x ∈ W.1 :=
    irreducibleComponentOpen_le_component W hxW
  change x ∈ (⋃₀ (irreducibleComponents X \ {Z.1}))ᶜ at hxZ
  apply hxZ
  refine Set.mem_sUnion_of_mem hxWComponent ?_
  refine ⟨W.2, ?_⟩
  have hWZ : W.1 ≠ Z.1 := fun h ↦ hZW (Subtype.ext h.symm)
  simpa only [Set.mem_singleton_iff] using hWZ

/-- Every exclusive component locus contains a nonempty affine open. -/
theorem exists_affineOpen_le_irreducibleComponentOpen
    (Z : irreducibleComponents X) :
    ∃ U : X.Opens,
      IsAffineOpen U ∧
        (U : Set X).Nonempty ∧
        U ≤ X.irreducibleComponentOpen Z.1 := by
  obtain ⟨x, hx⟩ := irreducibleComponentOpen_nonempty Z
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      hx (X.irreducibleComponentOpen Z.1).isOpen
  exact ⟨U, hU, ⟨x, hxU⟩, hUle⟩

/-- A Noetherian scheme admits componentwise affine opens in the
exclusive component loci. -/
theorem exists_noetherianComponentAffineOpenData :
    Nonempty (NoetherianComponentAffineOpenData X) := by
  classical
  choose U hU using
    fun Z : irreducibleComponents X =>
      exists_affineOpen_le_irreducibleComponentOpen Z
  exact
    ⟨{
      componentOpen := U
      isAffineOpen_componentOpen := fun Z => (hU Z).1
      nonempty_componentOpen := fun Z => (hU Z).2.1
      componentOpen_le_exclusive := fun Z => (hU Z).2.2
    }⟩

variable (D : NoetherianComponentAffineOpenData X)

/-- The chosen component opens are pairwise disjoint. -/
theorem pairwise_disjoint_componentOpen :
    Pairwise (Disjoint on D.componentOpen) := by
  intro Z W hZW
  exact
    (pairwise_disjoint_irreducibleComponentOpen hZW).mono
      (D.componentOpen_le_exclusive Z)
      (D.componentOpen_le_exclusive W)

/-- The union of the componentwise affine opens. -/
def denseAffineOpen : X.Opens :=
  ⨆ Z, D.componentOpen Z

/-- The finite disjoint union of the component opens is affine. -/
theorem isAffineOpen_denseAffineOpen :
    IsAffineOpen D.denseAffineOpen := by
  letI : Finite (irreducibleComponents X) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  exact
    IsAffineOpen.iSup_of_disjoint
      D.isAffineOpen_componentOpen
      D.pairwise_disjoint_componentOpen

/-- A chosen affine open is dense in its irreducible component. -/
theorem component_subset_closure_componentOpen
    (Z : irreducibleComponents X) :
    Z.1 ⊆ closure (D.componentOpen Z : Set X) := by
  have hUComponent :
      (D.componentOpen Z : Set X) ⊆ Z.1 :=
    (show
      (D.componentOpen Z : Set X) ⊆
        (X.irreducibleComponentOpen Z.1 : Set X) from
      D.componentOpen_le_exclusive Z).trans
      (irreducibleComponentOpen_le_component Z)
  have hinter :
      (Z.1 ∩ (D.componentOpen Z : Set X)).Nonempty := by
    simpa only [Set.inter_eq_right.mpr hUComponent] using
      D.nonempty_componentOpen Z
  have hclosure :=
    subset_closure_inter_of_isPreirreducible_of_isOpen
      Z.2.1.2 (D.componentOpen Z).isOpen hinter
  rwa [Set.inter_eq_right.mpr hUComponent] at hclosure

/-- The union of the componentwise affine opens is dense. -/
theorem dense_denseAffineOpen :
    Dense (D.denseAffineOpen : Set X) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.2
  intro x
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩
  have hxZ : x ∈ Z.1 :=
    mem_irreducibleComponent
  have hxClosure :
      x ∈ closure (D.componentOpen Z : Set X) :=
    D.component_subset_closure_componentOpen Z hxZ
  apply
    closure_mono
      (show
        (D.componentOpen Z : Set X) ⊆
          (D.denseAffineOpen : Set X) from
        le_iSup D.componentOpen Z)
  exact hxClosure

/-- The componentwise construction produces one dense affine open. -/
def toDenseAffineOpenData : DenseAffineOpenData X where
  openSubset := D.denseAffineOpen
  isAffineOpen_openSubset := D.isAffineOpen_denseAffineOpen
  dense_openSubset := D.dense_denseAffineOpen

end NoetherianComponentAffineOpenData

/-- Every Noetherian scheme contains a dense affine open subscheme. -/
theorem exists_denseAffineOpenData
    (X : Scheme.{u}) [IsNoetherian X] :
    Nonempty (DenseAffineOpenData X) := by
  obtain ⟨D⟩ :=
    NoetherianComponentAffineOpenData.exists_noetherianComponentAffineOpenData
      (X := X)
  exact ⟨D.toDenseAffineOpenData⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
