/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.NoetherianDenseAffineOpen
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine covers with a common dense affine open

Let `X` be Noetherian.  Starting from an affine open `V`, adjoin one of
the previously chosen componentwise affine opens for every irreducible
component missed by `V`.  These additional opens are disjoint from `V`
and from one another, so their union with `V` remains affine.  The
resulting affine open contains the generic point of every irreducible
component.

Applied to a nonempty finite affine cover, the enlarged members still
cover `X`, while their intersection is an affine dense open.  This is
the common domain used in the graph construction in Chow's lemma.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped Function

noncomputable section

universe u v

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

variable {X : Scheme.{u}} [IsNoetherian X]

namespace NoetherianComponentAffineOpenData

/-- The indexing type for an affine open together with the chosen
component opens belonging to components which it misses. -/
abbrev componentEnvelopeIndex (V : X.Opens) :=
  Unit ⊕
    {Z : irreducibleComponents X //
      Disjoint (V : Set X) Z.1}

/-- The pieces whose disjoint union enlarges `V`: first `V` itself,
then one chosen affine open in each component missed by `V`. -/
def componentEnvelopePiece
    (D : NoetherianComponentAffineOpenData X)
    (V : X.Opens) :
    componentEnvelopeIndex V → X.Opens
  | Sum.inl _ => V
  | Sum.inr Z => D.componentOpen Z.1

/-- Enlarge an open by the chosen affine opens in all irreducible
components which it misses. -/
def componentEnvelope
    (D : NoetherianComponentAffineOpenData X)
    (V : X.Opens) : X.Opens :=
  ⨆ a, D.componentEnvelopePiece V a

/-- Every chosen component open lies in its irreducible component. -/
theorem componentOpen_le_component
    (D : NoetherianComponentAffineOpenData X)
    (Z : irreducibleComponents X) :
    (D.componentOpen Z : Set X) ⊆ Z.1 :=
  (show
      (D.componentOpen Z : Set X) ⊆
        (X.irreducibleComponentOpen Z.1 : Set X) from
    D.componentOpen_le_exclusive Z).trans
      (irreducibleComponentOpen_le_component Z)

/-- The pieces of a component envelope are pairwise disjoint. -/
theorem pairwise_disjoint_componentEnvelopePiece
    (D : NoetherianComponentAffineOpenData X)
    (V : X.Opens) :
    Pairwise
      (Disjoint on D.componentEnvelopePiece V) := by
  intro a b hab
  rcases a with (_ | Z)
  · rcases b with (_ | W)
    · exact (hab rfl).elim
    · change Disjoint V (D.componentOpen W.1)
      rw [← Opens.coe_disjoint]
      exact W.2.mono_right (D.componentOpen_le_component W.1)
  · rcases b with (_ | W)
    · change Disjoint (D.componentOpen Z.1) V
      rw [← Opens.coe_disjoint]
      exact
        (Z.2.mono_right
          (D.componentOpen_le_component Z.1)).symm
    · exact
        D.pairwise_disjoint_componentOpen
          (fun hZW => hab (congrArg Sum.inr (Subtype.ext hZW)))

/-- If `V` is affine, then its component envelope is affine. -/
theorem isAffineOpen_componentEnvelope
    (D : NoetherianComponentAffineOpenData X)
    (V : X.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen (D.componentEnvelope V) := by
  letI : Finite (irreducibleComponents X) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  apply IsAffineOpen.iSup_of_disjoint
  · intro a
    rcases a with (_ | Z)
    · exact hV
    · exact D.isAffineOpen_componentOpen Z.1
  · exact D.pairwise_disjoint_componentEnvelopePiece V

/-- The original open is contained in its component envelope. -/
theorem le_componentEnvelope
    (D : NoetherianComponentAffineOpenData X)
    (V : X.Opens) :
    V ≤ D.componentEnvelope V := by
  exact
    le_iSup
      (D.componentEnvelopePiece V)
      (Sum.inl ())

/-- The generic point of each irreducible component belongs to its
chosen componentwise affine open. -/
theorem genericPoint_mem_componentOpen
    (D : NoetherianComponentAffineOpenData X)
    (Z : irreducibleComponents X) :
    (genericPoints.ofComponent Z : X) ∈
      D.componentOpen Z := by
  apply
    ((genericPoints.isGenericPoint_ofComponent Z).mem_open_set_iff
      (D.componentOpen Z).isOpen).2
  obtain ⟨x, hx⟩ := D.nonempty_componentOpen Z
  exact
    ⟨x, D.componentOpen_le_component Z hx, hx⟩

/-- Every component envelope contains the generic point of every
irreducible component. -/
theorem genericPoint_mem_componentEnvelope
    (D : NoetherianComponentAffineOpenData X)
    (V : X.Opens)
    (Z : irreducibleComponents X) :
    (genericPoints.ofComponent Z : X) ∈
      D.componentEnvelope V := by
  by_cases hη :
      (genericPoints.ofComponent Z : X) ∈ V
  · exact D.le_componentEnvelope V hη
  · have hdisjoint :
        Disjoint (V : Set X) Z.1 := by
      rw [disjoint_comm,
        (genericPoints.isGenericPoint_ofComponent Z).disjoint_iff
          V.isOpen]
      exact hη
    let Z' :
        {Z : irreducibleComponents X //
          Disjoint (V : Set X) Z.1} :=
      ⟨Z, hdisjoint⟩
    apply
      (le_iSup
        (D.componentEnvelopePiece V)
        (Sum.inr Z') :
          D.componentOpen Z ≤ D.componentEnvelope V)
    exact D.genericPoint_mem_componentOpen Z

/-- The common intersection of a finite family of component
envelopes. -/
def commonComponentEnvelope
    {ι : Type v} (D : NoetherianComponentAffineOpenData X)
    (V : ι → X.Opens) : X.Opens :=
  ⨅ i, D.componentEnvelope (V i)

/-- A nonempty finite intersection of affine component envelopes is
affine on a separated scheme. -/
theorem isAffineOpen_commonComponentEnvelope
    {ι : Type v} [Finite ι] [Nonempty ι]
    (D : NoetherianComponentAffineOpenData X)
    (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i))
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    IsAffineOpen (D.commonComponentEnvelope V) := by
  exact
    IsAffineOpen.iInf
      (fun i => D.isAffineOpen_componentEnvelope
        (V i) (hV i))

/-- The common component envelope contains every component's generic
point. -/
theorem genericPoint_mem_commonComponentEnvelope
    {ι : Type v} [Finite ι]
    (D : NoetherianComponentAffineOpenData X)
    (V : ι → X.Opens)
    (Z : irreducibleComponents X) :
    (genericPoints.ofComponent Z : X) ∈
      D.commonComponentEnvelope V := by
  classical
  letI := Fintype.ofFinite ι
  have hmem (s : Finset ι) :
      (genericPoints.ofComponent Z : X) ∈
        s.inf (fun i => D.componentEnvelope (V i)) := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha ih =>
        simp only [Finset.inf_insert, Opens.mem_inf]
        exact
          ⟨D.genericPoint_mem_componentEnvelope (V a) Z, ih⟩
  rw [commonComponentEnvelope,
    ← Finset.inf_univ_eq_iInf]
  exact hmem Finset.univ

/-- The common intersection of component envelopes is dense. -/
theorem dense_commonComponentEnvelope
    {ι : Type v} [Finite ι]
    (D : NoetherianComponentAffineOpenData X)
    (V : ι → X.Opens) :
    Dense (D.commonComponentEnvelope V : Set X) := by
  have hgeneric :
      genericPoints X ⊆
        (D.commonComponentEnvelope V : Set X) := by
    intro η hη
    let Z := genericPoints.component ⟨η, hη⟩
    have hηeq :
        (genericPoints.ofComponent Z : X) = η := by
      exact
        congrArg Subtype.val
          (genericPoints.ofComponent_component ⟨η, hη⟩)
    rw [← hηeq]
    exact D.genericPoint_mem_commonComponentEnvelope V Z
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.2
  intro x
  have hx :
      x ∈ closure (genericPoints X) := by
    rw [genericPoints.closure]
    trivial
  exact closure_mono hgeneric hx

end NoetherianComponentAffineOpenData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
