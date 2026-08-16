/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphCoproduct

/-!
# Isolating a clopen component of a closed subscheme

Suppose a closed subscheme `P ⟶ Y` splits as `B ⨿ W`.  Removing the closed
image of the unwanted component `W` from `Y` gives an open neighbourhood in
which the original closed subscheme is exactly `B`.  This file packages that
elementary geometric operation as a cartesian square.

The named downstream consumer is the local incidence graph comparison: its
étale equal-coordinate closed subscheme splits into the desired graph and
complementary sheets, and this construction deletes precisely those
complementary sheets.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.ClosedComponentNeighborhood

/-- The chosen first summand, transported back through a coproduct
presentation. -/
noncomputable def leftSummand {B W P : Scheme.{u}} (E : P ≅ B ⨿ W) :
    B ⟶ P :=
  coprod.inl ≫ E.inv

/-- The complementary summand, transported back through a coproduct
presentation. -/
noncomputable def rightSummand {B W P : Scheme.{u}} (E : P ≅ B ⨿ W) :
    W ⟶ P :=
  coprod.inr ≫ E.inv

instance leftSummand_open {B W P : Scheme.{u}} (E : P ≅ B ⨿ W) :
    IsOpenImmersion (leftSummand E) := by
  dsimp [leftSummand]
  infer_instance

instance rightSummand_open {B W P : Scheme.{u}} (E : P ≅ B ⨿ W) :
    IsOpenImmersion (rightSummand E) := by
  dsimp [rightSummand]
  infer_instance

instance rightSummand_closed {B W P : Scheme.{u}} (E : P ≅ B ⨿ W) :
    IsClosedImmersion (rightSummand E) := by
  haveI : IsClosedImmersion (coprod.inr : W ⟶ B ⨿ W) :=
    .of_isPreimmersion _ (by
      have hr : Set.range (coprod.inr : W ⟶ B ⨿ W) =
          (Set.range (coprod.inl : B ⟶ B ⨿ W))ᶜ :=
        (isCompl_range_inl_inr B W).symm.eq_compl
      rw [hr]
      exact (coprod.inl : B ⟶ B ⨿ W).opensRange.2.isClosed_compl)
  dsimp [rightSummand]
  infer_instance

/-- The two transported summands are complementary opens. -/
theorem summands_isCompl {B W P : Scheme.{u}} (E : P ≅ B ⨿ W) :
    IsCompl (leftSummand E).opensRange (rightSummand E).opensRange := by
  change IsCompl (coprod.inl ≫ E.inv).opensRange
    (coprod.inr ≫ E.inv).opensRange
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_comp]
  have himage (U : (B ⨿ W).Opens) :
      E.inv ''ᵁ U = E.inv.homeomorph.opensCongr U := by
    apply TopologicalSpace.Opens.ext
    ext p
    rw [Homeomorph.opensCongr_apply]
    rw [Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_comap]
    constructor
    · rintro ⟨x, hx, hxp⟩
      subst p
      change E.inv.homeomorph.symm (E.inv.homeomorph x) ∈ U
      rw [E.inv.homeomorph.symm_apply_apply]
      exact hx
    · intro hp
      refine ⟨E.inv.homeomorph.symm p, hp, ?_⟩
      exact E.inv.homeomorph.apply_symm_apply p
  rw [himage, himage]
  exact (isCompl_opensRange_inl_inr B W).map
    E.inv.homeomorph.opensCongr

/-- Delete from the ambient scheme the closed image of the unwanted
component. -/
noncomputable def complementOpen {W P Y : Scheme.{u}}
    (i : P ⟶ Y) [IsClosedImmersion i]
    (w : W ⟶ P) [IsClosedImmersion w] : Y.Opens :=
  ⟨(Set.range (w ≫ i))ᶜ,
    (w ≫ i).isClosedMap.isClosed_range.isOpen_compl⟩

/-- Pulling the complement open back to the original closed subscheme leaves
exactly the desired component. -/
theorem preimage_complementOpen {B W P Y : Scheme.{u}}
    (i : P ⟶ Y) [IsClosedImmersion i]
    (b : B ⟶ P) [IsOpenImmersion b]
    (w : W ⟶ P) [IsOpenImmersion w] [IsClosedImmersion w]
    (hcompl : IsCompl b.opensRange w.opensRange) :
    i ⁻¹ᵁ complementOpen i w = b.opensRange := by
  apply TopologicalSpace.Opens.ext
  ext p
  change i p ∉ Set.range (w ≫ i) ↔ p ∈ (b.opensRange : Set P)
  have hcompl' : IsCompl (b.opensRange : Set P) (w.opensRange : Set P) :=
    hcompl.map TopologicalSpace.Opens.frameHom
  rw [hcompl'.eq_compl]
  change (¬ ∃ x, i (w x) = i p) ↔ p ∉ Set.range w
  constructor
  · intro h hp
    obtain ⟨x, rfl⟩ := hp
    exact h ⟨x, rfl⟩
  · intro h hp
    obtain ⟨x, hx⟩ := hp
    apply h
    exact ⟨x, i.isClosedEmbedding.injective hx⟩

/-- The desired component factors through the complement open. -/
noncomputable def leftToComplementOpen {B W P Y : Scheme.{u}}
    (i : P ⟶ Y) [IsClosedImmersion i]
    (b : B ⟶ P) [IsOpenImmersion b]
    (w : W ⟶ P) [IsOpenImmersion w] [IsClosedImmersion w]
    (hcompl : IsCompl b.opensRange w.opensRange) :
    B ⟶ (complementOpen i w).toScheme :=
  IsOpenImmersion.lift (complementOpen i w).ι (b ≫ i) (by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    rw [Scheme.Opens.range_ι]
    change i (b x) ∉ Set.range (w ≫ i)
    intro hw
    obtain ⟨z, hz⟩ := hw
    have hzb : w z = b x := i.isClosedEmbedding.injective hz
    have hd : Disjoint (b.opensRange : Set P) (w.opensRange : Set P) :=
      (hcompl.map TopologicalSpace.Opens.frameHom).disjoint
    exact Set.disjoint_iff_forall_ne.mp hd
      (show b x ∈ (b.opensRange : Set P) from ⟨x, rfl⟩)
      (show w z ∈ (w.opensRange : Set P) from ⟨z, rfl⟩) hzb.symm)

@[reassoc]
theorem leftToComplementOpen_ι {B W P Y : Scheme.{u}}
    (i : P ⟶ Y) [IsClosedImmersion i]
    (b : B ⟶ P) [IsOpenImmersion b]
    (w : W ⟶ P) [IsOpenImmersion w] [IsClosedImmersion w]
    (hcompl : IsCompl b.opensRange w.opensRange) :
    leftToComplementOpen i b w hcompl ≫ (complementOpen i w).ι = b ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The complement open intersects the original closed subscheme in exactly
the desired component. -/
theorem isPullback_leftToComplementOpen {B W P Y : Scheme.{u}}
    (i : P ⟶ Y) [IsClosedImmersion i]
    (b : B ⟶ P) [IsOpenImmersion b]
    (w : W ⟶ P) [IsOpenImmersion w] [IsClosedImmersion w]
    (hcompl : IsCompl b.opensRange w.opensRange) :
    IsPullback (leftToComplementOpen i b w hcompl) b
      (complementOpen i w).ι i := by
  apply IsOpenImmersion.isPullback
  · exact (leftToComplementOpen_ι i b w hcompl).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      preimage_complementOpen i b w hcompl

/-- A coproduct presentation of a closed subscheme canonically supplies an
open ambient neighbourhood whose pullback is its first summand. -/
theorem exists_open_isPullback_firstSummand {B W P Y : Scheme.{u}}
    (i : P ⟶ Y) [IsClosedImmersion i] (E : P ≅ B ⨿ W) :
    ∃ (U : Y.Opens) (g : B ⟶ U.toScheme),
      IsPullback g (leftSummand E) U.ι i := by
  let b := leftSummand E
  let w := rightSummand E
  let hcompl := summands_isCompl E
  exact ⟨complementOpen i w, leftToComplementOpen i b w hcompl,
    isPullback_leftToComplementOpen i b w hcompl⟩

end MazurTorsion.AlgebraicGeometry.Jacobian.ClosedComponentNeighborhood
