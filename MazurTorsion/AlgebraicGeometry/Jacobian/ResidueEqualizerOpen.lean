/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Open loci where two relative morphisms differ on residue fields

For two morphisms into a separated relative scheme, the equalizer is a
closed immersion.  Its closed image records scheme-theoretic equality,
including residue-field data that equality of underlying topological point
maps cannot detect.  We package the complementary open and prove a residue-
field criterion for membership.

The named downstream consumer is the cross-support refinement in
`GeometricAssignedAffineSimultaneousNeighborhood`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.ResidueEqualizerOpen

variable {S : Scheme.{u}} {X Y : Over S}

/-- The open complement of the scheme-theoretic equalizer of two relative
morphisms. -/
noncomputable def complement (f g : X ⟶ Y) [IsSeparated Y.hom] :
    X.left.Opens :=
  ⟨(Set.range (equalizer.ι f g).left)ᶜ,
    (equalizer.ι f g).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- Unequal residue-field restrictions exclude a point from the closed
equalizer image.  Cancellation is valid because the residue-field extension
along an equalizer point induces a faithfully flat map of spectra. -/
theorem not_mem_range_of_residue_ne (f g : X ⟶ Y)
    (x : X.left)
    (h : X.left.fromSpecResidueField x ≫ f.left ≠
      X.left.fromSpecResidueField x ≫ g.left) :
    x ∉ Set.range (equalizer.ι f g).left := by
  rintro ⟨y, rfl⟩
  apply h
  let e := Spec.map ((equalizer.ι f g).left.residueFieldMap y)
  haveI : Flat e := by infer_instance
  haveI : Surjective e := by infer_instance
  letI : Epi e := Flat.epi_of_flat_of_surjective e
  rw [← cancel_epi e]
  simp only [e, ← Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hc := congrArg Over.Hom.left (equalizer.condition f g)
  change (equalizer.ι f g).left ≫ f.left =
    (equalizer.ι f g).left ≫ g.left at hc
  simpa only [Category.assoc] using congrArg
    (fun q ↦ (equalizer f g).left.fromSpecResidueField y ≫ q) hc

/-- A point whose residue-field restrictions differ lies in the open
complement of the equalizer. -/
theorem mem_complement_of_residue_ne (f g : X ⟶ Y) [IsSeparated Y.hom]
    (x : X.left)
    (h : X.left.fromSpecResidueField x ≫ f.left ≠
      X.left.fromSpecResidueField x ≫ g.left) :
    x ∈ complement f g :=
  not_mem_range_of_residue_ne f g x h

/-- Residue-field inequality descends from a test point to its image: if
the two maps agreed over the image residue field, functoriality of residue
fields would make their pullbacks agree at the original test point. -/
theorem residue_ne_at_image_of_comp_ne
    {B Z : Scheme.{u}} (p : B ⟶ X.left) (b : B)
    (f g : X.left ⟶ Z)
    (h : B.fromSpecResidueField b ≫ p ≫ f ≠
      B.fromSpecResidueField b ≫ p ≫ g) :
    X.left.fromSpecResidueField (p b) ≫ f ≠
      X.left.fromSpecResidueField (p b) ≫ g := by
  intro himage
  apply h
  let e := Spec.map (p.residueFieldMap b)
  have he : e ≫ X.left.fromSpecResidueField (p b) =
      B.fromSpecResidueField b ≫ p := by
    simpa only [e] using
      p.SpecMap_residueFieldMap_fromSpecResidueField b
  have hpull := congrArg (fun q ↦ e ≫ q) himage
  simpa only [← Category.assoc, he] using hpull

end MazurTorsion.AlgebraicGeometry.Jacobian.ResidueEqualizerOpen
