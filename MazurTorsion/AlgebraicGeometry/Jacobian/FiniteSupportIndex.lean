/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower

/-!
# Topological and geometric indices in a finite ordered support

An ordered divisor may repeat the same curve point.  Local neighborhoods must
be chosen once for each distinct underlying point, rather than once for each
occurrence: a repeated point contributes a power of one graph ideal, not
several artificial coproduct copies.  The occurrence-to-neighborhood map is
therefore indexed by the finite image in the underlying topological space.

That topological image is not enough for exact reconstruction: two coordinate
morphisms from the residue-field spectrum may have the same image but differ
on residue fields.  A second finite image therefore enumerates the actual
geometric coordinate morphisms.  Reindexing through representatives of this
geometric image and repeating them is proved to recover the original
residue-field point exactly, so no residue-field correlation is lost.

The named downstream consumer is the corrected finite-support chart in
`FiniteSupportEtaleCoordinates`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportIndex

open PermutationPower

variable (S : Scheme.{u}) (d : ℕ) (X : Over S)
variable (z : (power S (Fin d) X).left)

/-- The unique point of the spectrum of the residue field of `z`, expressed
as a point of the scheme rather than of the definitionally equal prime
spectrum. -/
noncomputable def residueClosedPoint :
    (Spec ((power S (Fin d) X).left.residueField z)).carrier :=
  IsLocalRing.closedPoint ↑((power S (Fin d) X).left.residueField z)

/-- The underlying point of the `i`-th ordered coordinate. -/
noncomputable def coordinatePoint (i : Fin d) : X.left :=
  (Pi.π (fun _ : Fin d ↦ X) i).left z

/-! ## Topological support: one local neighborhood per curve point -/

/-- The finite set of underlying curve points occurring in the ordered
support. -/
noncomputable def topologicalSupportFinset : Finset X.left := by
  classical
  exact Finset.univ.image (coordinatePoint S d X z)

/-- The type of distinct underlying curve points in the ordered support. -/
abbrev topologicalSupportSubtype :=
  {x // x ∈ topologicalSupportFinset S d X z}

/-- The number of distinct underlying curve points. -/
noncomputable def topologicalSupportCard : ℕ :=
  Fintype.card (topologicalSupportSubtype S d X z)

/-- A canonical finite-ordinal enumeration of the underlying support. -/
noncomputable def topologicalSupportEquiv :
    Fin (topologicalSupportCard S d X z) ≃
      topologicalSupportSubtype S d X z :=
  (Fintype.equivFin (topologicalSupportSubtype S d X z)).symm

/-- The underlying curve point with a given topological-support index. -/
noncomputable def topologicalSupportPoint
    (j : Fin (topologicalSupportCard S d X z)) : X.left :=
  (topologicalSupportEquiv S d X z j).1

/-- The topological-support index of an ordered coordinate. -/
noncomputable def topologicalCoordinateSupportIndex (i : Fin d) :
    Fin (topologicalSupportCard S d X z) :=
  (topologicalSupportEquiv S d X z).symm
    ⟨coordinatePoint S d X z i, by
      classical
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

/-- Returning from the topological-support index recovers the coordinate's
underlying curve point. -/
theorem topologicalSupportPoint_coordinateSupportIndex (i : Fin d) :
    topologicalSupportPoint S d X z
        (topologicalCoordinateSupportIndex S d X z i) =
      coordinatePoint S d X z i := by
  change ((topologicalSupportEquiv S d X z)
    ((topologicalSupportEquiv S d X z).symm
      ⟨coordinatePoint S d X z i, _⟩)).1 = _
  rw [Equiv.apply_symm_apply]

/-- Two occurrences select the same local neighborhood exactly when their
underlying curve points agree. -/
theorem topologicalCoordinateSupportIndex_eq_iff (i i' : Fin d) :
    topologicalCoordinateSupportIndex S d X z i =
        topologicalCoordinateSupportIndex S d X z i' ↔
      coordinatePoint S d X z i = coordinatePoint S d X z i' := by
  constructor
  · intro h
    rw [← topologicalSupportPoint_coordinateSupportIndex S d X z i,
      ← topologicalSupportPoint_coordinateSupportIndex S d X z i', h]
  · intro h
    change (topologicalSupportEquiv S d X z).symm
        ⟨coordinatePoint S d X z i, _⟩ =
      (topologicalSupportEquiv S d X z).symm
        ⟨coordinatePoint S d X z i', _⟩
    exact congrArg (topologicalSupportEquiv S d X z).symm (Subtype.ext h)

/-- Every enumerated topological-support point is represented by an original
ordered coordinate. -/
theorem exists_coordinatePoint_eq_topologicalSupportPoint
    (j : Fin (topologicalSupportCard S d X z)) :
    ∃ i : Fin d, coordinatePoint S d X z i =
      topologicalSupportPoint S d X z j := by
  classical
  have hj : topologicalSupportPoint S d X z j ∈
      topologicalSupportFinset S d X z :=
    (topologicalSupportEquiv S d X z j).2
  change topologicalSupportPoint S d X z j ∈
    Finset.univ.image (coordinatePoint S d X z) at hj
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hj
  exact ⟨i, hi⟩

/-- Every topological-support index occurs in the original tuple. -/
theorem topologicalCoordinateSupportIndex_surjective :
    Function.Surjective (topologicalCoordinateSupportIndex S d X z) := by
  intro j
  obtain ⟨i, hi⟩ :=
    exists_coordinatePoint_eq_topologicalSupportPoint S d X z j
  refine ⟨i, ?_⟩
  apply_fun topologicalSupportEquiv S d X z
  apply Subtype.ext
  change topologicalSupportPoint S d X z
      (topologicalCoordinateSupportIndex S d X z i) =
    topologicalSupportPoint S d X z j
  rw [topologicalSupportPoint_coordinateSupportIndex]
  exact hi

/-- The number of occurrences having one underlying support point. -/
noncomputable def topologicalSupportMultiplicity
    (j : Fin (topologicalSupportCard S d X z)) : ℕ :=
  Fintype.card
    {i : Fin d // topologicalCoordinateSupportIndex S d X z i = j}

/-- Multiplicities of the distinct underlying support points sum to the
ordered degree. -/
theorem sum_topologicalSupportMultiplicity :
    ∑ j : Fin (topologicalSupportCard S d X z),
        topologicalSupportMultiplicity S d X z j = d := by
  classical
  calc
    ∑ j : Fin (topologicalSupportCard S d X z),
        topologicalSupportMultiplicity S d X z j = Fintype.card (Fin d) := by
      simp only [topologicalSupportMultiplicity, Fintype.card_subtype]
      exact (Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ) (t := Finset.univ)
        (f := topologicalCoordinateSupportIndex S d X z) (by simp)).symm
    _ = d := Fintype.card_fin d

/-- A chosen ordered coordinate representing an underlying support point. -/
noncomputable def topologicalSupportRepresentative
    (j : Fin (topologicalSupportCard S d X z)) : Fin d :=
  Classical.choose
    (exists_coordinatePoint_eq_topologicalSupportPoint S d X z j)

/-- The chosen coordinate has the indexed underlying support point. -/
theorem coordinatePoint_topologicalSupportRepresentative
    (j : Fin (topologicalSupportCard S d X z)) :
    coordinatePoint S d X z
        (topologicalSupportRepresentative S d X z j) =
      topologicalSupportPoint S d X z j :=
  Classical.choose_spec
    (exists_coordinatePoint_eq_topologicalSupportPoint S d X z j)

/-- Select one original coordinate for every distinct underlying support
point.  This map chooses local neighborhoods; it is not claimed to retain
different residue-field embeddings with the same topological image. -/
noncomputable def topologicalDistinctSupportPowerHom :
    power S (Fin d) X ⟶
      power S (Fin (topologicalSupportCard S d X z)) X :=
  Pi.lift (fun j ↦ Pi.π (fun _ : Fin d ↦ X)
    (topologicalSupportRepresentative S d X z j))

@[reassoc]
theorem topologicalDistinctSupportPowerHom_comp_projection
    (j : Fin (topologicalSupportCard S d X z)) :
    topologicalDistinctSupportPowerHom S d X z ≫
        Pi.π (fun _ : Fin (topologicalSupportCard S d X z) ↦ X) j =
      Pi.π (fun _ : Fin d ↦ X)
        (topologicalSupportRepresentative S d X z j) :=
  Pi.lift_π _ j

/-- The relative-power point listing each underlying support point once. -/
noncomputable def topologicalDistinctSupportPoint :
    (power S (Fin (topologicalSupportCard S d X z)) X).left :=
  (topologicalDistinctSupportPowerHom S d X z).left z

/-- Each coordinate of the topologically deduplicated point is the indexed
underlying support point. -/
theorem topologicalDistinctSupportPoint_projection
    (j : Fin (topologicalSupportCard S d X z)) :
    (Pi.π (fun _ : Fin (topologicalSupportCard S d X z) ↦ X) j).left
        (topologicalDistinctSupportPoint S d X z) =
      topologicalSupportPoint S d X z j := by
  have h := congrArg Over.Hom.left
    (topologicalDistinctSupportPowerHom_comp_projection S d X z j)
  have hz := congrArg
    (fun f : (power S (Fin d) X).left ⟶ X.left ↦ f z) h
  change (Pi.π (fun _ : Fin (topologicalSupportCard S d X z) ↦ X) j).left
      ((topologicalDistinctSupportPowerHom S d X z).left z) =
    coordinatePoint S d X z
      (topologicalSupportRepresentative S d X z j) at hz
  exact hz.trans
    (coordinatePoint_topologicalSupportRepresentative S d X z j)

/-! ## Geometric support: exact residue-field coordinates -/

/-- The `i`-th coordinate as an actual geometric morphism from the residue
field of the original ordered-power point. -/
noncomputable def coordinateGeometricPoint (i : Fin d) :
    Spec ((power S (Fin d) X).left.residueField z) ⟶ X.left :=
  (power S (Fin d) X).left.fromSpecResidueField z ≫
    (Pi.π (fun _ : Fin d ↦ X) i).left

/-- Evaluating a coordinate geometric point at the unique point of its
field spectrum recovers the underlying coordinate point. -/
theorem coordinateGeometricPoint_closedPoint (i : Fin d) :
    coordinateGeometricPoint S d X z i
        (residueClosedPoint S d X z) =
      coordinatePoint S d X z i := by
  change (Pi.π (fun _ : Fin d ↦ X) i).left
      ((power S (Fin d) X).left.fromSpecResidueField z
        (residueClosedPoint S d X z)) = _
  rw [Scheme.fromSpecResidueField_apply]
  rfl

/-- The finite set of distinct geometric coordinate morphisms occurring in
the ordered support. -/
noncomputable def supportFinset : Finset
    (Spec ((power S (Fin d) X).left.residueField z) ⟶ X.left) := by
  classical
  exact Finset.univ.image (coordinateGeometricPoint S d X z)

/-- The type of distinct geometric support coordinates. -/
abbrev supportSubtype := {x // x ∈ supportFinset S d X z}

/-- The number of distinct geometric support coordinates. -/
noncomputable def supportCard : ℕ :=
  Fintype.card (supportSubtype S d X z)

/-- A canonical finite-ordinal enumeration of the distinct geometric
support. -/
noncomputable def supportEquiv :
    Fin (supportCard S d X z) ≃ supportSubtype S d X z :=
  (Fintype.equivFin (supportSubtype S d X z)).symm

/-- The geometric coordinate morphism with a given support index. -/
noncomputable def supportGeometricPoint
    (j : Fin (supportCard S d X z)) :
    Spec ((power S (Fin d) X).left.residueField z) ⟶ X.left :=
  (supportEquiv S d X z j).1

/-- The underlying curve point of an indexed geometric support coordinate. -/
noncomputable def supportPoint (j : Fin (supportCard S d X z)) : X.left :=
  supportGeometricPoint S d X z j
    (residueClosedPoint S d X z)

/-- The geometric support index of an ordered coordinate. -/
noncomputable def coordinateSupportIndex (i : Fin d) :
    Fin (supportCard S d X z) :=
  (supportEquiv S d X z).symm
    ⟨coordinateGeometricPoint S d X z i, by
      classical
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

/-- Returning from the support index of a coordinate recovers its geometric
coordinate morphism exactly. -/
theorem supportGeometricPoint_coordinateSupportIndex (i : Fin d) :
    supportGeometricPoint S d X z (coordinateSupportIndex S d X z i) =
      coordinateGeometricPoint S d X z i := by
  change ((supportEquiv S d X z)
    ((supportEquiv S d X z).symm
      ⟨coordinateGeometricPoint S d X z i, _⟩)).1 = _
  rw [Equiv.apply_symm_apply]

/-- Returning from the support index also recovers the underlying coordinate
point. -/
theorem supportPoint_coordinateSupportIndex (i : Fin d) :
    supportPoint S d X z (coordinateSupportIndex S d X z i) =
      coordinatePoint S d X z i := by
  rw [supportPoint, supportGeometricPoint_coordinateSupportIndex,
    coordinateGeometricPoint_closedPoint]

/-- Two ordered coordinates have the same support index exactly when their
geometric coordinate morphisms agree. -/
theorem coordinateSupportIndex_eq_iff (i i' : Fin d) :
    coordinateSupportIndex S d X z i = coordinateSupportIndex S d X z i' ↔
      coordinateGeometricPoint S d X z i =
        coordinateGeometricPoint S d X z i' := by
  constructor
  · intro h
    rw [← supportGeometricPoint_coordinateSupportIndex S d X z i,
      ← supportGeometricPoint_coordinateSupportIndex S d X z i', h]
  · intro h
    change (supportEquiv S d X z).symm
        ⟨coordinateGeometricPoint S d X z i, _⟩ =
      (supportEquiv S d X z).symm
        ⟨coordinateGeometricPoint S d X z i', _⟩
    exact congrArg (supportEquiv S d X z).symm (Subtype.ext h)

/-- Every enumerated support morphism is represented by an original ordered
coordinate. -/
theorem exists_coordinateGeometricPoint_eq_supportGeometricPoint
    (j : Fin (supportCard S d X z)) :
    ∃ i : Fin d, coordinateGeometricPoint S d X z i =
      supportGeometricPoint S d X z j := by
  classical
  have hj : supportGeometricPoint S d X z j ∈ supportFinset S d X z :=
    (supportEquiv S d X z j).2
  change supportGeometricPoint S d X z j ∈
    Finset.univ.image (coordinateGeometricPoint S d X z) at hj
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hj
  exact ⟨i, hi⟩

/-- Every distinct geometric support index occurs among the original ordered
coordinates. -/
theorem coordinateSupportIndex_surjective :
    Function.Surjective (coordinateSupportIndex S d X z) := by
  intro j
  obtain ⟨i, hi⟩ :=
    exists_coordinateGeometricPoint_eq_supportGeometricPoint S d X z j
  refine ⟨i, ?_⟩
  apply_fun supportEquiv S d X z
  apply Subtype.ext
  change supportGeometricPoint S d X z (coordinateSupportIndex S d X z i) =
    supportGeometricPoint S d X z j
  rw [supportGeometricPoint_coordinateSupportIndex]
  exact hi

/-- The number of ordered occurrences of one distinct geometric support
coordinate. -/
noncomputable def supportMultiplicity
    (j : Fin (supportCard S d X z)) : ℕ :=
  Fintype.card {i : Fin d // coordinateSupportIndex S d X z i = j}

/-- Multiplicities of the distinct geometric support coordinates sum to the
original ordered degree. -/
theorem sum_supportMultiplicity :
    ∑ j : Fin (supportCard S d X z), supportMultiplicity S d X z j = d := by
  classical
  calc
    ∑ j : Fin (supportCard S d X z), supportMultiplicity S d X z j =
        Fintype.card (Fin d) := by
      simp only [supportMultiplicity, Fintype.card_subtype]
      exact (Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ) (t := Finset.univ)
        (f := coordinateSupportIndex S d X z) (by simp)).symm
    _ = d := Fintype.card_fin d

/-- A chosen original coordinate representing a distinct geometric support
coordinate. -/
noncomputable def supportRepresentative
    (j : Fin (supportCard S d X z)) : Fin d :=
  Classical.choose
    (exists_coordinateGeometricPoint_eq_supportGeometricPoint S d X z j)

/-- The chosen coordinate really represents the indexed geometric support
coordinate. -/
theorem coordinateGeometricPoint_supportRepresentative
    (j : Fin (supportCard S d X z)) :
    coordinateGeometricPoint S d X z (supportRepresentative S d X z j) =
      supportGeometricPoint S d X z j :=
  Classical.choose_spec
    (exists_coordinateGeometricPoint_eq_supportGeometricPoint S d X z j)

/-- The underlying point of the chosen coordinate is the indexed support
point. -/
theorem coordinatePoint_supportRepresentative
    (j : Fin (supportCard S d X z)) :
    coordinatePoint S d X z (supportRepresentative S d X z j) =
      supportPoint S d X z j := by
  rw [← coordinateGeometricPoint_closedPoint]
  exact congrArg
    (fun f : Spec ((power S (Fin d) X).left.residueField z) ⟶ X.left ↦
      f (residueClosedPoint S d X z))
    (coordinateGeometricPoint_supportRepresentative S d X z j)

/-- Forget repeated occurrences and retain one representative coordinate for
every distinct geometric support coordinate. -/
noncomputable def distinctSupportPowerHom :
    power S (Fin d) X ⟶ power S (Fin (supportCard S d X z)) X :=
  Pi.lift (fun j ↦
    Pi.π (fun _ : Fin d ↦ X) (supportRepresentative S d X z j))

@[reassoc]
theorem distinctSupportPowerHom_comp_projection
    (j : Fin (supportCard S d X z)) :
    distinctSupportPowerHom S d X z ≫
        Pi.π (fun _ : Fin (supportCard S d X z) ↦ X) j =
      Pi.π (fun _ : Fin d ↦ X) (supportRepresentative S d X z j) :=
  Pi.lift_π _ j

/-- Repeat the distinct coordinates according to the original occurrence
assignment. -/
noncomputable def repeatSupportPowerHom :
    power S (Fin (supportCard S d X z)) X ⟶ power S (Fin d) X :=
  Pi.lift (fun i ↦
    Pi.π (fun _ : Fin (supportCard S d X z) ↦ X)
      (coordinateSupportIndex S d X z i))

@[reassoc]
theorem repeatSupportPowerHom_comp_projection (i : Fin d) :
    repeatSupportPowerHom S d X z ≫ Pi.π (fun _ : Fin d ↦ X) i =
      Pi.π (fun _ : Fin (supportCard S d X z) ↦ X)
        (coordinateSupportIndex S d X z i) :=
  Pi.lift_π _ i

/-- The residue-field point of the original ordered power, packaged over the
same base. -/
noncomputable def residuePointOver : Over S :=
  Over.mk ((power S (Fin d) X).left.fromSpecResidueField z ≫
    (power S (Fin d) X).hom)

/-- The canonical residue-field point as a morphism into the ordered power. -/
noncomputable def residuePointToPower :
    residuePointOver S d X z ⟶ power S (Fin d) X :=
  Over.homMk ((power S (Fin d) X).left.fromSpecResidueField z) rfl

/-- Reindexing to distinct coordinates and repeating them recovers the
original geometric residue-field point exactly. -/
theorem residuePointToPower_comp_distinct_comp_repeat :
    residuePointToPower S d X z ≫ distinctSupportPowerHom S d X z ≫
        repeatSupportPowerHom S d X z =
      residuePointToPower S d X z := by
  apply Pi.hom_ext
  intro i
  calc
    _ = residuePointToPower S d X z ≫ distinctSupportPowerHom S d X z ≫
        (repeatSupportPowerHom S d X z ≫
          Pi.π (fun _ : Fin d ↦ X) i) := by
      simp only [Category.assoc]
    _ = residuePointToPower S d X z ≫ distinctSupportPowerHom S d X z ≫
        Pi.π (fun _ : Fin (supportCard S d X z) ↦ X)
          (coordinateSupportIndex S d X z i) := by
      rw [repeatSupportPowerHom_comp_projection]
    _ = residuePointToPower S d X z ≫
        (distinctSupportPowerHom S d X z ≫
          Pi.π (fun _ : Fin (supportCard S d X z) ↦ X)
            (coordinateSupportIndex S d X z i)) := by
      rfl
    _ = residuePointToPower S d X z ≫
        Pi.π (fun _ : Fin d ↦ X)
          (supportRepresentative S d X z
            (coordinateSupportIndex S d X z i)) := by
      rw [distinctSupportPowerHom_comp_projection]
    _ = residuePointToPower S d X z ≫
        Pi.π (fun _ : Fin d ↦ X) i := by
      apply Over.OverMorphism.ext
      change coordinateGeometricPoint S d X z
          (supportRepresentative S d X z
            (coordinateSupportIndex S d X z i)) =
        coordinateGeometricPoint S d X z i
      rw [coordinateGeometricPoint_supportRepresentative,
        supportGeometricPoint_coordinateSupportIndex]

/-- The relative-power point listing every distinct geometric support
coordinate once. -/
noncomputable def distinctSupportPoint :
    (power S (Fin (supportCard S d X z)) X).left :=
  (distinctSupportPowerHom S d X z).left z

/-- The `j`-th coordinate of the reindexed point is exactly the indexed
underlying support point. -/
theorem distinctSupportPoint_projection
    (j : Fin (supportCard S d X z)) :
    (Pi.π (fun _ : Fin (supportCard S d X z) ↦ X) j).left
        (distinctSupportPoint S d X z) =
      supportPoint S d X z j := by
  have h := congrArg Over.Hom.left
    (distinctSupportPowerHom_comp_projection S d X z j)
  have hz := congrArg
    (fun f : (power S (Fin d) X).left ⟶ X.left ↦ f z) h
  change (Pi.π (fun _ : Fin (supportCard S d X z) ↦ X) j).left
      ((distinctSupportPowerHom S d X z).left z) =
    coordinatePoint S d X z (supportRepresentative S d X z j) at hz
  exact hz.trans (coordinatePoint_supportRepresentative S d X z j)

/-- Repeating the deduplicated point through the original occurrence map
recovers the exact original ordered-power point. -/
theorem repeatSupportPowerHom_distinctSupportPoint :
    (repeatSupportPowerHom S d X z).left (distinctSupportPoint S d X z) = z := by
  have h := congrArg Over.Hom.left
    (residuePointToPower_comp_distinct_comp_repeat S d X z)
  have hz := congrArg
    (fun f : (residuePointOver S d X z).left ⟶
      (power S (Fin d) X).left ↦
        f (residueClosedPoint S d X z)) h
  change (repeatSupportPowerHom S d X z).left
      ((distinctSupportPowerHom S d X z).left
        ((power S (Fin d) X).left.fromSpecResidueField z
          (residueClosedPoint S d X z))) =
    (power S (Fin d) X).left.fromSpecResidueField z
      (residueClosedPoint S d X z) at hz
  simpa only [Scheme.fromSpecResidueField_apply, distinctSupportPoint] using hz

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportIndex
