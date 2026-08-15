/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

/-!
# Assigned split charts for the geometric support

The local finite étale family is indexed by the distinct geometric
coordinates of an ordered point, while its ordered power still has the
original degree.  Thus genuinely repeated coordinates use the same family
member, but every occurrence contributes its own factor.

This file constructs the repeat map from the coherent product of the
geometric-support family to the degree-preserving assigned product.  Its map
back to the curve power is proved to recover the exact original point.  It
then inserts the assigned product into the ordered power of the single
disjoint split family.  The named downstream consumer is
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricSupportAssignedSplitChart

open FiniteEtaleAssignedCoproductPower
open FiniteEtaleCoproductPower
open FiniteEtaleRelativeProduct
open FiniteSupportEtaleCoordinates
open FiniteSupportIndex
open PermutationPower
open SplitFiniteBaseChange
open SplitFinitePowerPoint
open SplitFiniteSymmetricQuotient

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom]

/-- The coherent product base for the family indexed by distinct geometric
support coordinates. -/
noncomputable abbrev coherentBase (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Scheme.{u} :=
  coherentFpqcBase K C (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q

/-- The coherent product base maps to the ground-field spectrum. -/
noncomputable def coherentBaseToGround (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    coherentBase K C d z V T q ⟶ Spec (.of K) :=
  (∏ᶜ commonCoverFamily K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q).hom

/-- The coherent component attached to one distinct geometric coordinate. -/
noncomputable abbrev component (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme)
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Over (coherentBase K C d z V T q) :=
  coherentFpqcPulledComponent K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q j

/-- One geometric-support component maps back to the curve. -/
noncomputable def componentToCurve (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme)
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (component K C d z V T q j).left ⟶ C.left :=
  coherentFpqcPulledComponentToCurve K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q j

/-- Component-to-curve maps are compatible with the coherent base's map to
the ground field. -/
theorem componentToCurve_comp_structureMap (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme)
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    componentToCurve K C d z V T q j ≫ C.hom =
      (component K C d z V T q j).hom ≫
        coherentBaseToGround K C d z V T q :=
  coherentFpqcPulledComponentToCurve_comp_structureMap K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q j

/-- The coherent product of all distinct geometric components, regarded over
the ground field. -/
noncomputable abbrev componentProductOverGround (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Over (Spec (.of K)) :=
  coherentFpqcComponentFamilyOverGround K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q

/-- Repeat the geometric-support components according to the original
degree-`d` occurrence assignment. -/
noncomputable abbrev assignedComponentProductOverGround (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Over (Spec (.of K)) :=
  assignedProductOverOriginalBase (coherentBase K C d z V T q)
    (Spec (.of K)) (coherentBaseToGround K C d z V T q)
    (geometricDistinctSupportCard K C d z) d
    (component K C d z V T q) (geometricPointSupportIndex K C d z)

/-- The repeat map from one copy of each distinct geometric component to the
original occurrence-indexed assigned product. -/
noncomputable def productToAssigned (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    componentProductOverGround K C d z V T q ⟶
      assignedComponentProductOverGround K C d z V T q :=
  productToAssignedProductOverOriginalBase
    (coherentBase K C d z V T q) (Spec (.of K))
    (coherentBaseToGround K C d z V T q)
    (geometricDistinctSupportCard K C d z) d
    (component K C d z V T q) (geometricPointSupportIndex K C d z)

/-- Map the degree-preserving assigned product to the original curve power. -/
noncomputable def assignedProductToCurvePower (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    assignedComponentProductOverGround K C d z V T q ⟶
      power (Spec (.of K)) (Fin d) C :=
  assignedProductToTargetPower (coherentBase K C d z V T q)
    (Spec (.of K)) (coherentBaseToGround K C d z V T q)
    (geometricDistinctSupportCard K C d z) d
    (component K C d z V T q) (geometricPointSupportIndex K C d z)
    C (componentToCurve K C d z V T q)
    (componentToCurve_comp_structureMap K C d z V T q)

/-- The full geometric-support component product maps to the curve power of
the deduplicated geometric tuple. -/
noncomputable def componentProductToCurvePower (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    componentProductOverGround K C d z V T q ⟶
      power (Spec (.of K))
        (Fin (geometricDistinctSupportCard K C d z)) C :=
  coherentFpqcComponentFamilyToCurvePower K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q

/-- The underlying map of the geometric component product has the expected
coordinate projection. -/
theorem componentProductToCurvePower_comp_projection_left (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme)
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (componentProductToCurvePower K C d z V T q ≫
        Pi.π (fun _ : Fin (geometricDistinctSupportCard K C d z) ↦ C) j).left =
      (Pi.π (component K C d z V T q) j).left ≫
        componentToCurve K C d z V T q j := by
  unfold componentProductToCurvePower
    coherentFpqcComponentFamilyToCurvePower
    independentRelativeProductToTargets
  rw [congrArg Over.Hom.left (Pi.lift_π _ j)]
  rfl

/-- Repeating coherent components and then forgetting to the curve equals
first forgetting the distinct geometric tuple and then repeating its curve
coordinates. -/
theorem productToAssigned_comp_curvePower (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    productToAssigned K C d z V T q ≫
        assignedProductToCurvePower K C d z V T q =
      componentProductToCurvePower K C d z V T q ≫
        repeatSupportPowerHom (Spec (.of K)) d C z := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, repeatSupportPowerHom_comp_projection]
  apply Over.OverMorphism.ext
  change (productToAssigned K C d z V T q).left ≫
      (assignedProductToCurvePower K C d z V T q ≫
        Pi.π (fun _ : Fin d ↦ C) i).left =
    (componentProductToCurvePower K C d z V T q ≫
      Pi.π (fun _ : Fin (geometricDistinctSupportCard K C d z) ↦ C)
        (geometricPointSupportIndex K C d z i)).left
  rw [componentProductToCurvePower_comp_projection_left]
  unfold assignedProductToCurvePower
  rw [assignedProductToTargetPower_comp_projection_left]
  change (productToAssignedProduct
      (coherentBase K C d z V T q)
      (geometricDistinctSupportCard K C d z) d
      (component K C d z V T q)
      (geometricPointSupportIndex K C d z)).left ≫
        (Pi.π (fun i : Fin d ↦ component K C d z V T q
          (geometricPointSupportIndex K C d z i)) i).left ≫
            componentToCurve K C d z V T q
              (geometricPointSupportIndex K C d z i) =
    (Pi.π (component K C d z V T q)
      (geometricPointSupportIndex K C d z i)).left ≫
        componentToCurve K C d z V T q
          (geometricPointSupportIndex K C d z i)
  have hproj := congrArg Over.Hom.left
    (productToAssignedProduct_comp_projection
      (coherentBase K C d z V T q)
      (geometricDistinctSupportCard K C d z) d
      (component K C d z V T q)
      (geometricPointSupportIndex K C d z) i)
  change (productToAssignedProduct
      (coherentBase K C d z V T q)
      (geometricDistinctSupportCard K C d z) d
      (component K C d z V T q)
      (geometricPointSupportIndex K C d z)).left ≫
        (Pi.π (fun i : Fin d ↦ component K C d z V T q
          (geometricPointSupportIndex K C d z i)) i).left =
    (Pi.π (component K C d z V T q)
      (geometricPointSupportIndex K C d z i)).left at hproj
  simpa only [Category.assoc] using congrArg
    (fun h ↦ h ≫ componentToCurve K C d z V T q
      (geometricPointSupportIndex K C d z i)) hproj

/-- The coherent product chart contains a point above the deduplicated
geometric support tuple. -/
theorem exists_componentProductPoint_over_geometricSupport
    (d : ℕ) (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (hV : commonBasePoint K C
      (geometricDistinctSupportCard K C d z)
      (geometricDistinctSupportOrderedPoint K C d z)
      (geometricDistinctCharts K C d z)
      (geometricDistinctNeighborhoods K C d z) ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] :
    ∃ p : (componentProductOverGround K C d z V T q).left,
      (componentProductToCurvePower K C d z V T q).left p =
        geometricDistinctSupportOrderedPoint K C d z := by
  exact exists_coherentFpqcComponentFamilyPoint_over_support K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V hV T q

/-- Repeating the coherent geometric-support point produces a point of the
assigned product mapping to the exact original ordered point. -/
theorem exists_assignedProductPoint_over_support
    (d : ℕ) (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (hV : commonBasePoint K C
      (geometricDistinctSupportCard K C d z)
      (geometricDistinctSupportOrderedPoint K C d z)
      (geometricDistinctCharts K C d z)
      (geometricDistinctNeighborhoods K C d z) ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] :
    ∃ p : (assignedComponentProductOverGround K C d z V T q).left,
      (assignedProductToCurvePower K C d z V T q).left p = z := by
  obtain ⟨p, hp⟩ :=
    exists_componentProductPoint_over_geometricSupport K C d z V hV T q
  refine ⟨(productToAssigned K C d z V T q).left p, ?_⟩
  have h := congrArg Over.Hom.left
    (productToAssigned_comp_curvePower K C d z V T q)
  have hp' := congrArg
    (fun f : (componentProductOverGround K C d z V T q).left ⟶
      (power (Spec (.of K)) (Fin d) C).left ↦ f p) h
  change (assignedProductToCurvePower K C d z V T q).left
      ((productToAssigned K C d z V T q).left p) =
    (repeatSupportPowerHom (Spec (.of K)) d C z).left
      ((componentProductToCurvePower K C d z V T q).left p) at hp'
  rw [hp, repeatGeometricSupportOrderedPoint] at hp'
  exact hp'

/-- The degree-`d` power of the single disjoint geometric-support family,
regarded over the ground field. -/
noncomputable abbrev assignedCoproductPowerOverGround (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Over (Spec (.of K)) :=
  assignedCoproductPowerOverOriginalBase (coherentBase K C d z V T q)
    (Spec (.of K)) (coherentBaseToGround K C d z V T q)
    (geometricDistinctSupportCard K C d z) d
    (component K C d z V T q)

/-- Insert every occurrence through its exact geometric-support member. -/
noncomputable def assignedProductToCoproductPower (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    assignedComponentProductOverGround K C d z V T q ⟶
      assignedCoproductPowerOverGround K C d z V T q :=
  assignedProductToCoproductPowerOverOriginalBase
    (coherentBase K C d z V T q) (Spec (.of K))
    (coherentBaseToGround K C d z V T q)
    (geometricDistinctSupportCard K C d z) d
    (component K C d z V T q) (geometricPointSupportIndex K C d z)

/-- Forget the assigned coproduct power back to the original curve power. -/
noncomputable def assignedCoproductPowerToCurvePower (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    assignedCoproductPowerOverGround K C d z V T q ⟶
      power (Spec (.of K)) (Fin d) C :=
  assignedCoproductPowerToTargetPower (coherentBase K C d z V T q)
    (Spec (.of K)) (coherentBaseToGround K C d z V T q)
    (geometricDistinctSupportCard K C d z) d
    (component K C d z V T q) C
    (componentToCurve K C d z V T q)
    (componentToCurve_comp_structureMap K C d z V T q)

/-- The exact original support point lies in the assigned ordered power of
the single disjoint coherent family. -/
theorem exists_assignedCoproductPowerPoint_over_support
    (d : ℕ) (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (hV : commonBasePoint K C
      (geometricDistinctSupportCard K C d z)
      (geometricDistinctSupportOrderedPoint K C d z)
      (geometricDistinctCharts K C d z)
      (geometricDistinctNeighborhoods K C d z) ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] :
    ∃ p : (assignedCoproductPowerOverGround K C d z V T q).left,
      (assignedCoproductPowerToCurvePower K C d z V T q).left p = z := by
  obtain ⟨p, hp⟩ := exists_assignedProductPoint_over_support
    K C d z V hV T q
  refine ⟨(assignedProductToCoproductPower K C d z V T q).left p, ?_⟩
  have h := assignedProductToCoproductPower_comp_targetPower
    (coherentBase K C d z V T q) (Spec (.of K))
    (coherentBaseToGround K C d z V T q)
    (geometricDistinctSupportCard K C d z) d
    (component K C d z V T q) (geometricPointSupportIndex K C d z)
    C (componentToCurve K C d z V T q)
    (componentToCurve_comp_structureMap K C d z V T q)
  have hleft := congrArg Over.Hom.left h
  have hpoint := congrArg
    (fun f : (assignedComponentProductOverGround K C d z V T q).left ⟶
      (power (Spec (.of K)) (Fin d) C).left ↦ f p) hleft
  exact hpoint.trans hp

/-- The chosen componentwise split charts assemble into one split
presentation of the geometric-support family. -/
noncomputable def familySplitIso (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d z) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q) :
    familyCoproduct (coherentBase K C d z V (Spec (.of T)) q)
        (geometricDistinctSupportCard K C d z)
        (component K C d z V (Spec (.of T)) q) ≅
      splitFinite (coherentBase K C d z V (Spec (.of T)) q)
        (totalSheets (geometricDistinctSupportCard K C d z) r) :=
  coherentFpqcFamilyCoproductSplitIso K C
    (geometricDistinctSupportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V T q r E hE

/-- A point of the assigned coproduct power selects one split sheet for
each of the original `d` occurrences. -/
noncomputable def assignedSupportSheetTuple (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d z) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q)
    (p : (assignedCoproductPowerOverGround K C d z V
      (Spec (.of T)) q).left) :
    Fin d → Fin (totalSheets (geometricDistinctSupportCard K C d z) r) :=
  splitPowerPointTuple (coherentBase K C d z V (Spec (.of T)) q) d
    (totalSheets (geometricDistinctSupportCard K C d z) r)
    (familyCoproduct (coherentBase K C d z V (Spec (.of T)) q)
      (geometricDistinctSupportCard K C d z)
      (component K C d z V (Spec (.of T)) q))
    (familySplitIso K C d z V T q r E hE) p

/-- The symmetric-power component selected by an assigned support point. -/
noncomputable def assignedSupportComponent (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d z) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q)
    (p : (assignedCoproductPowerOverGround K C d z V
      (Spec (.of T)) q).left) :
    splitComponentIndex d
      (totalSheets (geometricDistinctSupportCard K C d z) r) :=
  splitPowerPointComponent
    (coherentBase K C d z V (Spec (.of T)) q) d
    (totalSheets (geometricDistinctSupportCard K C d z) r)
    (familyCoproduct (coherentBase K C d z V (Spec (.of T)) q)
      (geometricDistinctSupportCard K C d z)
      (component K C d z V (Spec (.of T)) q))
    (familySplitIso K C d z V T q r E hE) p

/-- Sheet multiplicity in the selected component is the actual cardinality
of the corresponding fiber of the assigned point's extracted sheet tuple. -/
theorem assignedSupportComponent_sheetMultiplicity (d : ℕ)
    (z : (power (Spec (.of K)) (Fin d) C).left)
    (V : (geometricDistinctCommonBase K C d z).left.Opens)
    (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (r : Fin (geometricDistinctSupportCard K C d z) → ℕ)
    (E : ∀ j, pullback
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q ≅
      Spec (.of (Fin (r j) → T)))
    (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
      pullback.snd
        (restrictedPulledComponentToBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)
          (geometricDistinctCharts K C d z)
          (geometricDistinctNeighborhoods K C d z) V j) q)
    (p : (assignedCoproductPowerOverGround K C d z V
      (Spec (.of T)) q).left)
    (s : Fin (totalSheets (geometricDistinctSupportCard K C d z) r)) :
    sheetMultiplicity d
        (totalSheets (geometricDistinctSupportCard K C d z) r)
        (assignedSupportComponent K C d z V T q r E hE p) s =
      Fintype.card {i : Fin d //
        assignedSupportSheetTuple K C d z V T q r E hE p i = s} :=
  splitPowerPointComponent_sheetMultiplicity
    (coherentBase K C d z V (Spec (.of T)) q) d
    (totalSheets (geometricDistinctSupportCard K C d z) r)
    (familyCoproduct (coherentBase K C d z V (Spec (.of T)) q)
      (geometricDistinctSupportCard K C d z)
      (component K C d z V (Spec (.of T)) q))
    (familySplitIso K C d z V T q r E hE) p s

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricSupportAssignedSplitChart
