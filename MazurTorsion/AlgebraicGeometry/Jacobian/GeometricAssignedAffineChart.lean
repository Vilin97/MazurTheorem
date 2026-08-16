/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteEtalePointSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFpqcRefinement
import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantSplitRefinement
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.RelativePowerBaseIso
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteActionSheets

/-!
# Affine occurrence-wise charts at a geometric divisor support

For every distinct geometric support morphism, choose one affine open in
the finite étale coordinate base containing its distinguished point.  Repeat
that same affine open for every occurrence assigned to the support member.
The resulting degree-`d` relative product is affine, has one independent
coordinate for every occurrence, and is stable under the block stabilizer
permuting equal occurrences.  Its coordinate map to ordered affine roots is
étale and equivariant, so its finite block quotient is defined.

The named downstream consumer is the local block-monic comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineChart

open AssignedProductStabilizer
open EquivariantFiniteGroupQuotient
open EquivariantFiniteEtalePointSplitChart
open EquivariantFpqcRefinement
open EquivariantSplitRefinement
open FiniteEtaleAssignedCoproductPower
open FiniteEtaleRelativeProduct
open FiniteFlatConstantRankNeighborhood
open FiniteGroupQuotient
open FiniteSupportEtaleCoordinates
open RelativePowerBaseIso
open SplitFiniteBaseChange
open SplitFiniteActionSheets
open SmoothCurveEtaleCoordinate

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)

/-- Every distinguished coordinate-base point has an affine open
neighbourhood. -/
theorem exists_baseAffineOpen
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    ∃ U : (geometricAssignedBaseFamily K C d z j).left.affineOpens,
      (geometricDistinctNeighborhoods K C d z j).basePoint ∈
        (U.1 : (geometricAssignedBaseFamily K C d z j).left.Opens) := by
  let X := (geometricAssignedBaseFamily K C d z j).left
  let x : X := (geometricDistinctNeighborhoods K C d z j).basePoint
  obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU⟩

/-- A chosen affine coordinate-base neighbourhood for each distinct
geometric support member. -/
noncomputable def baseAffineOpen
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (geometricAssignedBaseFamily K C d z j).left.affineOpens :=
  Classical.choose (exists_baseAffineOpen K C d z j)

theorem basePoint_mem_baseAffineOpen
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (geometricDistinctNeighborhoods K C d z j).basePoint ∈
      ((baseAffineOpen K C d z j).1 :
        (geometricAssignedBaseFamily K C d z j).left.Opens) :=
  Classical.choose_spec (exists_baseAffineOpen K C d z j)

/-- The affine restriction of every distinct coordinate-base family
member, still regarded over the common ground-field copy. -/
noncomputable def affineBaseFamily
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Over (coordinateBase K) :=
  Over.mk ((baseAffineOpen K C d z j).1.ι ≫
    (geometricAssignedBaseFamily K C d z j).hom)

instance affineBaseFamily_isAffine
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    IsAffine (affineBaseFamily K C d z j).left :=
  (baseAffineOpen K C d z j).2

/-- Inclusion of an affine restricted base into the original finite étale
coordinate base. -/
noncomputable def affineBaseInclusion
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineBaseFamily K C d z j ⟶ geometricAssignedBaseFamily K C d z j :=
  Over.homMk (baseAffineOpen K C d z j).1.ι rfl

instance affineBaseInclusion_isOpenImmersion
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    IsOpenImmersion (affineBaseInclusion K C d z j).left := by
  unfold affineBaseInclusion
  change IsOpenImmersion (baseAffineOpen K C d z j).1.ι
  infer_instance

/-- The affine occurrence-wise base, with the same affine restriction
repeated for every occurrence in a geometric-support block. -/
noncomputable abbrev commonAffineBase : Over (coordinateBase K) :=
  assignedProduct (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z)

instance commonAffineBase_isAffine :
    IsAffine (commonAffineBase K C d z).left := by
  apply product_isAffine (coordinateBase K)
  intro i
  exact affineBaseFamily_isAffine K C d z
    (geometricPointSupportIndex K C d z i)

/-- The distinguished point in each affine restricted base. -/
noncomputable def affineBasePoint
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (affineBaseFamily K C d z j).left :=
  ⟨(geometricDistinctNeighborhoods K C d z j).basePoint,
    basePoint_mem_baseAffineOpen K C d z j⟩

/-- The chosen affine coordinate-base open, viewed through the finite
neighbourhood's own `baseOver` presentation. -/
noncomputable def componentBaseAffineOpen
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (geometricDistinctNeighborhoods K C d z j).baseOver.left.affineOpens := by
  change (geometricAssignedBaseFamily K C d z j).left.affineOpens
  exact baseAffineOpen K C d z j

theorem basePoint_mem_componentBaseAffineOpen
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (geometricDistinctNeighborhoods K C d z j).basePoint ∈
      ((componentBaseAffineOpen K C d z j).1 :
        (geometricDistinctNeighborhoods K C d z j).baseOver.left.Opens) := by
  change (geometricDistinctNeighborhoods K C d z j).basePoint ∈
    ((baseAffineOpen K C d z j).1 :
      (geometricAssignedBaseFamily K C d z j).left.Opens)
  exact basePoint_mem_baseAffineOpen K C d z j

/-- The same affine base open packaged directly over the coordinate ground
scheme for the restricted selected component. -/
noncomputable abbrev componentAffineBaseFamily
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Over (coordinateBase K) :=
  let n := geometricDistinctNeighborhoods K C d z j
  let U := (componentBaseAffineOpen K C d z j).1
  Over.mk (U.ι ≫ n.baseOver.hom)

instance componentAffineBaseFamily_isAffine
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    IsAffine (componentAffineBaseFamily K C d z j).left :=
  (componentBaseAffineOpen K C d z j).2

/-- The selected finite curve component, restricted over the chosen affine
open in its étale coordinate base. -/
noncomputable abbrev affineComponentFamily
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Over (coordinateBase K) :=
  let n := geometricDistinctNeighborhoods K C d z j
  let U := (componentBaseAffineOpen K C d z j).1
  Over.mk ((n.componentToBase.left ⁻¹ᵁ U).ι ≫ n.componentOver.hom)

instance affineComponentFamily_isAffine
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    IsAffine (affineComponentFamily K C d z j).left := by
  let n := geometricDistinctNeighborhoods K C d z j
  letI hfinite : IsFinite n.componentToBase.left := n.selected_isFinite
  letI : IsAffineHom n.componentToBase.left := hfinite.toIsAffineHom
  exact (componentBaseAffineOpen K C d z j).2.preimage
    n.componentToBase.left

/-- The restricted selected component remains finite étale over its affine
coordinate base. -/
noncomputable def affineComponentToBase
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineComponentFamily K C d z j ⟶
      componentAffineBaseFamily K C d z j := by
  let n := geometricDistinctNeighborhoods K C d z j
  let U := (componentBaseAffineOpen K C d z j).1
  refine Over.homMk (n.componentToBase.left ∣_ U) ?_
  change (n.componentToBase.left ∣_ U) ≫ U.ι ≫ n.baseOver.hom =
    (n.componentToBase.left ⁻¹ᵁ U).ι ≫ n.componentOver.hom
  calc
    (n.componentToBase.left ∣_ U) ≫ U.ι ≫ n.baseOver.hom =
        ((n.componentToBase.left ∣_ U) ≫ U.ι) ≫ n.baseOver.hom :=
      (Category.assoc _ _ _).symm
    _ = ((n.componentToBase.left ⁻¹ᵁ U).ι ≫
          n.componentToBase.left) ≫ n.baseOver.hom := by
      rw [morphismRestrict_ι]
    _ = (n.componentToBase.left ⁻¹ᵁ U).ι ≫
        (n.componentToBase.left ≫ n.baseOver.hom) :=
      Category.assoc _ _ _
    _ = (n.componentToBase.left ⁻¹ᵁ U).ι ≫ n.componentOver.hom :=
      congrArg (fun f ↦ (n.componentToBase.left ⁻¹ᵁ U).ι ≫ f)
        n.componentToBase.w

instance affineComponentToBase_isFinite
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    IsFinite (affineComponentToBase K C d z j).left := by
  let n := geometricDistinctNeighborhoods K C d z j
  let U := (componentBaseAffineOpen K C d z j).1
  change IsFinite (n.componentToBase.left ∣_ U)
  letI : IsFinite n.componentToBase.left := n.selected_isFinite
  infer_instance

instance affineComponentToBase_etale
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (affineComponentToBase K C d z j).left := by
  let n := geometricDistinctNeighborhoods K C d z j
  let U := (componentBaseAffineOpen K C d z j).1
  change Etale (n.componentToBase.left ∣_ U)
  letI : Etale n.componentToBase.left := n.selected_etale
  infer_instance

/-- The base open used by the selected component is definitionally the same
affine base family member chosen for the occurrence chart. -/
theorem componentAffineBaseFamily_eq_affineBaseFamily
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    componentAffineBaseFamily K C d z j =
      affineBaseFamily K C d z j := by
  rfl

/-- The restricted selected component mapped to the chosen affine base
family member. -/
noncomputable def affineComponentToAffineBase
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineComponentFamily K C d z j ⟶ affineBaseFamily K C d z j :=
  affineComponentToBase K C d z j

instance affineComponentToAffineBase_isFinite
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    IsFinite (affineComponentToAffineBase K C d z j).left := by
  change IsFinite (affineComponentToBase K C d z j).left
  infer_instance

instance affineComponentToAffineBase_etale
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (affineComponentToAffineBase K C d z j).left := by
  change Etale (affineComponentToBase K C d z j).left
  infer_instance

/-- Inclusion of the restricted selected component into the original
finite-neighbourhood component. -/
noncomputable def affineComponentInclusion
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineComponentFamily K C d z j ⟶
      (geometricDistinctNeighborhoods K C d z j).componentOver :=
  Over.homMk
    ((geometricDistinctNeighborhoods K C d z j).componentToBase.left ⁻¹ᵁ
      (componentBaseAffineOpen K C d z j).1).ι rfl

instance affineComponentInclusion_isOpenImmersion
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    IsOpenImmersion (affineComponentInclusion K C d z j).left := by
  change IsOpenImmersion
    ((geometricDistinctNeighborhoods K C d z j).componentToBase.left ⁻¹ᵁ
      (componentBaseAffineOpen K C d z j).1).ι
  infer_instance

/-- The distinguished selected-component point, now regarded in the affine
restriction over its chosen base open. -/
noncomputable def affineComponentPoint
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (affineComponentFamily K C d z j).left := by
  let n := geometricDistinctNeighborhoods K C d z j
  refine ⟨n.selectedPoint, ?_⟩
  change n.componentToBase.left n.selectedPoint ∈
    (componentBaseAffineOpen K C d z j).1
  rw [n.componentToBase_selectedPoint]
  exact basePoint_mem_componentBaseAffineOpen K C d z j

@[simp]
theorem affineComponentToBase_point
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (affineComponentToBase K C d z j).left
        (affineComponentPoint K C d z j) =
      affineBasePoint K C d z j := by
  apply Subtype.ext
  change
    (((geometricDistinctNeighborhoods K C d z j).componentToBase.left ∣_
      (componentBaseAffineOpen K C d z j).1)
        (affineComponentPoint K C d z j)).1 =
      (geometricDistinctNeighborhoods K C d z j).basePoint
  rw [morphismRestrict_base_coe]
  exact (geometricDistinctNeighborhoods K C d z j).componentToBase_selectedPoint

@[simp]
theorem affineComponentToAffineBase_point
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (affineComponentToAffineBase K C d z j).left
        (affineComponentPoint K C d z j) =
      affineBasePoint K C d z j := by
  change (affineComponentToBase K C d z j).left
      (affineComponentPoint K C d z j) =
    affineBasePoint K C d z j
  exact affineComponentToBase_point K C d z j

/-- The restricted selected curve component maps back to the curve over the
coordinate copy of the ground field. -/
noncomputable def affineComponentToCurve
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineComponentFamily K C d z j ⟶
      PointChart.curveOverCoordinateBase K C.left C.hom :=
  affineComponentInclusion K C d z j ≫
    (geometricDistinctNeighborhoods K C d z j).componentToCurveOver

@[simp]
theorem affineComponentToCurve_point
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (affineComponentToCurve K C d z j).left
        (affineComponentPoint K C d z j) =
      point K C (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z) j := by
  change (geometricDistinctNeighborhoods K C d z j).componentToCurve
    (geometricDistinctNeighborhoods K C d z j).selectedPoint =
      point K C (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z) j
  exact (geometricDistinctNeighborhoods K C d z j).componentToCurve_selectedPoint

/-- Coordinate map on the selected affine curve component. -/
noncomputable def affineComponentToCoordinateLine
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineComponentFamily K C d z j ⟶ coordinateLine K :=
  affineComponentInclusion K C d z j ≫
    (geometricDistinctNeighborhoods K C d z j).componentToBase ≫
      neighborhoodBaseToCoordinateLine K C
        (geometricDistinctNeighborhoods K C d z j)

instance affineComponentToCoordinateLine_etale
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (affineComponentToCoordinateLine K C d z j).left := by
  unfold affineComponentToCoordinateLine
  change Etale ((affineComponentInclusion K C d z j).left ≫
    (geometricDistinctNeighborhoods K C d z j).componentToBase.left ≫
      (geometricDistinctNeighborhoods K C d z j).baseMap)
  apply MorphismProperty.comp_mem @Etale
  · exact HasRingHomProperty.of_isOpenImmersion
      RingHom.Etale.containsIdentities
  · apply MorphismProperty.comp_mem @Etale
    · exact (geometricDistinctNeighborhoods K C d z j).selected_etale
    · exact (geometricDistinctNeighborhoods K C d z j).baseMap_etale

/-- The actual affine occurrence-wise curve chart: repeat the selected
finite component once for every occurrence in its geometric-support block. -/
noncomputable abbrev commonAffineComponent : Over (coordinateBase K) :=
  assignedProduct (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)

instance commonAffineComponent_isAffine :
    IsAffine (commonAffineComponent K C d z).left := by
  apply product_isAffine (coordinateBase K)
  intro i
  exact affineComponentFamily_isAffine K C d z
    (geometricPointSupportIndex K C d z i)

/-- The occurrence-wise selected-component chart is finite étale over its
occurrence-wise affine coordinate-base chart. -/
noncomputable def componentToBasePower :
    commonAffineComponent K C d z ⟶ commonAffineBase K C d z :=
  assignedFamilyMap (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)
    (affineBaseFamily K C d z)
    (affineComponentToAffineBase K C d z)

instance componentToBasePower_isFinite :
    IsFinite (componentToBasePower K C d z).left := by
  unfold componentToBasePower assignedFamilyMap
  exact PermutationPower.piMap_mem (coordinateBase K) (Fin d) @IsFinite
    (fun i ↦ affineComponentToAffineBase K C d z
      (geometricPointSupportIndex K C d z i))
    (fun i ↦ affineComponentToAffineBase_isFinite K C d z
      (geometricPointSupportIndex K C d z i))

instance componentToBasePower_etale :
    Etale (componentToBasePower K C d z).left := by
  unfold componentToBasePower assignedFamilyMap
  exact PermutationPower.piMap_mem (coordinateBase K) (Fin d) @Etale
    (fun i ↦ affineComponentToAffineBase K C d z
      (geometricPointSupportIndex K C d z i))
    (fun i ↦ affineComponentToAffineBase_etale K C d z
      (geometricPointSupportIndex K C d z i))

@[reassoc]
theorem componentToBasePower_comp_projection (i : Fin d) :
    componentToBasePower K C d z ≫
        Pi.π (fun i : Fin d ↦ affineBaseFamily K C d z
          (geometricPointSupportIndex K C d z i)) i =
      Pi.π (fun i : Fin d ↦ affineComponentFamily K C d z
          (geometricPointSupportIndex K C d z i)) i ≫
        affineComponentToAffineBase K C d z
          (geometricPointSupportIndex K C d z i) := by
  exact assignedFamilyMap_comp_projection
    (coordinateBase K) (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)
    (affineBaseFamily K C d z)
    (affineComponentToAffineBase K C d z) i

/-- Product containing one affine selected component for every distinct
geometric support member. -/
noncomputable abbrev distinctAffineComponentProduct :
    Over (coordinateBase K) :=
  ∏ᶜ fun j : Fin (geometricDistinctSupportCard K C d z) ↦
    affineComponentFamily K C d z j

/-- Transport an ordered curve-power point from the original field spectrum
to the global-section presentation of that same base. -/
noncomputable def curvePowerPointOverCoordinateBase (n : ℕ)
    (p : (PermutationPower.power (Spec (.of K)) (Fin n) C).left) :
    (PermutationPower.power (coordinateBase K) (Fin n)
      (PointChart.curveOverCoordinateBase K C.left C.hom)).left :=
  powerPoint (Spec (.of K)) (coordinateBase K)
    (coordinateBaseIso K).symm C n p

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem curvePowerPointOverCoordinateBase_projection (n : ℕ)
    (p : (PermutationPower.power (Spec (.of K)) (Fin n) C).left)
    (i : Fin n) :
    (Pi.π (fun _ : Fin n ↦
      PointChart.curveOverCoordinateBase K C.left C.hom) i).left
        (curvePowerPointOverCoordinateBase K C n p) =
      (Pi.π (fun _ : Fin n ↦ C) i).left p := by
  exact powerPoint_projection (Spec (.of K)) (coordinateBase K)
    (coordinateBaseIso K).symm C n p i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Repeating the transported geometrically deduplicated tuple recovers the
transported original ordered point exactly. -/
@[simp]
theorem assignmentRepeatHom_curvePowerPointOverCoordinateBase :
    (assignmentRepeatHom (coordinateBase K)
      (geometricDistinctSupportCard K C d z) d
      (PointChart.curveOverCoordinateBase K C.left C.hom)
      (geometricPointSupportIndex K C d z)).left
        (curvePowerPointOverCoordinateBase K C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)) =
      curvePowerPointOverCoordinateBase K C d z := by
  rw [curvePowerPointOverCoordinateBase]
  change
    (assignmentRepeatHom (coordinateBase K)
      (geometricDistinctSupportCard K C d z) d
      ((Over.map (coordinateBaseIso K).symm.hom).obj C)
      (geometricPointSupportIndex K C d z)).left
        (powerPoint (Spec (.of K)) (coordinateBase K)
          (coordinateBaseIso K).symm C
          (geometricDistinctSupportCard K C d z)
          (geometricDistinctSupportOrderedPoint K C d z)) =
      powerPoint (Spec (.of K)) (coordinateBase K)
        (coordinateBaseIso K).symm C d z
  rw [assignmentRepeatHom_powerPoint]
  congr 1
  exact repeatGeometricSupportOrderedPoint K C d z

/-- The selected affine components contain a simultaneous point mapping to
the exact geometrically deduplicated curve-power point.  The finite-product
lifting theorem constructs this point through tensor products of local
rings, so its residue-field correlation is retained. -/
theorem exists_distinctAffineComponentProductPoint :
    ∃ p : (distinctAffineComponentProduct K C d z).left,
      (Limits.Pi.map (affineComponentToCurve K C d z)).left p =
          curvePowerPointOverCoordinateBase K C
            (geometricDistinctSupportCard K C d z)
            (geometricDistinctSupportOrderedPoint K C d z) ∧
        ∀ j, (Pi.π (affineComponentFamily K C d z) j).left p =
          affineComponentPoint K C d z j := by
  apply exists_fin_product_preimage (coordinateBase K)
    (geometricDistinctSupportCard K C d z)
    (fun _ : Fin (geometricDistinctSupportCard K C d z) ↦
      PointChart.curveOverCoordinateBase K C.left C.hom)
    (affineComponentFamily K C d z)
    (affineComponentToCurve K C d z)
    (curvePowerPointOverCoordinateBase K C
      (geometricDistinctSupportCard K C d z)
      (geometricDistinctSupportOrderedPoint K C d z))
    (affineComponentPoint K C d z)
  intro j
  rw [affineComponentToCurve_point,
    curvePowerPointOverCoordinateBase_projection]
  rfl

/-- A chosen simultaneous point in the product of distinct selected affine
components. -/
noncomputable def distinctAffineComponentProductPoint :
    (distinctAffineComponentProduct K C d z).left :=
  Classical.choose (exists_distinctAffineComponentProductPoint K C d z)

@[simp]
theorem distinctAffineComponentProductPoint_projection
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (Pi.π (affineComponentFamily K C d z) j).left
        (distinctAffineComponentProductPoint K C d z) =
      affineComponentPoint K C d z j :=
  (Classical.choose_spec
    (exists_distinctAffineComponentProductPoint K C d z)).2 j

/-- The chosen distinct-component point maps to the exact transported
geometric-support tuple. -/
theorem distinctAffineComponentProductPoint_mapsToCurvePower :
    (Limits.Pi.map (affineComponentToCurve K C d z)).left
        (distinctAffineComponentProductPoint K C d z) =
      curvePowerPointOverCoordinateBase K C
        (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z) :=
  (Classical.choose_spec
    (exists_distinctAffineComponentProductPoint K C d z)).1

/-- Repeat the distinct selected-component point across all ordered
occurrences. -/
noncomputable def commonAffineComponentPoint :
    (commonAffineComponent K C d z).left :=
  (productToAssignedProduct (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)).left
      (distinctAffineComponentProductPoint K C d z)

/-- The correlated occurrence-base point obtained from the exact selected-
component point.  This is the correct base point for subsequent fpqc
splitting; choosing its coordinates independently would lose residue-field
correlation. -/
noncomputable def exactCommonAffineBasePoint :
    (commonAffineBase K C d z).left :=
  (componentToBasePower K C d z).left
    (commonAffineComponentPoint K C d z)

/-- Block-stabilizer action on the actual affine curve chart. -/
noncomputable def componentAction :
    SchemeAction (geometricAssignedStabilizer K C d z)
      (commonAffineComponent K C d z).left :=
  AssignedProductStabilizer.action (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)

/-- The repeated distinct-component point is fixed by the full geometric
support block stabilizer. -/
theorem componentAction_fixed_commonAffineComponentPoint
    (g : geometricAssignedStabilizer K C d z) :
    (componentAction K C d z).hom g (commonAffineComponentPoint K C d z) =
      commonAffineComponentPoint K C d z := by
  have h := congrArg Over.Hom.left
    (productToAssignedProduct_invariant (coordinateBase K)
      (geometricDistinctSupportCard K C d z) d
      (affineComponentFamily K C d z)
      (geometricPointSupportIndex K C d z) g)
  exact congrArg
    (fun f ↦ f (distinctAffineComponentProductPoint K C d z)) h

/-- The actual affine curve chart maps equivariantly to ordered affine-root
space. -/
noncomputable def componentToCoordinatePower :
    commonAffineComponent K C d z ⟶
      PermutationPower.power (coordinateBase K) (Fin d)
        (coordinateLine K) :=
  assignedMap (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z) (coordinateLine K)
    (affineComponentToCoordinateLine K C d z)

instance componentToCoordinatePower_etale :
    Etale (componentToCoordinatePower K C d z).left := by
  unfold componentToCoordinatePower assignedMap
  exact PermutationPower.piMap_mem (coordinateBase K) (Fin d) @Etale
    (fun i ↦ affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i))
    (fun i ↦ affineComponentToCoordinateLine_etale K C d z
      (geometricPointSupportIndex K C d z i))

/-- Equivariance of the actual affine curve chart's ordered-coordinate map. -/
theorem componentToCoordinatePower_equivariant
    (g : geometricAssignedStabilizer K C d z) :
    (componentAction K C d z).hom g ≫
        (componentToCoordinatePower K C d z).left =
      (componentToCoordinatePower K C d z).left ≫
        (PermutationPower.action (coordinateBase K) (Fin d)
          (coordinateLine K)).hom g.1 :=
  assignedMap_equivariant (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z) (coordinateLine K)
    (affineComponentToCoordinateLine K C d z) g

/-- The occurrence-wise selected-component chart maps back to the ordered
curve power over the coordinate copy of the ground field. -/
noncomputable def componentToCurvePower :
    commonAffineComponent K C d z ⟶
      PermutationPower.power (coordinateBase K) (Fin d)
        (PointChart.curveOverCoordinateBase K C.left C.hom) :=
  assignedMap (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)
    (PointChart.curveOverCoordinateBase K C.left C.hom)
    (affineComponentToCurve K C d z)

/-- The distinguished point of the affine selected-component chart maps to
the exact original ordered curve-power point transported across the base
isomorphism. -/
theorem componentToCurvePower_commonAffineComponentPoint :
    (componentToCurvePower K C d z).left
        (commonAffineComponentPoint K C d z) =
      curvePowerPointOverCoordinateBase K C d z := by
  have h := congrArg Over.Hom.left
    (productToAssignedProduct_comp_assignedMap
      (coordinateBase K) (geometricDistinctSupportCard K C d z) d
      (affineComponentFamily K C d z)
      (geometricPointSupportIndex K C d z)
      (PointChart.curveOverCoordinateBase K C.left C.hom)
      (affineComponentToCurve K C d z))
  have hp := congrArg
    (fun q ↦ q (distinctAffineComponentProductPoint K C d z)) h
  change
    (componentToCurvePower K C d z).left
        (commonAffineComponentPoint K C d z) =
      (assignmentRepeatHom (coordinateBase K)
        (geometricDistinctSupportCard K C d z) d
        (PointChart.curveOverCoordinateBase K C.left C.hom)
        (geometricPointSupportIndex K C d z)).left
          ((Limits.Pi.map (affineComponentToCurve K C d z)).left
            (distinctAffineComponentProductPoint K C d z)) at hp
  rw [distinctAffineComponentProductPoint_mapsToCurvePower,
    assignmentRepeatHom_curvePowerPointOverCoordinateBase] at hp
  exact hp

/-- The map from the occurrence-wise selected-component chart to the curve
power is equivariant. -/
theorem componentToCurvePower_equivariant
    (g : geometricAssignedStabilizer K C d z) :
    (componentAction K C d z).hom g ≫
        (componentToCurvePower K C d z).left =
      (componentToCurvePower K C d z).left ≫
        (PermutationPower.action (coordinateBase K) (Fin d)
          (PointChart.curveOverCoordinateBase K C.left C.hom)).hom g.1 :=
  assignedMap_equivariant (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)
    (PointChart.curveOverCoordinateBase K C.left C.hom)
    (affineComponentToCurve K C d z) g

/-- The product of one affine base for every distinct geometric support
member. -/
noncomputable abbrev distinctAffineBaseProduct : Over (coordinateBase K) :=
  ∏ᶜ fun j : Fin (geometricDistinctSupportCard K C d z) ↦
    affineBaseFamily K C d z j

/-- The distinct affine bases contain a simultaneous point with the chosen
value in every factor. -/
theorem exists_distinctAffineBaseProductPoint :
    ∃ p : (distinctAffineBaseProduct K C d z).left,
      ∀ j, (Pi.π (affineBaseFamily K C d z) j).left p =
        affineBasePoint K C d z j := by
  exact exists_fin_product_point (coordinateBase K)
    (geometricDistinctSupportCard K C d z)
    (affineBaseFamily K C d z) (affineBasePoint K C d z)

/-- A chosen simultaneous point in the product of the distinct affine
bases. -/
noncomputable def distinctAffineBaseProductPoint :
    (distinctAffineBaseProduct K C d z).left :=
  Classical.choose (exists_distinctAffineBaseProductPoint K C d z)

@[simp]
theorem distinctAffineBaseProductPoint_projection
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    (Pi.π (affineBaseFamily K C d z) j).left
        (distinctAffineBaseProductPoint K C d z) =
      affineBasePoint K C d z j :=
  Classical.choose_spec (exists_distinctAffineBaseProductPoint K C d z) j

/-- Repeat the distinct-support point across all ordered occurrences.  This
retains the common residue-field correlation by construction. -/
noncomputable def commonAffineBasePoint :
    (commonAffineBase K C d z).left :=
  (productToAssignedProduct (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z)).left
      (distinctAffineBaseProductPoint K C d z)

/-- The block-stabilizer action on the affine occurrence-wise base. -/
noncomputable def action :
    SchemeAction (geometricAssignedStabilizer K C d z)
      (commonAffineBase K C d z).left :=
  AssignedProductStabilizer.action (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z)

/-- The finite étale map from selected curve components to their coordinate
bases is equivariant for the common block stabilizer. -/
theorem componentToBasePower_equivariant
    (g : geometricAssignedStabilizer K C d z) :
    (componentAction K C d z).hom g ≫
        (componentToBasePower K C d z).left =
      (componentToBasePower K C d z).left ≫ (action K C d z).hom g :=
  assignedFamilyMap_equivariant (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z)
    (affineBaseFamily K C d z)
    (affineComponentToAffineBase K C d z) g

/-- The correlated base point is fixed by the same block stabilizer. -/
theorem action_fixed_exactCommonAffineBasePoint
    (g : geometricAssignedStabilizer K C d z) :
    (action K C d z).hom g (exactCommonAffineBasePoint K C d z) =
      exactCommonAffineBasePoint K C d z := by
  have h := componentToBasePower_equivariant K C d z g
  have hp := congrArg
    (fun q ↦ q (commonAffineComponentPoint K C d z)) h
  change
    (componentToBasePower K C d z).left
        ((componentAction K C d z).hom g
          (commonAffineComponentPoint K C d z)) =
      (action K C d z).hom g (exactCommonAffineBasePoint K C d z) at hp
  rw [componentAction_fixed_commonAffineComponentPoint] at hp
  exact hp.symm

/-- The constant-rank locus through the correlated occurrence-base point is
stable under the block stabilizer. -/
theorem componentToBasePower_rankOpen_isStable :
    (action K C d z).IsStableOpen
      (rankOpen (componentToBasePower K C d z).left
        (exactCommonAffineBasePoint K C d z)) :=
  rankOpen_isStable (componentAction K C d z) (action K C d z)
    (componentToBasePower K C d z).left
    (componentToBasePower_equivariant K C d z)
    (exactCommonAffineBasePoint K C d z)

/-- Around the exact correlated occurrence-base point, the equivariant
finite étale selected-component product admits a block-stable affine
constant-rank neighborhood, with a block-stable source preimage, and an
fpqc cover on which it is a finite disjoint union of sheets. -/
theorem exists_componentToBasePower_affineOpen_fpqc_splitCover :
    ∃ (V : (commonAffineBase K C d z).left.Opens)
        (hV : IsAffineOpen V),
      (action K C d z).IsStableOpen V ∧
      (componentAction K C d z).IsStableOpen
        ((componentToBasePower K C d z).left ⁻¹ᵁ V) ∧
      exactCommonAffineBasePoint K C d z ∈ V ∧
      let f := (componentToBasePower K C d z).left
      let fV := f ∣_ V
      letI : IsAffine V.toScheme := hV
      letI : IsAffine (f ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom fV
      letI : Algebra Γ(V, ⊤) Γ(f ⁻¹ᵁ V, ⊤) := fV.appTop.hom.toAlgebra
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra Γ(V, ⊤) T)
        (_ : Module.FaithfullyFlat Γ(V, ⊤) T)
        (_ : Module.Finite Γ(V, ⊤) T)
        (_ : Algebra.Etale Γ(V, ⊤) T) (m : ℕ)
        (_e : T ⊗[Γ(V, ⊤)] Γ(f ⁻¹ᵁ V, ⊤) ≃ₐ[T] (Fin m → T))
        (q : Spec (.of T) ⟶ V.toScheme)
        (_E : pullback fV q ≅ Spec (.of (Fin m → T))),
        _E.hom ≫ EtaleSplitChart.splitProjection T m =
            pullback.snd fV q ∧
          m = f.finrank (exactCommonAffineBasePoint K C d z) ∧
            Flat q ∧ Surjective q ∧ QuasiCompact q :=
  exists_stableAffineOpen_fpqc_splitCover
    (componentAction K C d z) (action K C d z)
    (componentToBasePower K C d z).left
    (componentToBasePower_equivariant K C d z)
    (exactCommonAffineBasePoint K C d z)
    (action_fixed_exactCommonAffineBasePoint K C d z)

/-- The common refinement of all block translates of an fpqc cover of a
stable occurrence-base open. -/
noncomputable abbrev componentFpqcBlockRefinement
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {Z : Scheme.{u}} (q : Z ⟶ V.toScheme) : Over V.toScheme :=
  EquivariantFpqcRefinement.refinement
    ((action K C d z).restrict hVs) q

/-- The block-translate refinement remains affine, finite étale, and fpqc.
It is therefore a valid common refinement on which to transport the split
sheet presentation. -/
theorem componentFpqcBlockRefinement_isAffine_finiteEtale_fpqc
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {Z : Scheme.{u}} (q : Z ⟶ V.toScheme)
    [IsAffine V.toScheme] [IsAffine Z]
    [IsFinite q] [Etale q] [Surjective q] :
    IsAffine (componentFpqcBlockRefinement K C d z hVs q).left ∧
      IsFinite (componentFpqcBlockRefinement K C d z hVs q).hom ∧
      Etale (componentFpqcBlockRefinement K C d z hVs q).hom ∧
      Flat (componentFpqcBlockRefinement K C d z hVs q).hom ∧
      Surjective (componentFpqcBlockRefinement K C d z hVs q).hom ∧
      QuasiCompact (componentFpqcBlockRefinement K C d z hVs q).hom :=
  refinement_isAffine_finiteEtale_fpqc
    ((action K C d z).restrict hVs) q

/-- Every point of the stable base open, in particular the exact correlated
occurrence-base point, has a lift to the common block-translate refinement.
The lift need not itself be fixed by the block action. -/
theorem exists_componentFpqcBlockRefinementPoint_over_exact
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    {Z : Scheme.{u}} (q : Z ⟶ V.toScheme) [Surjective q] :
    ∃ s : (componentFpqcBlockRefinement K C d z hVs q).left,
      (componentFpqcBlockRefinement K C d z hVs q).hom s =
        ⟨exactCommonAffineBasePoint K C d z, hmem⟩ :=
  (inferInstance : Surjective
    (componentFpqcBlockRefinement K C d z hVs q).hom).1
      ⟨exactCommonAffineBasePoint K C d z, hmem⟩

/-- The exact correlated point, regarded as a point of a stable open, is
fixed by the restricted block action. -/
theorem restrictedAction_fixed_exactCommonAffineBasePoint
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (g : geometricAssignedStabilizer K C d z) :
    ((action K C d z).restrict hVs).hom g
        ⟨exactCommonAffineBasePoint K C d z, hmem⟩ =
      ⟨exactCommonAffineBasePoint K C d z, hmem⟩ := by
  apply Subtype.ext
  have hres := congrArg
    (fun f ↦ f ⟨exactCommonAffineBasePoint K C d z, hmem⟩)
    (Scheme.Hom.resLE_comp_ι ((action K C d z).hom g)
      (hVs.le_preimage g))
  change
    V.ι (((action K C d z).restrict hVs).hom g
      ⟨exactCommonAffineBasePoint K C d z, hmem⟩) =
      (action K C d z).hom g (exactCommonAffineBasePoint K C d z) at hres
  rw [action_fixed_exactCommonAffineBasePoint K C d z g] at hres
  exact hres

/-- Although a chosen lift of the exact point need not be fixed, its whole
block orbit in the common refinement remains above that exact point. -/
theorem componentFpqcBlockRefinement_orbit_maps_to_exact
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    {Z : Scheme.{u}} (q : Z ⟶ V.toScheme)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (hs : (componentFpqcBlockRefinement K C d z hVs q).hom s =
      ⟨exactCommonAffineBasePoint K C d z, hmem⟩)
    (g : geometricAssignedStabilizer K C d z) :
    (componentFpqcBlockRefinement K C d z hVs q).hom
        ((EquivariantFpqcRefinement.refinementAction
          ((action K C d z).restrict hVs) q).hom g s) =
      ⟨exactCommonAffineBasePoint K C d z, hmem⟩ := by
  have hcover := congrArg
    (fun f ↦ f s)
    (EquivariantFpqcRefinement.rawActionHom_comp_cover
      ((action K C d z).restrict hVs) q g)
  change
    (componentFpqcBlockRefinement K C d z hVs q).hom
        ((EquivariantFpqcRefinement.refinementAction
          ((action K C d z).restrict hVs) q).hom g s) =
      ((action K C d z).restrict hVs).hom g
        ((componentFpqcBlockRefinement K C d z hVs q).hom s) at hcover
  rw [hs, restrictedAction_fixed_exactCommonAffineBasePoint K C d z
    hVs hmem g] at hcover
  exact hcover

/-- The identity translate maps the block refinement back to the original
fpqc cover over the stable base open. -/
theorem componentFpqcBlockRefinement_projection_one_comp_cover
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {Z : Scheme.{u}} (q : Z ⟶ V.toScheme) :
    EquivariantFpqcRefinement.projection
          ((action K C d z).restrict hVs) q 1 ≫ q =
      (componentFpqcBlockRefinement K C d z hVs q).hom :=
  EquivariantFpqcRefinement.projection_one_comp_cover
    ((action K C d z).restrict hVs) q

/-- The factor-translation maps on the common refinement cover the
restricted block action on the stable base open. -/
theorem componentFpqcBlockRefinement_actionMap_comp_cover
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {Z : Scheme.{u}} (q : Z ⟶ V.toScheme)
    (g : geometricAssignedStabilizer K C d z) :
    EquivariantFpqcRefinement.rawActionHom
          ((action K C d z).restrict hVs) q g ≫
        (componentFpqcBlockRefinement K C d z hVs q).hom =
      (componentFpqcBlockRefinement K C d z hVs q).hom ≫
        ((action K C d z).restrict hVs).hom g :=
  EquivariantFpqcRefinement.rawActionHom_comp_cover
    ((action K C d z).restrict hVs) q g

/-- The selected-component source, first pulled to an fpqc splitting cover
and then to its common block-translate refinement. -/
noncomputable abbrev componentFpqcBlockSplitSource
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme) :
    Over (componentFpqcBlockRefinement K C d z hVs q).left :=
  EquivariantSplitRefinement.splitSource
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q

/-- The original split presentation transports to the common block
refinement through its identity-indexed projection. -/
noncomputable def componentFpqcBlockSplitIso
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q) :
    componentFpqcBlockSplitSource K C d z hVs q ≅
      splitFinite (componentFpqcBlockRefinement K C d z hVs q).left m :=
  EquivariantSplitRefinement.splitIso
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q m E hE

/-- The exact selected-component point, regarded as a point of the preimage
of any occurrence-base open containing its correlated image. -/
noncomputable def commonAffineComponentPointInPreimage
    {V : (commonAffineBase K C d z).left.Opens}
    (hmem : exactCommonAffineBasePoint K C d z ∈ V) :
    ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme :=
  ⟨commonAffineComponentPoint K C d z, hmem⟩

/-- In the direct pullback presentation used to transport the block action,
the split source maps canonically back to the selected-component preimage. -/
noncomputable def componentFpqcBlockSplitToComponentPreimage
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q) :
    (splitFinite
      (componentFpqcBlockRefinement K C d z hVs q).left m).left ⟶
        ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme :=
  (EquivariantSplitRefinement.directSplitIso
      ((action K C d z).restrict hVs)
      ((componentToBasePower K C d z).left ∣_ V) q m E hE).inv.left ≫
    pullback.fst ((componentToBasePower K C d z).left ∣_ V)
      (EquivariantFpqcRefinement.projection
        ((action K C d z).restrict hVs) q 1 ≫ q)

/-- Every chosen refinement lift of the exact correlated base point selects
an actual sheet mapping to the exact selected-component point. -/
theorem exists_componentFpqcBlockSheet_over_exact
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (hs : (componentFpqcBlockRefinement K C d z hVs q).hom s =
      ⟨exactCommonAffineBasePoint K C d z, hmem⟩) :
    ∃ j : Fin m,
      componentFpqcBlockSplitToComponentPreimage K C d z hVs q m E hE
          (sheetPoint (componentFpqcBlockRefinement K C d z hVs q).left
            m j s) =
        commonAffineComponentPointInPreimage K C d z hmem := by
  apply EquivariantSplitRefinement.exists_splitSheet_over_point
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q m E hE
      (commonAffineComponentPointInPreimage K C d z hmem) s
  calc
    ((componentToBasePower K C d z).left ∣_ V)
        (commonAffineComponentPointInPreimage K C d z hmem) =
        ⟨exactCommonAffineBasePoint K C d z, hmem⟩ := by
      apply Subtype.ext
      have hr := congrArg
        (fun f ↦ f (commonAffineComponentPointInPreimage K C d z hmem))
        (morphismRestrict_ι (componentToBasePower K C d z).left V)
      change
        V.ι (((componentToBasePower K C d z).left ∣_ V)
          (commonAffineComponentPointInPreimage K C d z hmem)) =
        (componentToBasePower K C d z).left
          (commonAffineComponentPoint K C d z) at hr
      exact hr
    _ = (componentFpqcBlockRefinement K C d z hVs q).hom s := hs.symm

/-- The transported split source maps back to the restricted selected
component product. -/
noncomputable def componentFpqcBlockSplitSourceToComponentPreimage
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme) :
    (componentFpqcBlockSplitSource K C d z hVs q).left ⟶
      ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme :=
  EquivariantSplitRefinement.splitSourceToOriginal
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q

/-- The map from the transported split source to the selected-component
preimage lies over the common block-refinement cover. -/
@[reassoc]
theorem componentFpqcBlockSplitSourceToComponentPreimage_comp
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme) :
    componentFpqcBlockSplitSourceToComponentPreimage K C d z hVs q ≫
        ((componentToBasePower K C d z).left ∣_ V) =
      (componentFpqcBlockSplitSource K C d z hVs q).hom ≫
        (componentFpqcBlockRefinement K C d z hVs q).hom :=
  EquivariantSplitRefinement.splitSourceToOriginal_comp
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q

/-- Restrict the selected-component block action to the preimage of a
stable occurrence-base open. -/
noncomputable def componentPreimageAction
    {V : (commonAffineBase K C d z).left.Opens}
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V)) :
    SchemeAction (geometricAssignedStabilizer K C d z)
      ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme :=
  (componentAction K C d z).restrict hpre

/-- Restriction to a stable base open and its stable source preimage
preserves equivariance of the selected-component morphism. -/
theorem componentToBasePower_restrict_equivariant
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    (g : geometricAssignedStabilizer K C d z) :
    (componentPreimageAction K C d z hpre).hom g ≫
        ((componentToBasePower K C d z).left ∣_ V) =
      ((componentToBasePower K C d z).left ∣_ V) ≫
        ((action K C d z).restrict hVs).hom g :=
  EquivariantSplitRefinement.restrictPreimage_equivariant
    (action K C d z) (componentToBasePower K C d z).left
    (componentAction K C d z)
    (componentToBasePower_equivariant K C d z) hVs hpre g

/-- The split finite source over the common block refinement carries the
transported block action. -/
noncomputable def componentFpqcBlockSplitAction
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q) :
    SchemeAction (geometricAssignedStabilizer K C d z)
      (splitFinite
        (componentFpqcBlockRefinement K C d z hVs q).left m).left :=
  EquivariantSplitRefinement.splitAction
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE

/-- The transported block action on the split finite source covers the
genuine block action on the common fpqc refinement. -/
theorem componentFpqcBlockSplitAction_equivariant
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (g : geometricAssignedStabilizer K C d z) :
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE).hom g ≫
        (splitFinite
          (componentFpqcBlockRefinement K C d z hVs q).left m).hom =
      (splitFinite
          (componentFpqcBlockRefinement K C d z hVs q).left m).hom ≫
        (EquivariantFpqcRefinement.refinementAction
          ((action K C d z).restrict hVs) q).hom g :=
  EquivariantSplitRefinement.splitAction_equivariant
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE g

/-- The exact selected-component point is fixed by the restricted component
action on the preimage of a stable base open. -/
theorem componentPreimageAction_fixed_commonAffineComponentPoint
    {V : (commonAffineBase K C d z).left.Opens}
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    (g : geometricAssignedStabilizer K C d z) :
    (componentPreimageAction K C d z hpre).hom g
        (commonAffineComponentPointInPreimage K C d z hmem) =
      commonAffineComponentPointInPreimage K C d z hmem := by
  apply Subtype.ext
  have hres := congrArg
    (fun f ↦ f (commonAffineComponentPointInPreimage K C d z hmem))
    (Scheme.Hom.resLE_comp_ι ((componentAction K C d z).hom g)
      (hpre.le_preimage g))
  change
    ((componentToBasePower K C d z).left ⁻¹ᵁ V).ι
        ((componentPreimageAction K C d z hpre).hom g
          (commonAffineComponentPointInPreimage K C d z hmem)) =
      (componentAction K C d z).hom g
        (commonAffineComponentPoint K C d z) at hres
  rw [componentAction_fixed_commonAffineComponentPoint K C d z g] at hres
  exact hres

/-- The sheet label reached by the transported block action above a point
of the common fpqc refinement. -/
noncomputable def componentFpqcBlockSheetTransition
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (g : geometricAssignedStabilizer K C d z)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) : Fin m :=
  sheetTransition
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE) g s j

/-- The block-induced sheet labels satisfy the transition cocycle law over
translated points of the common fpqc refinement. -/
theorem componentFpqcBlockSheetTransition_mul
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (g h : geometricAssignedStabilizer K C d z)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) :
    componentFpqcBlockSheetTransition K C d z hVs hpre q m E hE
        (g * h) s j =
      componentFpqcBlockSheetTransition K C d z hVs hpre q m E hE h
        ((EquivariantFpqcRefinement.refinementAction
          ((action K C d z).restrict hVs) q).hom g s)
        (componentFpqcBlockSheetTransition K C d z hVs hpre q m E hE
          g s j) :=
  SplitFiniteActionSheets.sheetTransition_mul
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q)
    (componentFpqcBlockSplitAction_equivariant K C d z hVs hpre
      q m E hE) g h s j

/-- At a fixed refinement point, every block element induces a permutation
of the split sheet labels. -/
noncomputable def componentFpqcBlockFixedSheetPerm
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (hs : ∀ g : geometricAssignedStabilizer K C d z,
      (EquivariantFpqcRefinement.refinementAction
        ((action K C d z).restrict hVs) q).hom g s = s)
    (g : geometricAssignedStabilizer K C d z) : Equiv.Perm (Fin m) :=
  fixedSheetPerm (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q)
    (componentFpqcBlockSplitAction_equivariant K C d z hVs hpre
      q m E hE) s hs g

/-- The stable clopen locus cut out by all transition signatures occurring
along the orbit of an arbitrary lift in the common refinement. -/
noncomputable abbrev componentFpqcBlockOrbitTransitionOpen
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left) :
    (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
  orbitTransitionOpen
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q) s

/-- The orbit-transition locus of any refinement lift is stable under the
transported block action. -/
theorem componentFpqcBlockOrbitTransitionOpen_isStable
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left) :
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q).IsStableOpen
        (componentFpqcBlockOrbitTransitionOpen K C d z hVs hpre
          q m E hE s) :=
  orbitTransitionOpen_isStable
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q)
    (componentFpqcBlockSplitAction_equivariant K C d z hVs hpre
      q m E hE) s

/-- The stable clopen union of the split source sheets reached from one
selected sheet along an arbitrary refinement orbit. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitSheetOpen
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) :
    (splitFinite
      (componentFpqcBlockRefinement K C d z hVs q).left m).left.Opens :=
  selectedOrbitSheetOpen
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q) s j

/-- The selected orbit-sheet open is stable under the transported block
action on the split source. -/
theorem componentFpqcBlockSelectedOrbitSheetOpen_isStable
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) :
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE).IsStableOpen
      (componentFpqcBlockSelectedOrbitSheetOpen K C d z hVs hpre
        q m E hE s j) :=
  selectedOrbitSheetOpen_isStable
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q)
    (componentFpqcBlockSplitAction_equivariant K C d z hVs hpre
      q m E hE) s j

/-- The clopen image of the selected orbit sheet inside the actual
selected-component preimage. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitTargetOpen
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q] :
    ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme.Opens :=
  selectedOrbitTargetOpen
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The selected-sheet image in the actual component chart is stable under
the restricted geometric block action. -/
theorem componentFpqcBlockSelectedOrbitTargetOpen_isStable
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q] :
    (componentPreimageAction K C d z hpre).IsStableOpen
      (componentFpqcBlockSelectedOrbitTargetOpen K C d z hVs hpre
        q m E hE s j) :=
  selectedOrbitTargetOpen_isStable
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The selected orbit sheet mapped onto its actual stable component-chart
image. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitSheetToTarget
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q] :
    (componentFpqcBlockSelectedOrbitSheetOpen K C d z hVs hpre
      q m E hE s j).toScheme ⟶
    (componentFpqcBlockSelectedOrbitTargetOpen K C d z hVs hpre
      q m E hE s j).toScheme :=
  selectedOrbitSheetToTargetOpen
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- On the actual Jacobian occurrence chart, the selected orbit sheet is a
surjective finite étale cover of its stable clopen image. -/
theorem componentFpqcBlockSelectedOrbitSheetToTarget_properties
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q] :
    Function.Surjective
        (componentFpqcBlockSelectedOrbitSheetToTarget K C d z hVs hpre
          q m E hE s j) ∧
      IsFinite
        (componentFpqcBlockSelectedOrbitSheetToTarget K C d z hVs hpre
          q m E hE s j) ∧
      Etale
        (componentFpqcBlockSelectedOrbitSheetToTarget K C d z hVs hpre
          q m E hE s j) := by
  refine ⟨selectedOrbitSheetToTargetOpen_surjective
      ((action K C d z).restrict hVs)
      ((componentToBasePower K C d z).left ∣_ V) q
      (componentPreimageAction K C d z hpre)
      (componentToBasePower_restrict_equivariant K C d z hVs hpre)
      m E hE s j, ?_⟩
  exact selectedOrbitSheetToTargetOpen_isFinite_etale
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- When the actual component preimage is affine, its clopen selected-sheet
image is an affine open. -/
theorem componentFpqcBlockSelectedOrbitTargetOpen_isAffine
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    IsAffineOpen
      (componentFpqcBlockSelectedOrbitTargetOpen K C d z hVs hpre
        q m E hE s j) :=
  selectedOrbitTargetOpen_isAffine
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- A sheet selected by the exact lifting theorem gives a stable clopen
target neighbourhood containing the actual selected-component point. -/
theorem commonAffineComponentPointInPreimage_mem_selectedOrbitTargetOpen
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    (hmem : exactCommonAffineBasePoint K C d z ∈ V)
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q]
    (hj : componentFpqcBlockSplitToComponentPreimage
        K C d z hVs q m E hE
          (sheetPoint (componentFpqcBlockRefinement K C d z hVs q).left
            m j s) =
      commonAffineComponentPointInPreimage K C d z hmem) :
    commonAffineComponentPointInPreimage K C d z hmem ∈
      componentFpqcBlockSelectedOrbitTargetOpen K C d z hVs hpre
        q m E hE s j := by
  have hsheet :
      sheetPoint (componentFpqcBlockRefinement K C d z hVs q).left
          m j s ∈
        componentFpqcBlockSelectedOrbitSheetOpen K C d z hVs hpre
          q m E hE s j := by
    have h := orbit_sheetPoint_mem_selectedOrbitSheetSet
      (componentFpqcBlockRefinement K C d z hVs q).left m
      (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
      (EquivariantFpqcRefinement.refinementAction
        ((action K C d z).restrict hVs) q) s j 1
    rw [sheetTransition_one
      (componentFpqcBlockRefinement K C d z hVs q).left m
      (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
      (EquivariantFpqcRefinement.refinementAction
        ((action K C d z).restrict hVs) q)
      (componentFpqcBlockSplitAction_equivariant
        K C d z hVs hpre q m E hE),
      (EquivariantFpqcRefinement.refinementAction
        ((action K C d z).restrict hVs) q).hom_one] at h
    rw [show (𝟙 (componentFpqcBlockRefinement K C d z hVs q).left)
      s = s from ConcreteCategory.id_apply s] at h
    exact h
  let y :
      (componentFpqcBlockSelectedOrbitSheetOpen K C d z hVs hpre
        q m E hE s j).toScheme :=
    ⟨sheetPoint (componentFpqcBlockRefinement K C d z hVs q).left
      m j s, hsheet⟩
  have hy := selectedOrbitSheetToOriginal_mem_targetOpen
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j y
  have hymap :
      selectedOrbitSheetToOriginal
        ((action K C d z).restrict hVs)
        ((componentToBasePower K C d z).left ∣_ V) q
        (componentPreimageAction K C d z hpre)
        (componentToBasePower_restrict_equivariant K C d z hVs hpre)
        m E hE s j y =
      commonAffineComponentPointInPreimage K C d z hmem := by
    exact hj
  rwa [hymap] at hy

/-- The finite-group quotient of the selected orbit-sheet source in the
actual occurrence chart. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitSheetQuotient
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m)
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left] :
    Scheme.{u} :=
  selectedOrbitSheetQuotient
    (componentFpqcBlockRefinement K C d z hVs q).left m
    (componentFpqcBlockSplitAction K C d z hVs hpre q m E hE)
    (EquivariantFpqcRefinement.refinementAction
      ((action K C d z).restrict hVs) q)
    (componentFpqcBlockSplitAction_equivariant
      K C d z hVs hpre q m E hE) s j

/-- The finite-group quotient of the actual stable clopen target
neighbourhood selected by a refinement sheet. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitTargetQuotient
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    Scheme.{u} :=
  selectedOrbitTargetQuotient
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The local finite-group quotient map induced from the selected-sheet
cover of its actual target neighbourhood. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitTargetDescendedMap
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q]
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    componentFpqcBlockSelectedOrbitSheetQuotient K C d z hVs hpre
        q m E hE s j ⟶
      componentFpqcBlockSelectedOrbitTargetQuotient K C d z hVs hpre
        q m E hE s j :=
  selectedOrbitSheetTargetDescendedMap
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The local quotient map produced by the selected-sheet construction is
surjective. -/
theorem componentFpqcBlockSelectedOrbitTargetDescendedMap_surjective
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q]
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    Function.Surjective
      (componentFpqcBlockSelectedOrbitTargetDescendedMap
        K C d z hVs hpre q m E hE s j) :=
  selectedOrbitSheetTargetDescendedMap_surjective
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The canonical invariant-ring quotient `Spec Γ(U)ᴳ` of the actual stable
clopen target neighbourhood. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitTargetLocalQuotient
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q] : Scheme.{u} :=
  selectedOrbitTargetLocalQuotient
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The selected-sheet quotient mapped to the canonical invariant-ring
quotient of its actual target neighbourhood. -/
noncomputable abbrev componentFpqcBlockSelectedOrbitTargetLocalDescendedMap
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q]
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    componentFpqcBlockSelectedOrbitSheetQuotient K C d z hVs hpre
        q m E hE s j ⟶
      componentFpqcBlockSelectedOrbitTargetLocalQuotient K C d z hVs hpre
        q m E hE s j :=
  selectedOrbitSheetTargetLocalDescendedMap
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The map to the actual target-neighbourhood invariant ring is
surjective. -/
theorem componentFpqcBlockSelectedOrbitTargetLocalDescendedMap_surjective
    {V : (commonAffineBase K C d z).left.Opens}
    (hVs : (action K C d z).IsStableOpen V)
    (hpre : (componentAction K C d z).IsStableOpen
      ((componentToBasePower K C d z).left ⁻¹ᵁ V))
    {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
    (m : ℕ)
    (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
      Spec (.of (Fin m → T)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
      pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
    (s : (componentFpqcBlockRefinement K C d z hVs q).left)
    (j : Fin m) [IsFinite q] [Etale q]
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    Function.Surjective
      (componentFpqcBlockSelectedOrbitTargetLocalDescendedMap
        K C d z hVs hpre q m E hE s j) :=
  selectedOrbitSheetTargetLocalDescendedMap_surjective
    ((action K C d z).restrict hVs)
    ((componentToBasePower K C d z).left ∣_ V) q
    (componentPreimageAction K C d z hpre)
    (componentToBasePower_restrict_equivariant K C d z hVs hpre)
    m E hE s j

/-- The central occurrence-wise point is fixed by the entire geometric
support block stabilizer. -/
theorem action_fixed_commonAffineBasePoint
    (g : geometricAssignedStabilizer K C d z) :
    (action K C d z).hom g (commonAffineBasePoint K C d z) =
      commonAffineBasePoint K C d z := by
  have h := congrArg Over.Hom.left
    (productToAssignedProduct_invariant (coordinateBase K)
      (geometricDistinctSupportCard K C d z) d
      (affineBaseFamily K C d z)
      (geometricPointSupportIndex K C d z) g)
  exact congrArg
    (fun f ↦ f (distinctAffineBaseProductPoint K C d z)) h

/-- The affine occurrence-wise base maps into the unrestricted occurrence
base coordinatewise. -/
noncomputable def inclusion :
    commonAffineBase K C d z ⟶ geometricAssignedCommonBase K C d z :=
  assignedFamilyMap (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z)
    (geometricAssignedBaseFamily K C d z)
    (affineBaseInclusion K C d z)

/-- The affine-base inclusion is equivariant for the block action. -/
theorem inclusion_equivariant
    (g : geometricAssignedStabilizer K C d z) :
    (action K C d z).hom g ≫ (inclusion K C d z).left =
      (inclusion K C d z).left ≫
        (geometricAssignedCommonBaseAction K C d z).hom g :=
  assignedFamilyMap_equivariant (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z)
    (geometricAssignedBaseFamily K C d z)
    (affineBaseInclusion K C d z) g

/-- The affine restricted coordinate map for every distinct support
member. -/
noncomputable def affineBaseToCoordinateLine
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineBaseFamily K C d z j ⟶ coordinateLine K :=
  affineBaseInclusion K C d z j ≫
    geometricAssignedBaseMapFamily K C d z j

/-- The selected component's coordinate map factors through its chosen
affine coordinate-base open. -/
@[reassoc]
theorem affineComponentToAffineBase_comp_affineBaseToCoordinateLine
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    affineComponentToAffineBase K C d z j ≫
        affineBaseToCoordinateLine K C d z j =
      affineComponentToCoordinateLine K C d z j := by
  apply Over.OverMorphism.ext
  change (affineComponentToBase K C d z j).left ≫
      (affineBaseInclusion K C d z j).left ≫
        (geometricAssignedBaseMapFamily K C d z j).left =
    (affineComponentToCoordinateLine K C d z j).left
  change (affineComponentToBase K C d z j).left ≫
      (affineBaseInclusion K C d z j).left ≫
        (geometricDistinctNeighborhoods K C d z j).baseMap =
    (affineComponentInclusion K C d z j).left ≫
      (geometricDistinctNeighborhoods K C d z j).componentToBase.left ≫
        (geometricDistinctNeighborhoods K C d z j).baseMap
  have h := morphismRestrict_ι
    (geometricDistinctNeighborhoods K C d z j).componentToBase.left
    (componentBaseAffineOpen K C d z j).1
  exact congrArg
    (fun q ↦ q ≫ (geometricDistinctNeighborhoods K C d z j).baseMap) h

instance affineBaseToCoordinateLine_etale
    (j : Fin (geometricDistinctSupportCard K C d z)) :
    Etale (affineBaseToCoordinateLine K C d z j).left := by
  unfold affineBaseToCoordinateLine
  change Etale ((affineBaseInclusion K C d z j).left ≫
    (geometricAssignedBaseMapFamily K C d z j).left)
  apply MorphismProperty.comp_mem @Etale
  · exact HasRingHomProperty.of_isOpenImmersion
      RingHom.Etale.containsIdentities
  · unfold geometricAssignedBaseMapFamily
    exact neighborhoodBaseToCoordinateLine_etale K C
      (geometricDistinctNeighborhoods K C d z j)

/-- The affine occurrence-wise base maps étale to the ordered affine-root
space. -/
noncomputable def toCoordinatePower :
    commonAffineBase K C d z ⟶
      PermutationPower.power (coordinateBase K) (Fin d)
        (coordinateLine K) :=
  assignedMap (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z) (coordinateLine K)
    (affineBaseToCoordinateLine K C d z)

@[reassoc]
theorem toCoordinatePower_comp_projection (i : Fin d) :
    toCoordinatePower K C d z ≫
        Pi.π (fun _ : Fin d ↦ coordinateLine K) i =
      Pi.π (fun i : Fin d ↦ affineBaseFamily K C d z
          (geometricPointSupportIndex K C d z i)) i ≫
        affineBaseToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i) := by
  exact assignedMap_comp_projection
    (coordinateBase K) (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z) (coordinateLine K)
    (affineBaseToCoordinateLine K C d z) i

@[reassoc]
theorem componentToCoordinatePower_comp_projection (i : Fin d) :
    componentToCoordinatePower K C d z ≫
        Pi.π (fun _ : Fin d ↦ coordinateLine K) i =
      Pi.π (fun i : Fin d ↦ affineComponentFamily K C d z
          (geometricPointSupportIndex K C d z i)) i ≫
        affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i) := by
  exact assignedMap_comp_projection
    (coordinateBase K) (geometricDistinctSupportCard K C d z) d
    (affineComponentFamily K C d z)
    (geometricPointSupportIndex K C d z) (coordinateLine K)
    (affineComponentToCoordinateLine K C d z) i

/-- The occurrence-wise selected-component coordinate map factors through
the finite étale occurrence-wise base map. -/
@[reassoc]
theorem componentToBasePower_comp_toCoordinatePower :
    componentToBasePower K C d z ≫ toCoordinatePower K C d z =
      componentToCoordinatePower K C d z := by
  apply Pi.hom_ext
  intro i
  calc
    (componentToBasePower K C d z ≫ toCoordinatePower K C d z) ≫
        Pi.π (fun _ : Fin d ↦ coordinateLine K) i =
      componentToBasePower K C d z ≫
        (toCoordinatePower K C d z ≫
          Pi.π (fun _ : Fin d ↦ coordinateLine K) i) :=
      Category.assoc _ _ _
    _ = componentToBasePower K C d z ≫
        (Pi.π (fun i : Fin d ↦ affineBaseFamily K C d z
            (geometricPointSupportIndex K C d z i)) i ≫
          affineBaseToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)) := by
      rw [toCoordinatePower_comp_projection]
    _ = (componentToBasePower K C d z ≫
          Pi.π (fun i : Fin d ↦ affineBaseFamily K C d z
            (geometricPointSupportIndex K C d z i)) i) ≫
        affineBaseToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i) :=
      (Category.assoc _ _ _).symm
    _ = (Pi.π (fun i : Fin d ↦ affineComponentFamily K C d z
            (geometricPointSupportIndex K C d z i)) i ≫
          affineComponentToAffineBase K C d z
            (geometricPointSupportIndex K C d z i)) ≫
        affineBaseToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i) := by
      rw [componentToBasePower_comp_projection]
    _ = Pi.π (fun i : Fin d ↦ affineComponentFamily K C d z
          (geometricPointSupportIndex K C d z i)) i ≫
        (affineComponentToAffineBase K C d z
            (geometricPointSupportIndex K C d z i) ≫
          affineBaseToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)) :=
      Category.assoc _ _ _
    _ = Pi.π (fun i : Fin d ↦ affineComponentFamily K C d z
          (geometricPointSupportIndex K C d z i)) i ≫
        affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i) := by
      rw [affineComponentToAffineBase_comp_affineBaseToCoordinateLine]
    _ = componentToCoordinatePower K C d z ≫
        Pi.π (fun _ : Fin d ↦ coordinateLine K) i :=
      (componentToCoordinatePower_comp_projection K C d z i).symm

instance toCoordinatePower_etale :
    Etale (toCoordinatePower K C d z).left := by
  unfold toCoordinatePower assignedMap
  exact PermutationPower.piMap_mem (coordinateBase K) (Fin d) @Etale
    (fun i ↦ affineBaseToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i))
    (fun i ↦ affineBaseToCoordinateLine_etale K C d z
      (geometricPointSupportIndex K C d z i))

/-- The affine coordinate map is equivariant for the geometric-support
block stabilizer. -/
theorem toCoordinatePower_equivariant
    (g : geometricAssignedStabilizer K C d z) :
    (action K C d z).hom g ≫ (toCoordinatePower K C d z).left =
      (toCoordinatePower K C d z).left ≫
        (PermutationPower.action (coordinateBase K) (Fin d)
          (coordinateLine K)).hom g.1 :=
  assignedMap_equivariant (coordinateBase K)
    (geometricDistinctSupportCard K C d z) d
    (affineBaseFamily K C d z)
    (geometricPointSupportIndex K C d z) (coordinateLine K)
    (affineBaseToCoordinateLine K C d z) g

/-- The block action on the affine occurrence chart has affine orbit
neighbourhoods (the whole affine chart suffices). -/
theorem action_hasAffineOrbit : HasAffineOrbit (action K C d z) := by
  intro x
  refine ⟨⊤, isAffineOpen_top _, ?_⟩
  intro g
  exact Set.mem_univ _

instance commonAffineBase_diagonal_isAffine :
    IsAffineHom (pullback.diagonal
      (terminal.from (commonAffineBase K C d z).left)) := by
  infer_instance

/-- The finite block quotient of the occurrence-wise affine étale chart. -/
noncomputable def quotient : Scheme.{u} :=
  FiniteGroupQuotient.quotient (action K C d z)
    (action_hasAffineOrbit K C d z)

/-- Projection from the occurrence-wise affine chart to its block
quotient. -/
noncomputable def quotientπ :
    (commonAffineBase K C d z).left ⟶ quotient K C d z :=
  FiniteGroupQuotient.quotientπ (action K C d z)
    (action_hasAffineOrbit K C d z)

instance quotientπ_surjective : Surjective (quotientπ K C d z) :=
  FiniteGroupQuotient.quotientπ_surjectiveProperty (action K C d z)
    (action_hasAffineOrbit K C d z)

/-- The block action on the actual affine selected-component chart has
affine orbit neighbourhoods. -/
theorem componentAction_hasAffineOrbit :
    HasAffineOrbit (componentAction K C d z) := by
  intro x
  refine ⟨⊤, isAffineOpen_top _, ?_⟩
  intro g
  exact Set.mem_univ _

instance commonAffineComponent_diagonal_isAffine :
    IsAffineHom (pullback.diagonal
      (terminal.from (commonAffineComponent K C d z).left)) := by
  infer_instance

/-- Finite block quotient of the actual affine selected-component curve
chart. -/
noncomputable def componentQuotient : Scheme.{u} :=
  FiniteGroupQuotient.quotient (componentAction K C d z)
    (componentAction_hasAffineOrbit K C d z)

/-- Projection from the actual affine selected-component curve chart to its
block quotient. -/
noncomputable def componentQuotientπ :
    (commonAffineComponent K C d z).left ⟶
      componentQuotient K C d z :=
  FiniteGroupQuotient.quotientπ (componentAction K C d z)
    (componentAction_hasAffineOrbit K C d z)

instance componentQuotientπ_surjective :
    Surjective (componentQuotientπ K C d z) :=
  FiniteGroupQuotient.quotientπ_surjectiveProperty
    (componentAction K C d z) (componentAction_hasAffineOrbit K C d z)

/-- The finite étale map from the selected-component chart to its affine
coordinate base descends to the corresponding block quotients. -/
noncomputable def componentQuotientToBaseQuotient :
    componentQuotient K C d z ⟶ quotient K C d z :=
  EquivariantFiniteGroupQuotient.descendedMap (componentAction K C d z)
    (action K C d z) (componentAction_hasAffineOrbit K C d z)
    (action_hasAffineOrbit K C d z) (componentToBasePower K C d z).left
    (componentToBasePower_equivariant K C d z)

/-- Defining square for the finite étale component-to-base map on block
quotients. -/
@[reassoc]
theorem componentQuotientπ_comp_componentQuotientToBaseQuotient :
    componentQuotientπ K C d z ≫
        componentQuotientToBaseQuotient K C d z =
      (componentToBasePower K C d z).left ≫ quotientπ K C d z :=
  EquivariantFiniteGroupQuotient.quotientπ_comp_descendedMap
    (componentAction K C d z) (action K C d z)
    (componentAction_hasAffineOrbit K C d z)
    (action_hasAffineOrbit K C d z) (componentToBasePower K C d z).left
    (componentToBasePower_equivariant K C d z)

/-- The descended component-to-base quotient map carries the exact central
component point to the quotient of its correlated base point. -/
theorem componentQuotientToBaseQuotient_apply_centralPoint :
    componentQuotientToBaseQuotient K C d z
        (componentQuotientπ K C d z
          (commonAffineComponentPoint K C d z)) =
      quotientπ K C d z (exactCommonAffineBasePoint K C d z) :=
  EquivariantFiniteGroupQuotient.descendedMap_apply_quotientPoint
    (componentAction K C d z) (action K C d z)
    (componentAction_hasAffineOrbit K C d z)
    (action_hasAffineOrbit K C d z) (componentToBasePower K C d z).left
    (componentToBasePower_equivariant K C d z)
    (commonAffineComponentPoint K C d z)

/-- Ordered affine-root space carrying the restricted action of the
geometric-support block stabilizer. -/
noncomputable abbrev coordinatePower : Scheme.{u} :=
  (PermutationPower.power (coordinateBase K) (Fin d)
    (coordinateLine K)).left

instance coordinatePower_isAffine :
    IsAffine (coordinatePower K d) := by
  apply product_isAffine (coordinateBase K)
  intro _
  change IsAffine (Spec (.of (coordinateRing K)))
  infer_instance

/-- Restrict coordinate permutations on ordered affine roots to the exact
block stabilizer of the geometric support assignment. -/
noncomputable def coordinateAction :
    SchemeAction (geometricAssignedStabilizer K C d z)
      (coordinatePower K d) where
  hom g := (PermutationPower.action (coordinateBase K) (Fin d)
    (coordinateLine K)).hom g.1
  hom_one := by
    simpa using (PermutationPower.action (coordinateBase K) (Fin d)
      (coordinateLine K)).hom_one
  hom_mul g h := by
    simpa using (PermutationPower.action (coordinateBase K) (Fin d)
      (coordinateLine K)).hom_mul g.1 h.1

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The whole ordered affine-root space is an affine orbit neighbourhood for
the restricted block action. -/
theorem coordinateAction_hasAffineOrbit :
    HasAffineOrbit (coordinateAction K C d z) := by
  intro x
  refine ⟨⊤, isAffineOpen_top _, ?_⟩
  intro g
  exact Set.mem_univ _

instance coordinatePower_diagonal_isAffine :
    IsAffineHom (pullback.diagonal
      (terminal.from (coordinatePower K d))) := by
  infer_instance

/-- The quotient of ordered affine roots by the geometric-support block
stabilizer. -/
noncomputable def coordinateQuotient : Scheme.{u} :=
  FiniteGroupQuotient.quotient (coordinateAction K C d z)
    (coordinateAction_hasAffineOrbit K C d z)

/-- Projection from ordered affine roots to their block quotient. -/
noncomputable def coordinateQuotientπ :
    coordinatePower K d ⟶ coordinateQuotient K C d z :=
  FiniteGroupQuotient.quotientπ (coordinateAction K C d z)
    (coordinateAction_hasAffineOrbit K C d z)

/-- The equivariant étale coordinate map descends canonically to the two
finite block quotients. -/
noncomputable def quotientToCoordinateQuotient :
    quotient K C d z ⟶ coordinateQuotient K C d z :=
  EquivariantFiniteGroupQuotient.descendedMap (action K C d z)
    (coordinateAction K C d z) (action_hasAffineOrbit K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (toCoordinatePower K C d z).left
    (toCoordinatePower_equivariant K C d z)

/-- Defining square for the occurrence-chart map on block quotients. -/
@[reassoc]
theorem quotientπ_comp_quotientToCoordinateQuotient :
    quotientπ K C d z ≫ quotientToCoordinateQuotient K C d z =
      (toCoordinatePower K C d z).left ≫
        coordinateQuotientπ K C d z :=
  EquivariantFiniteGroupQuotient.quotientπ_comp_descendedMap
    (action K C d z) (coordinateAction K C d z)
    (action_hasAffineOrbit K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (toCoordinatePower K C d z).left
    (toCoordinatePower_equivariant K C d z)

/-- The quotient coordinate map sends the central divisor point to the
quotient of its ordered affine-coordinate tuple. -/
theorem quotientToCoordinateQuotient_apply_centralPoint :
    quotientToCoordinateQuotient K C d z
        (quotientπ K C d z (commonAffineBasePoint K C d z)) =
      coordinateQuotientπ K C d z
        ((toCoordinatePower K C d z).left
          (commonAffineBasePoint K C d z)) :=
  EquivariantFiniteGroupQuotient.descendedMap_apply_quotientPoint
    (action K C d z) (coordinateAction K C d z)
    (action_hasAffineOrbit K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (toCoordinatePower K C d z).left
    (toCoordinatePower_equivariant K C d z)
    (commonAffineBasePoint K C d z)

/-- The quotient coordinate map at the correlated base point attached to the
exact selected-component point. -/
theorem quotientToCoordinateQuotient_apply_exactCentralPoint :
    quotientToCoordinateQuotient K C d z
        (quotientπ K C d z (exactCommonAffineBasePoint K C d z)) =
      coordinateQuotientπ K C d z
        ((toCoordinatePower K C d z).left
          (exactCommonAffineBasePoint K C d z)) :=
  EquivariantFiniteGroupQuotient.descendedMap_apply_quotientPoint
    (action K C d z) (coordinateAction K C d z)
    (action_hasAffineOrbit K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (toCoordinatePower K C d z).left
    (toCoordinatePower_equivariant K C d z)
    (exactCommonAffineBasePoint K C d z)

/-- The equivariant étale map from the actual selected-component curve chart
descends to its block quotient. -/
noncomputable def componentQuotientToCoordinateQuotient :
    componentQuotient K C d z ⟶ coordinateQuotient K C d z :=
  EquivariantFiniteGroupQuotient.descendedMap (componentAction K C d z)
    (coordinateAction K C d z) (componentAction_hasAffineOrbit K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (componentToCoordinatePower K C d z).left
    (componentToCoordinatePower_equivariant K C d z)

/-- Defining square for the actual selected-component curve chart on finite
block quotients. -/
@[reassoc]
theorem componentQuotientπ_comp_componentQuotientToCoordinateQuotient :
    componentQuotientπ K C d z ≫
        componentQuotientToCoordinateQuotient K C d z =
      (componentToCoordinatePower K C d z).left ≫
        coordinateQuotientπ K C d z :=
  EquivariantFiniteGroupQuotient.quotientπ_comp_descendedMap
    (componentAction K C d z) (coordinateAction K C d z)
    (componentAction_hasAffineOrbit K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (componentToCoordinatePower K C d z).left
    (componentToCoordinatePower_equivariant K C d z)

/-- The coordinate morphism on the selected-component quotient factors
through its affine-base quotient. -/
@[reassoc]
theorem componentQuotientToBaseQuotient_comp_quotientToCoordinateQuotient :
    componentQuotientToBaseQuotient K C d z ≫
        quotientToCoordinateQuotient K C d z =
      componentQuotientToCoordinateQuotient K C d z := by
  letI : Epi (componentQuotientπ K C d z) :=
    FiniteGroupQuotient.epi_quotientπ (componentAction K C d z)
      (componentAction_hasAffineOrbit K C d z)
  apply (cancel_epi (componentQuotientπ K C d z)).mp
  calc
    componentQuotientπ K C d z ≫
          (componentQuotientToBaseQuotient K C d z ≫
            quotientToCoordinateQuotient K C d z) =
        (componentQuotientπ K C d z ≫
          componentQuotientToBaseQuotient K C d z) ≫
            quotientToCoordinateQuotient K C d z :=
      (Category.assoc _ _ _).symm
    _ = ((componentToBasePower K C d z).left ≫
          quotientπ K C d z) ≫
            quotientToCoordinateQuotient K C d z := by
      rw [componentQuotientπ_comp_componentQuotientToBaseQuotient]
    _ = (componentToBasePower K C d z).left ≫
        (quotientπ K C d z ≫ quotientToCoordinateQuotient K C d z) :=
      Category.assoc _ _ _
    _ = (componentToBasePower K C d z).left ≫
        ((toCoordinatePower K C d z).left ≫
          coordinateQuotientπ K C d z) := by
      rw [quotientπ_comp_quotientToCoordinateQuotient]
    _ = ((componentToBasePower K C d z).left ≫
          (toCoordinatePower K C d z).left) ≫
        coordinateQuotientπ K C d z :=
      (Category.assoc _ _ _).symm
    _ = (componentToCoordinatePower K C d z).left ≫
        coordinateQuotientπ K C d z := by
      have h := congrArg Over.Hom.left
        (componentToBasePower_comp_toCoordinatePower K C d z)
      change (componentToBasePower K C d z).left ≫
          (toCoordinatePower K C d z).left =
        (componentToCoordinatePower K C d z).left at h
      exact congrArg (fun q ↦ q ≫ coordinateQuotientπ K C d z) h
    _ = componentQuotientπ K C d z ≫
        componentQuotientToCoordinateQuotient K C d z :=
      (componentQuotientπ_comp_componentQuotientToCoordinateQuotient
        K C d z).symm

/-- The actual quotient coordinate map carries the repeated
selected-component point to the quotient of its ordered affine coordinates. -/
theorem componentQuotientToCoordinateQuotient_apply_centralPoint :
    componentQuotientToCoordinateQuotient K C d z
        (componentQuotientπ K C d z
          (commonAffineComponentPoint K C d z)) =
      coordinateQuotientπ K C d z
        ((componentToCoordinatePower K C d z).left
          (commonAffineComponentPoint K C d z)) :=
  EquivariantFiniteGroupQuotient.descendedMap_apply_quotientPoint
    (componentAction K C d z) (coordinateAction K C d z)
    (componentAction_hasAffineOrbit K C d z)
    (coordinateAction_hasAffineOrbit K C d z)
    (componentToCoordinatePower K C d z).left
    (componentToCoordinatePower_equivariant K C d z)
    (commonAffineComponentPoint K C d z)

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineChart
