/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates
import MazurTorsion.AlgebraicGeometry.Jacobian.RelativePowerBaseIso

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

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineChart

open AssignedProductStabilizer
open EquivariantFiniteGroupQuotient
open FiniteEtaleAssignedCoproductPower
open FiniteEtaleRelativeProduct
open FiniteGroupQuotient
open FiniteSupportEtaleCoordinates
open RelativePowerBaseIso
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
