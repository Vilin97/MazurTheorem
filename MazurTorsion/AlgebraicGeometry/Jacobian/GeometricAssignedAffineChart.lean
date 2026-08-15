/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

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
open FiniteEtaleAssignedCoproductPower
open FiniteEtaleRelativeProduct
open FiniteGroupQuotient
open FiniteSupportEtaleCoordinates
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

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineChart
