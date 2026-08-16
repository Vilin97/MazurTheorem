/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricBlockMonicChart

/-!
# Local block-monic coordinates on the selected component chart

The equivariant splitting construction selects a stable clopen neighbourhood
inside the actual occurrence-wise curve chart.  Its inclusion into the full
component chart, followed by the component quotient's blockwise Vieta map,
is invariant.  The universal property of the canonical affine local quotient
therefore produces a map from the selected neighbourhood's invariant-ring
quotient to the global block-monic coefficient space.

The defining square is retained explicitly.  The named downstream consumer
is `PointedIncidenceDescent`, which will compare the restricted ordered graph
ideal with the universal blockwise monic root ideal on this chart.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricLocalBlockMonicChart

open MazurTorsion.AlgebraicGeometry.Jacobian
open EquivariantFpqcRefinement
open FiniteGroupQuotient
open FiniteSupportEtaleCoordinates
open GeometricAssignedAffineChart
open GeometricBlockMonicChart
open SplitFiniteActionSheets
open SmoothCurveEtaleCoordinate

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)

variable {V : (commonAffineBase K C d z).left.Opens}
variable (hVs : (action K C d z).IsStableOpen V)
variable (hpre : (componentAction K C d z).IsStableOpen
  ((componentToBasePower K C d z).left ⁻¹ᵁ V))
variable {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
variable (m : ℕ)
variable (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
  Spec (.of (Fin m → T)))
variable (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
  pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)
variable (s : (componentFpqcBlockRefinement K C d z hVs q).left)
variable (j : Fin m) [IsFinite q] [Etale q]

/-- The stable clopen image of the orbit sheet in the actual component
preimage. -/
abbrev selectedTargetOpen :=
  componentFpqcBlockSelectedOrbitTargetOpen K C d z hVs hpre
    q m E hE s j

/-- Include the selected target into the full component chart and take its
blockwise monic coefficients. -/
def selectedTargetToMonicCoefficientSpace :
    (selectedTargetOpen K C d z hVs hpre q m E hE s j).toScheme ⟶
      blockMonicCoefficientSpace K C d z :=
  (selectedTargetOpen K C d z hVs hpre q m E hE s j).ι ≫
    ((componentToBasePower K C d z).left ⁻¹ᵁ V).ι ≫
      componentQuotientπ K C d z ≫
        componentQuotientToMonicCoefficientSpace K C d z

/-- The coefficient map on the selected target is invariant under its
restricted geometric support action. -/
theorem selectedTargetToMonicCoefficientSpace_invariant
    (g : geometricAssignedStabilizer K C d z) :
    ((componentPreimageAction K C d z hpre).restrict
      (componentFpqcBlockSelectedOrbitTargetOpen_isStable
        K C d z hVs hpre q m E hE s j)).hom g ≫
        selectedTargetToMonicCoefficientSpace
          K C d z hVs hpre q m E hE s j =
      selectedTargetToMonicCoefficientSpace
        K C d z hVs hpre q m E hE s j := by
  let U := selectedTargetOpen K C d z hVs hpre q m E hE s j
  let Xpre := ((componentToBasePower K C d z).left ⁻¹ᵁ V)
  have hU :
      ((componentPreimageAction K C d z hpre).restrict
        (componentFpqcBlockSelectedOrbitTargetOpen_isStable
          K C d z hVs hpre q m E hE s j)).hom g ≫ U.ι =
        U.ι ≫ (componentPreimageAction K C d z hpre).hom g :=
    selectedOrbitTargetOpen_inclusion_equivariant
      ((action K C d z).restrict hVs)
      ((componentToBasePower K C d z).left ∣_ V) q
      (componentPreimageAction K C d z hpre)
      (componentToBasePower_restrict_equivariant K C d z hVs hpre)
      m E hE s j g
  have hX :
      (componentPreimageAction K C d z hpre).hom g ≫ Xpre.ι =
        Xpre.ι ≫ (componentAction K C d z).hom g :=
    Scheme.Hom.resLE_comp_ι ((componentAction K C d z).hom g)
      (hpre.le_preimage g)
  have hπ :
      (componentAction K C d z).hom g ≫
          componentQuotientπ K C d z =
        componentQuotientπ K C d z :=
    FiniteGroupQuotient.hom_quotientπ (componentAction K C d z)
      (componentAction_hasAffineOrbit K C d z) g
  let A := ((componentPreimageAction K C d z hpre).restrict
    (componentFpqcBlockSelectedOrbitTargetOpen_isStable
      K C d z hVs hpre q m E hE s j)).hom g
  let B := (componentPreimageAction K C d z hpre).hom g
  let D := (componentAction K C d z).hom g
  let P := componentQuotientπ K C d z
  let M := componentQuotientToMonicCoefficientSpace K C d z
  change A ≫ (U.ι ≫ (Xpre.ι ≫ (P ≫ M))) = _
  calc
    A ≫ (U.ι ≫ (Xpre.ι ≫ (P ≫ M))) =
        (A ≫ U.ι) ≫ (Xpre.ι ≫ (P ≫ M)) :=
      (Category.assoc _ _ _).symm
    _ = (U.ι ≫ B) ≫ (Xpre.ι ≫ (P ≫ M)) := by
      apply congrArg (fun r ↦ r ≫ (Xpre.ι ≫ (P ≫ M)))
      exact hU
    _ = U.ι ≫ (B ≫ (Xpre.ι ≫ (P ≫ M))) :=
      Category.assoc _ _ _
    _ = U.ι ≫ ((B ≫ Xpre.ι) ≫ (P ≫ M)) := by
      apply congrArg (fun r ↦ U.ι ≫ r)
      exact (Category.assoc _ _ _).symm
    _ = U.ι ≫ ((Xpre.ι ≫ D) ≫ (P ≫ M)) := by
      apply congrArg (fun r ↦ U.ι ≫ (r ≫ (P ≫ M)))
      exact hX
    _ = U.ι ≫ (Xpre.ι ≫ (D ≫ (P ≫ M))) := by
      apply congrArg (fun r ↦ U.ι ≫ r)
      exact Category.assoc _ _ _
    _ = U.ι ≫ (Xpre.ι ≫ ((D ≫ P) ≫ M)) := by
      apply congrArg (fun r ↦ U.ι ≫ (Xpre.ι ≫ r))
      exact (Category.assoc _ _ _).symm
    _ = U.ι ≫ (Xpre.ι ≫ (P ≫ M)) := by rw [hπ]
    _ = selectedTargetToMonicCoefficientSpace
        K C d z hVs hpre q m E hE s j := rfl

/-- Projection from the selected target to its canonical affine
invariant-ring quotient. -/
def selectedTargetLocalQuotientπ
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    (selectedTargetOpen K C d z hVs hpre q m E hE s j).toScheme ⟶
      componentFpqcBlockSelectedOrbitTargetLocalQuotient
        K C d z hVs hpre q m E hE s j :=
  componentFpqcBlockSelectedOrbitTargetLocalQuotientπ
    K C d z hVs hpre q m E hE s j

/-- The selected target's canonical local quotient mapped to the global
block-monic coefficient space. -/
def selectedTargetLocalQuotientToMonicCoefficientSpace
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    componentFpqcBlockSelectedOrbitTargetLocalQuotient
        K C d z hVs hpre q m E hE s j ⟶
      blockMonicCoefficientSpace K C d z :=
  Classical.choose (FiniteGroupQuotient.existsUnique_localQuotientπ_lift
    (componentPreimageAction K C d z hpre)
    (componentFpqcBlockSelectedOrbitTargetOpen_isStable
      K C d z hVs hpre q m E hE s j)
    (componentFpqcBlockSelectedOrbitTargetOpen_isAffine
      K C d z hVs hpre q m E hE s j)
    (selectedTargetToMonicCoefficientSpace
      K C d z hVs hpre q m E hE s j)
    (selectedTargetToMonicCoefficientSpace_invariant
      K C d z hVs hpre q m E hE s j))

/-- Defining square for the local block-monic coefficient map. -/
@[reassoc]
theorem selectedTargetLocalQuotientπ_comp_monic
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    selectedTargetLocalQuotientπ K C d z hVs hpre q m E hE s j ≫
        selectedTargetLocalQuotientToMonicCoefficientSpace
          K C d z hVs hpre q m E hE s j =
      selectedTargetToMonicCoefficientSpace
        K C d z hVs hpre q m E hE s j :=
  (Classical.choose_spec
    (FiniteGroupQuotient.existsUnique_localQuotientπ_lift
      (componentPreimageAction K C d z hpre)
      (componentFpqcBlockSelectedOrbitTargetOpen_isStable
        K C d z hVs hpre q m E hE s j)
      (componentFpqcBlockSelectedOrbitTargetOpen_isAffine
        K C d z hVs hpre q m E hE s j)
      (selectedTargetToMonicCoefficientSpace
        K C d z hVs hpre q m E hE s j)
      (selectedTargetToMonicCoefficientSpace_invariant
        K C d z hVs hpre q m E hE s j))).1

/-- Projection from the selected orbit-sheet open to its finite-group
quotient. -/
def selectedSheetQuotientπ
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left] :
    (componentFpqcBlockSelectedOrbitSheetOpen K C d z hVs hpre
        q m E hE s j).toScheme ⟶
      componentFpqcBlockSelectedOrbitSheetQuotient K C d z hVs hpre
        q m E hE s j :=
  componentFpqcBlockSelectedOrbitSheetQuotientπ
    K C d z hVs hpre q m E hE s j

/-- The selected-sheet quotient mapped through the target invariant quotient
to blockwise monic coefficients. -/
def selectedSheetQuotientToMonicCoefficientSpace
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    componentFpqcBlockSelectedOrbitSheetQuotient K C d z hVs hpre
        q m E hE s j ⟶
      blockMonicCoefficientSpace K C d z :=
  componentFpqcBlockSelectedOrbitTargetLocalDescendedMap
      K C d z hVs hpre q m E hE s j ≫
    selectedTargetLocalQuotientToMonicCoefficientSpace
      K C d z hVs hpre q m E hE s j

/-- The selected-sheet quotient map to block-monic coefficients is induced
by the actual selected-sheet map into the component chart. -/
@[reassoc]
theorem selectedSheetQuotientπ_comp_monic
    [IsAffine (componentFpqcBlockRefinement K C d z hVs q).left]
    [IsAffine ((componentToBasePower K C d z).left ⁻¹ᵁ V).toScheme] :
    selectedSheetQuotientπ K C d z hVs hpre q m E hE s j ≫
        selectedSheetQuotientToMonicCoefficientSpace
          K C d z hVs hpre q m E hE s j =
      componentFpqcBlockSelectedOrbitSheetToTarget
          K C d z hVs hpre q m E hE s j ≫
        selectedTargetToMonicCoefficientSpace
          K C d z hVs hpre q m E hE s j := by
  rw [selectedSheetQuotientπ, selectedSheetQuotientToMonicCoefficientSpace,
    ← Category.assoc]
  rw [componentFpqcBlockSelectedOrbitSheetQuotientπ_comp_targetLocalDescendedMap]
  change componentFpqcBlockSelectedOrbitSheetToTarget
        K C d z hVs hpre q m E hE s j ≫
      (selectedTargetLocalQuotientπ
          K C d z hVs hpre q m E hE s j ≫
        selectedTargetLocalQuotientToMonicCoefficientSpace
          K C d z hVs hpre q m E hE s j) = _
  rw [selectedTargetLocalQuotientπ_comp_monic]

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricLocalBlockMonicChart
