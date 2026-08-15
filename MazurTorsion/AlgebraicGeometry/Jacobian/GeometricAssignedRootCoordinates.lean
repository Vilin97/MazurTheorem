/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricSupportAssignedSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportCoordinateMaps
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphIdeal

/-!
# Ordered-root coordinates on a geometric assigned split chart

The polynomial root variables on a split symmetric-power component live
over the ground-field section ring.  A coherent geometric-support chart
supplies their actual values: position `i` is sent to the affine-line
coordinate belonging to the distinct geometric-support member assigned to
`i`.  Because a quotient component stores an arbitrary orbit
representative, the position-to-root equivalence includes the witnessing
permutation relating that representative to the actual assigned sheet
tuple.

The resulting ring homomorphism is the base-change map from the universal
ordered-root chart to the coherent affine chart.  In particular, it sends
every universal linear graph factor to the corresponding affine-line graph
equation on the coherent base.  The named downstream consumer is the local
curve-incidence comparison in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedRootCoordinates

open FiniteEtaleCoproductPower
open FiniteSupportCoordinateMaps
open FiniteSupportEtaleCoordinates
open GeometricSupportAssignedSplitChart
open SmoothCurveEtaleCoordinate
open SplitComponentGraphIdeal
open SplitComponentUniversalRoot
open SplitFiniteBaseChange
open SplitFinitePowerPoint
open SplitFiniteSymmetricQuotient

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K))) [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
variable (V : (geometricDistinctCommonBase K C d z).left.Opens)
variable (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
variable (r : Fin (geometricDistinctSupportCard K C d z) → ℕ)
variable
  (E : ∀ j, pullback
      (restrictedPulledComponentToBase K C
        (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z)
        (geometricDistinctCharts K C d z)
        (geometricDistinctNeighborhoods K C d z) V j) q ≅
    Spec (.of (Fin (r j) → T)))
variable
  (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
    pullback.snd
      (restrictedPulledComponentToBase K C
        (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z)
        (geometricDistinctCharts K C d z)
        (geometricDistinctNeighborhoods K C d z) V j) q)
variable (p : (assignedCoproductPowerOverGround K C d z V
  (Spec (.of T)) q).left)

/-- The coherent affine base carrying all assigned root coordinates. -/
noncomputable abbrev base : Scheme.{u} :=
  coherentBase K C d z V (Spec (.of T)) q

/-- The number of distinct geometric-support family members. -/
noncomputable abbrev supportCard : ℕ :=
  geometricDistinctSupportCard K C d z

/-- The total number of sheets after splitting every support component. -/
noncomputable abbrev sheetCount : ℕ :=
  totalSheets (supportCard K C d z) r

/-- The split symmetric-power component selected by the assigned point. -/
noncomputable abbrev selectedComponent :
    splitComponentIndex d (sheetCount K C d z r) :=
  assignedSupportComponent K C d z V T q r E hE p

/-- The actual tuple of split sheets selected by the ordered positions. -/
noncomputable abbrev assignedSheetTuple :
    Fin d → Fin (sheetCount K C d z r) :=
  assignedSupportSheetTuple K C d z V T q r E hE p

/-- Reindex actual ordered positions by the root variables of the selected
component, including the orbit permutation between the actual sheet tuple
and the quotient component's stored representative. -/
noncomputable def positionEquivRootIndex :
    Fin d ≃ componentRootIndex d (sheetCount K C d z r)
      (selectedComponent K C d z V T q r E hE p) := by
  let B := base K C d z V T q
  let s := supportCard K C d z
  let m := sheetCount K C d z r
  let X := component K C d z V (Spec (.of T)) q
  let F := familySplitIso K C d z V T q r E hE
  let a := assignedSheetTuple K C d z V T q r E hE p
  let c := selectedComponent K C d z V T q r E hE p
  letI : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
    tuplePermutationAction d (Fin m)
  exact orbitAdaptedPositionEquivRootIndex d m c a
    (by
      change MulAction.orbitRel (Equiv.Perm (Fin d)) (Fin d → Fin m)
        (splitPowerPointComponent B d m (familyCoproduct B s X) F p).out
        (splitPowerPointTuple B d m (familyCoproduct B s X) F p)
      exact splitPowerPointComponent_out_orbitRel B d m
        (familyCoproduct B s X) F p)

/-- The sheet of an actual position's root variable is its exact assigned
sheet, not merely a sheet of the same multiplicity. -/
@[simp]
theorem positionEquivRootIndex_fst (i : Fin d) :
    (positionEquivRootIndex K C d z V T q r E hE p i).1 =
      assignedSheetTuple K C d z V T q r E hE p i :=
  orbitAdaptedPositionEquivRootIndex_fst _ _ _ _ _ _

/-- The affine-line coordinate on the coherent base belonging to ordered
position `i`.  Repeated positions assigned to the same geometric support
member use the same coordinate map. -/
noncomputable def baseCoordinate (i : Fin d) :
    base K C d z V T q ⟶ Spec (.of (coordinateRing K)) :=
  coherentBaseToCoordinateLine K C (supportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V (Spec (.of T)) q
    (geometricPointSupportIndex K C d z i)

/-- The global function on the coherent base obtained by pulling back the
standard affine-line variable for ordered position `i`. -/
noncomputable def rootValue (i : Fin d) : Γ(base K C d z V T q, ⊤) :=
  (baseCoordinate K C d z V T q i).appTop
    ((Scheme.ΓSpecIso (.of (coordinateRing K))).inv
      (MvPolynomial.X (0 : Fin 1)))

/-- The ground-field section ring maps to the coherent base by its structure
morphism. -/
noncomputable def groundToBase :
    Γ(Spec (.of K), ⊤) →+* Γ(base K C d z V T q, ⊤) :=
  (coherentBaseToGround K C d z V (Spec (.of T)) q).appTop.hom

/-- Evaluate the universal ordered-root polynomial coordinates on their
actual coherent-chart coordinate functions. -/
noncomputable def rootCoordinateHom :
    coefficientRing Γ(Spec (.of K), ⊤) d (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE p) →+*
      Γ(base K C d z V T q, ⊤) :=
  MvPolynomial.eval₂Hom (groundToBase K C d z V T q)
    (fun x ↦ rootValue K C d z V T q
      ((positionEquivRootIndex K C d z V T q r E hE p).symm x))

/-- Every actual position's root variable evaluates to its matching
coherent affine-line coordinate function. -/
@[simp]
theorem rootCoordinateHom_X_position (i : Fin d) :
    rootCoordinateHom K C d z V T q r E hE p
        (MvPolynomial.X
          (positionEquivRootIndex K C d z V T q r E hE p i)) =
      rootValue K C d z V T q i := by
  simp [rootCoordinateHom]

/-- Base change along the actual coherent coordinate map sends the
universal owner-sheet graph factor to the concrete linear graph equation
for that ordered position. -/
theorem rootLinearFactor_map (i : Fin d) :
    (rootLinearFactor Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE p)
        (positionEquivRootIndex K C d z V T q r E hE p i)).map
      (rootCoordinateHom K C d z V T q r E hE p) =
    Polynomial.X - Polynomial.C (rootValue K C d z V T q i) := by
  simp [rootLinearFactor]

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedRootCoordinates
