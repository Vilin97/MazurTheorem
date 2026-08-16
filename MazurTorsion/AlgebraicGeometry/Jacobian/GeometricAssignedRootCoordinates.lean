/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricSupportAssignedSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportCoordinateMaps
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphBaseChange

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

The resulting ring homomorphism specializes the universal ordered-root chart
at the coherent support coordinates.  In particular, it sends every
universal linear graph factor to the corresponding affine-line graph equation
on the coherent base.  This is a pointwise compatibility check, not the final
dimension-preserving neighbourhood of the symmetric power: that neighbourhood
must retain independent root variables for repeated occurrences.  The named
downstream consumer is the local curve-incidence comparison in
`PointedIncidenceDescent`.
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
open SplitComponentGraphBaseChange
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

/-- An assigned component-product point, inserted into the unrestricted
power of the support-family coproduct.  This insertion forces position `i`
to use the geometric-support member assigned to `i`. -/
noncomputable def productPoint
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) :
    (assignedCoproductPowerOverGround K C d z V
      (Spec (.of T)) q).left :=
  (assignedProductToCoproductPower K C d z V (Spec (.of T)) q).left w

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

/-- For a point inserted from the assigned component product, the sheet of
the root variable at position `i` belongs to the genuine geometric-support
member assigned to `i`. -/
theorem positionRootOwner_productPoint
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    splitFamilySheetOwner (base K C d z V T q)
        (supportCard K C d z) r
        (positionEquivRootIndex K C d z V T q r E hE
          (productPoint K C d z V T q w) i).1 =
      geometricPointSupportIndex K C d z i := by
  rw [positionEquivRootIndex_fst]
  exact assignedSupportSheetOwner_productPoint K C d z V T q r E hE w i

/-- The local label, inside the correct geometric-support family member, of
the split sheet selected by ordered position `i`. -/
noncomputable def positionLocalSheet
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    Fin (r (geometricPointSupportIndex K C d z i)) := by
  rw [← positionRootOwner_productPoint K C d z V T q r E hE w i]
  exact splitFamilySheetLocalIndex (base K C d z V T q)
    (supportCard K C d z) r
    (positionEquivRootIndex K C d z V T q r E hE
      (productPoint K C d z V T q w) i).1

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

/-- Map the actual split sheet selected by ordered position `i` back to the
affine curve chart of its assigned geometric-support member. -/
noncomputable def rootSheetToChart
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    base K C d z V T q ⟶
      (((geometricDistinctCharts K C d z)
        (geometricPointSupportIndex K C d z i)).V : C.left.Opens).toScheme :=
  coherentSplitSheetToChart K C (supportCard K C d z)
    (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V (Spec (.of T)) q
    (geometricPointSupportIndex K C d z i)
    (r (geometricPointSupportIndex K C d z i))
    (componentSplitIso K C d z V T q r E hE
      (geometricPointSupportIndex K C d z i))
    (positionLocalSheet K C d z V T q r E hE w i)

/-- The selected curve sheet has exactly the affine-line coordinate used to
evaluate the corresponding universal root variable. -/
theorem rootSheetToChart_comp_schemeMap
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    rootSheetToChart K C d z V T q r E hE w i ≫
        ((geometricDistinctCharts K C d z)
          (geometricPointSupportIndex K C d z i)).schemeMap =
      baseCoordinate K C d z V T q i := by
  exact coherentSplitSheetToChart_comp_schemeMap K C
    (supportCard K C d z) (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V (Spec (.of T)) q
    (geometricPointSupportIndex K C d z i)
    (r (geometricPointSupportIndex K C d z i))
    (componentSplitIso K C d z V T q r E hE
      (geometricPointSupportIndex K C d z i))
    (positionLocalSheet K C d z V T q r E hE w i)

/-- In the equal-coordinate pullback of the assigned curve chart, the
actual root sheet is the first open-and-closed graph summand. -/
theorem rootSheet_exists_graphCoproduct
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    let B := base K C d z V T q
    let f := ((geometricDistinctCharts K C d z)
      (geometricPointSupportIndex K C d z i)).schemeMap
    let coordinate := baseCoordinate K C d z V T q i
    let sheet := rootSheetToChart K C d z V T q r E hE w i
    let graph : B ⟶ pullback f coordinate :=
      pullback.lift sheet (𝟙 B) (by
        simpa only [Category.id_comp] using
          rootSheetToChart_comp_schemeMap K C d z V T q r E hE w i)
    ∃ (W : Scheme.{u}) (G : pullback f coordinate ≅ B ⨿ W),
      graph ≫ G.hom = coprod.inl := by
  dsimp only
  exact coherentSplitSheet_exists_graphCoproduct K C
    (supportCard K C d z) (geometricDistinctSupportOrderedPoint K C d z)
    (geometricDistinctCharts K C d z)
    (geometricDistinctNeighborhoods K C d z) V (Spec (.of T)) q
    (geometricPointSupportIndex K C d z i)
    (r (geometricPointSupportIndex K C d z i))
    (componentSplitIso K C d z V T q r E hE
      (geometricPointSupportIndex K C d z i))
    (positionLocalSheet K C d z V T q r E hE w i)

/-- The ground-field section ring maps to the coherent base by its structure
morphism. -/
noncomputable def groundToBase :
    Γ(Spec (.of K), ⊤) →+* Γ(base K C d z V T q, ⊤) :=
  (coherentBaseToGround K C d z V (Spec (.of T)) q).appTop.hom

/-- Specialize the universal ordered-root polynomial coordinates at their
actual coherent-support coordinate functions. -/
noncomputable def rootCoordinateHom
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) :
    coefficientRing Γ(Spec (.of K), ⊤) d (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w)) →+*
      Γ(base K C d z V T q, ⊤) :=
  MvPolynomial.eval₂Hom (groundToBase K C d z V T q)
    (fun x ↦ rootValue K C d z V T q
      ((positionEquivRootIndex K C d z V T q r E hE
        (productPoint K C d z V T q w)).symm x))

/-- Every actual position's root variable evaluates to its matching
coherent affine-line coordinate function. -/
@[simp]
theorem rootCoordinateHom_X_position
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    rootCoordinateHom K C d z V T q r E hE w
        (MvPolynomial.X
          (positionEquivRootIndex K C d z V T q r E hE
            (productPoint K C d z V T q w) i)) =
      rootValue K C d z V T q i := by
  simp [rootCoordinateHom]

/-- Specialization along the actual coherent coordinate map sends the
universal owner-sheet graph factor to the concrete linear graph equation for
that ordered position. -/
theorem rootLinearFactor_map
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    (rootLinearFactor Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        (positionEquivRootIndex K C d z V T q r E hE
          (productPoint K C d z V T q w) i)).map
      (rootCoordinateHom K C d z V T q r E hE w) =
    Polynomial.X - Polynomial.C (rootValue K C d z V T q i) := by
  simp [rootLinearFactor]

/-- The sheetwise affine-line ambient algebra after evaluating all universal
root coordinates on the coherent base. -/
abbrev evaluatedOrderedAmbientAlgebra :=
  ∀ _ : Fin (sheetCount K C d z r),
    Polynomial Γ(base K C d z V T q, ⊤)

/-- The concrete graph ideal for ordered position `i` on sheet `j`: its
linear coordinate equation on the actual owner sheet, and the unit ideal on
every other sheet. -/
noncomputable def evaluatedRootGraphIdealOnSheet
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d)
    (j : Fin (sheetCount K C d z r)) :
    Ideal (Polynomial Γ(base K C d z V T q, ⊤)) :=
  if (positionEquivRootIndex K C d z V T q r E hE
      (productPoint K C d z V T q w) i).1 = j then
    Ideal.span {Polynomial.X - Polynomial.C (rootValue K C d z V T q i)}
  else ⊤

/-- The concrete owner-sheet graph ideal as an ideal in the product of all
sheetwise affine-line coordinate rings. -/
noncomputable def evaluatedRootGraphIdeal
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    Ideal (evaluatedOrderedAmbientAlgebra K C d z V T q r) :=
  Ideal.pi (evaluatedRootGraphIdealOnSheet K C d z V T q r E hE w i)

/-- Select the actual owner sheet and evaluate its affine-line coordinate
at the coherent root function for position `i`. -/
noncomputable def evaluatedRootGraphEvaluation
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    evaluatedOrderedAmbientAlgebra K C d z V T q r →+*
      Γ(base K C d z V T q, ⊤) :=
  (Polynomial.evalRingHom (rootValue K C d z V T q i)).comp
    (Pi.evalRingHom
      (fun _ : Fin (sheetCount K C d z r) ↦
        Polynomial Γ(base K C d z V T q, ⊤))
      (positionEquivRootIndex K C d z V T q r E hE
        (productPoint K C d z V T q w) i).1)

/-- The evaluated graph map has exactly the concrete owner-sheet graph
ideal as its kernel. -/
theorem evaluatedRootGraphEvaluation_ker
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    RingHom.ker (evaluatedRootGraphEvaluation K C d z V T q r E hE w i) =
      evaluatedRootGraphIdeal K C d z V T q r E hE w i := by
  ext f
  let x := positionEquivRootIndex K C d z V T q r E hE
    (productPoint K C d z V T q w) i
  let a := rootValue K C d z V T q i
  change Polynomial.evalRingHom a (f x.1) = 0 ↔
    ∀ j, f j ∈ if x.1 = j then
      Ideal.span {Polynomial.X - Polynomial.C a} else ⊤
  constructor
  · intro h j
    by_cases hj : x.1 = j
    · subst j
      simpa only [if_pos, ← Polynomial.ker_evalRingHom,
        RingHom.mem_ker] using h
    · simp [hj]
  · intro h
    have hx := h x.1
    simpa only [if_pos, ← Polynomial.ker_evalRingHom,
      RingHom.mem_ker] using hx

/-- Map every sheetwise universal affine-line polynomial to the evaluated
coherent-base polynomial with the same sheet label. -/
noncomputable def orderedAmbientCoordinateHom
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) :
    orderedAmbientAlgebra Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w)) →+*
      evaluatedOrderedAmbientAlgebra K C d z V T q r :=
  orderedAmbientBaseChangeHom Γ(Spec (.of K), ⊤) d
    (sheetCount K C d z r)
    (selectedComponent K C d z V T q r E hE
      (productPoint K C d z V T q w))
    Γ(base K C d z V T q, ⊤)
    (rootCoordinateHom K C d z V T q r E hE w)

/-- Evaluation of a universal owner-sheet graph commutes pointwise with the
actual coherent-coordinate specialization. -/
theorem evaluatedRootGraphEvaluation_orderedAmbientCoordinateHom
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d)
    (f : orderedAmbientAlgebra Γ(Spec (.of K), ⊤) d
      (sheetCount K C d z r)
      (selectedComponent K C d z V T q r E hE
        (productPoint K C d z V T q w))) :
    evaluatedRootGraphEvaluation K C d z V T q r E hE w i
        (orderedAmbientCoordinateHom K C d z V T q r E hE w f) =
      rootCoordinateHom K C d z V T q r E hE w
        (rootGraphEvaluation Γ(Spec (.of K), ⊤) d
          (sheetCount K C d z r)
          (selectedComponent K C d z V T q r E hE
            (productPoint K C d z V T q w))
          (positionEquivRootIndex K C d z V T q r E hE
            (productPoint K C d z V T q w) i) f) := by
  simp only [evaluatedRootGraphEvaluation, orderedAmbientCoordinateHom,
    orderedAmbientBaseChangeHom, rootGraphEvaluation, RingHom.comp_apply,
    Pi.evalRingHom_apply,
    RingHom.pi_apply, Polynomial.coe_mapRingHom,
    Polynomial.coe_evalRingHom, positionEquivRootIndex_fst]
  rw [Polynomial.eval_map]
  rw [← Polynomial.eval_map_apply]
  rw [rootCoordinateHom_X_position]
  exact (Polynomial.eval_map
    (rootCoordinateHom K C d z V T q r E hE w)
    (rootValue K C d z V T q i)).symm

/-- The product of all concrete owner-sheet graph ideals after evaluating
the universal root variables on the coherent support base.  The product is
still indexed by ordered occurrences, so repeated coordinates retain their
scheme-theoretic multiplicities. -/
noncomputable def evaluatedOrderedGraphIdeal
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) :
    Ideal (evaluatedOrderedAmbientAlgebra K C d z V T q r) :=
  ∏ i : Fin d, evaluatedRootGraphIdeal K C d z V T q r E hE w i

/-- Componentwise change of root coordinates sends one universal graph
ideal to the corresponding concrete owner-sheet graph ideal. -/
theorem orderedAmbientCoordinateHom_map_rootGraphIdeal
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) (i : Fin d) :
    Ideal.map (orderedAmbientCoordinateHom K C d z V T q r E hE w)
      (rootGraphIdeal Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        (positionEquivRootIndex K C d z V T q r E hE
          (productPoint K C d z V T q w) i)) =
      evaluatedRootGraphIdeal K C d z V T q r E hE w i := by
  apply (Ideal.piOrderIso
    (R := fun _ : Fin (sheetCount K C d z r) ↦
      Polynomial Γ(base K C d z V T q, ⊤))).injective
  funext j
  change Ideal.map (Pi.evalRingHom _ j)
      (Ideal.map (orderedAmbientCoordinateHom K C d z V T q r E hE w)
        (rootGraphIdeal Γ(Spec (.of K), ⊤) d
          (sheetCount K C d z r)
          (selectedComponent K C d z V T q r E hE
            (productPoint K C d z V T q w))
          (positionEquivRootIndex K C d z V T q r E hE
            (productPoint K C d z V T q w) i))) =
    Ideal.map (Pi.evalRingHom _ j)
      (evaluatedRootGraphIdeal K C d z V T q r E hE w i)
  rw [Ideal.map_map]
  change Ideal.map
      ((Polynomial.mapRingHom
        (rootCoordinateHom K C d z V T q r E hE w)).comp
          (Pi.evalRingHom
            (fun _ : Fin (sheetCount K C d z r) ↦
              Polynomial (coefficientRing Γ(Spec (.of K), ⊤) d
                (sheetCount K C d z r)
                (selectedComponent K C d z V T q r E hE
                  (productPoint K C d z V T q w)))) j))
      (rootGraphIdeal Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        (positionEquivRootIndex K C d z V T q r E hE
          (productPoint K C d z V T q w) i)) = _
  unfold rootGraphIdeal evaluatedRootGraphIdeal
  rw [Ideal.map_evalRingHom_pi]
  rw [← Ideal.map_map, Ideal.map_evalRingHom_pi]
  unfold rootGraphIdealOnSheet evaluatedRootGraphIdealOnSheet
  split_ifs with h
  · rw [Ideal.map_span]
    simp only [Set.image_singleton]
    congr 2
    exact rootLinearFactor_map K C d z V T q r E hE w i
  · exact Ideal.map_top _

private theorem ideal_map_fintype_prod {A D ι : Type*}
    [CommRing A] [CommRing D] [Fintype ι]
    (f : A →+* D) (I : ι → Ideal A) :
    Ideal.map f (∏ i, I i) = ∏ i, Ideal.map f (I i) := by
  let φ : Ideal A →* Ideal D :=
    { toFun := Ideal.map f
      map_one' := by
        simpa only [Ideal.one_eq_top] using Ideal.map_top f
      map_mul' := fun J L ↦ Ideal.map_mul f J L }
  change φ (∏ i, I i) = ∏ i, φ (I i)
  exact map_prod φ I Finset.univ

/-- Specializing all universal root coordinates sends the full product of
universal graph ideals to the full concrete graph product on the coherent
base.  This is an exact ideal equality, not merely equality of supports.
It is the algebraic half of the remaining geometric localization theorem. -/
theorem orderedAmbientCoordinateHom_map_orderedGraphIdeal
    (w : (assignedComponentProductOverGround K C d z V
      (Spec (.of T)) q).left) :
    Ideal.map (orderedAmbientCoordinateHom K C d z V T q r E hE w)
      (orderedGraphIdeal Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))) =
      evaluatedOrderedGraphIdeal K C d z V T q r E hE w := by
  classical
  rw [orderedGraphIdeal, ideal_map_fintype_prod,
    evaluatedOrderedGraphIdeal]
  let e := positionEquivRootIndex K C d z V T q r E hE
    (productPoint K C d z V T q w)
  rw [← Equiv.prod_comp e (fun x ↦
    Ideal.map (orderedAmbientCoordinateHom K C d z V T q r E hE w)
      (rootGraphIdeal Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w)) x))]
  apply Fintype.prod_congr
  intro i
  exact orderedAmbientCoordinateHom_map_rootGraphIdeal
    K C d z V T q r E hE w i

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedRootCoordinates
